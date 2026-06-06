#!/usr/bin/env python3
"""Per-folder breakdown of unclosed proof obligations across
benchmarks/<model>/<folder>/<crate>_modified/proofs/lean/extraction/*Obligations.lean.

The "sorry count" is one per unclosed public obligation — a public
theorem/lemma whose proof is not transitively sorry-free.  A public
obligation counts as one sorry if its own body OR any decl reachable
through name references (private helpers, definitions, …) contains a
real sorry.  Sorries that live only inside private decls add nothing
to the count directly; they bite only when a public theorem actually
relies on them.

Comments (block /- … -/ and line -- …) are stripped before counting.
Per-crate output also shows the closure rate — closed / total public
obligations.

Usage:
    python sorry_report.py                # default model: claude-opus-4-7
    python sorry_report.py MODEL
    python sorry_report.py --root benchmarks --model claude-opus-4-7
"""
import argparse
import re
import sys
from pathlib import Path

BLOCK = re.compile(r"/-.*?-/", re.DOTALL)        # /- ... -/ and /-! ... -/
LINE  = re.compile(r"--.*")                       # Lean line comments
SORRY = re.compile(r"\bsorry\b")

# Top-level declaration header. name is optional so anonymous examples
# still get a position; they get a synthetic name and are never live.
DECL = re.compile(
    r"^(?P<priv>private\s+)?"
    r"(?:(?:noncomputable|partial|unsafe|protected)\s+)*"
    r"(?P<kind>theorem|lemma|example|def|instance|abbrev)"
    r"(?:\s+(?P<name>[a-zA-Z_][\w.']*))?",
    re.MULTILINE,
)

# Kinds whose surviving sorrys represent unfinished proof obligations.
THM_KINDS = {"theorem", "lemma"}


def strip_comments(src: str) -> str:
    src = BLOCK.sub("", src)
    return "\n".join(LINE.sub("", l) for l in src.splitlines())


def parse_decls(stripped: str):
    """Return list of (is_private, kind, name, body) for every top-level decl.

    Anonymous examples get synthetic names so they can't be referenced.
    """
    ms = list(DECL.finditer(stripped))
    out = []
    for i, m in enumerate(ms):
        body_end = ms[i + 1].start() if i + 1 < len(ms) else len(stripped)
        name = m.group("name") or f"__anon_{i}"
        out.append((bool(m.group("priv")), m.group("kind"), name, stripped[m.end():body_end]))
    return out


def build_deps(decls):
    """Edges: i → j  iff j's name appears as an identifier in i's body."""
    name_to_idx = {d[2]: i for i, d in enumerate(decls)
                   if not d[2].startswith("_anon")}
    deps: dict[int, set[int]] = {i: set() for i in range(len(decls))}
    for i, (_, _, _, body) in enumerate(decls):
        for name, j in name_to_idx.items():
            if i == j:
                continue
            if re.search(r"\b" + re.escape(name) + r"\b", body):
                deps[i].add(j)
    return deps


def count_in_file(path: Path) -> tuple[int, int, int]:
    """Returns (unclosed_obligations, closed_obligations, total_obligations).

    An "obligation" is a public theorem/lemma.  It's closed iff neither
    its own body nor any transitively-referenced decl contains a real
    sorry.  Private theorem sorries never count toward the tally
    directly — they only matter when a public theorem actually depends
    on them, in which case the public theorem itself counts as one open
    obligation regardless of how many private sorries it pulls in.
    """
    stripped = strip_comments(path.read_text())
    decls = parse_decls(stripped)
    deps = build_deps(decls)
    has_sorry_direct = [bool(SORRY.search(d[3])) for d in decls]

    def transitively_unclosed(root: int) -> bool:
        seen: set[int] = set()
        stack = [root]
        while stack:
            i = stack.pop()
            if i in seen:
                continue
            seen.add(i)
            if has_sorry_direct[i]:
                return True
            stack.extend(deps[i])
        return False

    publics = [i for i, d in enumerate(decls) if d[1] in THM_KINDS and not d[0]]
    unclosed = sum(1 for i in publics if transitively_unclosed(i))
    return unclosed, len(publics) - unclosed, len(publics)


def fmt_closure(closed: int, total: int) -> str:
    if total == 0:
        return "no live theorems"
    pct = round(100 * closed / total)
    return f"{closed}/{total} closed, {pct}%"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("model", nargs="?", default="claude-opus-4-7",
                    help="model directory under <root>/ (default: claude-opus-4-7)")
    ap.add_argument("--root", default="benchmarks",
                    help="benchmarks root (default: benchmarks)")
    args = ap.parse_args()

    base = Path(args.root) / args.model
    if not base.is_dir():
        print(f"error: not a directory: {base}", file=sys.stderr)
        return 2

    # rows: folder -> list[(sorries, closed, total, crate)]
    by_folder: dict[str, list[tuple[int, int, int, str]]] = {}
    for f in base.glob("*/*/proofs/lean/extraction/*Obligations.lean"):
        folder, crate = f.relative_to(base).parts[0:2]
        s, c, t = count_in_file(f)
        by_folder.setdefault(folder, []).append((s, c, t, crate))

    if not by_folder:
        print(f"no Obligations files found under {base}")
        return 0

    folders = sorted(by_folder.items(),
                     key=lambda kv: (-sum(n for n, _, _, _ in kv[1]), kv[0]))
    grand_sorries = 0
    grand_crates = 0
    grand_with = 0
    grand_closed = 0
    grand_total_thms = 0
    clean_folders: list[tuple[str, int, int, int]] = []  # (folder, files, closed, total)

    for folder, items in folders:
        items.sort(reverse=True)
        sum_sorry = sum(n for n, _, _, _ in items)
        files = len(items)
        with_sorry = sum(1 for n, _, _, _ in items if n > 0)
        folder_closed = sum(c for _, c, _, _ in items)
        folder_total = sum(t for _, _, t, _ in items)
        grand_sorries += sum_sorry
        grand_crates += files
        grand_with += with_sorry
        grand_closed += folder_closed
        grand_total_thms += folder_total
        if sum_sorry == 0:
            clean_folders.append((folder, files, folder_closed, folder_total))
            continue
        print(f"\n=== {folder}  —  {sum_sorry} sorries across {with_sorry}/{files} crates  "
              f"({fmt_closure(folder_closed, folder_total)}) ===")
        for n, c, t, crate in items:
            if n == 0:
                continue
            print(f"  {n:>3}  {crate}  ({fmt_closure(c, t)})")

    if clean_folders:
        print("\n=== fully clean folders ===")
        for folder, files, c, t in sorted(clean_folders):
            print(f"     {folder}  ({files} crates, {fmt_closure(c, t)})")

    print(f"\n--- totals ---")
    print(f"  {grand_sorries} real sorries across "
          f"{grand_with}/{grand_crates} crates in {len(folders)} folder(s)")
    print(f"  overall closure: {fmt_closure(grand_closed, grand_total_thms)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())