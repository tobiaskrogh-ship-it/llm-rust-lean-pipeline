"""Run pipeline.py on every Rust crate in a folder, sequentially.

Discovers subdirectories that look like Rust crates (have a `Cargo.toml`,
aren't `_modified` working copies) and runs the full pipeline on each.
By default, skips crates whose `_modified` copy already has a closed
obligations file (no `sorry`).

Source crates live under `benchmarks/code/<parent>/<crate>/`. The per-model
`_modified` working copies live under `benchmarks/<MODEL_NAME>/<parent>/
<crate>_modified/` — the same convention pipeline.py uses. The CLAUDE_MODEL
env var selects which model's `_modified` tree this script consults for the
skip-if-already-closed check (default "claude-opus-4-7").

Usage:
  python run_batch.py <folder> [--force]

Examples:
  python run_batch.py benchmarks/code/num-integer-0.1.46
  python run_batch.py benchmarks/code/num-integer-0.1.46 --force
"""

import argparse
import os
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PIPELINE = ROOT / "pipeline.py"
BENCHMARKS_DIR = ROOT / "benchmarks"
CODE_DIR = BENCHMARKS_DIR / "code"
MODEL_NAME = os.getenv("CLAUDE_MODEL", "claude-opus-4-7")
MODEL_DIR = BENCHMARKS_DIR / MODEL_NAME


def working_crate_for(source_crate: Path) -> Path | None:
    """Map a source crate path under `benchmarks/code/` to its per-model
    working `_modified` path under `benchmarks/<MODEL_NAME>/`. Returns None
    if the source isn't under `benchmarks/code/` (caller should error
    appropriately)."""
    try:
        rel = source_crate.relative_to(CODE_DIR)
    except ValueError:
        return None
    return MODEL_DIR / rel.parent / (source_crate.name + "_modified")


def discover_crates(folder: Path) -> list[Path]:
    """Subdirectories with a Cargo.toml, excluding `_modified` working copies."""
    crates = []
    for entry in sorted(folder.iterdir()):
        if not entry.is_dir():
            continue
        if entry.name.endswith("_modified"):
            continue
        if not (entry / "Cargo.toml").exists():
            continue
        crates.append(entry)
    return crates


def _strip_lean_comments(text: str) -> str:
    """Remove `--` line comments and `/- ... -/` block comments (nestable).

    The boilerplate header of every obligations file mentions `sorry` inside
    a `--` comment, which fooled the naive `\\bsorry\\b` scan."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    while i < n:
        c = text[i]
        if block_depth > 0:
            if c == '/' and i + 1 < n and text[i + 1] == '-':
                block_depth += 1
                i += 2
                continue
            if c == '-' and i + 1 < n and text[i + 1] == '/':
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            if c == '\\' and i + 1 < n:
                out.append(c)
                out.append(text[i + 1])
                i += 2
                continue
            if c == '"':
                in_string = False
            out.append(c)
            i += 1
            continue
        if c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if c == '-' and i + 1 < n and text[i + 1] == '-':
            while i < n and text[i] != '\n':
                i += 1
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '-':
            block_depth = 1
            i += 2
            continue
        out.append(c)
        i += 1
    return ''.join(out)


def is_completed(crate: Path) -> bool:
    """A crate is considered already verified if its `_modified` copy under
    `benchmarks/<MODEL_NAME>/` has an obligations file with no remaining
    `sorry` outside of comments. Comments are stripped before the scan so
    the file-level boilerplate header doesn't cause false negatives."""
    modified = working_crate_for(crate)
    if modified is None or not modified.is_dir():
        return False
    extraction = modified / "proofs" / "lean" / "extraction"
    if not extraction.is_dir():
        return False
    obligs = [
        p for p in extraction.glob("*Obligations.lean")
        if ".lake" not in p.parts
    ]
    if not obligs:
        return False
    for oblig in obligs:
        text = oblig.read_text(encoding="utf-8", errors="ignore")
        if re.search(r"\bsorry\b", _strip_lean_comments(text)):
            return False
    return True


def display_path(p: Path) -> str:
    try:
        return str(p.relative_to(ROOT))
    except ValueError:
        return str(p)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "folder",
        help="Folder under benchmarks/code/ containing Rust crate subdirectories "
             "(e.g. benchmarks/code/num-integer-0.1.46)",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Re-run pipeline even on crates whose modified copy is already closed",
    )
    parser.add_argument(
        "--no-harvest",
        action="store_true",
        help="Pass --no-harvest to pipeline.py: skip the pattern-harvest stages so "
             "the shared libraries stay frozen (use when benchmarking models head-to-head)",
    )
    args = parser.parse_args()

    folder = Path(args.folder).resolve()
    if not folder.is_dir():
        print(f"Folder not found: {args.folder}", file=sys.stderr)
        return 2

    crates = discover_crates(folder)
    if not crates:
        print(f"No Rust crates found in {args.folder}", file=sys.stderr)
        return 1

    print(f"Folder:        {display_path(folder)}/")
    print(f"Model:         {MODEL_NAME}  (working copies under benchmarks/{MODEL_NAME}/)")
    print(f"Discovered {len(crates)} crate(s):")
    for c in crates:
        marker = "  (completed)" if (not args.force and is_completed(c)) else ""
        print(f"  - {c.name}{marker}")
    print(f"Force re-run:  {args.force}")
    print(f"Harvest:       {'disabled (--no-harvest, libraries frozen)' if args.no_harvest else 'enabled'}")

    started_at = datetime.now()
    results: list[tuple[Path, str, int | None]] = []
    interrupted = False

    try:
        for c in crates:
            if not args.force and is_completed(c):
                print(f"\n[skip] {c.name} — already verified (no sorries in obligations)")
                results.append((c, "skip-completed", 0))
                continue

            print(f"\n{'=' * 70}")
            print(f"Running pipeline on  {display_path(c)}")
            print(f"{'=' * 70}")

            cmd = [sys.executable, str(PIPELINE), str(c)]
            if args.no_harvest:
                cmd.append("--no-harvest")
            try:
                result = subprocess.run(cmd, check=False)
                status = "pass" if result.returncode == 0 else "fail"
                results.append((c, status, result.returncode))
            except FileNotFoundError as exc:
                print(f"  [error] could not invoke pipeline: {exc}", file=sys.stderr)
                results.append((c, "error", None))
    except KeyboardInterrupt:
        print(f"\n[interrupted]")
        interrupted = True

    # Aggregate report
    pass_n = sum(1 for _, s, _ in results if s == "pass")
    fail_n = sum(1 for _, s, _ in results if s == "fail")
    skip_n = sum(1 for _, s, _ in results if s == "skip-completed")
    err_n = sum(1 for _, s, _ in results if s == "error")
    not_run = len(crates) - len(results)

    elapsed = datetime.now() - started_at
    print(f"\n{'=' * 70}")
    print(f"Aggregate report  (elapsed: {elapsed})")
    print(f"{'=' * 70}")
    for c, status, code in results:
        symbol = {"pass": "✓", "fail": "✗", "skip-completed": "·", "error": "!"}.get(status, "?")
        rc = f" rc={code}" if code is not None and status == "fail" else ""
        print(f"  {symbol}  {status:<15}  {c.name}{rc}")
    if interrupted and not_run > 0:
        print(f"  …  not-run         {not_run} crate(s) (interrupted)")
    print()
    print(f"  pass: {pass_n}  /  fail: {fail_n}  /  skip: {skip_n}  /  errors: {err_n}  /  total considered: {len(crates)}")

    return 1 if fail_n + err_n > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
