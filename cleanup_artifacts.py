"""Recursively delete cargo/lake build artifacts.

Removes everything that `cargo build` and `lake build` regenerate on demand:
  - `target/` directories
  - `proofs/lean/extraction/.lake/` directories
  - `proofs/lean/extraction/lake-manifest.json` files

Leaves source files, `Cargo.toml`, `Cargo.lock`, and proof `.lean` files alone.

Usage:
  python cleanup_artifacts.py [path] [--dry-run]

  path       Directory to scan (default: the project root containing this
             script). The walker descends into every subdirectory.
  --dry-run  Report what would be deleted without actually deleting.

Examples:
  python cleanup_artifacts.py                       # clean entire repo
  python cleanup_artifacts.py benchmarks            # clean only benchmarks/
  python cleanup_artifacts.py benchmarks --dry-run  # preview
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

# Top-level directory names that are pruned when found.
PRUNE_DIRS = {"target", ".lake"}
# File names that are deleted when found at any depth (typically the
# top-level lake-manifest, but the recursive walk catches nested ones too —
# any nested manifest sits inside a `.lake/` we've already pruned).
PRUNE_FILES = {"lake-manifest.json"}


def dir_size(path: Path) -> int:
    total = 0
    for entry in path.rglob("*"):
        try:
            if entry.is_file() and not entry.is_symlink():
                total += entry.stat().st_size
        except OSError:
            pass
    return total


def human_bytes(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.1f}{unit}"
        n /= 1024
    return f"{n:.1f}TB"


def scan(root: Path) -> tuple[list[Path], list[Path]]:
    """Return (dirs_to_prune, files_to_prune) under `root`. Pruned dirs are
    not descended into, so artifacts nested inside (e.g. nested target/s
    under cargo's deps) are removed wholesale with their parent."""
    dirs_out: list[Path] = []
    files_out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        # Identify dirs to prune at this level and remove them from
        # `dirnames` so os.walk doesn't descend further into them.
        kept: list[str] = []
        for d in dirnames:
            if d in PRUNE_DIRS:
                dirs_out.append(Path(dirpath) / d)
            else:
                kept.append(d)
        dirnames[:] = kept
        for f in filenames:
            if f in PRUNE_FILES:
                files_out.append(Path(dirpath) / f)
    return dirs_out, files_out


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=str(ROOT),
        help="Directory to scan (default: repo root).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Report what would be deleted without actually deleting.",
    )
    args = parser.parse_args()

    scan_root = Path(args.path).resolve()
    if not scan_root.is_dir():
        print(f"Not a directory: {scan_root}", file=sys.stderr)
        return 2

    dirs, files = scan(scan_root)

    total_bytes = 0
    for d in dirs:
        try:
            total_bytes += dir_size(d)
        except OSError:
            pass
    for f in files:
        try:
            total_bytes += f.stat().st_size
        except OSError:
            pass

    try:
        shown_root = scan_root.relative_to(ROOT)
    except ValueError:
        shown_root = scan_root

    print(f"Scanning {shown_root}/")
    print(f"  {len(dirs)} target/ or .lake/ directories")
    print(f"  {len(files)} lake-manifest.json files")
    print(f"  total: {human_bytes(total_bytes)}")

    if args.dry_run:
        print("\n[dry-run] no changes made. Listing first 20 matches:")
        for p in (dirs + files)[:20]:
            try:
                shown = p.relative_to(ROOT)
            except ValueError:
                shown = p
            print(f"  {shown}")
        return 0

    if not dirs and not files:
        print("Nothing to clean.")
        return 0

    failed = 0
    for path in dirs + files:
        try:
            subprocess.run(["rm", "-rf", str(path)], check=True)
        except subprocess.CalledProcessError as exc:
            print(f"  failed to remove {path}: {exc}", file=sys.stderr)
            failed += 1

    print(f"\nFreed {human_bytes(total_bytes)}.")
    if failed:
        print(f"({failed} path(s) failed to delete.)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
