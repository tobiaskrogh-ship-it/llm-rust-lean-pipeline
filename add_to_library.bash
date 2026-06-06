#!/usr/bin/env bash
#
# Promote a verified crate into the proof_patterns library.
# Usage: ./add_to_library.bash <source-path> [--force]
#
# Copies <source-path>/ to proof_patterns/<basename>/, preserving the source
# directory name verbatim (including any trailing '_modified' suffix).
# Keeping the suffix makes it easy to spot when an unmodified crate was
# accidentally promoted — its example dir will be named `<crate>` rather
# than `<crate>_modified`. Drops build artifacts and writes a placeholder
# manifest. Warns if the obligations file still contains `sorry`.

set -euo pipefail

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
    echo "Usage: $0 <source-path> [--force]" >&2
    echo "  e.g. $0 benchmarks/claude-opus-4-7/starting_examples/add_one_modified" >&2
    exit 1
fi

SRC_INPUT="$1"
FORCE=""
if [ $# -eq 2 ]; then
    if [ "$2" != "--force" ]; then
        echo "Error: unknown flag '$2' (only --force is supported)" >&2
        exit 1
    fi
    FORCE="1"
fi

if [ ! -d "$SRC_INPUT" ]; then
    echo "Error: source directory not found: $SRC_INPUT" >&2
    exit 1
fi

# Resolve to an absolute path so subsequent operations are unambiguous.
SRC="$(cd "$SRC_INPUT" && pwd)"

ROOT="$(cd "$(dirname "$0")" && pwd)"
PROOF_PATTERNS_DIR="$ROOT/proof_patterns"

# Destination name = source basename verbatim (including any _modified suffix).
NAME="$(basename "$SRC")"
DEST="$PROOF_PATTERNS_DIR/$NAME"

if [ -e "$DEST" ]; then
    if [ -z "$FORCE" ]; then
        echo "Error: $DEST already exists. Re-run with --force to overwrite." >&2
        exit 1
    fi
    echo "Overwriting existing $DEST."
    rm -rf "$DEST"
fi

mkdir -p "$PROOF_PATTERNS_DIR"

echo "Copying $SRC -> $DEST"
cp -R "$SRC" "$DEST"

# Strip build artifacts so the library stays small and reproducible.
rm -rf "$DEST/target"
rm -rf "$DEST/proofs/lean/extraction/.lake"
rm -f  "$DEST/proofs/lean/extraction/lake-manifest.json"
rm -f  "$DEST/Cargo.lock"

# Warn if the obligations file still has open proofs. We strip `--` line
# comments before scanning so the file-level boilerplate (which mentions
# `sorry`) doesn't trigger a false warning.
OBLIG_GLOB=("$DEST"/proofs/lean/extraction/*Obligations.lean)
if [ -e "${OBLIG_GLOB[0]}" ]; then
    OBLIG="${OBLIG_GLOB[0]}"
    SORRY_HITS="$(sed 's|--.*||' "$OBLIG" | grep -nE '\bsorry\b' || true)"
    if [ -n "$SORRY_HITS" ]; then
        echo
        echo "WARNING: $OBLIG still contains 'sorry' outside comments. Library entries should have closed proofs." >&2
        echo "$SORRY_HITS" >&2
    fi
else
    echo "WARNING: no *Obligations.lean found under $DEST/proofs/lean/extraction/" >&2
fi

# Drop a placeholder manifest. Fill in by running the manifest-generation skill.
MANIFEST="$DEST/manifest.json"
if [ ! -f "$MANIFEST" ]; then
    cat > "$MANIFEST" <<'EOF'
{
  "features": [],
  "summary": "TODO: fill in by running the manifest-generation skill"
}
EOF
    echo "Wrote placeholder $MANIFEST"
else
    echo "Kept existing $MANIFEST"
fi

echo
echo "Done. Library entry at $DEST"
echo "Next: run the manifest-generation skill to populate features + summary."
