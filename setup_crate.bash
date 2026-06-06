#!/usr/bin/env bash
#
# Set up Hax + Lean extraction infrastructure for an existing Rust crate.
# Usage: ./setup_crate.bash <path-to-crate>

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: $0 <path-to-crate>" >&2
    echo "  e.g. $0 ./square" >&2
    exit 1
fi

CRATE_DIR="$1"

if [ ! -d "$CRATE_DIR" ]; then
    echo "Error: $CRATE_DIR is not a directory" >&2
    exit 1
fi

if [ ! -f "$CRATE_DIR/Cargo.toml" ]; then
    echo "Error: $CRATE_DIR/Cargo.toml not found — is this a Rust crate?" >&2
    exit 1
fi

# Parse the [package] name field out of Cargo.toml.
CRATE_NAME=$(awk '
    /^\[package\]/ { in_pkg = 1; next }
    /^\[/         { in_pkg = 0 }
    in_pkg && /^[[:space:]]*name[[:space:]]*=/ {
        match($0, /"[^"]+"/)
        if (RLENGTH > 0) {
            print substr($0, RSTART + 1, RLENGTH - 2)
            exit
        }
    }
' "$CRATE_DIR/Cargo.toml")

if [ -z "$CRATE_NAME" ]; then
    echo "Error: could not parse the [package] name from $CRATE_DIR/Cargo.toml" >&2
    exit 1
fi

echo "Crate name: $CRATE_NAME"
echo "Target dir: $CRATE_DIR"

cd "$CRATE_DIR"

# Add the hax-lib dependency (no-op if already present).
cargo add hax-lib

mkdir -p proofs/lean/extraction

cat > proofs/lean/extraction/lakefile.toml <<EOF
name = "$CRATE_NAME"
version = "0.1.0"
defaultTargets = ["$CRATE_NAME"]

[[lean_lib]]
name = "$CRATE_NAME"

[[require]]
name = "Hax"
git.url = "https://github.com/cryspen/hax"
git.subDir = "hax-lib/proof-libs/lean"
rev = "main"
EOF

echo "leanprover/lean4:v4.29.0-rc1" > proofs/lean/extraction/lean-toolchain

echo
echo "Done. Wrote:"
echo "  $CRATE_DIR/proofs/lean/extraction/lakefile.toml"
echo "  $CRATE_DIR/proofs/lean/extraction/lean-toolchain"
echo "  hax-lib added to $CRATE_DIR/Cargo.toml"
