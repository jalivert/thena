#!/bin/sh
# Build the Haddock API documentation and put it at a stable path.
#
# 'cabal haddock' writes into dist-newstyle under a path that names the
# architecture, the GHC version and the package version, so it moves whenever
# any of those does. Every link in docs/*.md points at docs/api/, and this
# script is what makes that path exist.
#
#   --haddock-hyperlinked-source  every entity gets a "Source" link, and on the
#                                 source page every identifier is itself a link,
#                                 across modules and into unexported helpers.
#   --haddock-quickjump           the 'S' key search overlay.
#
# Usage:  sh docs/build-api.sh        (from the repository root)
set -e

cd "$(dirname "$0")/.."

cabal haddock --haddock-hyperlinked-source --haddock-quickjump

# 'cabal haddock' prints the directory it wrote as its last line; ask it rather
# than reconstructing the path.
built=$(cabal haddock --haddock-hyperlinked-source --haddock-quickjump 2>/dev/null | tail -1)

if [ ! -d "$built" ]; then
  echo "docs/build-api.sh: could not find the generated documentation" >&2
  echo "  cabal reported: $built" >&2
  exit 1
fi

rm -rf docs/api
mkdir -p docs/api
cp -R "$built"/. docs/api/

echo
echo "API documentation at docs/api/index.html"
