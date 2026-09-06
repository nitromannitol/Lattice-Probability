#!/usr/bin/env bash
# Push the library to its private GitHub repository through the sandbox host,
# which holds the credential.  The local machine never sees a token.
set -euo pipefail
cd ~/Lattice-Probability
[ -z "$(git status --porcelain)" ] || { echo "working tree dirty; commit first"; exit 1; }
rsync -a --delete --exclude .lake --exclude scratch --exclude __pycache__ \
  ~/Lattice-Probability/ sandbox:~/Lattice-Probability/
ssh -o BatchMode=yes sandbox 'cd ~/Lattice-Probability && git push origin main 2>&1 | tail -2'
