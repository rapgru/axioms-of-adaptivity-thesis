#!/usr/bin/env bash

set -euo pipefail

# Ensure local Verso patch is applied to cloned package before building docs
if [ -x scripts/patch_verso.sh ]; then
	echo "Applying local Verso patch..."
	scripts/patch_verso.sh
else
	echo "No patch script found or not executable; skipping patch step."
fi

lake exe docs
python3 serve.py