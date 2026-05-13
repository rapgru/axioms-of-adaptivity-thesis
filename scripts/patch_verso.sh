#!/usr/bin/env bash
set -euo pipefail
# Apply local fixes to the cloned Verso package inside .lake/packages/verso
# This script is idempotent and will print status.

PKG_DIR=".lake/packages/verso"
if [ ! -d "$PKG_DIR" ]; then
  echo "Verso package not found at $PKG_DIR; run 'lake update' first." >&2
  exit 1
fi

TARGET="$PKG_DIR/src/verso-manual/VersoManual/Bibliography.lean"
if [ ! -f "$TARGET" ]; then
  echo "Target file not found: $TARGET" >&2
  exit 1
fi

echo "Applying et al. spacing fix to $TARGET"

# Use Python for robust inplace editing
python3 - "$TARGET" <<'PY'
import sys, re
fn = sys.argv[1]
with open(fn, 'r', encoding='utf-8') as f:
    s = f.read()

# HTML form: replace exact snippet
s = s.replace('(· ++ {{<em>"et al"</em>}}) <$> go (Bibliography.lastName p.authors[0])',
              '(· ++ {{" "<em>"et al."</em>}}) <$> go (Bibliography.lastName p.authors[0])')

# TeX form: replace common pattern \TeX{\em{"et al"} } with \TeX{" " \em{"et al."} }
def _repl_tex(m):
  return '\\TeX{" " \\em{"et al."} }'
s = re.sub(r"\\TeX\{\\em\{\"et al\"\}\s*\}", _repl_tex, s)

with open(fn, 'w', encoding='utf-8') as f:
    f.write(s)
print('patched')
PY

echo "Patch applied." 
