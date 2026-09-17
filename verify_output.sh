#!/usr/bin/env bash
# Independently verify a translated Megalodon->Lean4 output directory.
#   ./verify_output.sh lean_v15
# Checks, for every .lean file: it compiles, has no errors, and contains no
# `sorry`. Then audits which axioms the theorems actually rest on -- a proof
# that secretly depends on `sorryAx` proves nothing, so that is failed loudly.
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
D="${1:-lean_v15}"

[ -d "$D" ] || { echo "no such directory: $D"; exit 2; }
command -v lean >/dev/null || { echo "lean not on PATH"; exit 2; }

echo "directory : $D"
echo "lean      : $(lean --version)"
echo

fail=0
total=0
seen=""
# Prelude first (everything else depends on it), then the rest once each
for f in "$D"/Prelude.lean "$D"/All.lean "$D"/*.lean; do
  [ -f "$f" ] || continue
  case " $seen " in *" $f "*) continue;; esac
  seen="$seen $f"
  printf '%-22s ' "$(basename "$f")"
  n=$(grep -c '^theorem ' "$f")
  s=$(grep -c '\bsorry\b' "$f")
  # in-file `set_option maxErrors` is ignored by lean; it must be passed with -D
  if out=$(lean -D maxErrors=20000 "$f" 2>&1) && [ "$s" -eq 0 ]; then
    echo "PASS   theorems=$n  sorry=0"
  else
    echo "FAIL   theorems=$n  sorry=$s"
    printf '%s\n' "$out" | grep ': error' | head -5
    fail=1
  fi
  [ "$(basename "$f")" = "All.lean" ] && total=$n
done

echo
if [ -f "$D/All.lean" ]; then
  echo "axiom audit on All.lean ($total theorems)"
  tmp=$(mktemp -d)
  head -n -1 "$D/All.lean" > "$tmp/ax.lean"
  grep -o "^theorem [A-Za-z_][A-Za-z_0-9']*" "$D/All.lean" \
    | sed 's/^theorem /#print axioms /' >> "$tmp/ax.lean"
  echo "end Megalodon" >> "$tmp/ax.lean"
  axout=$(lean "$tmp/ax.lean" 2>&1)
  bad=$(printf '%s' "$axout" | grep -c sorryAx)
  free=$(printf '%s' "$axout" | grep -c 'does not depend on any axioms')
  echo "  sorryAx occurrences : $bad   (must be 0)"
  echo "  axiom-free theorems : $free"
  echo "  axioms used         :"
  printf '%s' "$axout" | grep 'depends on axioms' | sed 's/.*axioms: //' \
    | tr -d '[]' | tr ',' '\n' | sed 's/^ *//' | grep -v '^$' | sort -u | sed 's/^/    /'
  rm -rf "$tmp"
  [ "$bad" -ne 0 ] && fail=1
fi

echo
[ $fail -eq 0 ] && { echo "RESULT : PASS"; exit 0; } || { echo "RESULT : FAIL"; exit 1; }
