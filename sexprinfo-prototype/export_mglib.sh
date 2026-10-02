#!/bin/bash
# Export every mgwiki mglib file's proof terms, chaining the index and
# owned-object state in dependency order.
#
# Two things Megalodon needs that are not in the .mg file itself:
#   * the `(** $I sig/X.mgs **)` comments are not read by Megalodon -- the
#     wiki's own wrapper turns them into `-I` flags, so we do the same;
#   * identifiers established by earlier files must be supplied as an
#     index (`-ind`) plus owned-object set (`-owned`), which earlier runs
#     emit with `-indout` / `-ownedout`.
MEG="$1"; OUT="$2"
# a checkout of https://github.com/mgwiki/mgw_test
WIKI="${MGWIKI:-$HOME/mgw_test}"
if [ -z "$MEG" ] || [ -z "$OUT" ]; then
  echo "usage: export_mglib.sh <patched-megalodon> <outdir>" >&2
  echo "       set MGWIKI if the wiki checkout is not at ~/mgw_test" >&2
  exit 2
fi
mkdir -p "$OUT"
IND="$OUT/cum.ind"; OWN="$OUT/cum.owned"
: > "$IND"; : > "$OWN"
cd "$WIKI"
ORDER="Part1 Part2 Part3 Part4 Part5 Part6 Part7 Part8 Part9 Part10 Part11 Part12 Part13 Part14"
EXTRA=$(ls mglib/*.mg | sed 's|mglib/||;s|\.mg$||' | grep -vxE 'Part[0-9]+')
for f in $ORDER $EXTRA; do
  src="mglib/$f.mg"
  [ -f "$src" ] || continue
  inc=$(grep -oE '^\(\*\*[[:space:]]+\$I[[:space:]]+\S+' "$src" | awk '{print "-I "$3}' | tr '\n' ' ')
  thy=$(grep -oE '^\(\*\*[[:space:]]+\$T[[:space:]]+\S+' "$src" | awk '{print "-"$3}' | tail -1)
  args=""
  [ -s "$IND" ] && args="$args -ind $IND"
  [ -s "$OWN" ] && args="$args -owned $OWN"
  start=$(date +%s)
  # Flag order matters: `-I` processes the signature file as soon as it is
  # parsed, so the index and owned set have to be loaded before it.
  timeout 1800 "$MEG" $thy $args $inc \
      -indout "$OUT/$f.ind" -ownedout "$OUT/$f.owned" \
      -sexprinfo "$src" > "$OUT/$f.sexpr" 2> "$OUT/$f.err"
  rc=$?; dur=$(( $(date +%s) - start ))
  thm=$(grep -c '^(THM' "$OUT/$f.sexpr" 2>/dev/null | head -1)
  prf=$(grep -c '^(PROOF' "$OUT/$f.sexpr" 2>/dev/null | head -1)
  fail=$(cat "$OUT/$f.sexpr" "$OUT/$f.err" 2>/dev/null | grep -m1 -i 'failure' | cut -c1-105)
  printf '%-45s rc=%-3s %4ss  THM=%-5s PROOF=%-5s %s\n' "$f" "$rc" "$dur" "$thm" "$prf" "$fail"
  # carry the state forward only if this file checked
  if [ "$rc" = "0" ]; then
    [ -s "$OUT/$f.ind" ]   && cat "$OUT/$f.ind"   >> "$IND"
    [ -s "$OUT/$f.owned" ] && cat "$OUT/$f.owned" >> "$OWN"
    sort -u "$IND" -o "$IND"; sort -u "$OWN" -o "$OWN"
  fi
done
