#!/bin/sh
# Certify the typing of every example and test program (roadmap 6b):
# `boltcore --cert` prints a certificate, the Lean checker
# (`lake exe boltcore-check`) verifies it. Programs come from examples/*.sub,
# the `-e` programs of test/*.t (except --rectypes ones: the Lean development
# has no recursive types) and test/certs.txt. Items with type errors are left
# out of a certificate. Exit status 1 if a certificate is rejected, other
# than the known rejections below.
#
# Usage: scripts/check-certs.sh [-v]   (-v: print each result)
set -eu
cd "$(dirname "$0")/.."
verbose=${1:-}

# Known rejections, with the reason (none at the moment).
known() {
  case "$1" in
    *) return 1 ;;
  esac
}

dune build 2>&1
(cd lean && lake build boltcore-check >/dev/null)
boltcore=_build/default/bin/main.exe
check=lean/.lake/build/bin/boltcore-check
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# One program per line in $tmp/programs; files are named, inline ones given.
for f in examples/*.sub; do echo "file $f"; done > "$tmp/programs"
sed -n "s/^  \$ boltcore \(--raw \|--self-check \)*-e '\([^']*\)'.*/expr \2/p" test/*.t >> "$tmp/programs"
grep -v '^#' test/certs.txt | grep . | sed 's/^/expr /' >> "$tmp/programs"

accepted=0 partial=0 rejected=0 known_rej=0 skipped=0 n=0
while IFS= read -r line; do
  n=$((n + 1))
  kind=${line%% *} prog=${line#* }
  cert="$tmp/$n.json"
  if [ "$kind" = file ]; then name=$prog; set -- "$prog"; else name="-e '$prog'"; set -- -e "$prog"; fi
  out=$("$boltcore" --cert "$cert" "$@" 2>&1 || true)
  if [ ! -f "$cert" ]; then  # a parse error (some tests are)
    skipped=$((skipped + 1))
    [ -z "$verbose" ] || echo "skipped, does not parse: $name"
    continue
  fi
  errors=$(printf '%s\n' "$out" | grep -c 'type error' || true)
  if res=$("$check" "$cert" 2>&1); then
    if [ "$errors" -gt 0 ]; then
      partial=$((partial + 1))
      [ -z "$verbose" ] || echo "accepted, $errors item(s) with type errors left out: $name"
    else
      accepted=$((accepted + 1))
      [ -z "$verbose" ] || echo "accepted: $name"
    fi
  elif reason=$(known "$name"); then
    known_rej=$((known_rej + 1))
    echo "rejected (known: $reason): $name"
  else
    rejected=$((rejected + 1))
    echo "REJECTED: $name"
    printf '%s\n' "$res" | sed "s|$cert|certificate|; s/^/  /"
  fi
done < "$tmp/programs"

echo "$n programs: $accepted accepted, $partial accepted without their ill-typed items," \
  "$known_rej known rejections, $rejected rejected, $skipped skipped (parse errors)"
[ "$rejected" -eq 0 ]
