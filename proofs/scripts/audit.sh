#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

theorems=theorems.txt
scratch=.lake/Axioms.lean
trap 'rm -f "$scratch"' EXIT
trap 'exit 1' INT TERM

if [[ ! -f "$theorems" ]]; then
  printf '%s\n' "audit: missing $theorems" >&2
  exit 1
fi

names=()
while IFS= read -r line; do
  line="${line%$'\r'}"
  [[ -z "${line// }" ]] && continue
  names+=("$line")
done < "$theorems"

if [[ ${#names[@]} -eq 0 ]]; then
  printf '%s\n' "audit: $theorems lists no theorem" >&2
  exit 1
fi

mkdir -p .lake
{
  printf '%s\n' 'import ElegantGeometry' 'import Elegant' ''
  for n in "${names[@]}"; do
    printf '#print axioms %s\n' "$n"
  done
} > "$scratch"

failed=0

if ! out="$(lake env lean "$scratch" 2>&1)"; then
  printf '%s\n' "$out" >&2
  printf '%s\n' 'audit: the axioms scratch file failed to elaborate; a listed theorem name may not exist' >&2
  exit 1
fi

flat="$(tr '\n' ' ' <<< "$out")"

for n in "${names[@]}"; do
  if ! grep -qF -e "'$n' depends on axioms:" -e "'$n' does not depend on any axioms" <<< "$flat"; then
    printf '%s\n' "audit: no axiom report for $n" >&2
    failed=1
  fi
done

while IFS= read -r report; do
  [[ -z "$report" ]] && continue
  list="${report#*\[}"
  list="${list%\]}"
  IFS=',' read -r -a axs <<< "$list"
  for a in "${axs[@]}"; do
    a="${a// /}"
    [[ -z "$a" ]] && continue
    case "$a" in
      propext|Classical.choice|Quot.sound) ;;
      *)
        printf '%s\n' "audit: forbidden axiom $a in: $report" >&2
        failed=1
        ;;
    esac
  done
done < <(grep -oE "'[^']+' depends on axioms: \[[^]]*\]" <<< "$flat" || true)

pattern='sorry|partial def|\bunsafe\b|implemented_by|\bextern\b|native_decide|^axiom'
forbidden=0
while IFS= read -r f; do
  case "$f" in
    Elegant/Gen/*) hits="$(sed -E 's/"([^"\\]|\\.)*"//g' "$f" | grep -nE "$pattern" || true)" ;;
    *) hits="$(grep -nE "$pattern" "$f" || true)" ;;
  esac
  if [[ -n "$hits" ]]; then
    printf '%s\n' "audit: forbidden construct in $f" >&2
    printf '%s\n' "$hits" >&2
    forbidden=$((forbidden + $(grep -c '' <<< "$hits")))
    failed=1
  fi
done < <(find ElegantGeometry Elegant -name '*.lean' -type f 2>/dev/null | sort)

printf 'theorems checked: %d\n' "${#names[@]}"
printf 'forbidden constructs: %d\n' "$forbidden"

exit "$failed"
