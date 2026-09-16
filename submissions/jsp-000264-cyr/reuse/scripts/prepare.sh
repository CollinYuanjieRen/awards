#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 NEW_DIRECTORY" >&2
  exit 64
fi

bundle_dir="$(cd "$(dirname "$0")/.." && pwd)"
destination="$1"

if [[ -e "$destination" ]]; then
  echo "destination must not exist: $destination" >&2
  exit 73
fi

plby_commit="8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
raw_base="https://raw.githubusercontent.com/plby/lean-proofs/${plby_commit}/src/latest"

mkdir -p "$destination"

while read -r expected relative_path; do
  [[ -n "$expected" && -n "$relative_path" ]] || continue
  target="$destination/$relative_path"
  mkdir -p "$(dirname "$target")"
  curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
    "$raw_base/$relative_path" --output "$target"
  actual="$(shasum -a 256 "$target" | awk '{print $1}')"
  if [[ "$actual" != "$expected" ]]; then
    echo "SHA-256 mismatch for $relative_path" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 65
  fi
done < "$bundle_dir/sources.sha256"

cp "$destination/ErdosProblems/Erdos318.lean" \
  "$destination/ErdosProblems/Erdos318Reused.lean"

python3 - "$destination/ErdosProblems/Erdos318Reused.lean" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
source = path.read_text()
old = "erdos_318.variants.infinite_AP"
new = "erdos_318.variants.infinite_AP_reused"
if source.count(old) != 4:
    raise SystemExit(f"expected exactly four AP endpoint occurrences, found {source.count(old)}")
path.write_text(source.replace(old, new))
PY

renamed_sha="$(shasum -a 256 "$destination/ErdosProblems/Erdos318Reused.lean" | awk '{print $1}')"
expected_renamed_sha="0a63fcc4a5a0e90c587f6007b3db1245ce75c2782a426c8f353038829b271137"
if [[ "$renamed_sha" != "$expected_renamed_sha" ]]; then
  echo "renamed source SHA-256 mismatch" >&2
  exit 65
fi

cp "$bundle_dir/ErdosProblems/Erdos318Canonical.lean" \
  "$destination/ErdosProblems/Erdos318Canonical.lean"
cp "$bundle_dir/ErdosProblems/FormalConjecturesAP.lean" \
  "$destination/ErdosProblems/FormalConjecturesAP.lean"
cp "$bundle_dir/lakefile.toml" "$bundle_dir/lake-manifest.json" \
  "$bundle_dir/lean-toolchain" "$destination/"

echo "Prepared $destination"
echo "Verified 12 pinned plby sources and the four-occurrence AP rename."
