#!/usr/bin/env bash
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Runs `scripts/TrustedClosure.lean` after `lake build`; every argument is passed through to it
# (see its docstring: `--out-dir DIR`, `--symbolic`, `--headline ...`, `--headlines-file ...`).
# With `--lean-file FILE`, elaborates `FILE` under the same merged `Arm64` `LEAN_PATH`.
# It always runs from the repository root, so relative paths in the arguments are resolved against
# the repository root, not the caller's directory.
#
# Why a wrapper: `arm64-semantics` splits the `Arm64` module root between two Lake packages,
# `Arm64.Trusted.*` in its nested `arm64` package and `Arm64.Testing.*` in its nested
# `arm64-testing` package (`Arm64/Testing`). Lean's module search takes the first `LEAN_PATH` entry that has an `Arm64/`
# directory, so a plain `lake env lean --run scripts/TrustedClosure.lean` cannot find
# `Arm64.Testing.*`, which the statement files import (`LibsignalE2E/Machine.lean`). This script
# links both halves into one temporary directory and puts it first on `LEAN_PATH`
# (`Computational/docs/TRUSTED_BASE.md` §1).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

nested=arm64-semantics/Arm64/.lake/build/lib/lean # nested `arm64` package: `Arm64.Trusted.*`
engine=arm64-semantics/Arm64/Testing/.lake/build/lib/lean # nested `arm64-testing` package: `Arm64.Testing.*` (when built)
if [[ ! -d "$nested/Arm64" ]]; then
  echo "trusted-closure.sh: $nested/Arm64 does not exist; run \`lake build\` first" >&2
  exit 2
fi

merged=$(mktemp -d)
trap 'rm -rf "$merged"' EXIT
mkdir "$merged/Arm64"
shopt -s nullglob
for f in "$nested"/Arm64.*; do # top-level `Arm64.*` files, if the package has any
  ln -s "$PWD/$f" "$merged/"
done
for f in "$nested"/Arm64/* "$engine"/Arm64/*; do
  # `Symbolic/scripts/check_refinement_hygiene.sh` symlinks the engine's `Arm64/Testing` into the
  # nested half. Skip such a link, so the engine entry it points to is linked as usual.
  e="$engine/Arm64/$(basename "$f")"
  if [[ $f == "$nested"/* && -L $f && -e $e && $(realpath "$f") == "$(realpath "$e")" ]]; then
    continue
  fi
  # Without `-f`, `ln` fails if both halves have an entry of the same name.
  ln -s "$PWD/$f" "$merged/Arm64/" || {
    echo "trusted-closure.sh: both halves of \`Arm64\` contain $(basename "$f")" >&2
    exit 2
  }
done

export TRUSTED_CLOSURE_MERGED_ARM64="$merged"
if [[ ${1:-} == --lean-file ]]; then
  if [[ $# -lt 2 ]]; then
    echo "trusted-closure.sh: --lean-file requires a path argument" >&2
    exit 2
  fi
  export TRUSTED_CLOSURE_TARGET_FILE="$2"
  shift 2
  echo "[trusted-closure] lean argv: lean $* $TRUSTED_CLOSURE_TARGET_FILE" >&2
  lake env bash -c \
    'LEAN_PATH="$TRUSTED_CLOSURE_MERGED_ARM64:$LEAN_PATH" exec lean "$@" "$TRUSTED_CLOSURE_TARGET_FILE"' \
    trusted-closure "$@"
else
  lake env bash -c \
    'LEAN_PATH="$TRUSTED_CLOSURE_MERGED_ARM64:$LEAN_PATH" exec lean --run scripts/TrustedClosure.lean "$@"' \
    trusted-closure "$@"
fi
