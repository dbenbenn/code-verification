/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Harness.ElfLoaderDiff

/-!
# Whole-Process ELF Loader Differential Harness

Standalone `elf_eval` CLI for differential testing of `Arm64.Process.ElfImage` loading and initial
process state construction against reference ELF snapshots (`--loader-diff`) and dumping loaded
ELF states (`--dump-load-state`).
-/

@[expose] public section

namespace Testing.ElfEval

open Testing.Harness

def parseHexArgs : List String → List String
  | "--hex" :: spec :: rest => spec :: parseHexArgs rest
  | _ :: rest => parseHexArgs rest
  | [] => []

def usage : String :=
  "usage: elf_eval (--loader-diff [<manifest.json> | <elf> <snap.json>] | " ++
  "--dump-load-state <elf> [<snap.json> [--hex <spec>]...])"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--loader-diff"] =>
    let cases ← Testing.ElfLoaderDiff.runDefaultElfLoaderDiffIO
    return (← runTestSuite cases)
  | ["--loader-diff", manifestPath] =>
    let cases ← Testing.ElfLoaderDiff.runManifestPathIO manifestPath
    return (← runTestSuite cases)
  | ["--loader-diff", elfPath, snapJsonPath] =>
    return (← Testing.ElfLoaderDiff.runSingleEntryDiffIO elfPath snapJsonPath)
  | ["--dump-load-state", elfPath] =>
    return (← Testing.ElfLoaderDiff.dumpLoadStateIO elfPath none [])
  | "--dump-load-state" :: elfPath :: snapJsonPath :: rest =>
    return (← Testing.ElfLoaderDiff.dumpLoadStateIO elfPath (some snapJsonPath) (parseHexArgs rest))
  | _ =>
    IO.eprintln usage
    return 1

end Testing.ElfEval

def main (args : List String) : IO UInt32 :=
  Testing.ElfEval.main args
