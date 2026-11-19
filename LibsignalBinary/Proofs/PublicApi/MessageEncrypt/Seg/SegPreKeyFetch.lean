/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
import ProofLib.GenDecodes
public import ProofLib.ProgramReflection.SortedFresh

/-!
# Instruction Decode and Fetch Lemmas for `segPreKey_ok`

Kernel-checked decode lemmas and fetch tactics across the `segPreKey` code ranges (`+0x344..+0x390`,
`+0x680..+0x730`, `+0x78c..+0x7ec`, and `+0x880..+0xa70`) of `session_message_encrypt_with_stores`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi

open Lean Elab Tactic in
elab "messageEncryptPreKey_code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
