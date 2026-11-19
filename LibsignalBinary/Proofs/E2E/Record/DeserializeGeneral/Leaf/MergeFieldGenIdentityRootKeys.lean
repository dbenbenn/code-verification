/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeIdentityRootKeys -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Tags 2–4 Leaf (`mergeFieldGenIdentityRootKeys_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenIdentityRootKeys_ok` for `local_identity_public` (tag `2`, `@0`),
`remote_identity_public` (tag `3`, `@0x18`), and `root_key` (tag `4`, `@0x30`) via `bytes::merge`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys
  calleeSavedVRegs_setPC_pre_identityRootKeys
  calleeSavedVRegs_setMem_setPC_pre_identityRootKeys

/-! ## Tag 2/3/4 Field Helpers and `prostSSGAt` Decomposition -/

theorem genField_tag_234_cases {fl : GenField}
    (hP : fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) (hok : fl.Ok) :
    (∃ b, fl = .lik b ∧ b.length = 33) ∨
    (∃ b, fl = .rik b ∧ b.length = 33) ∨
    (∃ b, fl = .root b ∧ b.length = 32) := by
  cases fl <;> simp [GenField.tag, GenField.Ok] at hP hok ⊢ <;> exact hok

@[expose] def prostSSGRest_identityRootKeys (ss : BitVec 64) (v : SSG) : SepProp :=
  vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) v.recv ∗
    vecU8 A0 (ss + 0x60#64) [] ∗ vecU8 A0 (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A0 (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSGAt_eq_split_identityRootKeys (ss : BitVec 64) (v : SSG) :
    prostSSGAt A0 ss v =
      vecU8 A0 ss v.lik ∗ vecU8 A0 (ss + 0x18#64) v.rik ∗ vecU8 A0 (ss + 0x30#64) v.root ∗
        prostSSGRest_identityRootKeys ss v := by
  unfold prostSSGAt prostSSGRest_identityRootKeys
  ac_rfl

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
