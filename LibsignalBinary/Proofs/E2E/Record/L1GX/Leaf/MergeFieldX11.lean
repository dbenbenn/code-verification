/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX10
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::merge_field` on tag 11 (`local_registration_id`)

Proves `mergeFieldX11_ok` (`0x581c`, arm `+0x36c` calling `uint32::merge` into `ss + 0x154`),
reusing the shared helpers from `MergeFieldX10`.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX11

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX10

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero int64_raw_toBitVec_mf1011

private theorem genFieldX_tag_eq_11_iff (fl : GenFieldX) :
    fl.tag = 11 ↔ ∃ v, fl = .locReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag]
  | pendingId i k => simp [GenFieldX.tag]
  | pendingSpk i k spk => simp [GenFieldX.tag]
  | remReg v => simp [GenFieldX.tag]
  | locReg v => simp [GenFieldX.tag]
  | abk b => simp [GenFieldX.tag]
  | kyber i ct => simp [GenFieldX.tag]
  | pq b => simp [GenFieldX.tag]

private def prostSSGXRest_mf11 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg))

private theorem prostSSGXAt_eq_locReg_sep_rest_mf11 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = ((ss + 0x154#64) ↦₃₂ v.ext.locReg) ∗ prostSSGXRest_mf11 A ss v := by
  unfold prostSSGXAt prostSSGXRest_mf11
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX11
