/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeIdentityRootKeys -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `SessionStructure::merge_field` on tag 15 (`pq_ratchet_state`)

Proves `mergeFieldX15_ok` (`0x581c`, jump-table byte `0x24` at `.rodata + 0x7902a` dispatching
to `+0xd0`), which invokes `prost::encoding::bytes::merge` (`0x2788`) on the `Vec<u8>` field at
`ss + 0x78` and exits via `+0x758`.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX15

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed
    CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral CryptoVerification.E2E.Record.L1GX

set_option autoImplicit false
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

/-! ## Instruction decodes (`0x58ec..0x58fc`) -/

/-- Portion of `prostSSGXAt` outside the `pq_ratchet_state` `Vec<u8>` at `ss + 0x78`. -/
@[expose] def prostSSGXRest_mf15 (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A0 ss v.base.lik ∗ vecU8 A0 (ss + 0x18#64) v.base.rik ∗
      vecU8 A0 (ss + 0x30#64) v.base.root ∗
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A0 (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A0 (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A0 ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXAt_eq_split_mf15 (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A0 ss v = vecU8 A0 (ss + 0x78#64) v.ext.pq ∗ prostSSGXRest_mf15 ss v := by
  unfold prostSSGXAt prostSSGXRest_mf15
  rw [sepConj_left_comm (vecU8 A0 (ss + 0x60#64) _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecOf A0 104 8 _ _ _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x30#64) _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x18#64) _) (vecU8 A0 (ss + 0x78#64) _),
    sepConj_left_comm (vecU8 A0 ss _) (vecU8 A0 (ss + 0x78#64) _)]
  rfl

theorem genFieldX_tag15 {fl : GenFieldX} (h : fl.tag = 15) : ∃ b, fl = .pq b := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | pendingId i k => simp [GenFieldX.tag] at h
  | pendingSpk i k spk => simp [GenFieldX.tag] at h
  | remReg u => simp [GenFieldX.tag] at h
  | locReg u => simp [GenFieldX.tag] at h
  | abk b => simp [GenFieldX.tag] at h
  | kyber i ct => simp [GenFieldX.tag] at h
  | pq b => exact ⟨b, rfl⟩

/-! ## Post-call epilogue -/

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX15
