/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX10

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem genFieldX_tag_eq_10_iff (fl : GenFieldX) :
    fl.tag = 10 ↔ ∃ v, fl = .remReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag]
  | pendingId i k => simp [GenFieldX.tag]
  | pendingSpk i k spk => simp [GenFieldX.tag]
  | remReg v => simp [GenFieldX.tag]
  | locReg v => simp [GenFieldX.tag]
  | abk b => simp [GenFieldX.tag]
  | kyber i ct => simp [GenFieldX.tag]
  | pq b => simp [GenFieldX.tag]

theorem drop_left_sepWPp_mf1011 {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

@[expose] def prostSSGXRest_mf10 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
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
        ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXAt_eq_remReg_sep_rest_mf10 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ prostSSGXRest_mf10 A ss v := by
  unfold prostSSGXAt prostSSGXRest_mf10
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

theorem stackAt_mergeField_split_mf1011 (sp : BitVec 64) :
    stackAt sp mergeFieldStack =
      memRegion (sp - 16384#64) 7792 ∗
        stackAt (sp - 240#64) Prost.int32MergeStack ∗
        memRegion (sp - 240#64) 160 ∗
        memRegion (sp - 56#64) 8 ∗
        (∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
         ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64,
         ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
          ((sp - 80#64) ↦₆₄ w29) ∗ ((sp - 72#64) ↦₆₄ w30) ∗
          ((sp - 64#64) ↦₆₄ w25) ∗
          ((sp - 48#64) ↦₆₄ w24) ∗ ((sp - 40#64) ↦₆₄ w23) ∗
          ((sp - 32#64) ↦₆₄ w22) ∗ ((sp - 24#64) ↦₆₄ w21) ∗
          ((sp - 16#64) ↦₆₄ w20) ∗ ((sp - 8#64) ↦₆₄ w19)) := by
  have h0 := LibsignalTripleRatchet.stackAt_split_cells sp 16144 30 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 30)) 30 (by decide)] at h0
  change stackAt sp mergeFieldStack = stackAt (sp - 240#64) 16144 ∗
      memRegion (sp - 240#64) 240 at h0
  have hsub := ProofLib.stackAt_split_bottom (sp - 240#64) Prost.int32MergeStack 7792 (by decide)
  change stackAt (sp - 240#64) 16144 =
    memRegion (sp - 240#64 - 16144#64) 7792 ∗ stackAt (sp - 240#64) Prost.int32MergeStack at hsub
  have hsub_addr : sp - 240#64 - 16144#64 = sp - 16384#64 := by bv_omega
  rw [hsub_addr] at hsub
  have s1 := Prost.memRegion_split (sp - 240#64) 160 80 (by decide)
  rw [bv_sub_add_lit sp 240 160] at s1
  have s2 := Prost.memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s2
  have s3 := Prost.memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s3
  have s4 := Prost.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s4
  have s5 := Prost.memRegion_split (sp - 56#64) 8 48 (by decide)
  rw [bv_sub_add_lit sp 56 8] at s5
  have s6 := Prost.memRegion_split (sp - 48#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 48 8] at s6
  have s7 := Prost.memRegion_split (sp - 40#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 40 8] at s7
  have s8 := Prost.memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s8
  have s9 := Prost.memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s9
  have s10 := Prost.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s10
  rw [h0, hsub, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    Prost.memRegion_eight (sp - 80#64), Prost.memRegion_eight (sp - 72#64),
    Prost.memRegion_eight (sp - 64#64),
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem setWidth8_zext64_trunc32_mf1011 (v : BitVec 64) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) = BitVec.setWidth 8 v := by
  change BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = BitVec.setWidth 8 v
  rw [BitVec.setWidth_setWidth_of_le (BitVec.setWidth 32 v) (by decide),
    BitVec.setWidth_setWidth_of_le v (by decide)]

theorem int64_raw_toBitVec_mf1011 (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % 18446744073709551616
  exact (Nat.mod_eq_of_lt h).symm

theorem allowPanic_call_mf1011 {s_call s0 sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  have h1 : allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    unfold allocFailedIn
    rw [htr]
    exact id
  exact allowPanic_frame h1 hm

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero int64_raw_toBitVec_mf1011

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX10
