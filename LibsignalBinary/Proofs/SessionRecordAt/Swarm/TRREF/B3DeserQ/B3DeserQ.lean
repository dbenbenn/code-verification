/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxWPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxW -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField14WPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserCalleesX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.RecordDeserializeX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.LoopW
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.LoopWPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField10_11_13_15W
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField14W
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField9PW
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField9PWPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `Q`-Scope `SessionRecord::deserialize` Assembly

Assembles all `GenFieldQ` tag leaves (tags 1–7, 9, 10, 11, 13, 14, 15) into `mergeFieldQW_ok`,
`mergeFieldQWA_ok`, and `mergeFieldQPlacedW_ok`, and combines them with the loop and representation
bridges to establish `recordDeserializeOpenQ_ok_of_stage2`, `recordDeserializeOpenQ_ok_of_stage2A`,
and relocatable `recordDeserializeOpenQ_placed_ok_of_alloc` / `recordDeserializeOpenQ_placed_ok_of_stage2`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.Serialization (CanonRecord allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem L1_B3DeserQ : True := trivial

private theorem mergeUint32_encode_dq8 (u : BitVec 32) (tail : List (BitVec 8)) :
    mergeUint32 .varint (encodeVarint (u.setWidth 64) ++ tail) = some (u, tail) := by
  simp [mergeUint32, decodeVarint_encodeVarint]

/-! ## Framing helpers for tags 9P and 14 -/

private theorem allocPanic_frame_dq8 {α β : Type} (g : α) (x : β) (s0 sf : State) (F R : SepProp)
    (hm : sf.mem ⊨ allocPanic g s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ allocPanic x s0 sf ∗ R := by
  dsimp only [allocPanic] at hm ⊢
  have hm' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact hm
  exact allowPanic_frame id hm'

/-- `prostSSGQAt` without `remote_registration_id` (`+0x150`). -/
@[expose] def prostSSGQRest10 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
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

theorem prostSSGQAt_eq_remReg_sep_rest10 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ prostSSGQRest10 A ss v := by
  unfold prostSSGQAt prostSSGQRest10
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

/-- `prostSSGQAt` without `local_registration_id` (`+0x154`). -/
@[expose] def prostSSGQRest11 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
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

theorem prostSSGQAt_eq_locReg_sep_rest11 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = ((ss + 0x154#64) ↦₃₂ v.ext.locReg) ∗ prostSSGQRest11 A ss v := by
  unfold prostSSGQAt prostSSGQRest11
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

/-- `prostSSGQAt` without `alice_base_key` (`+0x60`). -/
@[expose] def prostSSGQRest13 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x78#64) v.ext.pq ∗
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
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_abk_sep_rest13 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x60#64) v.ext.abk ∗ prostSSGQRest13 A ss v := by
  unfold prostSSGQAt prostSSGQRest13
  ac_rfl

/-- `mergeBytes` on an arbitrary length-delimited byte slice `b` with `b.length < 2 ^ 64`. -/
theorem mergeBytes_encode_varint (b tail : List (BitVec 8)) (hb : b.length < 2 ^ 64) :
    mergeBytes .lengthDelimited (encodeVarint (BitVec.ofNat 64 b.length) ++ b ++ tail) =
      some (b, tail) := by
  rw [List.append_assoc]
  have hdv : decodeVarint (encodeVarint (BitVec.ofNat 64 b.length) ++ (b ++ tail)) =
      some (BitVec.ofNat 64 b.length, b ++ tail) :=
    decodeVarint_encodeVarint (BitVec.ofNat 64 b.length) (b ++ tail)
  have hlen : (BitVec.ofNat 64 b.length).toNat = b.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  unfold mergeBytes
  simp [hdv, hlen]

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_B3DeserQ_Placed : True := trivial

/-- Lift `MergeField9PPlacedOkW` (over `prostSSGXNoPqAt_x9pW`) to `MergeFieldQPlacedOkW` by framing
`vecU8 A0 (x.ss + 0x78#64) x.v.ext.pq` via `prostSSGQAt_eq_x9pW_sep_pq`. -/
theorem mergeFieldQPlacedOkW_of_9P [LibsignalPlacement] (H : LibsignalHooks)
    (h9P : MergeField9PPlacedOkW H
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk))) :
    MergeFieldQPlacedOkW H
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) := by
  refine placedOk_of_imp_frame h9P (fun _ _ _ _ => rfl) allocPanic_frame_dq8 ?_
  intro x s0 R hpre
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hx4, hP, hok, hfresh, hlen⟩, hmem⟩
  have hfx : ∃ fx : GenFieldX,
      ((∃ i k, fx = .pendingId i k) ∨ (∃ o k spk, fx = .pendingSpk o k spk)) ∧
      x.fld = GenFieldX.toGenFieldQ fx := by
    rcases hP with ⟨i, k, hfl⟩ | ⟨o, k, spk, hfl⟩
    · exact ⟨.pendingId i k, Or.inl ⟨i, k, rfl⟩, hfl⟩
    · exact ⟨.pendingSpk o k spk, Or.inr ⟨o, k, spk, rfl⟩, hfl⟩
  rcases hfx with ⟨fx, hfxP, hfl⟩
  rw [hfl] at hx1 hx2 hok hfresh hlen hmem
  rw [toGenFieldQ_tag] at hx1
  rw [toGenFieldQ_wt] at hx2
  rw [toGenFieldQ_payload] at hlen hmem
  have hnpq : GenFieldX.NoPq fx := by rcases hfxP with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> trivial
  have hok_fx : fx.Ok := (toGenFieldQ_ok fx).mp hok
  have hfresh_fx : fx.Fresh x.v.toSSGX := ((toGenFieldQ_fresh_iff x.v fx).mp hfresh).1
  refine ⟨⟨x.ss, x.v.toSSGX, fx, x.bufRef, x.slot, x.ptr, x.tail⟩,
    vecU8 A0 (x.ss + 0x78#64) x.v.ext.pq, ?_, ?_⟩
  · dsimp only [mergeField9PPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeField9PRawSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hfxP, hok_fx, hfresh_fx, hlen⟩, ?_⟩
    rw [prostSSGQAt_eq_x9pW_sep_pq A0 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField9PPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeField9PRawSpecW] at hpost
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW]
    rw [hfl, toGenFieldQ_payload,
      prostSSGQAt_eq_x9pW_sep_pq A0 x.ss (x.v.apply (GenFieldX.toGenFieldQ fx)),
      apply_toGenFieldQ_toSSGX x.v fx hnpq, apply_toGenFieldQ_pq x.v fx hnpq]
    convert hpost using 1; ac_rfl

/-- Lift `MergeField14PlacedOkW` (over `prostSSGXNoPqAt_x14`) to `MergeFieldQPlacedOkW` by framing
`vecU8 A0 (x.ss + 0x78#64) x.v.ext.pq` via `prostSSGQAt_eq_x14_sep_pq`. -/
theorem mergeFieldQPlacedOkW_of_14 [LibsignalPlacement] (H : LibsignalHooks)
    (h14 : MergeField14PlacedOkW H (fun fl => fl.tag = 14)) :
    MergeFieldQPlacedOkW H (fun fl => ∃ i ct, fl = .kyber i ct) := by
  refine placedOk_of_imp_frame h14 (fun _ _ _ _ => rfl) allocPanic_frame_dq8 ?_
  intro x s0 R hpre
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hx4, ⟨i, ct, hfl⟩, hok, hfresh, hlen⟩, hmem⟩
  let fx : GenFieldX := .kyber i ct
  have hfl' : x.fld = GenFieldX.toGenFieldQ fx := hfl
  rw [hfl'] at hx1 hx2 hok hfresh hlen hmem
  rw [toGenFieldQ_tag] at hx1
  rw [toGenFieldQ_wt] at hx2
  rw [toGenFieldQ_payload] at hlen hmem
  have hok_fx : fx.Ok := (toGenFieldQ_ok fx).mp hok
  have hfresh_fx : fx.Fresh x.v.toSSGX := ((toGenFieldQ_fresh_iff x.v fx).mp hfresh).1
  have hnpq : GenFieldX.NoPq fx := trivial
  refine ⟨⟨x.ss, x.v.toSSGX, fx, x.bufRef, x.slot, x.ptr, x.tail⟩,
    vecU8 A0 (x.ss + 0x78#64) x.v.ext.pq, ?_, ?_⟩
  · dsimp only [mergeField14PlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeField14RawSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, rfl, hok_fx, hfresh_fx, hlen⟩, ?_⟩
    rw [prostSSGQAt_eq_x14_sep_pq A0 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField14PlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeField14RawSpecW] at hpost
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW]
    rw [hfl', toGenFieldQ_payload,
      prostSSGQAt_eq_x14_sep_pq A0 x.ss (x.v.apply (GenFieldX.toGenFieldQ fx)),
      apply_toGenFieldQ_toSSGX x.v fx hnpq, apply_toGenFieldQ_pq x.v fx hnpq]
    convert hpost using 1; ac_rfl

/-- Tag 10 (`remote_registration_id`) `MergeFieldQPlacedOkW` from `mergeField10Field_placed_ok_extW`. -/
theorem mergeFieldQ10_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H) :
    MergeFieldQPlacedOkW H (fun fl => ∃ u, fl = .remReg u) := by
  refine placedOk_of_imp_frame (mergeField10Field_placed_ok_extW hint32)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq8 ?_
  intro x s0 R hpre
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, _, ⟨u, hfl⟩, _, _, hlen⟩, hmem⟩
  rw [hfl] at hx1 hx2 hlen hmem
  refine ⟨⟨x.ss, x.v.ext.remReg, u, (GenFieldQ.remReg u).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGQRest10 A0 x.ss x.v, ?_, ?_⟩
  · dsimp only [mergeField10FieldPlacedSpecW, mergeFieldU32FieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldU32FieldRawSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, mergeUint32_encode_dq8 u x.tail, hlen⟩, ?_⟩
    rw [prostSSGQAt_eq_remReg_sep_rest10 A0 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField10FieldPlacedSpecW, mergeFieldU32FieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldU32FieldRawSpecW,
      DQ5Placed.u32Post] at hpost
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW]
    rw [hfl, prostSSGQAt_eq_remReg_sep_rest10 A0 x.ss (x.v.apply (.remReg u))]
    convert hpost using 1; ac_rfl

/-- Tag 11 (`local_registration_id`) `MergeFieldQPlacedOkW` from `mergeField11Field_placed_ok_extW`. -/
theorem mergeFieldQ11_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H) :
    MergeFieldQPlacedOkW H (fun fl => ∃ u, fl = .locReg u) := by
  refine placedOk_of_imp_frame (mergeField11Field_placed_ok_extW hint32)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq8 ?_
  intro x s0 R hpre
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, _, ⟨u, hfl⟩, _, _, hlen⟩, hmem⟩
  rw [hfl] at hx1 hx2 hlen hmem
  refine ⟨⟨x.ss, x.v.ext.locReg, u, (GenFieldQ.locReg u).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGQRest11 A0 x.ss x.v, ?_, ?_⟩
  · dsimp only [mergeField11FieldPlacedSpecW, mergeFieldU32FieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldU32FieldRawSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, mergeUint32_encode_dq8 u x.tail, hlen⟩, ?_⟩
    rw [prostSSGQAt_eq_locReg_sep_rest11 A0 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField11FieldPlacedSpecW, mergeFieldU32FieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldU32FieldRawSpecW,
      DQ5Placed.u32Post] at hpost
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW]
    rw [hfl, prostSSGQAt_eq_locReg_sep_rest11 A0 x.ss (x.v.apply (.locReg u))]
    convert hpost using 1; ac_rfl

/-- Tag 13 (`alice_base_key`) `MergeFieldQPlacedOkW` from `mergeField13Field_placed_ok_extW`. -/
theorem mergeFieldQ13_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    MergeFieldQPlacedOkW H (fun fl => ∃ b, fl = .abk b) := by
  refine placedOk_of_imp_frame (mergeField13Field_placed_ok_extW hbytes)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq8 ?_
  intro x s0 R hpre
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, _, ⟨b, hfl⟩, hok, _, hlen⟩, hmem⟩
  rw [hfl] at hx1 hx2 hok hlen hmem
  have hb : b.length = 33 := hok
  have hb_lt64 : b.length < 2 ^ 64 := by omega
  refine ⟨⟨x.ss, x.v.ext.abk, b, (GenFieldQ.abk b).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGQRest13 A0 x.ss x.v, ?_, ?_⟩
  · dsimp only [mergeField13FieldPlacedSpecW, mergeFieldBytesFieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldBytesFieldRawSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, ?_, hlen⟩, ?_⟩
    · dsimp only [GenFieldQ.payload]
      exact mergeBytes_encode_varint b x.tail hb_lt64
    · rw [prostSSGQAt_eq_abk_sep_rest13 A0 x.ss x.v] at hmem
      convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField13FieldPlacedSpecW, mergeFieldBytesFieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldBytesFieldRawSpecW,
      DQ5Placed.bytesPost] at hpost
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW]
    rw [hfl, prostSSGQAt_eq_abk_sep_rest13 A0 x.ss (x.v.apply (.abk b))]
    convert hpost using 1; ac_rfl

/-- Tag 15 (`pq_ratchet_state`) `MergeFieldQPlacedOkW` from `mergeField15Field_placed_ok_extW`
by framing `prostSSGXNoPqAt A0 x.ss x.v.toSSGX`. -/
theorem mergeFieldQ15_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    MergeFieldQPlacedOkW H (fun fl => ∃ b, fl = .pq b) := by
  refine placedOk_of_imp_frame (mergeField15Field_placed_ok_extW hbytes)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq8 ?_
  intro x s0 R hpre
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldQRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, _, ⟨b, hfl⟩, hok, _, hlen⟩, hmem⟩
  rw [hfl] at hx1 hx2 hok hlen hmem
  have hb_lt64 : b.length < 2 ^ 64 := by
    dsimp only [GenFieldQ.Ok] at hok; omega
  refine ⟨⟨x.ss, x.v.ext.pq, b, (GenFieldQ.pq b).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGXNoPqAt A0 x.ss x.v.toSSGX, ?_, ?_⟩
  · dsimp only [mergeField15FieldPlacedSpecW, mergeFieldBytesFieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldBytesFieldRawSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, ?_, hlen⟩, ?_⟩
    · dsimp only [GenFieldQ.payload]
      exact mergeBytes_encode_varint b x.tail hb_lt64
    · rw [prostSSGQAt_eq_noPq_sep_pq A0 x.ss x.v] at hmem
      have hcomm : (prostSSGXNoPqAt A0 x.ss x.v.toSSGX ∗ vecU8 A0 (x.ss + 0x78#64) x.v.ext.pq) =
          (vecU8 A0 (x.ss + 0x78#64) x.v.ext.pq ∗ prostSSGXNoPqAt A0 x.ss x.v.toSSGX) :=
        sepConj_comm _ _
      rw [hcomm] at hmem
      convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField15FieldPlacedSpecW, mergeFieldBytesFieldPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldBytesFieldRawSpecW,
      DQ5Placed.bytesPost] at hpost
    dsimp only [mergeFieldQPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldQRawSpecW]
    rw [hfl, prostSSGQAt_eq_noPq_sep_pq A0 x.ss (x.v.apply (.pq b))]
    have hcomm : (prostSSGXNoPqAt A0 x.ss (x.v.apply (.pq b)).toSSGX ∗
          vecU8 A0 (x.ss + 0x78#64) (x.v.apply (.pq b)).ext.pq) =
        (vecU8 A0 (x.ss + 0x78#64) b ∗ prostSSGXNoPqAt A0 x.ss x.v.toSSGX) :=
      sepConj_comm _ _
    rw [hcomm]
    convert hpost using 1; ac_rfl

/-- Relocatable `SessionStructure::merge_field` on all `GenFieldQ` constructors on `lsProg_15 H`. -/
theorem mergeFieldQPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H) :
    MergeFieldQPlacedOkW H (fun _ => True) := by
  have hBaseGen : MergeFieldGenPlacedOkW H (fun _ => True) :=
    mergeFieldGenPlacedW_ok H
      (mergeFieldLeavesPlacedW_of_callees H hCallees)
      (chainMergeGenPlacedW_ok H (chainLeavesPlacedW_of_callees H hCallees))
  have hBase : MergeFieldQPlacedOkW H (fun fl => ∃ f, True ∧ fl = .base f) :=
    mergeFieldQPlacedOkW_base H hBaseGen
  have h9P : MergeFieldQPlacedOkW H
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) :=
    mergeFieldQPlacedOkW_of_9P H (mergeField9PW_placed_ok H hCallees)
  have h10 : MergeFieldQPlacedOkW H (fun fl => ∃ u, fl = .remReg u) :=
    mergeFieldQ10_placed_ok_extW hCallees.2.1
  have h11 : MergeFieldQPlacedOkW H (fun fl => ∃ u, fl = .locReg u) :=
    mergeFieldQ11_placed_ok_extW hCallees.2.1
  have h13 : MergeFieldQPlacedOkW H (fun fl => ∃ b, fl = .abk b) :=
    mergeFieldQ13_placed_ok_extW hCallees.2.2.1
  have h14 : MergeFieldQPlacedOkW H (fun fl => ∃ i ct, fl = .kyber i ct) :=
    mergeFieldQPlacedOkW_of_14 H (mergeField14W_placed_ok H hCallees)
  have h15 : MergeFieldQPlacedOkW H (fun fl => ∃ b, fl = .pq b) :=
    mergeFieldQ15_placed_ok_extW hCallees.2.2.1
  have hAll :=
    mergeFieldQPlacedOkW_or H hBase
      (mergeFieldQPlacedOkW_or H h9P
        (mergeFieldQPlacedOkW_or H h10
          (mergeFieldQPlacedOkW_or H h11
            (mergeFieldQPlacedOkW_or H h13
              (mergeFieldQPlacedOkW_or H h14 h15)))))
  refine mergeFieldQPlacedOkW_of_imp H (fun fl _ => ?_) hAll
  cases fl with
  | base f => exact Or.inl ⟨f, trivial, rfl⟩
  | pendingId i k => exact Or.inr (Or.inl (Or.inl ⟨i, k, rfl⟩))
  | pendingSpk pid k spk => exact Or.inr (Or.inl (Or.inr ⟨pid, k, spk, rfl⟩))
  | remReg u => exact Or.inr (Or.inr (Or.inl ⟨u, rfl⟩))
  | locReg u => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, rfl⟩)))
  | abk b => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))))
  | kyber i ct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, ct, rfl⟩)))))
  | pq b => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, rfl⟩)))))

/-- Relocatable exact `Q`-scope `SessionRecord::deserialize` contract (`deserializeQExactPlacedSpecW`)
on `lsProg_46 H` from minimal allocator + `memcpy` contracts. -/
theorem deserializeExactAtQ_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQExactPlacedSpecW := by
  have hCallees := deserializeCalleesPlacedW_of_alloc hA hMemcpy
  exact deserializeExactQPlacedW_ok H
    (deserLeavesQPlacedW_of_memcpy H hCallees hMemcpy)
    (mergeFieldQPlacedW_ok H hCallees)

/-- Relocatable general `Q`-scope `SessionRecord::deserialize` contract (`deserializeQPlacedSpecW`)
on `lsProg_46 H` from minimal allocator + `memcpy` contracts. -/
theorem deserializeBodyQ_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQPlacedSpecW := by
  have hCallees := deserializeCalleesPlacedW_of_alloc hA hMemcpy
  exact deserializeBodyQPlacedW_ok H
    (deserLeavesQPlacedW_of_memcpy H hCallees hMemcpy)
    (mergeFieldQPlacedW_ok H hCallees)

/-- Relocatable `withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)` on `lsProg_46 H`
from minimal allocator + `memcpy` contracts. -/
theorem recordDeserializeOpenQ_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)) :=
  recordDeserializeOpen_placed_of_exactQ lsmpl
    (deserializeExactAtQ_placed_ok_of_alloc hA hMemcpy)

/-- Relocatable exact `Q`-scope `SessionRecord::deserialize` contract (`deserializeQExactPlacedSpecW`)
on `lsProg_46 H` from `Stage2ContractsA0Placed H`. -/
theorem deserializeExactAtQ_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQExactPlacedSpecW :=
  deserializeExactAtQ_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

/-- Relocatable general `Q`-scope `SessionRecord::deserialize` contract (`deserializeQPlacedSpecW`)
on `lsProg_46 H` from `Stage2ContractsA0Placed H`. -/
theorem deserializeBodyQ_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQPlacedSpecW :=
  deserializeBodyQ_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

/-- Relocatable `withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)` on `lsProg_46 H`
from `Stage2ContractsA0Placed H`. -/
theorem recordDeserializeOpenQ_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)) :=
  recordDeserializeOpenQ_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

end Placed

end Symbolic.Swarm.TRREF.B3DeserQ
