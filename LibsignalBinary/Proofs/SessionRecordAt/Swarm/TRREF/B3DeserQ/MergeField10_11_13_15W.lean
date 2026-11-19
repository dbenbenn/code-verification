/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField10_11_13_15WPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

/-!
# `SessionStructure::merge_field` on Tags 10, 11, 13, and 15

Verifies `<SessionStructure as prost::Message>::merge_field::<&mut &[u8]>` at `mergeFieldStackX`
with slice length `< 2 ^ 62` on `SP2Ext` and re-exports the relocatable `[LibsignalPlacement]`
leaves for:
- Tag 10 (`remote_registration_id`, `uint32` at `ss + 0x150`),
- Tag 11 (`local_registration_id`, `uint32` at `ss + 0x154`),
- Tag 13 (`alice_base_key`, `Vec<u8>` at `ss + 0x60`),
- Tag 15 (`pq_ratchet_state`, `Vec<u8>` at `ss + 0x78`, replace/last-wins semantics).
-/

public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
open CryptoVerification.E2E.Record.L1GX
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem L1_MergeField10_11_13_15W : True := trivial

private theorem int64_raw_toBitVec_dq5 (n : Nat) (h : n < 2 ^ 64) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % (2 ^ 64)
  exact (Nat.mod_eq_of_lt h).symm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys int64_raw_toBitVec_dq5
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys

/-! ## `mergeFieldXSpecAtW` specification -/

/-- Ghost state for a standalone `uint32` (`int32::merge`) field of `SessionStructure`
(tag 10 `remote_registration_id` at `ss + 0x150`, tag 11 `local_registration_id` at `ss + 0x154`). -/
structure MergeFieldU32Ghost where
  ss : BitVec 64
  oldVal : BitVec 32
  val : BitVec 32
  payload : List (BitVec 8)
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

/-- Ghost state for a standalone `Vec<u8>` (`bytes::merge`) field of `SessionStructure`
(tag 13 `alice_base_key` at `ss + 0x60`, tag 15 `pq_ratchet_state` at `ss + 0x78`). -/
structure MergeFieldBytesGhost where
  ss : BitVec 64
  oldBytes : List (BitVec 8)
  bytes : List (BitVec 8)
  payload : List (BitVec 8)
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

/-! ## Stack split and epilogue helpers -/

theorem stackAt_bytesMergeW_eq_int32MergeW (sp : BitVec 64) :
    stackAt sp Prost.X.bytesMergeStackW =
      memRegion (sp - 24880#64) 144 ∗ stackAt sp Prost.X.int32MergeStackW :=
  ProofLib.stackAt_split_bottom sp Prost.X.int32MergeStackW 144 (by decide)

private theorem allocPanic_frame_dq5 {α β : Type} (g : α) (x : β) (s0 sf : State) (F R : SepProp)
    (hm : sf.mem ⊨ Serialization.allocPanic g s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R := by
  dsimp only [Serialization.allocPanic] at hm ⊢
  have hm' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact hm
  exact allowPanic_frame id hm'

private theorem mergeUint32_encode_dq5 (u : BitVec 32) (tail : List (BitVec 8)) :
    mergeUint32 .varint (encodeVarint (u.setWidth 64) ++ tail) = some (u, tail) := by
  simp [mergeUint32, decodeVarint_encodeVarint]

private theorem genFieldX_tag10 {fl : GenFieldX} (h : fl.tag = 10) : ∃ v, fl = .remReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | remReg v => exact ⟨v, rfl⟩
  | _ => simp [GenFieldX.tag] at h

private theorem genFieldX_tag11 {fl : GenFieldX} (h : fl.tag = 11) : ∃ v, fl = .locReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | locReg v => exact ⟨v, rfl⟩
  | _ => simp [GenFieldX.tag] at h

private theorem genFieldX_tag13 {fl : GenFieldX} (h : fl.tag = 13) : ∃ b, fl = .abk b := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | abk b => exact ⟨b, rfl⟩
  | _ => simp [GenFieldX.tag] at h

/-- `prostSSGXAt` split at `remote_registration_id` (`+0x150`). -/
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

/-- `prostSSGXAt` split at `local_registration_id` (`+0x154`). -/
@[expose] def prostSSGXRest_dq5_mf11 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
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

theorem prostSSGXAt_eq_locReg_sep_rest_dq5 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = ((ss + 0x154#64) ↦₃₂ v.ext.locReg) ∗ prostSSGXRest_dq5_mf11 A ss v := by
  unfold prostSSGXAt prostSSGXRest_dq5_mf11
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

/-- `prostSSGXAt` without `alice_base_key` (`+0x60`). -/
@[expose] def prostSSGXRest_mf13 (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A0 ss v.base.lik ∗ vecU8 A0 (ss + 0x18#64) v.base.rik ∗
      vecU8 A0 (ss + 0x30#64) v.base.root ∗
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A0 (ss + 0x78#64) v.ext.pq ∗
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

theorem prostSSGXAt_eq_split_mf13 (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A0 ss v = vecU8 A0 (ss + 0x60#64) v.ext.abk ∗ prostSSGXRest_mf13 ss v := by
  unfold prostSSGXAt prostSSGXRest_mf13
  rw [sepConj_left_comm (vecOf A0 104 8 _ _ _) (vecU8 A0 (ss + 0x60#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x30#64) _) (vecU8 A0 (ss + 0x60#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x18#64) _) (vecU8 A0 (ss + 0x60#64) _),
    sepConj_left_comm (vecU8 A0 ss _) (vecU8 A0 (ss + 0x60#64) _)]
  rfl

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_MergeField10_11_13_15W_Placed : True := trivial

@[expose] def mergeFieldU32FieldRawSpecW (tag : Nat) (fieldOff : BitVec 64) : Spec MergeFieldU32Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeUint32 .varint (x.payload ++ x.tail) = some (x.val, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      ((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf => DQ5Placed.u32Post x.ss fieldOff x.bufRef x.slot x.ptr x.val x.payload x.tail s0 sf
  onPanic := Serialization.allocPanic

abbrev mergeFieldU32FieldPlacedSpecW [LibsignalPlacement] (tag : Nat) (fieldOff : BitVec 64) :
    Spec MergeFieldU32Ghost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldU32FieldRawSpecW tag fieldOff)
abbrev mergeField10FieldPlacedSpecW [LibsignalPlacement] := mergeFieldU32FieldPlacedSpecW 10 0x150#64
abbrev mergeField11FieldPlacedSpecW [LibsignalPlacement] := mergeFieldU32FieldPlacedSpecW 11 0x154#64

@[expose] def mergeFieldBytesFieldRawSpecW (tag : Nat) (fieldOff : BitVec 64) : Spec MergeFieldBytesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeBytes .lengthDelimited (x.payload ++ x.tail) = some (x.bytes, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      vecU8 A0 (x.ss + fieldOff) x.oldBytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf => DQ5Placed.bytesPost x.ss fieldOff x.bufRef x.slot x.ptr x.bytes x.payload x.tail s0 sf
  onPanic := Serialization.allocPanic

abbrev mergeFieldBytesFieldPlacedSpecW [LibsignalPlacement] (tag : Nat) (fieldOff : BitVec 64) :
    Spec MergeFieldBytesGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldBytesFieldRawSpecW tag fieldOff)
abbrev mergeField13FieldPlacedSpecW [LibsignalPlacement] := mergeFieldBytesFieldPlacedSpecW 13 0x60#64
abbrev mergeField15FieldPlacedSpecW [LibsignalPlacement] := mergeFieldBytesFieldPlacedSpecW 15 0x78#64

theorem mergeFieldU32Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    {tag : Nat} {fieldOff : BitVec 64} (hint32 : Prost.X.Int32MergePlacedOkW A0 H)
    (h_case : (tag = 10 ∧ fieldOff = 0x150#64) ∨ (tag = 11 ∧ fieldOff = 0x154#64)) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldU32FieldPlacedSpecW tag fieldOff) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hal
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldU32FieldRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen⟩, hmem⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hmem
  exact DQ5Placed.mergeFieldU32_placed_sepWPp hint32 h_case x.ss x.bufRef x.slot x.ptr
    x.oldVal x.val x.payload x.tail hpc hrun hal hcrl0 hx0 hx1 hx2 hx3 hmerge hlen hmem

theorem mergeFieldBytesField_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    {tag : Nat} {fieldOff : BitVec 64} (hbytes : Prost.X.BytesMergePlacedOkW A0 H)
    (h_case : (tag = 13 ∧ fieldOff = 0x60#64) ∨ (tag = 15 ∧ fieldOff = 0x78#64)) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldBytesFieldPlacedSpecW tag fieldOff) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hal
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldBytesFieldRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen⟩, hmem⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hmem
  exact DQ5Placed.mergeFieldBytes_placed_sepWPp hbytes h_case x.ss x.bufRef x.slot x.ptr
    x.oldBytes x.bytes x.payload x.tail hpc hrun hal hcrl0 hx0 hx1 hx2 hx3 hmerge hlen hmem

theorem mergeField10Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField10FieldPlacedSpecW :=
  mergeFieldU32Field_placed_ok_extW hint32 (Or.inl ⟨rfl, rfl⟩)
theorem mergeField11Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField11FieldPlacedSpecW :=
  mergeFieldU32Field_placed_ok_extW hint32 (Or.inr ⟨rfl, rfl⟩)
theorem mergeField13Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField13FieldPlacedSpecW :=
  mergeFieldBytesField_placed_ok_extW hbytes (Or.inl ⟨rfl, rfl⟩)
theorem mergeField15Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField15FieldPlacedSpecW :=
  mergeFieldBytesField_placed_ok_extW hbytes (Or.inr ⟨rfl, rfl⟩)
end Placed
end Symbolic.Swarm.TRREF.B3DeserQ
