/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `PreKeyRecord::deserialize` Post-Loop `Ok` Packing and Cleanup Tails

Result/frame memory packing helpers, shared `Ok` tail (`+0x190 .. +0x1a4`), empty-input fast path
(`+0x174 .. +0x18c`), and `DecodeError` / `Vec<u8>` deallocation tails.
-/

public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Memory packing & unpacking helpers for result and frame -/

theorem extractLsb_lo_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

theorem extractLsb_hi_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem vecU8Buf_zero_elim (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  have hle := h.1
  have hbs : bs = [] := by simp at hle; exact hle
  subst hbs
  exact Entails.refl _

theorem emp_entails_two_vecU8Buf_zero (A : RustAlloc) :
    emp ⊢ vecU8Buf A 0#64 1#64 [] ∗ vecU8Buf A 0#64 1#64 [] := by
  have hz : emp ⊢ vecU8Buf A 0#64 1#64 [] := by
    unfold vecU8Buf
    rw [pure_true_emp ⟨by decide, by decide, by decide⟩, emp_sepConj]
    exact Entails.refl _
  rw [← emp_sepConj emp]
  exact sepConj_mono hz hz

theorem pkMemRegion40_unpack (sp' : BitVec 64) :
    memRegion sp' 40 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
        ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
        memRegion (sp' + 32#64) 8 := by
  rw [ProofLib.memRegion_split sp' 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0)
  refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2)
  refine Entails.trans ?_ (Entails.sepExists_intro w3)
  exact Entails.refl _

theorem pkMemRegion40_pack (sp' w0 w1 w2 w3 : BitVec 64) :
    (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
      ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ⊢ memRegion sp' 40 := by
  rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) by decide,
    ProofLib.memRegion_split sp' 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))

theorem pkMemRegion56_unpack (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
      ∃∗ r3 : BitVec 64, ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗
        ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₆₄ r4) ∗
        ((a + 40#64) ↦₆₄ r5) ∗ ((a + 48#64) ↦₆₄ r6) := by
  rw [ProofLib.memRegion_split a 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r6 => Entails.sepExists_elim fun r5 =>
    Entails.sepExists_elim fun r4 => Entails.sepExists_elim fun r3 =>
    Entails.sepExists_elim fun r2 => Entails.sepExists_elim fun r1 =>
    Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  refine Entails.trans ?_ (Entails.sepExists_intro r2)
  refine Entails.trans ?_ (Entails.sepExists_intro r3)
  refine Entails.trans ?_ (Entails.sepExists_intro r4)
  refine Entails.trans ?_ (Entails.sepExists_intro r5)
  refine Entails.trans ?_ (Entails.sepExists_intro r6)
  exact Entails.refl _

theorem pkMemRegion56_err_unpack (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ memRegion (a + 16#64) 24 ∗
        ((a + 40#64) ↦₆₄ r5) ∗ ((a + 48#64) ↦₆₄ r6) := by
  rw [ProofLib.memRegion_split a 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 24 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 24#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r6 => Entails.sepExists_elim fun r5 =>
    Entails.sepExists_elim fun r1 => Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  refine Entails.trans ?_ (Entails.sepExists_intro r5)
  refine Entails.trans ?_ (Entails.sepExists_intro r6)
  exact Entails.refl _

theorem pkStruct56_pack (sp' pubCap pubPtr pubLen privCap privPtr privLen : BitVec 64)
    (idVal padVal : BitVec 32) :
    vecHeader (sp' + 56#64) pubCap pubPtr pubLen ∗
      vecHeader (sp' + 80#64) privCap privPtr privLen ∗
      ((sp' + 104#64) ↦₃₂ idVal) ∗ ((sp' + 108#64) ↦₃₂ padVal) ⊢
      memRegion (sp' + 56#64) 56 := by
  have hp8 : ((sp' + 104#64) ↦₃₂ idVal) ∗ ((sp' + 108#64) ↦₃₂ padVal) ⊢
      memRegion (sp' + 104#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_pair_entails_memRegion8 (sp' + 104#64) idVal padVal
  rw [show (56 : Nat) = 24 + (24 + 8) by decide,
    ProofLib.memRegion_split (sp' + 56#64) 24 32 (by decide),
    ProofLib.memRegion_split (sp' + 56#64 + 24#64) 24 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (vecHeader_entails_memRegion24 (sp' + 56#64) pubCap pubPtr pubLen)
    (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 80#64) privCap privPtr privLen) hp8)

theorem pkMemRegion160_pack (sp' : BitVec 64) :
    memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ⊢
      memRegion sp' 160 := by
  rw [show (160 : Nat) = 40 + (16 + (56 + 48)) by decide,
    ProofLib.memRegion_split sp' 40 120 (by decide),
    ProofLib.memRegion_split (sp' + 40#64) 16 104 (by decide),
    ProofLib.memRegion_split (sp' + 40#64 + 16#64) 56 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem pkSpeInvalidProto56_intro (A : RustAlloc) (x19 r5 r6 : BitVec 64)
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
      memRegion (x19 + 16#64) 24 ∗
      ((x19 + 40#64) ↦₆₄ r5) ∗ ((x19 + 48#64) ↦₆₄ r6) ⊢
      preKeyResultAt A x19 out := by
  rw [herr]
  dsimp only [preKeyResultAt, errResultAt, speAt]
  have h0 : (56 : Nat) - 56 = 0 := rfl
  rw [h0, memRegion_zero, sepConj_emp]
  have h40 : memRegion (x19 + 8#64 + 8#64) 40 =
      memRegion (x19 + 16#64) 24 ∗ memRegion (x19 + 40#64) 8 ∗ memRegion (x19 + 48#64) 8 := by
    have ha1 : x19 + 8#64 + 8#64 = x19 + 16#64 := by bv_omega
    rw [ha1, show (40 : Nat) = 24 + (8 + 8) by decide,
      ProofLib.memRegion_split (x19 + 16#64) 24 16 (by decide),
      ProofLib.memRegion_split (x19 + 16#64 + 24#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h40]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))

theorem pkRecordOk56_intro (A : RustAlloc) (g : PreKeyGhost) (x19 : BitVec 64)
    (m : PreKeyRecordStructure) (pad32 : BitVec 32)
    {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨m⟩) :
    (x19 ↦₆₄ g.pub.cap) ∗ ((x19 + 8#64) ↦₆₄ g.pub.ptr) ∗
      ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((x19 + 24#64) ↦₆₄ g.priv.cap) ∗ ((x19 + 32#64) ↦₆₄ g.priv.ptr) ∗
      ((x19 + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((x19 + 48#64) ↦₆₄ (pad32 ++ m.id)) ∗
      vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ⊢
      preKeyResultAt A x19 out := by
  rw [hok]
  dsimp only [preKeyResultAt]
  refine Entails.trans ?_ (preKeyStructAt_entails_recordAt A g x19 m)
  unfold preKeyStructAt
  rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf]
  dsimp only [vecHeader]
  have hp : ((x19 + 48#64) ↦₆₄ (pad32 ++ m.id)) =
      ((x19 + 0x30#64) ↦₃₂ m.id) ∗ ((x19 + 0x34#64) ↦₃₂ pad32) := by
    have hs := (pointsTo32_pair (x19 + 48#64) m.id pad32).symm
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using hs
  rw [hp]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right
          (pointsTo32_entails_memRegion (x19 + 52#64) pad32))))))))))
  apply entails_of_eq; ac_rfl

/-! ## Shared `Ok` packing tail `+0x190..+0x1a4` + `+0x220` → `+0x224` -/

abbrev pkSubStack : Nat := smallRootStack - 224

theorem pkSpAligned_sub224 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

theorem pkFrame64_pack (sp' bufPtr : BitVec 64) (s0 : State) :
    pkCalleeSavedAt sp' s0 ∗ ((sp' + 184#64) ↦₆₄ bufPtr) ⊢
      memRegion (sp' + 160#64) 64 := by
  unfold pkCalleeSavedAt
  rw [ProofLib.memRegion_split (sp' + 160#64) 8 56 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans ?_
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 160#64) (s0.readReg64 .x29))
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 168#64) (s0.readReg64 .x30))
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 176#64) (s0.readReg64 .x23))
          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 184#64) bufPtr)
            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 192#64) (s0.readReg64 .x22))
              (sepConj_mono (pointsTo64_entails_memRegion (sp' + 200#64) (s0.readReg64 .x21))
                (sepConj_mono (pointsTo64_entails_memRegion (sp' + 208#64) (s0.readReg64 .x20))
                  (pointsTo64_entails_memRegion (sp' + 216#64) (s0.readReg64 .x19)))))))))
  apply entails_of_eq; ac_rfl

theorem pkStack_smallRoot_split (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 224#64) pkSubStack ∗
        memRegion (sp - 224#64) 160 ∗
        memRegion (sp - 224#64 + 160#64) 64 := by
  have h1 := stackAt_sub_split sp 224 smallRootStack
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) pkSubStack =
      stackAt (sp - 224#64) pkSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 224#64 - BitVec.ofNat 64 pkSubStack := by
      change sp - 65536#64 = sp - 224#64 - 65312#64
      bv_omega
    rw [ha]
  have h3 : stackAt sp 224 =
      memRegion (sp - 224#64) 160 ∗ memRegion (sp - 224#64 + 160#64) 64 := by
    unfold stackAt
    exact ProofLib.memRegion_split (sp - 224#64) 160 64 (by decide)
  rw [h1, h2, h3]

theorem pkSubStack_split (sp' : BitVec 64) :
    stackAt sp' pkSubStack =
      stackAt sp' (skipFieldStackX 100) ∗
        memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100) := by
  have hs := stackAt_sub_split sp' (skipFieldStackX 100) pkSubStack
  rw [hs]
  ac_rfl

theorem pkStack_smallRoot_unsplit (sp : BitVec 64) (s0 : State) :
    memRegion (sp - 224#64) 160 ∗
      pkCalleeSavedAt (sp - 224#64) s0 ∗
      ((sp - 224#64 + 184#64) ↦₆₄ (sp - 224#64 + 40#64)) ∗
      stackAt (sp - 224#64) (skipFieldStackX 100) ∗
      memRegion (sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100) ⊢
      stackAt sp smallRootStack := by
  rw [pkStack_smallRoot_split sp, pkSubStack_split (sp - 224#64)]
  have hf64 := pkFrame64_pack (sp - 224#64) (sp - 224#64 + 40#64) s0
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right hf64))
  apply entails_of_eq; ac_rfl

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem pack_tail_190_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr w0 w1 : BitVec 64} {pad32 : BitVec 32}
    {g : PreKeyGhost} {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (400)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx8 : s.readReg64 .x8 = g.pub.cap)
    (hx0 : s.readReg64 .x0 = g.pub.ptr) (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 m.publicKey.length)
    (hx9 : s.readReg64 .x9 = g.priv.cap) (hx11 : s.readReg64 .x11 = g.priv.ptr) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      ((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 24#64) ↦₆₄ (pad32 ++ m.id)) ∗ memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗ vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
        vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_unpack x19))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 => Wire.SepWPp.exists_pre fun r6 => ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h8 : s.readReg64 (Reg.gpr 8#5) = g.pub.cap := hx8
  have h0 : s.readReg64 (Reg.gpr 0#5) = g.pub.ptr := hx0
  have h10 : s.readReg64 (Reg.gpr 10#5) = BitVec.ofNat 64 m.publicKey.length := hx10
  have h9 : s.readReg64 (Reg.gpr 9#5) = g.priv.cap := hx9
  have h11 : s.readReg64 (Reg.gpr 11#5) = g.priv.ptr := hx11
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcrl1, by simp [htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  have h40 := pkMemRegion40_pack sp' (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
    (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
  unfold pkEpilogueMem
  refine Entails.trans ?_ (sepConj_mono (pkMemRegion160_pack sp') (sepConj_mono_right (sepConj_mono_left (pkRecordOk56_intro A g x19 m pad32 hok))))
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left h40))
  apply entails_of_eq; ac_rfl

theorem fast_empty_174_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨PreKeyRecordStructure.empty⟩) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (372)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
        vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗ ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ memRegion x19 56 ∗
        (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr [] out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp') (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pad32 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w3 => ?_
  have hp104 : ((sp' + 104#64) ↦₃₂ 0#32) ∗ ((sp' + 108#64) ↦₃₂ pad32) = ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) 0#32 pad32
  refine Wire.SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗ ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗
      ((sp' + 72#64) ↦₆₄ 0#64) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion x19 56 ∗ (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by dsimp only [vecHeader]; rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ 0#32), hp104]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (400)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (pack_tail_190_placed_wp (g := ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩) (m := PreKeyRecordStructure.empty)
      (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcrl1,
       by simp [htr, arm64_norm], ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [PreKeyRecordStructure.empty, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [PreKeyRecordStructure.empty, arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗ ((sp' + 72#64) ↦₆₄ 0#64) ∗
      ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]; simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using pkStruct56_pack sp' 0#64 1#64 0#64 0#64 1#64 0#64 0#32 pad32
  rw [← emp_sepConj (A.pool ∗ stackAt sp' (skipFieldStackX 100)), ← sepConj_assoc (vecU8Buf A 0#64 1#64 [])]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono h56
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (emp_entails_two_vecU8Buf_zero A))))))))))))
  apply entails_of_eq; ac_rfl

theorem epilogue_224_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} (hst : PkEpilogueStatePlaced s0 (s0.sp - 224#64) s)
    (hpc : s.pc = (blkPl_65).base + bv% (548)) (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_65 H) (s0.readReg64 .x30) s
      (pkEpilogueMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes (PreKeyRecord.deserialize x.bytes) ∗
        pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100))
      (fun sf Pf => sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializePlacedSpec A).post x s0 sf)) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, hsaved⟩
  unfold pkEpilogueMem pkCalleeSavedAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro _
  refine ⟨by simp [arm64_norm], fun hv => ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simpa [arm64_norm] using hsaved.x24,
    by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
    by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
    by simp [arm64_norm], hv⟩, ?_⟩
  dsimp only [preKeyDeserializePlacedSpec, withLsCodeRoLoaded, preKeyDeserializeRawSpec]
  rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
  have hstk := pkStack_smallRoot_unsplit s0.sp s0; unfold pkCalleeSavedAt at hstk
  simp only [arm64_norm]
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
  apply entails_of_eq; ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
