/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Stack -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `segPreKey` Unacknowledged Items Call and Staleness Arithmetic (`+0x344..+0x390`, `+0x680..+0x6fc`)

Steps from `KeyState` (`+0x344`) through `unacknowledged_pre_key_message_items`, `baseKey` and
pre-key field extraction, `duration_since`, and `timeAdd` (`+ 2592000` s) to `StalenessAddState`
at `+0x6fc`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `unackOutAt` and `baseKey` Unpack/Pack Helpers -/

theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ v : BitVec 32, bs = unpack32 v := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0, (unpack32_pack32 b0 b1 b2 b3).symm⟩

@[expose] def baseKeyShiftProp (bs : List (BitVec 8)) (bk0 bk1 bk2 bk3 : BitVec 64) (bk4 : BitVec 32) : Prop :=
  ∃ pad : List (BitVec 8), pad.length = 4 ∧
    pad ++ bs = unpack64 bk0 ++ unpack64 bk1 ++ unpack64 bk2 ++ unpack64 bk3 ++ unpack32 bk4

theorem baseKeyShift_unpack (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    (memRegion a 4 ∗ ((a + 4#64) ↦ₛ bs)) ⊢
      ∃∗ bk0 : BitVec 64, ∃∗ bk1 : BitVec 64, ∃∗ bk2 : BitVec 64, ∃∗ bk3 : BitVec 64,
      ∃∗ bk4 : BitVec 32,
        ⌜baseKeyShiftProp bs bk0 bk1 bk2 bk3 bk4⌝ ∗
        (a ↦₆₄ bk0) ∗ ((a + 8#64) ↦₆₄ bk1) ∗ ((a + 16#64) ↦₆₄ bk2) ∗
        ((a + 24#64) ↦₆₄ bk3) ∗ ((a + 32#64) ↦₃₂ bk4) := by
  rw [memRegion_eq_exists_bytes a 4 (by decide), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun pad => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hpad => ?_
  have h1 : (pad ++ bs).length = 36 := by simp [hpad, h]
  have h32 : ((pad ++ bs).take 32).length = 32 := by simp [h1]
  have h4 : ((pad ++ bs).drop 32).length = 4 := by simp [h1]
  obtain ⟨bk0, bk1, bk2, bk3, hbk32, heq32⟩ := exists_unpack64_of_length_32 h32
  obtain ⟨bk4, hbk4⟩ := exists_unpack32_of_length_4 h4
  have htot : pad ++ bs = unpack64 bk0 ++ unpack64 bk1 ++ unpack64 bk2 ++ unpack64 bk3 ++ unpack32 bk4 := by
    rw [← hbk32, ← hbk4, List.take_append_drop]
  refine Entails.sepExists_right bk0 (Entails.sepExists_right bk1
    (Entails.sepExists_right bk2 (Entails.sepExists_right bk3
      (Entails.sepExists_right bk4 ?_))))
  refine Entails.pure_right ⟨pad, hpad, htot⟩ ?_
  have hcomb : (a ↦ₛ pad) ∗ ((a + 4#64) ↦ₛ bs) = (a ↦ₛ (pad ++ bs)) := by
    rw [pointsToBytes_append, hpad]
  rw [hcomb]
  have hsplit : pad ++ bs = (pad ++ bs).take 32 ++ (pad ++ bs).drop 32 :=
    (List.take_append_drop 32 (pad ++ bs)).symm
  rw [hsplit, pointsToBytes_append, h32, heq32 a, hbk4, ← pointsTo32_eq_pointsToBytes]
  simp only [sepConj_assoc]; exact Entails.refl _

theorem baseKeyShift_pack (b : BitVec 64) {bs : List (BitVec 8)}
    (bk0 bk1 bk2 bk3 : BitVec 64) (bk4 : BitVec 32) :
    (⌜baseKeyShiftProp bs bk0 bk1 bk2 bk3 bk4⌝ ∗
      (b ↦₆₄ bk0) ∗ ((b + 8#64) ↦₆₄ bk1) ∗ ((b + 16#64) ↦₆₄ bk2) ∗
      ((b + 24#64) ↦₆₄ bk3) ∗ ((b + 32#64) ↦₃₂ bk4)) ⊢
      (memRegion b 4 ∗ ((b + 4#64) ↦ₛ bs)) := by
  refine Entails.pure_left fun ⟨pad, hpad, htot⟩ => ?_
  have hrhs : ((b ↦₆₄ bk0) ∗ ((b + 8#64) ↦₆₄ bk1) ∗ ((b + 16#64) ↦₆₄ bk2) ∗
      ((b + 24#64) ↦₆₄ bk3) ∗ ((b + 32#64) ↦₃₂ bk4)) =
      (b ↦ₛ (pad ++ bs)) := by
    rw [htot, List.append_assoc, List.append_assoc, List.append_assoc,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
    simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
      BitVec.add_assoc, BitVec.reduceAdd]
  rw [hrhs, pointsToBytes_append, hpad]
  refine sepConj_mono_left ?_
  have hmr := pointsToBytes_entails_memRegion b pad
  rwa [hpad] at hmr

@[expose] def optU32ValProp (opt : Option (BitVec 32)) (val : BitVec 32) : Prop :=
  ∀ v, opt = some v → val = v

theorem optU32At_unpack32 (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢
      ∃∗ val : BitVec 32, ⌜optU32ValProp opt val⌝ ∗
        (a ↦₃₂ (if opt.isSome then 1#32 else 0#32)) ∗ ((a + 4#64) ↦₃₂ val) := by
  cases opt with
  | none =>
    unfold optU32At optU32ValProp
    rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
    refine Entails.sepExists_elim fun val => Entails.sepExists_right val ?_
    exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)
  | some v =>
    unfold optU32At optU32ValProp
    refine Entails.sepExists_right v ?_
    exact Entails.pure_right (by intro _ h; exact Option.some.inj h) (Entails.refl _)

theorem optU32At_unpack64 (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢
      ∃∗ val : BitVec 32, ⌜optU32ValProp opt val⌝ ∗
        (a ↦₆₄ (val ++ (if opt.isSome then 1#32 else 0#32))) := by
  refine Entails.trans (optU32At_unpack32 a opt) ?_
  refine Entails.sepExists_elim fun val => Entails.sepExists_right val ?_
  rw [pointsTo32_pair]
  exact Entails.refl _

@[expose] def unackKyberSliceProp (kyG : Option TailVecGhost) (kyPtr kyLen : BitVec 64) : Prop :=
  match kyG with
  | none => kyPtr = 0#64
  | some g => kyPtr = g.vec.ptr ∧ kyLen = BitVec.ofNat 64 g.vec.bytes.length

theorem unackKyberSliceAt_unpack (a : BitVec 64) (kyG : Option TailVecGhost) :
    unackKyberSliceAt a kyG ⊢
      ∃∗ kyPtr : BitVec 64, ∃∗ kyLen : BitVec 64,
        ⌜unackKyberSliceProp kyG kyPtr kyLen⌝ ∗
        (a ↦₆₄ kyPtr) ∗ ((a + 8#64) ↦₆₄ kyLen) := by
  cases kyG with
  | none =>
    unfold unackKyberSliceAt unackKyberSliceProp
    rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_right]
    refine Entails.sepExists_elim fun kyLen =>
      Entails.sepExists_right 0#64 (Entails.sepExists_right kyLen ?_)
    exact Entails.pure_right rfl (Entails.refl _)
  | some g =>
    unfold unackKyberSliceAt unackKyberSliceProp
    refine Entails.sepExists_right g.vec.ptr
      (Entails.sepExists_right (BitVec.ofNat 64 g.vec.bytes.length) ?_)
    exact Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)

theorem takenRecord_sessionRecordAt_unpack (A : RustAlloc) (sp : BitVec 64)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken)) ⊢
      ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64, ∃∗ G : SessionGhost,
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } := by
  refine Entails.sepExists_elim fun ⟨prevCap, prevPtr, cur⟩ => ?_
  cases cur with
  | none =>
    unfold sessionRecordAt takenRecord
    dsimp only
    rw [sepConj_comm]
    exact Entails.pure_left False.elim
  | some G =>
    unfold sessionRecordAt takenRecord
    dsimp only
    have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
    rw [h128]
    exact Entails.sepExists_right prevCap
      (Entails.sepExists_right prevPtr (Entails.sepExists_right G (Entails.refl _)))

theorem takenRecord_sessionRecordAt_pack (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ⊢
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken)) := by
  refine Entails.sepExists_right ⟨prevCap, prevPtr, some G⟩ ?_
  unfold sessionRecordAt takenRecord
  dsimp only
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128]
  exact Entails.refl _

/-! ## Region Split and Join Helpers -/

theorem curScratch_unackItems_unpack (sp : BitVec 64) :
    curScratch sp ⊢
      ∃∗ s48 : BitVec 64, ∃∗ s40 : BitVec 64, ∃∗ s38 : BitVec 64,
        ∃∗ s34 : BitVec 32, ∃∗ s28 : BitVec 64, ∃∗ s24 : BitVec 32, ∃∗ s18 : BitVec 64,
        memRegion sp 0x18 ∗
        ((sp + 0x18#64) ↦₆₄ s18) ∗
        memRegion (sp + 0x20#64) 4 ∗
        ((sp + 0x24#64) ↦₃₂ s24) ∗
        ((sp + 0x28#64) ↦₆₄ s28) ∗
        memRegion (sp + 0x30#64) 4 ∗
        ((sp + 0x34#64) ↦₃₂ s34) ∗
        ((sp + 0x38#64) ↦₆₄ s38) ∗
        ((sp + 0x40#64) ↦₆₄ s40) ∗
        ((sp + 0x48#64) ↦₆₄ s48) ∗
        ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) := by
  unfold curScratch
  rw [memRegion_split sp 0x18 0x38 (by decide),
      mr_cut_add sp 0x18 8 0x30 (by decide),
      mr_cut_add sp 0x20 4 0x2c (by decide),
      mr_cut_add sp 0x24 4 0x28 (by decide),
      mr_cut_add sp 0x28 8 0x20 (by decide),
      mr_cut_add sp 0x30 4 0x1c (by decide),
      mr_cut_add sp 0x34 4 0x18 (by decide),
      mr_cut_add sp 0x38 8 0x10 (by decide),
      mr_cut_add sp 0x40 8 8 (by decide),
      ProofLib.memRegion_eight (sp + 0x18#64),
      ProofLib.memRegion_four (sp + 0x24#64),
      ProofLib.memRegion_eight (sp + 0x28#64),
      ProofLib.memRegion_four (sp + 0x34#64),
      ProofLib.memRegion_eight (sp + 0x38#64),
      ProofLib.memRegion_eight (sp + 0x40#64),
      ProofLib.memRegion_eight (sp + 0x48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

theorem poll_unackItems_regions (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x298 ∗
      memRegion (sp + 0x870#64) 36 ∗
      memRegion (sp + 0x894#64) 0x21c ∗
      memRegion (sp + 0xab0#64) 36 ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      memRegion (sp + 0xb00#64) 16 ∗
      memRegion (sp + 0xb10#64) 0x70 := by
  rw [mr_cut_add sp 0x46a 0x116 0x600 (by decide),
      mr_cut_add sp 0x580 88 0x5a8 (by decide),
      mr_cut_add sp 0x5d8 0x298 0x310 (by decide),
      mr_cut_add sp 0x870 36 0x2ec (by decide),
      mr_cut_add sp 0x894 0x21c 0xd0 (by decide),
      mr_cut_add sp 0xab0 36 0xac (by decide),
      mr_cut_add sp 0xad4 0x2c 0x80 (by decide),
      mr_cut_add sp 0xb00 16 0x70 (by decide)]

theorem memRegion_36_unpack (a : BitVec 64) :
    memRegion a 36 ⊢
      ∃∗ w4 : BitVec 32, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
        ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₃₂ w4) := by
  rw [memRegion_split a 8 28 (by decide),
      mr_cut_add a 8 8 20 (by decide),
      mr_cut_add a 16 8 12 (by decide),
      mr_cut_add a 24 8 4 (by decide)]
  simp only [ProofLib.memRegion_eight, ProofLib.memRegion_four,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion_16_ts_unpack (a : BitVec 64) :
    memRegion a 16 ⊢
      ∃∗ w1 : BitVec 32, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₃₂ w1) ∗ memRegion (a + 12#64) 4 := by
  rw [memRegion_split a 8 8 (by decide),
      mr_cut_add a 8 4 4 (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_four (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem unackOut_cells_entails_memRegion_88 (a : BitVec 64)
    (w0 w1 : BitVec 32) (w2 w3 : BitVec 64) (w4 : BitVec 32)
    (bk0 bk1 bk2 bk3 : BitVec 64) (bk4 : BitVec 32)
    (kyPtr kyLen : BitVec 64) (spk : BitVec 32) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
      ((a + 24#64) ↦₃₂ w4) ∗ ((a + 28#64) ↦₆₄ bk0) ∗ ((a + 36#64) ↦₆₄ bk1) ∗
      ((a + 44#64) ↦₆₄ bk2) ∗ ((a + 52#64) ↦₆₄ bk3) ∗ ((a + 60#64) ↦₃₂ bk4) ∗
      ((a + 64#64) ↦₆₄ kyPtr) ∗ ((a + 72#64) ↦₆₄ kyLen) ∗
      ((a + 80#64) ↦₃₂ spk) ∗ memRegion (a + 84#64) 4) ⊢
      memRegion a 88 := by
  rw [memRegion_split a 4 84 (by decide),
      mr_cut_add a 4 4 80 (by decide),
      mr_cut_add a 8 8 72 (by decide),
      mr_cut_add a 16 8 64 (by decide),
      mr_cut_add a 24 4 60 (by decide),
      mr_cut_add a 28 8 52 (by decide),
      mr_cut_add a 36 8 44 (by decide),
      mr_cut_add a 44 8 36 (by decide),
      mr_cut_add a 52 8 28 (by decide),
      mr_cut_add a 60 4 24 (by decide),
      mr_cut_add a 64 8 16 (by decide),
      mr_cut_add a 72 8 8 (by decide),
      mr_cut_add a 80 4 4 (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo32_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (sepConj_mono_left (pointsTo32_entails_memRegion _ _)))))))))))))

theorem cells36_entails_memRegion_36 (a : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₃₂ w4)) ⊢
      memRegion a 36 := by
  rw [memRegion_split a 8 28 (by decide),
      mr_cut_add a 8 8 20 (by decide),
      mr_cut_add a 16 8 12 (by decide),
      mr_cut_add a 24 8 4 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo32_entails_memRegion _ _))))

theorem ts_cells_entails_memRegion_16 (a : BitVec 64) (w0 : BitVec 64) (w1 : BitVec 32) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₃₂ w1) ∗ memRegion (a + 12#64) 4) ⊢
      memRegion a 16 := by
  rw [memRegion_split a 8 8 (by decide),
      mr_cut_add a 8 4 4 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo32_entails_memRegion _ _))

/-! ## State Before `duration_since` (`+0x6c4`) -/

/-- Call scratch layout `sp + 0x00 .. sp + 0x58` after `+0x6b8`, extending `cmScratch` with the
four pre-key spills in `sp + 0x18 .. sp + 0x38`. -/
@[expose] def preKeyScratch (sp kyLen : BitVec 64) (spk kyIdVal pkVal : BitVec 32)
    (kyber : Option PendingKyberPreKey) : SepProp :=
  memRegion sp 0x18 ∗
    ((sp + 0x18#64) ↦₆₄ kyLen) ∗
    memRegion (sp + 0x20#64) 4 ∗
    ((sp + 0x24#64) ↦₃₂ spk) ∗
    ((sp + 0x28#64) ↦₆₄ (kyIdVal ++ (if (kyber.map (·.preKeyId)).isSome then 1#32 else 0#32))) ∗
    memRegion (sp + 0x30#64) 4 ∗
    ((sp + 0x34#64) ↦₃₂ pkVal) ∗
    ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
    ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
    ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
    ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Poll buffer layout `sp + 0x46a .. sp + 0xb80` holding `items.baseKey` at `sp + 0xab4`. -/
@[expose] def pollWithBaseKey (sp : BitVec 64) (items : PendingPreKey) : SepProp :=
  memRegion (sp + 0x46a#64) 0x64a ∗
    ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0xac

theorem encSubStack_split_unack {sp ssp : BitVec 64} (hsp : ssp = sp) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack)
        (encSubStack - unackItemsStack) ∗
      stackAt ssp unackItemsStack := by
  subst ssp
  show memRegion (sp - BitVec.ofNat 64 encSubStack) encSubStack = _
  rw [mr_cut' sp encSubStack unackItemsStack (encSubStack - unackItemsStack)
    unackItemsStack encSubStack rfl rfl (by decide) (by decide) (by decide)]

theorem encSeam_mem_group {m : Memory} {A1 A2 A3 A4 A5 A6 R : SepProp}
    (h : m ⊨ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) :
    m ⊨ (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6) ∗ R := by
  simpa only [sepConj_assoc] using h

theorem sepWPp_elim_ex {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {C : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (C x ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ x : α, C x) ∗ F) Q Qp := by
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

theorem sepWPp_fold_ex1 {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {φ : α → Prop} {C : α → SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ ∃∗ x : α, ⌜φ x⌝ ∗ C x) (hf : P = T ∗ F)
    (h : ∀ x, φ x → SepWPp prog ret s (C x ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.fold hent hf ?_
  refine sepWPp_elim_ex fun x => ?_
  rw [sepConj_assoc]
  exact SepWPp.pure_elim (h x)

theorem sepWPp_fold_ex2 {α β : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {φ : α → β → Prop} {C : α → β → SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ ∃∗ x : α, ∃∗ y : β, ⌜φ x y⌝ ∗ C x y) (hf : P = T ∗ F)
    (h : ∀ x y, φ x y → SepWPp prog ret s (C x y ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.fold hent hf ?_
  refine sepWPp_elim_ex fun x => sepWPp_elim_ex fun y => ?_
  rw [sepConj_assoc]
  exact SepWPp.pure_elim (h x y)

theorem sepWPp_fold_ex5 {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {φ : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 32 → Prop}
    {C : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 32 → SepProp}
    {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ ∃∗ x0 : BitVec 64, ∃∗ x1 : BitVec 64, ∃∗ x2 : BitVec 64, ∃∗ x3 : BitVec 64,
      ∃∗ x4 : BitVec 32, ⌜φ x0 x1 x2 x3 x4⌝ ∗ C x0 x1 x2 x3 x4)
    (hf : P = T ∗ F)
    (h : ∀ x0 x1 x2 x3 x4, φ x0 x1 x2 x3 x4 → SepWPp prog ret s (C x0 x1 x2 x3 x4 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.fold hent hf ?_
  refine sepWPp_elim_ex fun x0 => sepWPp_elim_ex fun x1 => sepWPp_elim_ex fun x2 =>
    sepWPp_elim_ex fun x3 => sepWPp_elim_ex fun x4 => ?_
  rw [sepConj_assoc]
  exact SepWPp.pure_elim (h x0 x1 x2 x3 x4)

theorem baseKeyShift_unpack_59c (sp : BitVec 64) (k : PublicKey) :
    (memRegion (sp + 0x59c#64) 4 ∗ ((sp + 0x5a0#64) ↦ₛ k.bytes.toList)) ⊢
      ∃∗ bk0 : BitVec 64, ∃∗ bk1 : BitVec 64, ∃∗ bk2 : BitVec 64, ∃∗ bk3 : BitVec 64,
      ∃∗ bk4 : BitVec 32,
        ⌜baseKeyShiftProp k.bytes.toList bk0 bk1 bk2 bk3 bk4⌝ ∗
        ((sp + 0x59c#64) ↦₆₄ bk0) ∗ ((sp + 0x5a4#64) ↦₆₄ bk1) ∗ ((sp + 0x5ac#64) ↦₆₄ bk2) ∗
        ((sp + 0x5b4#64) ↦₆₄ bk3) ∗ ((sp + 0x5bc#64) ↦₃₂ bk4) := by
  have h := baseKeyShift_unpack (sp + 0x59c#64) (bs := k.bytes.toList) (by simp)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

theorem baseKeyShift_pack_ab0 (sp : BitVec 64) (k : PublicKey)
    (bk0 bk1 bk2 bk3 : BitVec 64) (bk4 : BitVec 32)
    (hbk : baseKeyShiftProp k.bytes.toList bk0 bk1 bk2 bk3 bk4) :
    (((sp + 0xab0#64) ↦₆₄ bk0) ∗ ((sp + 0xab8#64) ↦₆₄ bk1) ∗ ((sp + 0xac0#64) ↦₆₄ bk2) ∗
      ((sp + 0xac8#64) ↦₆₄ bk3) ∗ ((sp + 0xad0#64) ↦₃₂ bk4)) ⊢
      (memRegion (sp + 0xab0#64) 4 ∗ ((sp + 0xab4#64) ↦ₛ k.bytes.toList)) := by
  have h' : (((sp + 0xab0#64) ↦₆₄ bk0) ∗ ((sp + 0xab0#64 + 8#64) ↦₆₄ bk1) ∗
      ((sp + 0xab0#64 + 16#64) ↦₆₄ bk2) ∗ ((sp + 0xab0#64 + 24#64) ↦₆₄ bk3) ∗
      ((sp + 0xab0#64 + 32#64) ↦₃₂ bk4)) ⊢
      (memRegion (sp + 0xab0#64) 4 ∗ ((sp + 0xab0#64 + 4#64) ↦ₛ k.bytes.toList)) :=
    Entails.trans (Entails.pure_right hbk (Entails.refl _))
      (baseKeyShift_pack (sp + 0xab0#64) (bs := k.bytes.toList) bk0 bk1 bk2 bk3 bk4)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h'

theorem unackOutAt_taken_some (sp : BitVec 64) (kyG : Option TailVecGhost)
    (sess : Session (List (BitVec 8))) (items : PendingPreKey)
    (hpk : sess.pendingPreKey = some items) :
    unackOutAt (sp + 0x580#64) kyG sess.pendingKyberPreKey sess.pendingPreKey ⊢
    ∃∗ ts : SystemTime, ⌜SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts⌝ ∗
      optU32At (sp + 0x580#64) items.preKeyId ∗
      optU32At (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)) ∗
      ((sp + 0x590#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0x598#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0x59c#64) 4 ∗
      ((sp + 0x5a0#64) ↦ₛ items.baseKey.bytes.toList) ∗
      unackKyberSliceAt (sp + 0x5c0#64) kyG ∗
      ((sp + 0x5d0#64) ↦₃₂ items.signedPreKeyId) ∗
      memRegion (sp + 0x5d4#64) 4 := by
  dsimp only [unackOutAt]
  rw [hpk]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

@[simp, arm64_norm, wp_norm]
theorem ite_one_zero_add_one_beq_zero (b : Bool) :
    ((if b = true then 1#32 else 0#32) + 1#32 == 0#32) = false := by
  cases b <;> rfl

@[simp, arm64_norm, wp_norm]
theorem ite_one_zero_sub_two_beq_zero (b : Bool) :
    ((if b = true then 1#32 else 0#32) - 2#32 == 0#32) = false := by
  cases b <;> rfl

@[simp, arm64_norm, wp_norm]
theorem ite_one_zero_beq_two (b : Bool) :
    ((if b = true then 1#32 else 0#32) == 2#32) = false := by
  cases b <;> rfl

@[simp, arm64_norm, wp_norm]
theorem ite_one_zero_bne_two (b : Bool) :
    ((if b = true then 1#32 else 0#32) != 2#32) = true := by
  cases b <;> rfl

theorem sp_sub_60_eq_add_b80 (sp0 : BitVec 64) :
    sp0 - 0x60#64 = (sp0 - 0xbe0#64) + 0xb80#64 := by
  bv_omega

theorem calleeSavedPreserved_after_bl {s s1 : State} {lr pc : BitVec 64}
    (h : CalleeSavedPreserved ((s.writeReg64 (.gpr 30#5) lr).setPC pc) s1) :
    CalleeSavedPreserved s s1 := by
  rwa [CalleeSavedPreserved_setPC_left,
    CalleeSavedPreserved_writeReg64_caller_left _ _ _ _ (by decide)] at h

theorem sp_after_bl (s : State) (lr pc : BitVec 64) :
    ((s.writeReg64 (.gpr 30#5) lr).setPC pc).sp = s.sp := rfl

theorem trace_after_bl (s : State) (lr pc : BitVec 64) :
    ((s.writeReg64 (.gpr 30#5) lr).setPC pc).trace = s.trace := rfl

theorem memRegion_16_ts_unpack_b00 (sp : BitVec 64) :
    memRegion (sp + 0xb00#64) 16 ⊢
      ∃∗ w1 : BitVec 32, ∃∗ w0 : BitVec 64,
        ((sp + 0xb00#64) ↦₆₄ w0) ∗ ((sp + 0xb08#64) ↦₃₂ w1) ∗ memRegion (sp + 0xb0c#64) 4 := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
    memRegion_16_ts_unpack (sp + 0xb00#64)

theorem ts_cells_entails_memRegion_16_b00 (sp : BitVec 64) (w0 : BitVec 64) (w1 : BitVec 32) :
    (((sp + 0xb00#64) ↦₆₄ w0) ∗ ((sp + 0xb08#64) ↦₃₂ w1) ∗ memRegion (sp + 0xb0c#64) 4) ⊢
      memRegion (sp + 0xb00#64) 16 := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
    ts_cells_entails_memRegion_16 (sp + 0xb00#64) w0 w1

theorem cells36_entails_memRegion_36_870 (sp : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    (((sp + 0x870#64) ↦₆₄ w0) ∗ ((sp + 0x878#64) ↦₆₄ w1) ∗ ((sp + 0x880#64) ↦₆₄ w2) ∗
      ((sp + 0x888#64) ↦₆₄ w3) ∗ ((sp + 0x890#64) ↦₃₂ w4)) ⊢
      memRegion (sp + 0x870#64) 36 := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    cells36_entails_memRegion_36 (sp + 0x870#64) w0 w1 w2 w3 w4

theorem unackOut_cells_entails_memRegion_88_580 (sp : BitVec 64)
    (w0 w1 : BitVec 32) (w2 w3 : BitVec 64) (w4 : BitVec 32)
    (bk0 bk1 bk2 bk3 : BitVec 64) (bk4 : BitVec 32)
    (kyPtr kyLen : BitVec 64) (spk : BitVec 32) :
    (((sp + 0x580#64) ↦₃₂ w0) ∗ ((sp + 0x584#64) ↦₃₂ w1) ∗ ((sp + 0x588#64) ↦₆₄ w2) ∗
      ((sp + 0x590#64) ↦₆₄ w3) ∗ ((sp + 0x598#64) ↦₃₂ w4) ∗ ((sp + 0x59c#64) ↦₆₄ bk0) ∗
      ((sp + 0x5a4#64) ↦₆₄ bk1) ∗ ((sp + 0x5ac#64) ↦₆₄ bk2) ∗ ((sp + 0x5b4#64) ↦₆₄ bk3) ∗
      ((sp + 0x5bc#64) ↦₃₂ bk4) ∗ ((sp + 0x5c0#64) ↦₆₄ kyPtr) ∗ ((sp + 0x5c8#64) ↦₆₄ kyLen) ∗
      ((sp + 0x5d0#64) ↦₃₂ spk) ∗ memRegion (sp + 0x5d4#64) 4) ⊢
      memRegion (sp + 0x580#64) 88 := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    unackOut_cells_entails_memRegion_88 (sp + 0x580#64) w0 w1 w2 w3 w4 bk0 bk1 bk2 bk3 bk4 kyPtr kyLen spk

theorem poll_unackItems_pack_pollWithBaseKey (sp : BitVec 64) (items : PendingPreKey) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x298 ∗
      memRegion (sp + 0x870#64) 36 ∗
      memRegion (sp + 0x894#64) 0x21c ∗
      memRegion (sp + 0xab0#64) 4 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      memRegion (sp + 0xb00#64) 16 ∗
      memRegion (sp + 0xb10#64) 0x70) ⊢
    pollWithBaseKey sp items := by
  unfold pollWithBaseKey
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 88 0x4dc (by decide),
      mr_cut_add sp 0x5d8 0x298 0x244 (by decide),
      mr_cut_add sp 0x870 36 0x220 (by decide),
      mr_cut_add sp 0x894 0x21c 4 (by decide),
      mr_cut_add sp 0xad4 0x2c 0x80 (by decide),
      mr_cut_add sp 0xb00 16 0x70 (by decide)]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem sepWP_fold_preKeyScratch {prog : Program} {pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop}
    (sp kyLen w28 : BitVec 64) (spk kyIdVal pkVal : BitVec 32)
    (kyber : Option PendingKyberPreKey)
    (hf : P = (memRegion sp 0x18 ∗
      ((sp + 0x18#64) ↦₆₄ kyLen) ∗
      memRegion (sp + 0x20#64) 4 ∗
      ((sp + 0x24#64) ↦₃₂ spk) ∗
      ((sp + 0x28#64) ↦₆₄ w28) ∗
      memRegion (sp + 0x30#64) 4 ∗
      ((sp + 0x34#64) ↦₃₂ pkVal) ∗
      ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
      ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗ F)
    (hw28 : w28 = kyIdVal ++ (if (kyber.map (·.preKeyId)).isSome then 1#32 else 0#32))
    (h : SepWP prog pc s (preKeyScratch sp kyLen spk kyIdVal pkVal kyber ∗ F) post) :
    SepWP prog pc s P post := by
  subst hw28
  exact SepWP.fold (Entails.refl _) hf h

theorem encSubStack_pack_unack {sp : BitVec 64} {s : State} (hsp : s.sp = sp)
    (lr pc : BitVec 64) :
    (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
      stackAt ((s.writeReg64 (.gpr 30#5) lr).setPC pc).sp unackItemsStack) ⊢
    stackAt sp encSubStack := by
  dsimp only [State.sp, State.setPC, State.writeReg64, State.readReg64] at hsp ⊢
  rw [hsp, ← encSubStack_split_unack rfl]
  exact Entails.refl _

theorem encSubStack_split_ext {sp ssp : BitVec 64} (hsp : ssp = sp) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack)
        (encSubStack - extHookStack) ∗
      stackAt ssp extHookStack := by
  subst ssp
  show memRegion (sp - BitVec.ofNat 64 encSubStack) encSubStack = _
  rw [mr_cut' sp encSubStack extHookStack (encSubStack - extHookStack)
    extHookStack encSubStack rfl rfl (by decide) (by decide) (by decide)]

theorem stackAt_eq_sp {s_call s_ret : State} {n : Nat} (hsp : s_ret.sp = s_call.sp) :
    stackAt s_call.sp n ⊢ stackAt s_ret.sp n := by
  rw [hsp]; exact Entails.refl _

theorem encSubStack_pack_ext {sp : BitVec 64} {s : State} (hsp : s.sp = sp)
    (lr pc : BitVec 64) :
    (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      stackAt ((s.writeReg64 (.gpr 30#5) lr).setPC pc).sp extHookStack) ⊢
    stackAt sp encSubStack := by
  dsimp only [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64] at hsp ⊢
  rw [hsp, ← encSubStack_split_ext rfl]
  exact Entails.refl _

theorem pollWithBaseKey_dur_unpack (sp : BitVec 64) (items : PendingPreKey) :
    pollWithBaseKey sp items =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 0x300 ∗
      memRegion (sp + 0x898#64) 8 ∗
      memRegion (sp + 0x8a0#64) 0x214 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      memRegion (sp + 0xb00#64) 16 ∗
      memRegion (sp + 0xb10#64) 0x70 := by
  unfold pollWithBaseKey
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 24 0x51c (by decide),
      mr_cut_add sp 0x598 0x300 0x21c (by decide),
      mr_cut_add sp 0x898 8 0x214 (by decide),
      mr_cut_add sp 0xad4 0x2c 0x80 (by decide),
      mr_cut_add sp 0xb00 16 0x70 (by decide)]
  simp only [sepConj_assoc]

theorem dur_ret_24_unpack (sp : BitVec 64) :
    memRegion (sp + 0x580#64) 24 ⊢
      ∃∗ w588 : BitVec 64, ∃∗ w580 : BitVec 32,
        ((sp + 0x580#64) ↦₃₂ w580) ∗ memRegion (sp + 0x584#64) 4 ∗
        ((sp + 0x588#64) ↦₆₄ w588) ∗ memRegion (sp + 0x590#64) 8 := by
  rw [mr_cut_add sp 0x580 4 20 (by decide),
      mr_cut_add sp 0x584 4 16 (by decide),
      mr_cut_add sp 0x588 8 8 (by decide),
      ProofLib.memRegion_four (sp + 0x580#64),
      ProofLib.memRegion_eight (sp + 0x588#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion_8_898_unpack (sp : BitVec 64) :
    memRegion (sp + 0x898#64) 8 ⊢ ∃∗ w898 : BitVec 64, (sp + 0x898#64) ↦₆₄ w898 := by
  rw [ProofLib.memRegion_eight (sp + 0x898#64)]
  exact Entails.refl _

theorem pollWithBaseKey_dur_pack (sp : BitVec 64) (items : PendingPreKey)
    (w580 : BitVec 32) (w588 w898 : BitVec 64) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      ((sp + 0x580#64) ↦₃₂ w580) ∗ memRegion (sp + 0x584#64) 4 ∗
      ((sp + 0x588#64) ↦₆₄ w588) ∗ memRegion (sp + 0x590#64) 8 ∗
      memRegion (sp + 0x598#64) 0x300 ∗
      ((sp + 0x898#64) ↦₆₄ w898) ∗
      memRegion (sp + 0x8a0#64) 0x214 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      memRegion (sp + 0xb00#64) 16 ∗
      memRegion (sp + 0xb10#64) 0x70) ⊢
    pollWithBaseKey sp items := by
  rw [pollWithBaseKey_dur_unpack sp items,
      mr_cut_add sp 0x580 4 20 (by decide),
      mr_cut_add sp 0x584 4 16 (by decide),
      mr_cut_add sp 0x588 8 8 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))))

theorem dur_mem_group {m : Memory}
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R : SepProp}
    (h : m ⊨ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) :
    m ⊨ (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13) ∗ R := by
  simpa only [sepConj_assoc] using h

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
