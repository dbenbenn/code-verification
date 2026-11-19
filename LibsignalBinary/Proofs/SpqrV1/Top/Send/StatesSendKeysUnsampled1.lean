/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled -- proof-setup: allow-public-import
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `.keysUnsampled` Sub-Steps (`+372..+684`)

**Checked by Lean.**

Verifies `+372..+684` of the inlined `.keysUnsampled` arm of `<States>::send`:
64-byte RNG draw, ML-KEM keypair generation (`from_seed`, `pk1`, `pk2`), and heap allocation
of `hdr` (`64`B), `ek` (`1152`B), and `dk` (`2400`B).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

theorem stackAt_spqrSendCallee_to_extHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack ⊢
    memRegion (sp - 123008#64) 106624 ∗ stackAt sp extHookStack := by
  rw [stackAt_spqrSendCallee_split sp extHookStack (by decide)]
  exact Entails.refl _

theorem stackAt_spqrSendCallee_from_extHook (sp : BitVec 64) :
    memRegion (sp - 123008#64) 106624 ∗ stackAt sp extHookStack ⊢
    stackAt sp spqrSendCalleeStack := by
  rw [stackAt_spqrSendCallee_split sp extHookStack (by decide)]
  exact Entails.refl _

theorem stackAt_spqrSendCallee_to_allocHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack ⊢
    memRegion (sp - 123008#64) 118912 ∗ stackAt sp allocHookStack := by
  rw [stackAt_spqrSendCallee_split sp allocHookStack (by decide)]
  exact Entails.refl _

theorem stackAt_spqrSendCallee_from_allocHook (sp : BitVec 64) :
    memRegion (sp - 123008#64) 118912 ∗ stackAt sp allocHookStack ⊢
    stackAt sp spqrSendCalleeStack := by
  rw [stackAt_spqrSendCallee_split sp allocHookStack (by decide)]
  exact Entails.refl _

theorem finish_oom_panic {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp}
    {post : State → SepProp → Prop}
    (hextern : prog.externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.panic hrun hextern fun hm => ?_
  simpa only [sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, htr])) hm

/-- Eight consecutive 64-bit words (`64` bytes) at `a`. -/
@[expose] def words8At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
  ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)

theorem words8At_entails_memRegion (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    words8At a w0 w1 w2 w3 w4 w5 w6 w7 ⊢ memRegion a 64 := by
  unfold words8At
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 56) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 48) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 40) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 32) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 24) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 16) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 8) (b' := a + 56#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (ProofLib.pointsTo64_entails_memRegion _ _)))))))

theorem memRegion_64_eq_words8 (a : BitVec 64) :
    memRegion a 64 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (a + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (a + 56#64) ↦₆₄ d7) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 56) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 48) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 40) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 32) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 24) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 16) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 8) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
      ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 56#64)]

theorem exists_words8_of_len64 (bs : List (BitVec 8)) (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) = words8At a w0 w1 w2 w3 w4 w5 w6 w7 := by
  have h1 : (bs.take 32).length = 32 := by rw [List.length_take]; omega
  have h2 : (bs.drop 32).length = 32 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, hw1⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32 (bs.take 32) h1
  obtain ⟨w4, w5, w6, w7, hw2⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32 (bs.drop 32) h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  rw [← List.take_append_drop 32 bs, pointsToBytes_append a (bs.take 32) (bs.drop 32), h1,
      hw1, hw2,
      CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq a,
      CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq (a + 32#64)]
  unfold words8At
  rw [show (a + 32#64) + 8#64 = a + 40#64 by bv_omega,
      show (a + 32#64) + 16#64 = a + 48#64 by bv_omega,
      show (a + 32#64) + 24#64 = a + 56#64 by bv_omega]
  ac_rfl

theorem pointsToBytes_2400_expose_pk1 {K : MlKem} (sp : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1 : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList) :
    let dk := (K.fromSeed seed).2.2.toList
    ((sp + 4704#64) ↦ₛ dk) =
      ((sp + 7008#64) ↦ₛ (K.fromSeed seed).1.toList) ∗
      (((sp + 4704#64) ↦ₛ dk.take 2304) ∗
       ((sp + 7072#64) ↦ₛ (dk.drop 2304).drop 64)) := by
  intro dk
  have hlen : dk.length = 2400 := List.Vector.toList_length _
  have h1 : (dk.take 2304).length = 2304 := by rw [List.length_take]; omega
  have h2 : ((dk.drop 2304).take 64).length = 64 := by rw [List.length_take, List.length_drop]; omega
  conv_lhs => rw [← List.take_append_drop 2304 dk, ← List.take_append_drop 64 (dk.drop 2304)]
  rw [pointsToBytes_append (sp + 4704#64) (dk.take 2304), h1,
      show (sp + 4704#64) + 2304#64 = sp + 7008#64 by bv_omega,
      pointsToBytes_append (sp + 7008#64) ((dk.drop 2304).take 64), h2,
      show (sp + 7008#64) + 64#64 = sp + 7072#64 by bv_omega,
      hpk1]
  ac_rfl

theorem pointsToBytes_2400_expose_pk2 {K : MlKem} (sp : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk2 : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList) :
    let dk := (K.fromSeed seed).2.2.toList
    ((sp + 4704#64) ↦ₛ dk) =
      ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
      (((sp + 4704#64) ↦ₛ dk.take 1152) ∗
       ((sp + 7008#64) ↦ₛ (dk.drop 1152).drop 1152)) := by
  intro dk
  have hlen : dk.length = 2400 := List.Vector.toList_length _
  have h1 : (dk.take 1152).length = 1152 := by rw [List.length_take]; omega
  have h2 : ((dk.drop 1152).take 1152).length = 1152 := by rw [List.length_take, List.length_drop]; omega
  conv_lhs => rw [← List.take_append_drop 1152 dk, ← List.take_append_drop 1152 (dk.drop 1152)]
  rw [pointsToBytes_append (sp + 4704#64) (dk.take 1152), h1,
      show (sp + 4704#64) + 1152#64 = sp + 5856#64 by bv_omega,
      pointsToBytes_append (sp + 5856#64) ((dk.drop 1152).take 1152), h2,
      show (sp + 5856#64) + 1152#64 = sp + 7008#64 by bv_omega,
      hpk2]
  ac_rfl

/-- Unused stack padding slots within `[sp + 3328, sp + 7936)` during `.keysUnsampled`. -/
@[irreducible] def keysUnsampledUnusedAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 3328#64) 224 ∗
  memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4184#64) 8 ∗
  memRegion (sp + 4696#64) 8 ∗
  memRegion (sp + 7128#64) 8

theorem memRegion_4608_split_keysUnsampled (sp : BitVec 64) :
    memRegion (sp + 3328#64) 4608 =
      keysUnsampledUnusedAt sp ∗
      memRegion (sp + 3552#64) 504 ∗
      (∃∗ d4056 : BitVec 64, (sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 := by
  unfold keysUnsampledUnusedAt
  rw [ProofLib.memRegion_split' (b := sp + 3328#64) (n := 224) (k := 4384) (b' := sp + 3552#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 3552#64) (n := 504) (k := 3880) (b' := sp + 4056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4056#64) (n := 8) (k := 3872) (b' := sp + 4064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4064#64) (n := 16) (k := 3856) (b' := sp + 4080#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 104) (k := 3752) (b' := sp + 4184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4184#64) (n := 8) (k := 3744) (b' := sp + 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 504) (k := 3240) (b' := sp + 4696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4696#64) (n := 8) (k := 3232) (b' := sp + 4704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4704#64) (n := 2400) (k := 832) (b' := sp + 7104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 24) (k := 808) (b' := sp + 7128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7128#64) (n := 8) (k := 800) (b' := sp + 7136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 400) (k := 400) (b' := sp + 7536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4056#64)]
  ac_rfl

theorem rngFill_take64_eq (ctl cur dst : BitVec 64) (rest : List (BitVec 8))
    (h64 : 64 ≤ rest.length) :
    (dst ↦ₛ (rest ++ List.replicate 64 0#8).take 64) ∗ tapeAfter ctl cur rest (min 64 rest.length) =
      (dst ↦ₛ rest.take 64) ∗ tapeAfter ctl cur rest 64 := by
  rw [List.take_append_of_le_length h64, Nat.min_eq_left h64]

theorem live_pointsTo_entails_vecU8Buf {A : RustAlloc} (ptr : BitVec 64) (bs : List (BitVec 8))
    (size : Nat) (hlen : bs.length = size) (hpos : 0 < size) (hlt : size < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    A.live ptr size 1 ∗ (ptr ↦ₛ bs) ⊢
    RustHeap.vecU8Buf A (BitVec.ofNat 64 size) ptr bs := by
  have htoNat : (BitVec.ofNat 64 size).toNat = size := Nat.mod_eq_of_lt (by omega)
  have hne0 : BitVec.ofNat 64 size ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [htoNat] at this
    change size = 0 at this
    omega
  unfold RustHeap.vecU8Buf
  simp only [hne0, ↓reduceIte, htoNat, hlen, Nat.sub_self,
    ProofLib.memRegion_zero, sepConj_emp, emp_sepConj]
  exact Entails.pure_right ⟨Nat.le_refl size, hlt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem fold_vecU8_at (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  have heq :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs =
      vecU8At A a cap ptr bs := by
    unfold vecU8At vecHeader RustHeap.vecU8Buf
    have hp : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
        (ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63) := propext ⟨fun ⟨h1, h2, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨h1, h2, h3⟩⟩
    rw [hp]
    by_cases hc : cap = 0 <;> simp only [hc, ↓reduceIte] <;> ac_rfl
  rw [heq]
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem memRegion_48_eq_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64)]

end CryptoVerification.SpqrV1.Top.Send

