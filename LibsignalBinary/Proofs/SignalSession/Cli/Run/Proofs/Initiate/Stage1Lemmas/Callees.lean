/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.StringCloneFlatX
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Stage 1 Callee Wrappers and Shared Error Epilogue

Provides stack-frame split/merge lemmas, `SpeOwned` error payload builders, direct `BL` callee
wrappers at residual stack `stk - cliInitiateFrame`, and the shared Stage 1 error epilogue
(`0x0350 → ret`) for `signal_session_handshake::initiate`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open Stage1Norm

/-! ## Stack split/merge and `SpeOwned` payload builders -/

theorem stackAt_sub_split_local (sp : BitVec 64) {sub full : Nat}
    (hle : sub ≤ full) (hfull : full ≤ 2 ^ 64) :
    stackAt sp full =
      memRegion (sp - BitVec.ofNat 64 full) (full - sub) ∗ stackAt sp sub := by
  have h := stackAt_split_bottom sp sub (full - sub) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

theorem stackAt_entry_split (s0 : State) {stk : Nat}
    (hge : cliInitiateFrame ≤ stk) (hle : stk ≤ 2 ^ 63) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    stackAt s0.sp stk =
      stackAt fsp (stk - cliInitiateFrame) ∗
        memRegion fsp initLocalsSize ∗
        memRegion (s0.sp - 0x60#64) 0x60 := by
  intro fsp
  have h1 : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliInitiateFrame) ∗
        stackAt s0.sp cliInitiateFrame :=
    stackAt_sub_split_local s0.sp hge (by omega)
  have hbot : memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliInitiateFrame) =
      stackAt fsp (stk - cliInitiateFrame) := by
    unfold stackAt
    have haddr : s0.sp - BitVec.ofNat 64 stk =
        fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) := by
      dsimp only [fsp]
      have hd : BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) =
          BitVec.ofNat 64 stk := by
        rw [← BitVec.ofNat_add, Nat.add_sub_cancel' hge]
      rw [← hd]
      exact (BitVec.sub_sub s0.sp _ _).symm
    rw [haddr]
  have htop : stackAt s0.sp cliInitiateFrame =
      memRegion fsp initLocalsSize ∗ memRegion (s0.sp - 0x60#64) 0x60 := by
    unfold stackAt
    change memRegion fsp (initLocalsSize + 0x60) = _
    rw [memRegion_split fsp initLocalsSize 0x60 (by decide)]
    have hfp : fsp + BitVec.ofNat 64 initLocalsSize = s0.sp - 0x60#64 := by
      dsimp only [fsp]
      change (s0.sp - 7408#64) + 7312#64 = s0.sp - 96#64
      bv_omega
    rw [hfp]
  rw [h1, hbot, htop]

theorem memRegion_saved_split (b : BitVec 64) :
    memRegion b 0x60 =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((b + 0x00#64) ↦₆₄ w0) ∗ ((b + 0x08#64) ↦₆₄ w1) ∗
        ((b + 0x10#64) ↦₆₄ w2) ∗ ((b + 0x18#64) ↦₆₄ w3) ∗
        ((b + 0x20#64) ↦₆₄ w4) ∗ ((b + 0x28#64) ↦₆₄ w5) ∗
        ((b + 0x30#64) ↦₆₄ w6) ∗ ((b + 0x38#64) ↦₆₄ w7) ∗
        ((b + 0x40#64) ↦₆₄ w8) ∗ ((b + 0x48#64) ↦₆₄ w9) ∗
        ((b + 0x50#64) ↦₆₄ w10) ∗ ((b + 0x58#64) ↦₆₄ w11) := by
  have split8 : ∀ a n, n ≥ 8 → n ≤ 96 →
      memRegion a n = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) (n - 8) := by
    intro a n hge _hle
    have hn : n = 8 + (n - 8) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split a 8 (n - 8) (by omega), ProofLib.memRegion_eight]
  rw [split8 b 96 (by decide) (by decide),
      split8 _ 88 (by decide) (by decide),
      split8 _ 80 (by decide) (by decide),
      split8 _ 72 (by decide) (by decide),
      split8 _ 64 (by decide) (by decide),
      split8 _ 56 (by decide) (by decide),
      split8 _ 48 (by decide) (by decide),
      split8 _ 40 (by decide) (by decide),
      split8 _ 32 (by decide) (by decide),
      split8 _ 24 (by decide) (by decide),
      split8 _ 16 (by decide) (by decide),
      ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    sepExists_sepConj_left, sepExists_sepConj_right]

theorem initSaved_entails_memRegion (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  unfold initSaved
  dsimp only
  rw [memRegion_saved_split (s0.sp - 0x60#64)]
  sep_frame

theorem memRegion_48_words (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  have split8 : ∀ p n, n ≥ 8 → n ≤ 48 →
      memRegion p n = (∃∗ w : BitVec 64, p ↦₆₄ w) ∗ memRegion (p + 8#64) (n - 8) := by
    intro p n hge _hle
    have hn : n = 8 + (n - 8) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split p 8 (n - 8) (by omega), ProofLib.memRegion_eight]
  rw [split8 a 48 (by decide) (by decide),
      split8 _ 40 (by decide) (by decide),
      split8 _ 32 (by decide) (by decide),
      split8 _ 24 (by decide) (by decide),
      split8 _ 16 (by decide) (by decide),
      ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

abbrev stage1Err : Except (ApiError AddrVal Unit) Unit :=
  .error (.untrustedIdentity ⟨[], 0#8⟩)

theorem words_to_plain11_initResAt (A : RustAlloc) (r w0 w1 w2 w3 w4 w5 : BitVec 64)
    (hw0 : w0 = speWord 11) :
    (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗
      ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ⊢
      initResAt A r stage1Err := by
  subst hw0
  have h11 : RunDrop.PlainSpeTag 11 := by decide
  change _ ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k
  refine Entails.sepExists_right (RunDrop.SpeOwned.plain 11 h11) ?_
  dsimp only [RunDrop.speOwnedAt]
  have htail :
      ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗
        ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ⊢
        memRegion (r + 8#64) 40 := by
    have split8 : ∀ p n, n ≥ 8 → n ≤ 40 →
        memRegion p n = (∃∗ w : BitVec 64, p ↦₆₄ w) ∗ memRegion (p + 8#64) (n - 8) := by
      intro p n hge _hle
      have hn : n = 8 + (n - 8) := by omega
      conv_lhs => rw [hn]
      rw [memRegion_split p 8 (n - 8) (by omega), ProofLib.memRegion_eight]
    rw [split8 (r + 8#64) 40 (by decide) (by decide),
        split8 _ 32 (by decide) (by decide),
        split8 _ 24 (by decide) (by decide),
        split8 _ 16 (by decide) (by decide),
        ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    sep_frame
  exact sepConj_mono_right htail

theorem pointsTo64_low_byte_entails (p w : BitVec 64) :
    (p ↦₆₄ w) ⊢ (p ↦₈ BitVec.extractLsb' 0 8 w) ∗ memRegion (p + 1#64) 7 := by
  have hlen1 : ([BitVec.extractLsb' 0 8 w]).length = 1 := rfl
  have hlen7 : ((unpack64 w).drop 1).length = 7 := by simp [unpack64_length]
  have hhead : (unpack64 w).take 1 = [BitVec.extractLsb' 0 8 w] := by
    simp [unpack64]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 1 (unpack64 w),
      pointsToBytes_append, hhead, hlen1]
  have h1 : (p ↦ₛ [BitVec.extractLsb' 0 8 w]) = (p ↦₈ BitVec.extractLsb' 0 8 w) := by
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rw [h1]
  refine sepConj_mono_right ?_
  have hr := pointsToBytes_entails_memRegion (p + 1#64) ((unpack64 w).drop 1)
  rwa [hlen7] at hr

@[expose] def stage1VecBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8_unpack_words (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8 A p bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (p ↦₆₄ cap) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        stage1VecBuf A cap ptr bs := by
  unfold RustHeap.vecU8 vecU8At vecHeader stage1VecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem stage1VecBuf_to_vecU8 (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      stage1VecBuf A cap ptr bs) ⊢ RustHeap.vecU8 A v bs := by
  unfold RustHeap.vecU8 vecU8At vecHeader stage1VecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem words_to_untrusted_initResAt (A : RustAlloc) (r : BitVec 64) (addr : AddrVal)
    (w0 cap ptr len w4 w5 : BitVec 64)
    (hw0 : w0 = speWord speUntrustedIdentity)
    (hlen : len = BitVec.ofNat 64 addr.name.length)
    (hdev : BitVec.extractLsb' 0 8 w4 = addr.device) :
    (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
      ((r + 24#64) ↦₆₄ len) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ∗
      stage1VecBuf A cap ptr addr.name ⊢
      initResAt A r stage1Err := by
  subst hw0; subst hlen
  change _ ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k
  refine Entails.sepExists_right (RunDrop.SpeOwned.untrustedIdentity addr) ?_
  dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
  have hv :
      ((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
        ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
        stage1VecBuf A cap ptr addr.name ⊢ RustHeap.vecU8 A (r + 8#64) addr.name := by
    have h0 := stage1VecBuf_to_vecU8 A (r + 8#64) cap ptr addr.name
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h0
  have hw4 : ((r + 32#64) ↦₆₄ w4) ⊢ ((r + 32#64) ↦₈ addr.device) ∗ memRegion (r + 33#64) 7 := by
    have h := pointsTo64_low_byte_entails (r + 32#64) w4
    rw [hdev] at h
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hw5 : ((r + 40#64) ↦₆₄ w5) ⊢ memRegion (r + 40#64) 8 :=
    pointsTo64_entails_memRegion (r + 40#64) w5
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have rearrange :
      (r ↦₆₄ speWord speUntrustedIdentity) ∗ ((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
        ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
        ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ∗ stage1VecBuf A cap ptr addr.name =
      (r ↦₆₄ speWord speUntrustedIdentity) ∗
        (((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
          ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗ stage1VecBuf A cap ptr addr.name) ∗
        ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) := by ac_rfl
  rw [rearrange]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hv (sepConj_mono hw4 hw5))) ?_
  sep_frame

/-! ## Direct `BL` callee wrappers at residual stack `stk - cliInitiateFrame` -/

@[expose] def stringCloneAtStkSpec (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp calleeStk
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def pubKeySerializeAtStkSpec (A : RustAlloc) (calleeStk : Nat) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp calleeStk
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
      A.pool ∗ stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def verifySigAtStkSpec (P : SignalPqxdh.Primitives) (calleeStk : Nat) :
    Spec VerifySignatureGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.pkPtr ∧
      s.readReg64 .x1 = g.msgPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧
      s.readReg64 .x3 = g.sigPtr ∧
      s.readReg64 .x4 = 64#64 ∧
      g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧
      g.sig.length = 64⌝ ∗
      (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
      stackAt s.sp calleeStk
  post := fun g s0 sf =>
    ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
      stackAt s0.sp calleeStk

@[expose] def memcpyScratchSpec (n calleeStk : Nat) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (dst, src) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = n⌝ ∗
      memRegion dst n ∗ memRegion src n ∗ stackAt s.sp calleeStk
  post := fun (dst, src) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion dst n ∗ memRegion src n ∗ stackAt s0.sp calleeStk

theorem memRegion_merge (a b : BitVec 64) (m n mn : Nat)
    (hb : a + BitVec.ofNat 64 m = b) (hmn : m + n = mn) (hle : mn ≤ 2 ^ 64) :
    memRegion a m ∗ memRegion b n = memRegion a mn := by
  subst hb; subst hmn
  exact (memRegion_split a m n hle).symm

theorem pointsTo16_zero_eq (a : BitVec 64) :
    (a ↦₁₆ 0#16) = ((a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8)) := by
  rw [pointsTo16_split8]; rfl

theorem byte_and_pad7_entails_word64 (p : BitVec 64) (b : BitVec 8) :
    (p ↦₈ b) ∗ memRegion (p + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜BitVec.extractLsb' 0 8 w = b⌝ ∗ (p ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (p + 1#64) 7 (by decide),
      sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [show (p ↦₈ b) ∗ (⌜bs.length = 7⌝ ∗ ((p + 1#64) ↦ₛ bs)) =
        ⌜bs.length = 7⌝ ∗ ((p ↦₈ b) ∗ ((p + 1#64) ↦ₛ bs)) by ac_rfl]
  refine pure_sepConj_elim fun hlen => ?_
  have hcons : ((p ↦₈ b) ∗ ((p + 1#64) ↦ₛ bs)) = (p ↦ₛ (b :: bs)) :=
    (pointsToBytes_cons p b bs).symm
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := b :: bs) (by simp [hlen])
  have hb : BitVec.extractLsb' 0 8 w = b := by
    have h0 := congrArg List.head? hw
    simp [unpack64] at h0
    exact h0.symm
  rw [hcons, hw, ← pointsTo64_eq_pointsToBytes]
  exact Entails.sepExists_right w (pure_sepConj_intro hb (Entails.refl _))

theorem idTrustBoxAt_entails_memRegion (box self addrA keyA : BitVec 64) (st d : BitVec 8) :
    idTrustBoxAt box self addrA keyA st d ⊢ memRegion box 32 := by
  unfold idTrustBoxAt
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo8_entails_memRegion _ _)
            (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))))) ?_
  rw [← sepConj_assoc, memRegion_merge box (box + 8#64) 8 8 16 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x10#64) 16 8 24 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x18#64) 24 1 25 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x19#64) 25 1 26 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge box (box + 0x1a#64) 26 6 32 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem sessLoadBoxAt_entails_memRegion (box self addrA : BitVec 64) (st : BitVec 8) :
    sessLoadBoxAt box self addrA st ⊢ memRegion box 24 := by
  unfold sessLoadBoxAt
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))) ?_
  rw [← sepConj_assoc, memRegion_merge box (box + 8#64) 8 8 16 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x10#64) 16 1 17 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge box (box + 0x11#64) 17 7 24 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem memRegion_two_pointsTo16 (a : BitVec 64) :
    memRegion a 2 ⊢ ∃∗ v : BitVec 16, a ↦₁₆ v := by
  rw [show (2 : Nat) = 1 + 1 from rfl, memRegion_split a 1 1 (by decide),
    ProofLib.memRegion_one, ProofLib.memRegion_one]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro b0
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b1
  refine Entails.sepExists_right (b1 ++ b0) ?_
  have h0 : BitVec.extractLsb' 0 8 (b1 ++ b0) = b0 := by bv_bits
  have h1 : BitVec.extractLsb' 8 8 (b1 ++ b0) = b1 := by bv_bits
  rw [pointsTo16_split8, h0, h1]
  exact Entails.refl _

theorem getLsbD0_of_extract8_one {w : BitVec 64} (h : BitVec.extractLsb' 0 8 w = 1#8) :
    w.getLsbD 0 = true := by
  have h0 : (BitVec.extractLsb' 0 8 w).getLsbD 0 = (1#8).getLsbD 0 := congrArg (·.getLsbD 0) h
  simpa using h0

theorem getLsbD0_of_extract8_zero {w : BitVec 64} (h : BitVec.extractLsb' 0 8 w = 0#8) :
    w.getLsbD 0 = false := by
  have h0 : (BitVec.extractLsb' 0 8 w).getLsbD 0 = (0#8).getLsbD 0 := congrArg (·.getLsbD 0) h
  simpa using h0

/-! ## Shared error epilogue (`0x0350 → ret`) -/

theorem sp_sub_96_sub_4096 (sp : BitVec 64) : (sp - 96#64) - 4096#64 = sp - 4192#64 := by bv_omega
theorem sp_sub_4192_sub_3216 (sp : BitVec 64) : (sp - 4192#64) - 3216#64 = sp - 7408#64 := by bv_omega
theorem sp_sub_96_add_96 (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

theorem initSaved_norm (s0 : State) :
    initSaved s0 =
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  unfold initSaved
  dsimp only
  rw [BitVec.add_zero,
      bv_sub_add_lit s0.sp 96 8,
      bv_sub_add_lit s0.sp 96 16,
      bv_sub_add_lit s0.sp 96 24,
      bv_sub_add_lit s0.sp 96 32,
      bv_sub_add_lit s0.sp 96 40,
      bv_sub_add_lit s0.sp 96 48,
      bv_sub_add_lit s0.sp 96 56,
      bv_sub_add_lit s0.sp 96 64,
      bv_sub_add_lit s0.sp 96 72,
      bv_sub_add_lit s0.sp 96 80,
      bv_sub_add_lit s0.sp 96 88]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
