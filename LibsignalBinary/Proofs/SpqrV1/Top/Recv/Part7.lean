/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. 88-Byte (`11`-Word) Stack Slot Helpers (`Words11`) for `Chain` Moves -/

structure Words11 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64

@[expose] def words11At (out : BitVec 64) (d : Words11) : SepProp :=
  (out ↦₆₄ d.w0) ∗ ((out + 8#64) ↦₆₄ d.w1) ∗ ((out + 16#64) ↦₆₄ d.w2) ∗
  ((out + 24#64) ↦₆₄ d.w3) ∗ ((out + 32#64) ↦₆₄ d.w4) ∗ ((out + 40#64) ↦₆₄ d.w5) ∗
  ((out + 48#64) ↦₆₄ d.w6) ∗ ((out + 56#64) ↦₆₄ d.w7) ∗ ((out + 64#64) ↦₆₄ d.w8) ∗
  ((out + 72#64) ↦₆₄ d.w9) ∗ ((out + 80#64) ↦₆₄ d.w10)

@[expose] def words11SubAt (sp0 : BitVec 64) (m : Nat) (d : Words11) : SepProp :=
  ((sp0 - BitVec.ofNat 64 m) ↦₆₄ d.w0) ∗
  ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ d.w1) ∗
  ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ d.w2) ∗
  ((sp0 - BitVec.ofNat 64 (m - 24)) ↦₆₄ d.w3) ∗
  ((sp0 - BitVec.ofNat 64 (m - 32)) ↦₆₄ d.w4) ∗
  ((sp0 - BitVec.ofNat 64 (m - 40)) ↦₆₄ d.w5) ∗
  ((sp0 - BitVec.ofNat 64 (m - 48)) ↦₆₄ d.w6) ∗
  ((sp0 - BitVec.ofNat 64 (m - 56)) ↦₆₄ d.w7) ∗
  ((sp0 - BitVec.ofNat 64 (m - 64)) ↦₆₄ d.w8) ∗
  ((sp0 - BitVec.ofNat 64 (m - 72)) ↦₆₄ d.w9) ∗
  ((sp0 - BitVec.ofNat 64 (m - 80)) ↦₆₄ d.w10)

theorem memRegion_88_entails_words11 (out : BitVec 64) :
    memRegion out 88 ⊢ ∃∗ d : Words11, words11At out d := by
  rw [ProofLib.memRegion_split' (b := out) (n := 24) (k := 64)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 out]
  refine Entails.trans (sepConj_mono_right (memRegion_64_entails_words8 (out + 24#64))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepExists_left_entails; intro a
  apply sepExists_left_entails; intro w2
  apply sepExists_left_entails; intro w1
  apply sepExists_left_entails; intro w0
  refine Entails.sepExists_right
    ⟨w0, w1, w2, a.w0, a.w1, a.w2, a.w3, a.w4, a.w5, a.w6, a.w7⟩ ?_
  dsimp only [words8At, words11At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem words11At_sub_eq (sp0 : BitVec 64) (m : Nat) (d : Words11)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    words11At (sp0 - BitVec.ofNat 64 m) d = words11SubAt sp0 m d := by
  have hadd (k : Nat) (hk : k < m) :
      (sp0 - BitVec.ofNat 64 m) + BitVec.ofNat 64 k = sp0 - BitVec.ofNat 64 (m - k) :=
    bv_sub_add_lit sp0 m k hk h0
  dsimp only [words11At, words11SubAt]
  rw [hadd 8 (by omega), hadd 16 (by omega), hadd 24 (by omega), hadd 32 (by omega),
      hadd 40 (by omega), hadd 48 (by omega), hadd 56 (by omega), hadd 64 (by omega),
      hadd 72 (by omega), hadd 80 (by omega)]

theorem memRegion_88_sub_entails_words11 (sp0 : BitVec 64) (m : Nat)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    memRegion (sp0 - BitVec.ofNat 64 m) 88 ⊢
      ∃∗ d : Words11, words11SubAt sp0 m d := by
  refine Entails.trans (memRegion_88_entails_words11 (sp0 - BitVec.ofNat 64 m)) ?_
  apply sepExists_left_entails; intro d
  rw [words11At_sub_eq sp0 m d h0 h80]
  exact Entails.sepExists_right d (Entails.refl _)

theorem words11SubAt_to_memRegion_88 (sp0 : BitVec 64) (m : Nat) (d : Words11)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    words11SubAt sp0 m d ⊢ memRegion (sp0 - BitVec.ofNat 64 m) 88 := by
  rw [← words11At_sub_eq sp0 m d h0 h80]
  exact words11_to_memRegion_88 (sp0 - BitVec.ofNat 64 m)
    d.w0 d.w1 d.w2 d.w3 d.w4 d.w5 d.w6 d.w7 d.w8 d.w9 d.w10

@[expose] def chainWords11 (G : ChainProofs.ChainGhost) (c : Chain) (pad : BitVec 32) : Words11 :=
  { w0 := G.linksCap
    w1 := G.linksPtr
    w2 := G.linksHead
    w3 := BitVec.ofNat 64 (G.epochs.zip c.links).length
    w4 := G.nextRoot.cap
    w5 := G.nextRoot.ptr
    w6 := BitVec.ofNat 64 c.nextRoot.length
    w7 := c.currentEpoch
    w8 := c.sendEpoch
    w9 := c.params.maxOooKeys ++ c.params.maxJump
    w10 := pad ++ c.dir.toI32 }

theorem chainRepr_sub_entails_words11 (A : RustAlloc) (sp0 : BitVec 64) (m : Nat) (c : Chain)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    chainRepr A (sp0 - BitVec.ofNat 64 m) c ⊢
      ∃∗ (G : ChainProofs.ChainGhost), ∃∗ (pad : BitVec 32),
        ⌜G.linksCap ≠ Top.ChainFromVersionNegotiation.noneCap⌝ ∗
        words11SubAt sp0 m (chainWords11 G c pad) ∗
        chainAtHeap A G c := by
  refine Entails.trans (chainRepr_entails_words11 A (sp0 - BitVec.ofNat 64 m) c) ?_
  apply sepExists_left_entails; intro G
  apply sepExists_left_entails; intro pad
  refine Entails.sepExists_right G (Entails.sepExists_right pad ?_)
  rw [← words11At_sub_eq sp0 m (chainWords11 G c pad) h0 h80]
  dsimp only [words11At, chainWords11]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem words11_entails_chainAt (A : RustAlloc) (out : BitVec 64) (G : ChainProofs.ChainGhost) (c : Chain)
    (pad : BitVec 32) :
    words11At out (chainWords11 G c pad) ∗ chainAtHeap A G c ⊢
      ChainProofs.chainAt A out G c := by
  dsimp only [words11At, chainWords11]
  unfold ChainProofs.chainAt vecDequeAt vecDequeHeader vecU8At vecHeader chainParamsAt directionAt chainAtHeap
  have hp72 :
      ((out + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) =
        ((out + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (out + 72#64) c.params.maxJump c.params.maxOooKeys).symm
  have hp80 :
      ((out + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) =
        ((out + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((out + 0x54#64) ↦₃₂ pad) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (out + 80#64) c.dir.toI32 pad).symm
  rw [hp72, hp80]
  have hpad : ((out + 0x54#64) ↦₃₂ pad) ⊢ memRegion (out + 0x54#64) 4 := by
    rw [ProofLib.memRegion_four (out + 0x54#64)]
    exact Entails.sepExists_right pad (Entails.refl _)
  rw [show
    ((out ↦₆₄ G.linksCap) ∗
      ((out + 8#64) ↦₆₄ G.linksPtr) ∗
      ((out + 16#64) ↦₆₄ G.linksHead) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      ((out + 32#64) ↦₆₄ G.nextRoot.cap) ∗
      ((out + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((out + 56#64) ↦₆₄ c.currentEpoch) ∗
      ((out + 64#64) ↦₆₄ c.sendEpoch) ∗
      (((out + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys)) ∗
      (((out + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((out + 0x54#64) ↦₃₂ pad))) ∗
      (⌜G.epochs.length = c.links.length⌝ ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links) ∗
        ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
            G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
        if G.nextRoot.cap = 0 then emp
        else
          A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
            memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
              (G.nextRoot.cap.toNat - c.nextRoot.length)) =
    ⌜G.epochs.length = c.links.length⌝ ∗
      ((out ↦₆₄ G.linksCap ∗ (out + 0x08#64) ↦₆₄ G.linksPtr ∗ (out + 0x10#64) ↦₆₄ G.linksHead ∗
          (out + 0x18#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links)) ∗
      (((out + 0x20#64) ↦₆₄ G.nextRoot.cap ∗ (out + 0x20#64 + 8#64) ↦₆₄ G.nextRoot.ptr ∗
          (out + 0x20#64 + 16#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
        ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
            G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
          if G.nextRoot.cap = 0 then emp
          else
            A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
              memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
                (G.nextRoot.cap.toNat - c.nextRoot.length)) ∗
      (out + 0x38#64) ↦₆₄ c.currentEpoch ∗ (out + 0x40#64) ↦₆₄ c.sendEpoch ∗
      ((out + 0x48#64) ↦₃₂ c.params.maxJump ∗ (out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) ∗
      (out + 0x50#64) ↦₃₂ c.dir.toI32 ∗ ((out + 0x54#64) ↦₃₂ pad) by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hpad))))))

theorem words11SubAt_entails_chainAt (A : RustAlloc) (sp0 : BitVec 64) (m : Nat)
    (G : ChainProofs.ChainGhost) (c : Chain) (pad : BitVec 32)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    words11SubAt sp0 m (chainWords11 G c pad) ∗ chainAtHeap A G c ⊢
      ChainProofs.chainAt A (sp0 - BitVec.ofNat 64 m) G c := by
  rw [← words11At_sub_eq sp0 m (chainWords11 G c pad) h0 h80]
  exact words11_entails_chainAt A (sp0 - BitVec.ofNat 64 m) G c pad

/-! ## 2. Success Path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420 -> +1424`) -/

theorem sp_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl

theorem sp_setPState (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_48 (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551568#64 = sp0 - 144#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_544 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold Kdf.HkdfToSliceProof.hsp
  bv_omega

theorem not_ult_two_imp_two_ule {v : BitVec 32} (h : ¬(v.ult 2#32 = true)) :
    (2#32).ule v = true := by
  revert v h; bv_kernel

theorem ult_two_imp_two_ule_false {v : BitVec 32} (h : v.ult 2#32 = true) :
    (2#32).ule v = false := by
  revert v h; bv_kernel

/-- Expose `w0, w1, vn.authKey.length, w1 ↦ₛ vn.authKey, vn.direction` for `+1252 .. +1296`
    (`init_inner`). -/
theorem vn_some_expose_dir_and_initInner (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) ⊢
    ⌜w1 ≠ 0#64⌝ ∗
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      (w1 ↦ₛ vn.authKey) ∗
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
      (∃∗ P_vn : SepProp,
        ⌜((sp0 - 4992#64) ↦₆₄ w0) ∗
          ((sp0 - 4984#64) ↦₆₄ w1) ∗
          ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (w1 ↦ₛ vn.authKey) ∗
          ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn ⊢
          Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn⌝ ∗ P_vn) := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  have h36 : (sp0 - 4992#64) + 36#64 = sp0 - 4956#64 := bv_sub_add_lit sp0 4992 36
  have hvn_eq :
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) =
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn := by
    rw [← h8, ← h16]
    exact vnTail_some_eq_versionNegotiationPBAt A (sp0 - 4992#64) w0 w1 vn
  have hvn_def : Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn =
      vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey ∗
      Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
      (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
      (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
      memRegion ((sp0 - 4992#64) + 44#64) 4 := rfl
  have hunpack := vecU8At_entails_header_bytesAt_rest A (sp0 - 4992#64) w0 w1 vn.authKey
  have hbytes : ChainProofs.bytesAt false w1 vn.authKey = (w1 ↦ₛ vn.authKey) := rfl
  rw [hbytes, h8, h16] at hunpack
  refine Entails.trans (Entails.of_eq (hvn_eq.trans hvn_def)) ?_
  refine Entails.trans (sepConj_mono_left hunpack) ?_
  rw [h36]
  refine Entails.trans
    (Entails.of_eq (show
      (⌜vn.authKey.length < 2 ^ 63⌝ ∗
        ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        vecU8BufRest A w0 w1 vn.authKey.length) ∗
        Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4992#64) + 44#64) 4 =
      ⌜vn.authKey.length < 2 ^ 63⌝ ∗
        (vecU8BufRest A w0 w1 vn.authKey.length ∗
          (((sp0 - 4992#64) ↦₆₄ w0) ∗
            ((sp0 - 4984#64) ↦₆₄ w1) ∗
            ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            (w1 ↦ₛ vn.authKey) ∗
            ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
            (Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
              (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
              memRegion ((sp0 - 4992#64) + 44#64) 4))) by ac_rfl)) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (sepConj_mono_left (vecU8BufRest_expose_ptr_ne_zero A w0 w1 vn.authKey.length)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hptr => Entails.pure_right hptr ?_
  let P_vn : SepProp :=
    vecU8BufRest A w0 w1 vn.authKey.length ∗
      Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
      (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
      memRegion ((sp0 - 4992#64) + 44#64) 4
  have hjoin :
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn ⊢
        Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn := by
    have hpack := header_bytesAt_rest_entails_vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey
    rw [hbytes, h8, h16] at hpack
    rw [hvn_def, h36]
    refine Entails.trans (Entails.of_eq (show
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn =
      (((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        vecU8BufRest A w0 w1 vn.authKey.length) ∗
        Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4992#64) + 44#64) 4 by
      unfold P_vn; ac_rfl)) ?_
    exact sepConj_mono_left hpack
  refine Entails.trans (Entails.of_eq (show
    vecU8BufRest A w0 w1 vn.authKey.length ∗
      (((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
          (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
          memRegion ((sp0 - 4992#64) + 44#64) 4)) =
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      (w1 ↦ₛ vn.authKey) ∗
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn by
    unfold P_vn; ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (Entails.sepExists_right P_vn (Entails.pure_right hjoin (Entails.refl _)))))))

theorem versionNegotiationPBAt_entails_vnTail_some (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn ⊢
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  rw [← h8, ← h16, ← vnTail_some_eq_versionNegotiationPBAt A (sp0 - 4992#64) w0 w1 vn]
  exact Entails.refl _

theorem optProtoPqRatchetInnerAt_none_entails_memRegion_224 (A : RustAlloc) (a : BitVec 64) :
    Drop.optProtoPqRatchetInnerAt A a none ⊢ memRegion a 224 := by
  dsimp only [Drop.optProtoPqRatchetInnerAt]
  rw [show (224 : Nat) = 8 + 216 by decide, memRegion_split a 8 216 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion a Drop.none3Cap')

theorem frame4544_join_1320 (sp0 : BitVec 64) (b0 : BitVec 8) (w30 : BitVec 32) :
    memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 1055 ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44 ⊢
      memRegion (sp0 - 4640#64) 1584 ∗ memRegion (sp0 - 2008#64) 1912 := by
  have hlow :
      memRegion (sp0 - 4640#64) 528 ∗
        ((sp0 - 4112#64) ↦₈ b0) ∗
        memRegion (sp0 - 4111#64) 1055 ⊢
      memRegion (sp0 - 4640#64) 1584 := by
    conv_rhs =>
      rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 528) (k := 1056)
          (b' := sp0 - 4112#64) (by decide) (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 1) (k := 1055)
          (b' := sp0 - 4111#64) (by decide) (by bv_omega) (by decide),
        ProofLib.memRegion_one (sp0 - 4112#64)]
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right b0 (Entails.refl _)))
  have hhigh :
      memRegion (sp0 - 2008#64) 1864 ∗
        ((sp0 - 144#64) ↦₃₂ w30) ∗
        memRegion (sp0 - 140#64) 44 ⊢
      memRegion (sp0 - 2008#64) 1912 := by
    conv_rhs =>
      rw [ProofLib.memRegion_split' (b := sp0 - 2008#64) (n := 1864) (k := 48)
          (b' := sp0 - 144#64) (by decide) (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 4) (k := 44)
          (b' := sp0 - 140#64) (by decide) (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion (sp0 - 144#64) w30))
  refine Entails.trans (Entails.of_eq (show
    memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 1055 ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44 =
    (memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 1055) ∗
    (memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44) by ac_rfl)) ?_
  exact sepConj_mono hlow hhigh

end CryptoVerification.SpqrV1.Top.Recv
