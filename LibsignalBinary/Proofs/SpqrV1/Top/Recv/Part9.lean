/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
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
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
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
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

@[simp] private theorem except_bind_ok_iff {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by cases m <;> simp [Bind.bind, Except.bind]
@[simp] private theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] private theorem decoderFromPbStateDecode_none :
    decoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl
@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (pure x >>= f) = f x := rfl
@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
@[simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'} {m : Except ε α} {a : α} :
    m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[simp] private theorem liftM_spqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    (liftM r : Except StatesPanic α) = .ok v ↔ r = .ok v := by
  cases r <;> simp [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
@[simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε] {r : Except ε α} {v : α} :
    StatesResult.ofPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [StatesResult.ofPanic]

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

@[local simp, local arm64_norm, local wp_norm]
theorem fp_sub_32_add_eq (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551584#64 = sp0 - 128#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_560_eq' (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  change (s0.sp - 688#64) + 560#64 = s0.sp - 128#64
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fp_sub_48_add_eq (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551568#64 = sp0 - 144#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_544_eq' (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  change (s0.sp - 688#64) + 544#64 = s0.sp - 144#64
  bv_omega

/-! ## 1. `recvKeyErrAt` Exposure and `onPanic` Bridge for `Chain::recv_key` -/

theorem recvKeyErrAt_entails_code_memRegion23 (out : BitVec 64) (e : Error) :
    recvKeyErrAt out e ⊢
      (out ↦₆₄ 1#64) ∗
      ((out + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      memRegion (out + 9#64) 23 := by
  unfold recvKeyErrAt
  split
  · rename_i epoch
    have h23 :
        memRegion (out + 0x09#64) 7 ∗ ((out + 0x10#64) ↦₆₄ epoch) ∗ memRegion (out + 0x18#64) 8 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 8)
            (b' := out + 0x18#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rename_i ctr atIdx
    have h23 :
        memRegion (out + 0x09#64) 3 ∗ ((out + 0x0c#64) ↦₃₂ ctr) ∗
          ((out + 0x10#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x14#64) 12 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20)
            (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x10#64) (n := 4) (k := 12)
            (b' := out + 0x14#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rename_i atIdx
    have h23 :
        memRegion (out + 0x09#64) 3 ∗ ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20)
            (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rename_i atIdx
    have h23 :
        memRegion (out + 0x09#64) 3 ∗ ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20)
            (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rw [← sepConj_emp ⌜False⌝]; exact Entails.pure_left False.elim

theorem onPanic_of_chainRecvKey {F : ShaCompress} {K : MlKem}
    {st msg : VecArg} {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {chain0 : Chain}
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s sm : State) :
    (⌜((Chain.recvKey (spqrHkdfWith F) chain0 0#64 pre.index).isPanic = true ∧ sm.trace = s.trace) ∨
        (allocFailedIn s sm ∧ s.trace <+: sm.trace)⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(allocFailedIn s sm ∨ (spqrV1Recv F K).recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left
  rintro (⟨hpan, htr⟩ | ⟨haf, hsub⟩)
  · have hpan_recv := spqrV1Recv_gt_recvKey_panic (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf hpan
    exact Entails.pure_right ⟨Or.inr hpan_recv, htr ▸ List.prefix_refl _⟩ (Entails.refl _)
  · exact Entails.pure_right ⟨Or.inl haf, hsub⟩ (Entails.refl _)

theorem memRegion_88_sub3056_split_32_56 (sp0 : BitVec 64) :
    memRegion (sp0 - 3056#64) 88 =
      memRegion (sp0 - 3056#64) 32 ∗ memRegion (sp0 - 3024#64) 56 :=
  ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 32) (k := 56)
    (b' := sp0 - 3024#64) rfl (by bv_omega) (by decide)

theorem memRegion_872_sub2968_split_ok_680 (sp0 : BitVec 64) :
    memRegion (sp0 - 3024#64) 56 ∗ memRegion (sp0 - 2968#64) 872 =
      (∃∗ u4 : BitVec 64, (sp0 - 3024#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (sp0 - 3016#64) ↦₆₄ u5) ∗
      memRegion (sp0 - 3008#64) 80 ∗
      memRegion (sp0 - 2928#64) 224 ∗
      memRegion (sp0 - 2704#64) 608 := by
  rw [← ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 56) (k := 872)
        (b' := sp0 - 2968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 16) (k := 912)
        (b' := sp0 - 3008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3008#64) (n := 80) (k := 832)
        (b' := sp0 - 2928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2928#64) (n := 224) (k := 608)
        (b' := sp0 - 2704#64) rfl (by bv_omega) (by decide),
      memRegion_16_split (sp0 - 3024#64),
      bv_sub_add_lit sp0 3024 8]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]

theorem tail680_join_1952 (sp0 d48 d40 d32 : BitVec 64) (d : Words11) :
    ((sp0 - 2048#64) ↦₆₄ d.w6) ∗
      ((sp0 - 2040#64) ↦₆₄ d.w7) ∗
      ((sp0 - 2032#64) ↦₆₄ d.w8) ∗
      ((sp0 - 2024#64) ↦₆₄ d.w9) ∗
      ((sp0 - 2016#64) ↦₆₄ d.w10) ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₆₄ d48) ∗
      ((sp0 - 136#64) ↦₆₄ d40) ∗
      ((sp0 - 128#64) ↦₆₄ d32) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 2048#64) 1952 := by
  have hsplit (m n k m' : Nat)
      (hmn : m' = m - n) (hm : n < m) (hnk : m < 2 ^ 64) (hr : n + k ≤ 2 ^ 64) :
      memRegion (sp0 - BitVec.ofNat 64 m) (n + k) =
        memRegion (sp0 - BitVec.ofNat 64 m) n ∗
        memRegion (sp0 - BitVec.ofNat 64 m') k := by
    subst hmn
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 m) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 (m - n)) rfl (bv_sub_add_lit sp0 m n hm hnk).symm hr
  rw [show (1952 : Nat) = 8 + (8 + (8 + (8 + (8 + (1864 + (8 + (8 + (8 + 24)))))))) by decide,
      hsplit 2048 8 1944 2040 rfl (by decide) (by decide) (by decide),
      hsplit 2040 8 1936 2032 rfl (by decide) (by decide) (by decide),
      hsplit 2032 8 1928 2024 rfl (by decide) (by decide) (by decide),
      hsplit 2024 8 1920 2016 rfl (by decide) (by decide) (by decide),
      hsplit 2016 8 1912 2008 rfl (by decide) (by decide) (by decide),
      hsplit 2008 1864 48 144 rfl (by decide) (by decide) (by decide),
      hsplit 144 8 40 136 rfl (by decide) (by decide) (by decide),
      hsplit 136 8 32 128 rfl (by decide) (by decide) (by decide),
      hsplit 128 8 24 120 rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem frame4544_join_err_740 (sp0 : BitVec 64)
    (d880 d888 d896 u0 u1 u2 u3 e0 e1 e2 e3 e4 e5 : BitVec 64) :
    memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      ((sp0 - 4112#64) ↦₆₄ d880) ∗
      ((sp0 - 4104#64) ↦₆₄ d888) ∗
      ((sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      ((sp0 - 3056#64) ↦₆₄ u0) ∗
      ((sp0 - 3048#64) ↦₆₄ u1) ∗
      ((sp0 - 3040#64) ↦₆₄ u2) ∗
      ((sp0 - 3032#64) ↦₆₄ u3) ∗
      memRegion (sp0 - 3024#64) 56 ∗
      memRegion (sp0 - 2968#64) 872 ∗
      ((sp0 - 2096#64) ↦₆₄ e0) ∗
      ((sp0 - 2088#64) ↦₆₄ e1) ∗
      ((sp0 - 2080#64) ↦₆₄ e2) ∗
      ((sp0 - 2072#64) ↦₆₄ e3) ∗
      ((sp0 - 2064#64) ↦₆₄ e4) ∗
      ((sp0 - 2056#64) ↦₆₄ e5) ∗
      memRegion (sp0 - 2048#64) 1952 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have hsplit (m n k m' : Nat)
      (hmn : m' = m - n) (hm : n < m) (hnk : m < 2 ^ 64) (hr : n + k ≤ 2 ^ 64) :
      memRegion (sp0 - BitVec.ofNat 64 m) (n + k) =
        memRegion (sp0 - BitVec.ofNat 64 m) n ∗
        memRegion (sp0 - BitVec.ofNat 64 m') k := by
    subst hmn
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 m) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 (m - n)) rfl (bv_sub_add_lit sp0 m n hm hnk).symm hr
  rw [show (4544 : Nat) = 352 + (88 + (88 + (8 + (8 + (8 + (1032 + (8 + (8 + (8 + (8 +
        (56 + (872 + (8 + (8 + (8 + (8 + (8 + (8 + 1952)))))))))))))))))) by decide,
      hsplit 4640 352 4192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 4104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 4016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 4008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 4000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 3992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 2960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 8 2952 3048 rfl (by decide) (by decide) (by decide),
      hsplit 3048 8 2944 3040 rfl (by decide) (by decide) (by decide),
      hsplit 3040 8 2936 3032 rfl (by decide) (by decide) (by decide),
      hsplit 3032 8 2928 3024 rfl (by decide) (by decide) (by decide),
      hsplit 3024 56 2872 2968 rfl (by decide) (by decide) (by decide),
      hsplit 2968 872 2000 2096 rfl (by decide) (by decide) (by decide),
      hsplit 2096 8 1992 2088 rfl (by decide) (by decide) (by decide),
      hsplit 2088 8 1984 2080 rfl (by decide) (by decide) (by decide),
      hsplit 2080 8 1976 2072 rfl (by decide) (by decide) (by decide),
      hsplit 2072 8 1968 2064 rfl (by decide) (by decide) (by decide),
      hsplit 2064 8 1960 2056 rfl (by decide) (by decide) (by decide),
      hsplit 2056 8 1952 2048 rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-! ## 2. `step_v0_after_chainFrom_604` (`+604 .. +740 -> +2184 / +2540`) -/

theorem frame4544_split_v0 (sp0 : BitVec 64) :
    memRegion (sp0 - 4640#64) 4544 =
      memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      (∃∗ d880 : BitVec 64, (sp0 - 4112#64) ↦₆₄ d880) ∗
      (∃∗ d888 : BitVec 64, (sp0 - 4104#64) ↦₆₄ d888) ∗
      (∃∗ d896 : BitVec 64, (sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      memRegion (sp0 - 3056#64) 88 ∗
      memRegion (sp0 - 2968#64) 872 ∗
      memRegion (sp0 - 2096#64) 88 ∗
      memRegion (sp0 - 2008#64) 1912 := by
  have hsplit (a n k b : Nat) (h1 : a - 96 = n + k) (h2 : a - n = b)
      (ha : a < 2 ^ 64) (hn : n < a) :
      memRegion (sp0 - BitVec.ofNat 64 a) (a - 96) =
        memRegion (sp0 - BitVec.ofNat 64 a) n ∗
        memRegion (sp0 - BitVec.ofNat 64 b) k := by
    refine ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 a) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 b) h1 ?_ (by omega)
    rw [bv_sub_add_lit sp0 a n hn ha, h2]
  rw [show (4544 : Nat) = 4640 - 96 from rfl,
      hsplit 4640 352 4192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 4104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 4016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 4008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 4000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 3992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 2960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 88 2872 2968 rfl (by decide) (by decide) (by decide),
      hsplit 2968 872 2000 2096 rfl (by decide) (by decide) (by decide),
      hsplit 2096 88 1912 2008 rfl (by decide) (by decide) (by decide),
      ProofLib.memRegion_eight (sp0 - 4112#64),
      ProofLib.memRegion_eight (sp0 - 4104#64),
      ProofLib.memRegion_eight (sp0 - 4096#64)]

theorem frame2544_join_v0 (sp0 d880 d888 d896 : BitVec 64) :
    memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      ((sp0 - 4112#64) ↦₆₄ d880) ∗
      ((sp0 - 4104#64) ↦₆₄ d888) ∗
      ((sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      memRegion (sp0 - 3056#64) 88 ∗
      memRegion (sp0 - 2968#64) 872 ⊢
      memRegion (sp0 - 4640#64) 2544 := by
  have hsplit (a n k b : Nat) (h1 : a - 2096 = n + k) (h2 : a - n = b)
      (ha : a < 2 ^ 64) (hn : n < a) :
      memRegion (sp0 - BitVec.ofNat 64 a) (a - 2096) =
        memRegion (sp0 - BitVec.ofNat 64 a) n ∗
        memRegion (sp0 - BitVec.ofNat 64 b) k := by
    refine ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 a) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 b) h1 ?_ (by omega)
    rw [bv_sub_add_lit sp0 a n hn ha, h2]
  rw [show (2544 : Nat) = 4640 - 2096 from rfl,
      hsplit 4640 352 2192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 2104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 2016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 2008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 2000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 1992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 88 872 2968 rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem memRegion_88_sub2096_split_byte8 (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 88 =
      (∃∗ d2896 : BitVec 64, (sp0 - 2096#64) ↦₆₄ d2896) ∗
      (∃∗ b0 : BitVec 8, (sp0 - 2088#64) ↦₈ b0) ∗
      memRegion (sp0 - 2087#64) 79 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 8) (k := 80)
        (b' := sp0 - 2088#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2088#64) (n := 1) (k := 79)
        (b' := sp0 - 2087#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp0 - 2096#64),
      ProofLib.memRegion_one (sp0 - 2088#64)]

theorem vn_some_unpack_sub4992 (A : RustAlloc) (sp0 w0 w1 : BitVec 64) (vn : VersionNegotiationPB) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) =
      vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey ∗
      Top.ChainFromVersionNegotiation.optChainParamsPBAt (sp0 - 4968#64) vn.chainParams ∗
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
      ((sp0 - 4952#64) ↦₃₂ vn.minVersion) ∗
      memRegion (sp0 - 4948#64) 4 := by
  unfold optVersionNegotiationPBTailAt versionNegotiationPBTailAt vecU8Heap vecU8At vecHeader
  dsimp only []
  rw [← optChainParamsPBAt_eq_protoRepr,
      bv_sub_add_lit sp0 4992 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4992 16 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 20 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 24 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 28 (by decide) (by decide)]
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  ac_rfl

theorem vecU8At_sub4992_unpack (A : RustAlloc) (sp0 w0 w1 : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp0 - 4992#64) w0 w1 bs ⊢
      ⌜bs.length < 2 ^ 63⌝ ∗
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false w1 bs ∗
      vecU8BufRest A w0 w1 bs.length := by
  have h := vecU8At_entails_header_bytesAt_rest A (sp0 - 4992#64) w0 w1 bs
  rw [bv_sub_add_lit sp0 4992 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4992 16 (by decide) (by decide)] at h
  exact h

theorem vecU8At_sub4992_repack (A : RustAlloc) (sp0 w0 w1 : BitVec 64) (bs : List (BitVec 8)) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false w1 bs ∗
      vecU8BufRest A w0 w1 bs.length ⊢
      vecU8At A (sp0 - 4992#64) w0 w1 bs := by
  have h := header_bytesAt_rest_entails_vecU8At A (sp0 - 4992#64) w0 w1 bs
  rw [bv_sub_add_lit sp0 4992 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4992 16 (by decide) (by decide)] at h
  exact h

theorem byte_memRegion79_sub2096_to_v0_err (sp0 : BitVec 64) (e : Error) :
    ((sp0 - 2088#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      memRegion (sp0 - 2087#64) 79 ⊢
    (∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
      ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
      ((sp0 - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((sp0 - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 2072#64) ↦₆₄ w3)) ∗
    memRegion (sp0 - 2064#64) 56 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2087#64) (n := 7) (k := 72)
        (b' := sp0 - 2080#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2080#64) (n := 8) (k := 64)
        (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2072#64) (n := 8) (k := 56)
        (b' := sp0 - 2064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eq_exists_bytes (sp0 - 2087#64) 7 (by decide),
      ProofLib.memRegion_eight (sp0 - 2080#64),
      ProofLib.memRegion_eight (sp0 - 2072#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepExists_left_entails; intro w2
  apply sepExists_left_entails; intro w1
  apply sepExists_left_entails; intro bs7
  rw [show
    ((sp0 - 2088#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      ((⌜bs7.length = 7⌝ ∗ ((sp0 - 2087#64) ↦ₛ bs7)) ∗
        ((sp0 - 2080#64) ↦₆₄ w1) ∗ ((sp0 - 2072#64) ↦₆₄ w2) ∗ memRegion (sp0 - 2064#64) 56) =
    ⌜bs7.length = 7⌝ ∗
      (((sp0 - 2088#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
        ((sp0 - 2087#64) ↦ₛ bs7) ∗
        ((sp0 - 2080#64) ↦₆₄ w1)) ∗
      ((sp0 - 2072#64) ↦₆₄ w2) ∗
      memRegion (sp0 - 2064#64) 56 by ac_rfl]
  refine Entails.pure_left fun hbs7 => ?_
  have h1 := byte_bs7_word_to_pointsTo128 (sp0 - 2088#64) (Top.ChainFromVersionNegotiation.spqrErrorTag e) hbs7 w1
  rw [bv_sub_add_lit sp0 2088 1 (by decide) (by decide),
      bv_sub_add_lit sp0 2088 8 (by decide) (by decide)] at h1
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h1
  refine Entails.trans (sepConj_mono_left h1) ?_
  simp only [sepExists_sepConj_left]
  apply sepExists_left_entails; intro q0
  refine Entails.trans ?_ (Entails.sepExists_intro q0)
  refine Entails.trans ?_ (Entails.sepExists_intro w2)
  unfold pointsTo128
  rw [bv_sub_add_lit sp0 2088 8 (by decide) (by decide)]
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  exact Entails.of_eq (by ac_rfl)

theorem pack_v0_err_sub2088 (sp0 : BitVec 64) (e : Error) (q0 : BitVec 128) (w3 : BitVec 64)
    (htag : BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e) :
    ((sp0 - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((sp0 - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 2072#64) ↦₆₄ w3) ⊢
    ∃∗ q0' : BitVec 128, ∃∗ w3' : BitVec 64,
      ⌜BitVec.truncate 8 q0' = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
      ((sp0 - 2088#64) ↦₆₄ q0'.extractLsb' 0 64) ∗
      ((sp0 - 2080#64) ↦₆₄ q0'.extractLsb' 64 64) ∗
      ((sp0 - 2072#64) ↦₆₄ w3') :=
  Entails.sepExists_right q0 (Entails.sepExists_right w3 (Entails.pure_right htag (Entails.refl _)))

theorem chainErrorAt_sub3056_unpack (sp0 : BitVec 64) (e : Error) :
    chainErrorAt (sp0 - 3056#64) e =
      ∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
        ((sp0 - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp0 - 3040#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3024#64) 56 := by
  have h := chainErrorAt_unpack_words4 (sp0 - 3056#64) e
  rw [bv_sub_add_lit sp0 3056 8 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 16 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 24 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 32 (by decide) (by decide)] at h
  exact h

theorem words4_rest_sub3056_to_memRegion_88 (sp0 w0 w1 w2 w3 : BitVec 64) :
    ((sp0 - 3056#64) ↦₆₄ w0) ∗
      ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗
      ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 56 ⊢
      memRegion (sp0 - 3056#64) 88 := by
  have h := words4_rest_to_memRegion_88 (sp0 - 3056#64) w0 w1 w2 w3
  rw [bv_sub_add_lit sp0 3056 8 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 16 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 24 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 32 (by decide) (by decide)] at h
  exact h

theorem memRegion_88_sub2096_words4_rest (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 88 =
      (∃∗ d0 : BitVec 64, (sp0 - 2096#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp0 - 2088#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp0 - 2080#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp0 - 2072#64) ↦₆₄ d3) ∗
      memRegion (sp0 - 2064#64) 56 := by
  have h := ChainFromNorm.memRegion_88_words4_rest (sp0 - 2096#64)
  rw [bv_sub_add_lit sp0 2096 8 (by decide) (by decide),
      bv_sub_add_lit sp0 2096 16 (by decide) (by decide),
      bv_sub_add_lit sp0 2096 24 (by decide) (by decide),
      bv_sub_add_lit sp0 2096 32 (by decide) (by decide)] at h
  exact h

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  ult_one_toI32

/-! ## 4. `step_v0_chain_none_2108` (`+2108 .. +2140`, `+2384 .. +2388`, `+2920 .. +2948`) -/

end CryptoVerification.SpqrV1.Top.Recv

