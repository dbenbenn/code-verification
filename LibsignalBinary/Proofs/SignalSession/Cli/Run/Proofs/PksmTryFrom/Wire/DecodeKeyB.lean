/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas -- shake: keep
public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  memRegion_split decodeVarint_suffix pointsTo64_pair_entails_memRegion16
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_DecodeKeyB : True := trivial

abbrev SepWPp := Wire.SepWPp
abbrev SepWP.done := @Wire.SepWP.done
abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
abbrev SepWPp.panic := @Wire.SepWPp.panic
abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
abbrev SepWPp.bind := @Wire.SepWPp.bind
abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

/-- Native stack budget of `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (`32,832` B). -/
abbrev dk_varintSlowStackX : Nat := 64 + 2 * extHookStack

theorem PreKeyLoopRegs.of_calleeSaved {sp' sret len ptr : BitVec 64} {vb : BitVec 8}
    {s1 s2 : State} (h1 : PreKeyLoopRegs sp' sret len ptr vb s1)
    (hsp : s2.sp = s1.sp) (hcs : CalleeSavedPreserved s1 s2) :
    PreKeyLoopRegs sp' sret len ptr vb s2 := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, _, h25, _, h27, _, h29, _⟩
  exact ⟨hsp.trans h1.sp, h29.trans h1.x29, h27.trans h1.x27, h25.trans h1.x25,
    h23.trans h1.x23, h22.trans h1.x22, h21.trans h1.x21, h20.trans h1.x20, h19.trans h1.x19⟩

theorem wirePreKeyOf_entails_exists_of (A : RustAlloc) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A a m ⊢ ∃∗ mErr : ProtoPreKeySignalMessage, wirePreKeyOf A a mErr :=
  Entails.sepExists_intro m

theorem preKeyLoopExitMem_append_prefix (A : RustAlloc) (sp' ptr : BitVec 64)
    (bs : List (BitVec 8)) (k : Nat) (hk : k ≤ bs.length)
    (x24 : BitVec 64) (res : Option ProtoPreKeySignalMessage) :
    preKeyLoopExitMem A sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) x24 res ∗ (ptr ↦ₛ bs.take k) =
      preKeyLoopExitMem A sp' ptr bs x24 res := by
  unfold preKeyLoopExitMem; rw [← pointsToBytes_take_drop ptr bs k hk]; ac_nf

theorem preKeyLoopExitMem_err_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (x24 : BitVec 64) (hx24 : x24 ≠ 0#64) (n : Nat) (mErr : ProtoPreKeySignalMessage) :
    memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      decodeErrorAtStackLen A x24 n ∗ wirePreKeyOf A (sp' + 312#64) mErr ⊢
      preKeyLoopExitMem A sp' ptr bs x24 none := by
  unfold preKeyLoopExitMem; dsimp only; rw [pure_true_emp hx24, emp_sepConj]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  exact sepConj_mono (decodeErrorWith_entails_at A x24 n)
    (wirePreKeyOf_entails_exists_of A (sp' + 312#64) mErr)

theorem preKeyLoopExitMem_ok_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) :
    sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      wirePreKeyOf A (sp' + 312#64) m ⊢
      preKeyLoopExitMem A sp' ptr bs 0#64 (some m) := by
  unfold preKeyLoopExitMem sliceCursorAt; dsimp only
  rw [pure_true_emp rfl, emp_sepConj,
    ← sepConj_assoc ((sp' + 296#64) ↦₆₄ ptr) ((sp' + 296#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) (ptr ↦ₛ bs),
    sepConj_assoc (((sp' + 296#64) ↦₆₄ ptr) ∗ ((sp' + 296#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length))]
  exact sepConj_mono_left (pointsTo64_pair_entails_memRegion16 (sp' + 296#64) ptr (BitVec.ofNat 64 bs.length))

theorem memRegion64_split24 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 64 = memRegion (sp' + 448#64) 24 ∗ memRegion (sp' + 472#64) 40 := by
  have hs := memRegion_split (sp' + 448#64) 24 40 (by decide)
  have ha : sp' + 448#64 + 24#64 = sp' + 472#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem memRegion56_split40 (sp' : BitVec 64) :
    memRegion (sp' + 456#64) 56 = memRegion (sp' + 456#64) 40 ∗ memRegion (sp' + 496#64) 16 := by
  have hs := memRegion_split (sp' + 456#64) 40 16 (by decide)
  have ha : sp' + 456#64 + 40#64 = sp' + 496#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem memRegion48_16_eq_64 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 48 ∗ memRegion (sp' + 496#64) 16 = memRegion (sp' + 448#64) 64 := by
  have hs := (memRegion_split (sp' + 448#64) 48 16 (by decide)).symm
  have ha : sp' + 448#64 + 48#64 = sp' + 496#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem scratch24_ok_entails_memRegion64 (sp' v w : BitVec 64) :
    ((sp' + 448#64) ↦₃₂ 0#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) ∗ ((sp' + 456#64) ↦₆₄ v) ∗
      ((sp' + 464#64) ↦₆₄ w) ∗ memRegion (sp' + 472#64) 40 ⊢ memRegion (sp' + 448#64) 64 := by
  have h0 : ((sp' + 448#64) ↦₃₂ 0#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) = ((sp' + 448#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32 (sp' + 448#64)).symm
    have ha : sp' + 448#64 + 4#64 = sp' + 452#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h0, memRegion64_split24 sp', memRegion_split (sp' + 448#64) 8 16 (by decide),
    memRegion_split (sp' + 448#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  have ha2 : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha1, ha2]; refine Entails.trans ?_
    (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (sp' + 448#64) 0#64)
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 456#64) v)
        (pointsTo64_entails_memRegion (sp' + 464#64) w))) (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem scratch24_err_entails_memRegion64 (sp' e : BitVec 64) :
    ((sp' + 448#64) ↦₃₂ 1#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) ∗ ((sp' + 456#64) ↦₆₄ e) ∗
      memRegion (sp' + 464#64) 8 ∗ memRegion (sp' + 472#64) 40 ⊢ memRegion (sp' + 448#64) 64 := by
  have h1 : ((sp' + 448#64) ↦₃₂ 1#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) = ((sp' + 448#64) ↦₆₄ 1#64) := by
    have hs := (pointsTo64_one_split32 (sp' + 448#64)).symm
    have ha : sp' + 448#64 + 4#64 = sp' + 452#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h1, memRegion64_split24 sp', memRegion_split (sp' + 448#64) 8 16 (by decide),
    memRegion_split (sp' + 448#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  have ha2 : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha1, ha2]; refine Entails.trans ?_
    (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (sp' + 448#64) 1#64)
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 456#64) e) (Entails.refl _))) (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem memRegion64_split_448_456_464 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 64 =
      (∃∗ w0 : BitVec 64, (sp' + 448#64) ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (sp' + 456#64) ↦₆₄ w1) ∗
      memRegion (sp' + 464#64) 48 := by
  rw [memRegion_split (sp' + 448#64) 8 56 (by decide), memRegion_split (sp' + 448#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  have ha1 : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  have ha2 : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha1, ha2]

theorem pointsTo64_456_memRegion48_entails_memRegion56 (sp' v : BitVec 64) :
    ((sp' + 456#64) ↦₆₄ v) ∗ memRegion (sp' + 464#64) 48 ⊢ memRegion (sp' + 456#64) 56 := by
  rw [memRegion_split (sp' + 456#64) 8 48 (by decide)]
  have ha : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha]; exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 456#64) v)

theorem decodeKeyPK_err_entailsX (A : RustAlloc) (sp' ptr w0 v : BitVec 64)
    (bs rest : List (BitVec 8)) (m : ProtoPreKeySignalMessage) :
    sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      ((sp' + 448#64) ↦₆₄ w0) ∗ ((sp' + 456#64) ↦₆₄ v) ∗ memRegion (sp' + 464#64) 48 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ wirePreKeyOf A (sp' + 312#64) m ⊢
    memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      ((sp' + 448#64) ↦₆₄ w0) ∗ memRegion (sp' + 456#64) 56 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ wirePreKeyOf A (sp' + 312#64) m := by
  refine Entails.trans (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 296#64) ptr bs rest)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  rw [← sepConj_assoc]; exact sepConj_mono_left (pointsTo64_456_memRegion48_entails_memRegion56 sp' v)

theorem memRegion64_split8 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 64 = memRegion (sp' + 448#64) 8 ∗ memRegion (sp' + 456#64) 56 := by
  have hs := memRegion_split (sp' + 448#64) 8 56 (by decide)
  have ha : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  rw [ha] at hs; exact hs

abbrev memRegion64_split8_448 := memRegion64_split8

/-! ## 2. Loop Head (`+0x0e4..+0x0f0`, `+0x300..+0x304`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
