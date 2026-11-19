/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBB -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `PreKeySignalMessage::try_from`: Pack, `IdentityKey`, and `SignalMessage` Error/Dealloc Tails

Proves the `+0x970..+0xa58` `Option<Vec<u8>>` and Kyber `Box<[u8]>` deallocation chains, the
`+0xa68` `try_clone_from_ref` OOM panic branch, and the exact-`pksmErrE` error entries at
`+0x978` (`IdentityKey::try_from`) and `+0x9f0` (`SignalMessage::try_from`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem etc_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem etc_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem etc_bv_add_sub_lit (x a b : BitVec 64) : x + a - b = x + (a - b) := by bv_omega
private theorem etc_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by
  bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit etc_bv_sub_add_lit' etc_bv_sub_sub_lit etc_bv_add_sub_lit etc_bv_add_neg_160
  BitVec.toNat_zero cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-! ## 1. Shared Dealloc Chain (`+0xa24 .. +0xa58` → `+0x80c` / `+0x504`) -/

/-- Ownership of the Kyber `Box<[u8]>` slot `(x28, x25) = (ptr, len)` at the Kyber-box error
entries: active (`len > 0`, live `u8` block) or inactive (`ptr = 0` or `len = 0`). -/
@[expose] def boxSlot (A : RustAlloc) (ptr len : BitVec 64) (act : Bool) : SepProp :=
  if act then
    ⌜0 < len.toNat ∧ len.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ A.live ptr len.toNat 1 ∗
      memRegion ptr len.toNat
  else ⌜ptr = 0#64 ∨ len = 0#64⌝

/-- An absent Kyber box (`ptr = 0`) is an inactive `boxSlot`. -/
theorem boxSlot_of_null (A : RustAlloc) (len : BitVec 64) :
    SepProp.emp ⊢ boxSlot A 0#64 len false := by
  show SepProp.emp ⊢ ⌜(0#64 : BitVec 64) = 0#64 ∨ len = 0#64⌝
  exact Entails.pure_right_only (Or.inl rfl) (Entails.refl _)

/-- A `boxSlot` with `ptr = 0` owns no heap. -/
theorem boxSlot_null_elim (A : RustAlloc) (len : BitVec 64) (act : Bool) :
    boxSlot A 0#64 len act ⊢ SepProp.emp := by
  cases act with
  | false =>
    show ⌜(0#64 : BitVec 64) = 0#64 ∨ len = 0#64⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  | true =>
    show (⌜0 < len.toNat ∧ len.toNat < 2 ^ 63 ∧ (0#64 : BitVec 64) ≠ 0#64⌝ ∗
      A.live 0#64 len.toNat 1 ∗ memRegion 0#64 len.toNat) ⊢ SepProp.emp
    exact Entails.pure_left fun ⟨_, _, h⟩ => absurd rfl h

/-- Bridge from upstream `boxU8Buf` to `boxSlot`. -/
theorem boxU8Buf_entails_boxSlot (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf A ptr bs ⊢ boxSlot A ptr (BitVec.ofNat 64 bs.length) (!bs.isEmpty) := by
  cases bs with
  | nil =>
    unfold boxU8Buf
    rw [ite_eq_left rfl]
    refine Entails.pure_left fun _ => ?_
    show SepProp.emp ⊢ ⌜ptr = 0#64 ∨ BitVec.ofNat 64 0 = 0#64⌝
    exact Entails.pure_right_only (Or.inr rfl) (Entails.refl _)
  | cons b bs' =>
    unfold boxU8Buf
    rw [ite_eq_right (List.cons_ne_nil _ _)]
    refine Entails.pure_left fun ⟨hptr, hlt⟩ => ?_
    have hlen : (BitVec.ofNat 64 (b :: bs').length).toNat = (b :: bs').length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))
    show (A.live ptr (b :: bs').length 1 ∗ (ptr ↦ₛ (b :: bs'))) ⊢
      (⌜0 < (BitVec.ofNat 64 (b :: bs').length).toNat ∧
          (BitVec.ofNat 64 (b :: bs').length).toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr (BitVec.ofNat 64 (b :: bs').length).toNat 1 ∗
        memRegion ptr (BitVec.ofNat 64 (b :: bs').length).toNat)
    rw [hlen]
    exact Entails.pure_right ⟨Nat.succ_pos _, hlt, hptr⟩
      (sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: bs')))

private theorem etc_memRegion24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

private theorem etc_memRegion248_words7 (r : BitVec 64) :
    memRegion r 248 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 := by
  rw [ProofLib.memRegion_split r 8 240 (by decide),
    ProofLib.memRegion_split (r + 8#64) 24 216 (by decide),
    ProofLib.memRegion_split (r + 8#64 + 24#64) 24 192 (by decide),
    ProofLib.memRegion_eight r,
    etc_memRegion24_words3 (r + 8#64),
    etc_memRegion24_words3 (r + 8#64 + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem etc_words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) w2)
        (pointsTo64_entails_memRegion (a + 24#64) w3)))

private theorem etc_words5_entails_memRegion40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      etc_words4_entails_memRegion32 (a + 8#64) w1 w2 w3 w4)

private theorem etc_ikErr_speDetached_intro {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (w2 w3 w4 w5 : BitVec 64) :
    SepProp.emp ⊢
      pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 w2 w3 w4 w5 e := by
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show SepProp.emp ⊢ ⌜speWord 7 = speWord 7⌝
    exact Entails.pure_right_only rfl (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 8 = speWord 8 ∧ (t.zeroExtend 64).truncate 8 = t⌝
    exact Entails.pure_right_only ⟨rfl, by bv_bits⟩ (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 9 = speWord 9 ∧ BitVec.ofNat 64 n = BitVec.ofNat 64 n⌝
    exact Entails.pure_right_only ⟨rfl, rfl⟩ (Entails.refl _)

private theorem etc_ikErr_speDetached_elim {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (d0 d1 d2 d3 d4 d5 : BitVec 64) :
    pksm0c_speDetached A fn d0 d1 d2 d3 d4 d5 e ⊢ SepProp.emp := by
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show ⌜d0 = speWord 7⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 8 ∧ d1.truncate 8 = t⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 9 ∧ d1 = BitVec.ofNat 64 n⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _

private theorem etc_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
