/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalMem
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segSignal` `OTR::encrypt` Error Path (`+0x3a4..+0x3c8` → `+0xc14`)

Routes an `Err p` result of `OTR::encrypt` at `SegSignalRetStateV` (`+0x3a4`) through `+0x3c8` to
the shared protocol-error tail `tailSignalEncryptErr_ok` (`+0xc14`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

theorem segSignal_apply {m : Memory} {B L L' G : SepProp} (hent : L ⊢ L') (hB : B = L ∗ G)
    (hm : m ⊨ B) : m ⊨ L' ∗ G := by
  subst hB
  exact Satisfies.mono (sepConj_mono_left hent) hm

theorem segSignal_focusR {m : Memory} {B T G F : SepProp} (R : SepProp) (hB : B = T ∗ G)
    (hG : G = R ∗ F) (hm : m ⊨ B) : m ⊨ T ∗ (F ∗ R) := by
  subst hB hG
  rwa [sepConj_comm R F] at hm

theorem segSignal_ofProtocol {p : SignalProtocolError} (hp : p ≠ .panic) :
    (ApiError.ofProtocol p : ApiError AddrVal Unit) = .protocol p := by
  cases p <;> first | rfl | exact absurd rfl hp

theorem segSignal_err_tail_ent (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) (k : IdentityKey)
    (pqCap pqPtr : BitVec 64) (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        words64At (sp + 0xb00#64) [w3, w4, w5]) ∗
      (cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        otrAt A (sp + 0x288#64) pqCap pqPtr ot ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5b8#64) 64 ∗
        memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb18#64) 0x68) ⊢
      dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap, pqPtr, ot)) none
        (pollWith sp 0xb00 [w3, w4, w5]) := by
  have hkey : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
    simpa using h
  have hw6 : words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ⊢ memRegion (sp + 0x588#64) 48 :=
    SegFrom.words64At_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp + 0x588#64)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hcm : memRegion (sp + 0x350#64) 0x119 =
      memRegion (sp + 0x350#64) 0x20 ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        memRegion (sp + 0x468#64) 1 := by
    rw [show (0x119 : Nat) = 0x20 + 0xf9 from rfl,
      mr_cut_add sp 0x350 0x20 0xf9 (by decide),
      show (0xf9 : Nat) = 0xf8 + 1 from rfl,
      mr_cut_add sp (0x350 + 0x20) 0xf8 1 (by decide)]
  have hpoll : pollWith sp 0xb00 [w3, w4, w5] =
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
        memRegion (sp + 0x588#64) 48 ∗ memRegion (sp + 0x5b8#64) 64 ∗
        memRegion (sp + 0x5f8#64) 0x508) ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    unfold pollWith
    have h1 : memRegion (sp + 0x46a#64) (0xb00 - 0x46a) =
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
          memRegion (sp + 0x588#64) 48 ∗ memRegion (sp + 0x5b8#64) 64 ∗
          memRegion (sp + 0x5f8#64) 0x508 := by
      rw [show (0xb00 - 0x46a : Nat) = 0x116 + (8 + (48 + (64 + 0x508))) from rfl,
        mr_cut_add sp 0x46a 0x116 _ (by decide),
        mr_cut_add sp (0x46a + 0x116) 8 _ (by decide),
        mr_cut_add sp (0x46a + 0x116 + 8) 48 _ (by decide),
        mr_cut_add sp (0x46a + 0x116 + 8 + 48) 64 _ (by decide)]
    rw [h1]
    rfl
  unfold dropRecordSlots otrSlotAt cmSlotAt
  dsimp only
  rw [hcm, hpoll]
  refine Entails.trans ?_ (Entails.of_eq rfl)
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono_left hw6))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hkey))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))))))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem segSignal_list_len3 {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

theorem segSignal_pure_front {m : Memory} {φ : Prop} {P G : SepProp} (hm : m ⊨ (⌜φ⌝ ∗ P) ∗ G) :
    φ ∧ (m ⊨ P ∗ G) := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
