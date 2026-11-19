/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts
import ProofLib.RegChain
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segPreKey` `OTR::encrypt` Call and Error Branch (`+0x8b4..+0x8ec`)

Steps from `PreKeyEncryptState'` (`+0x8b4`) through `otrEncryptSpecQ` to `PreKeyEncryptRetState`
(`+0x8c8`), and routes the `.error e` branch (`+0x8c8..+0x8ec`) to `tailPreKeyEncryptErr_ok` at
`+0xc38`.
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Separation-Logic Helpers (`+0x8b4..+0x8c8`) -/

@[expose] def preKeyEncryptScratchRest (sp : BitVec 64) (regId spk pkVal : BitVec 32) : SepProp :=
  memRegion sp 0x14 ∗
  ((sp + 0x14#64) ↦₃₂ regId) ∗
  memRegion (sp + 0x18#64) 0xc ∗
  ((sp + 0x24#64) ↦₃₂ spk) ∗
  memRegion (sp + 0x28#64) 0xc ∗
  ((sp + 0x34#64) ↦₃₂ pkVal) ∗
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
  ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

theorem preKeyEncryptScratch'_eq (sp : BitVec 64) (regId spk pkVal : BitVec 32) :
    preKeyEncryptScratch' sp regId spk pkVal =
      ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ preKeyEncryptScratchRest sp regId spk pkVal := by
  unfold preKeyEncryptScratch' preKeyEncryptScratchRest
  ac_rfl

@[expose] def encSpillsRest (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0x108#64) ↦₆₄ x.remA)

theorem encSpillsAt_eq (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsAtV ss_vt id_vt sp x =
      (((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      encSpillsRest ss_vt id_vt sp x := by
  unfold encSpillsAtV encSpillsRest
  ac_rfl

theorem tapeAfter_zero_entails_tapeAt (ctl cur : BitVec 64) (rest : List (BitVec 8))
    (hrest : rest.length < 2 ^ 63) :
    tapeAfter ctl cur rest 0 ⊢ tapeAt ctl cur rest := by
  unfold tapeAfter tapeAt
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := rfl
  rw [hcur, hlen]
  exact Entails.pure_right hrest (Entails.refl _)

theorem pollPreKeyEncrypt_split_580 (A : RustAlloc) (sp : BitVec 64) (kyBoxPtr : BitVec 64)
    (items : PendingPreKey) (kyber : Option PendingKyberPreKey) :
    pollE6c' A sp kyBoxPtr items kyber =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 120 ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac := by
  unfold pollE6c'
  rw [mr_cut_add sp 0x46a 0x116 0x320 (by decide),
      mr_cut_add sp 0x580 120 0x2a8 (by decide)]
  simp only [sepConj_assoc]

theorem bitvec_ofNat_toNat_lt_32 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  omega

@[expose] def preKeyEncryptCallRestFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (x : WithStoresEncGhost)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x370#64) 0xf8 ∗
  preKeyEncryptScratchRest sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
  encSpillsRest ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5f8#64) 0x2a8 ∗
  optKyberAt A (sp + 0x8a0#64) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
  memRegion (sp + 0x8b8#64) 0x1fc ∗
  ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
  memRegion (sp + 0xad4#64) 0xac ∗
  memRegion x.ret 248 ∗
  nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

theorem preKeyEncryptScratch'_weaken_cmScratch (sp : BitVec 64) (regId spk pkVal : BitVec 32) :
    preKeyEncryptScratch' sp regId spk pkVal ⊢ cmScratch sp := by
  unfold preKeyEncryptScratch' cmScratch
  rw [memRegion_split sp 0x14 0x24 (by decide),
      mr_cut_add sp 0x14 4 0x20 (by decide),
      mr_cut_add sp 0x18 0xc 0x14 (by decide),
      mr_cut_add sp 0x24 4 0x10 (by decide),
      mr_cut_add sp 0x28 0xc 4 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (pointsTo64_entails_memRegion _ _)))))))))

private theorem list_len6 {α : Type} (ws : List α) (h : ws.length = 6) :
    ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
  rcases ws with _ | ⟨w0, ws⟩; · nomatch h
  rcases ws with _ | ⟨w1, ws⟩; · nomatch h
  rcases ws with _ | ⟨w2, ws⟩; · nomatch h
  rcases ws with _ | ⟨w3, ws⟩; · nomatch h
  rcases ws with _ | ⟨w4, ws⟩; · nomatch h
  rcases ws with _ | ⟨w5, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩
  · nomatch h

private theorem memRegion_24_exists_words64At (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ v0 v1 v2 : BitVec 64, m ⊨ words64At a [v0, v1, v2] ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 3 a (by decide) hm
  rcases ws with _ | ⟨v0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨v1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨v2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, hws⟩
  · nomatch hlen

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
