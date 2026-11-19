/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefix -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
  (vecU8Buf vecU8BufRest vecU8At_eq_header_buf layoutOk_align1
   vecU8Buf_entails_slice_rest slice_rest_entails_vecU8Buf)
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

/-! ## 5. Segment 3 (`176 .. 224` & `308 .. 336`): optional reserve + `memcpy` of `dec` -/

theorem cmp_hi_ult_true {cap : BitVec 64} {pfxLen decLen : Nat}
    (hpfx : pfxLen ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hdec : decLen ≤ 3)
    (hlt : cap.toNat < pfxLen + decLen) :
    (cap - BitVec.ofNat 64 pfxLen).ult (BitVec.ofNat 64 decLen) = true := by
  have hp : (BitVec.ofNat 64 pfxLen).toNat = pfxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd : (BitVec.ofNat 64 decLen).toNat = decLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle_bv : BitVec.ofNat 64 pfxLen ≤ cap := BitVec.le_def.mpr (by omega)
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_sub_of_le hle_bv, hp, hd]
  omega

theorem cmp_hi_ult_false {cap : BitVec 64} {pfxLen decLen : Nat}
    (hcap : cap.toNat < 2 ^ 63) (hdec : decLen ≤ 3)
    (hle : pfxLen + decLen ≤ cap.toNat) :
    (cap - BitVec.ofNat 64 pfxLen).ult (BitVec.ofNat 64 decLen) = false := by
  have hp : (BitVec.ofNat 64 pfxLen).toNat = pfxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd : (BitVec.ofNat 64 decLen).toNat = decLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle_bv : BitVec.ofNat 64 pfxLen ≤ cap := BitVec.le_def.mpr (by omega)
  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_sub_of_le hle_bv, hp, hd]
  omega

theorem vecU8At_header_unpack (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs) := by
  rw [vecU8At_eq_header_buf]
  refine Entails.trans (sepConj_mono_right (vecU8Buf_entails_slice_rest A cap ptr bs)) ?_
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (slice_rest_entails_vecU8Buf A cap ptr bs)))))
  unfold vecHeader
  apply entails_of_eq
  ac_rfl

end CryptoVerification.SignalSession.Cli.AddressText.Helpers
