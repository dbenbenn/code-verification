/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Heap.SpecBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg

/-!
# Real-Consumer `E2E.Pqxdh.Shared.cryptoLeafStubSpec` Bridge for `<EdwardsPoint as Neg>::neg` (`LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNegConsumer`)

Discharges the real consumer contract `CryptoVerification.E2E.Pqxdh.Shared.cryptoLeafStubSpec`
(`LibsignalBinary/Proofs/E2E/Pqxdh/Shared/IsCanonical.lean:179`) directly without any local mirror
definitions, keeping `EdwardsNeg.lean` outside `GeneratedLean.*`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNegConsumer

open Arm64 ProofLib
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification.E2E (u8Vec vecU8 toU8 ofU8 fitVec)
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhHookStack CryptoLeafCall bytesToBv8 fitBv8
  cryptoLeafStubSpec)
open CryptoVerification.SignalSession.CliExt (inputAfter)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack subroutine_ok_drop_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (withFsPred
  subroutine_ok_withFsPred_of_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk (hasInstrs_of_hasWords
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords)
open LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg (edwardsPointNegWords
  edwardsPointNegInstrs edwardsPointNegUnstackedSpec edwardsPointNeg_withStack_keepsFs_ok
  pureWordsProg_hasInstrs_edNeg pureWordsProg_noSvcMsr_edNeg)

private theorem inputAfter_false (inA : BitVec 64) (v : List.Vector (BitVec 8) 160) :
    inputAfter false inA v = (inA ↦ₛ v.toList) := rfl

private theorem bytesToBv8_eq_ofU8 (bs : List UInt8) :
    bytesToBv8 bs = ofU8 bs := by
  unfold bytesToBv8 ofU8
  apply List.map_congr_left
  intro b _
  cases b
  simp [UInt8.toNat]

private theorem bytesToBv8_toU8 (bs : List (BitVec 8)) :
    bytesToBv8 (toU8 bs) = bs := by
  rw [bytesToBv8_eq_ofU8]
  unfold ofU8 toU8
  rw [List.map_map]
  simp [Function.comp_def]

private theorem u8Vec_toList_of_len {n : Nat} {bs : List UInt8}
    (h : bs.length = n) :
    (u8Vec n bs).toList = bytesToBv8 bs := by
  unfold u8Vec fitVec
  dsimp only [List.Vector.toList]
  rw [← bytesToBv8_eq_ofU8]
  have hlen : (bytesToBv8 bs).length = n := by simp [bytesToBv8, h]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem fitBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    fitBv8 n (vecU8 v) = v.toList := by
  unfold fitBv8 vecU8
  rw [bytesToBv8_toU8]
  have hlen : v.toList.length = n := List.Vector.toList_length v
  simp [hlen]

theorem unstacked_simulates_real_cryptoLeafStubSpec :
    SpecSimulates
      (keepsFs (withStack (edwardsPointNegUnstackedSpec false) pqxdhHookStack))
      (keepsFs
        (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  dsimp only [keepsFs, cryptoLeafStubSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hlen⟩, hpre⟩ := hpre
  have hv_list : (u8Vec 160 g.inBytes).toList = bytesToBv8 g.inBytes := u8Vec_toList_of_len hlen
  refine ⟨(g.inPtr, u8Vec 160 g.inBytes, g.outPtr), R, ?_, fun sf _hret _hcc hpost => ?_⟩
  · dsimp only [keepsFs, withStack, edwardsPointNegUnstackedSpec]
    rw [hv_list]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, Satisfies.mono (by sep_entail) hpre⟩
  · dsimp only [keepsFs, withStack, edwardsPointNegUnstackedSpec, cryptoLeafStubSpec] at hpost ⊢
    rw [inputAfter_false] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hfs, hpost⟩ := hpost
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    rw [hv_list] at hpost
    rw [fitBv8_vecU8]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

/-- Exact real `E2E.Pqxdh.Shared.cryptoLeafStubSpec` `keepsFs` discharge for `dalekEdNegVec`. -/
theorem edwardsPointNeg_cryptoLeafStubSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr
      (keepsFs (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  unstacked_simulates_real_cryptoLeafStubSpec.subroutine_ok
    (edwardsPointNeg_withStack_keepsFs_ok false pqxdhHookStack hcode)

/-- Exact real `E2E.Pqxdh.Shared.cryptoLeafStubSpec` (`IsCanonical.lean:179`) discharge from
    `P.hasWords addr edwardsPointNegWords`. -/
theorem edwardsPointNeg_cryptoLeafStubSpec_words_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr edwardsPointNegWords) :
    subroutine_ok P addr
      (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160) :=
  subroutine_ok_drop_keepsFs
    (edwardsPointNeg_cryptoLeafStubSpec_keepsFs_ok (hasInstrs_of_hasWords hc))

/-- Process- and VM-preserving `keepsFs` discharge for real `E2E.Pqxdh.Shared.cryptoLeafStubSpec`
    on a hook-free `P`. -/
theorem edwardsPointNeg_cryptoLeafStubBudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      (keepsFs
        (withVmPreserved
          (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160))) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (subroutine_ok_drop_keepsFs
      (edwardsPointNeg_cryptoLeafStubSpec_keepsFs_ok (pureWordsProg_hasInstrs_edNeg addr)))
    (pureWordsProg_noSvcMsr_edNeg addr) hc h_no_ext

/-- Process- and VM-preserving discharge for real `E2E.Pqxdh.Shared.cryptoLeafStubSpec` on a
    hook-free `P`. -/
theorem edwardsPointNeg_cryptoLeafStubBudgetSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      (withVmPreserved
        (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  subroutine_ok_drop_keepsFs (edwardsPointNeg_cryptoLeafStubBudgetSpec_keepsFs_ok hc h_no_ext)

/-- `withFsPred` process- and VM-preserving discharge for real `E2E.Pqxdh.Shared.cryptoLeafStubSpec`
    on a hook-free `P`. -/
theorem edwardsPointNeg_cryptoLeafStubBudgetSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      (withFsPred Pfs
        (withVmPreserved
          (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160))) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs
    (edwardsPointNeg_cryptoLeafStubBudgetSpec_keepsFs_ok hc h_no_ext)

end LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNegConsumer
