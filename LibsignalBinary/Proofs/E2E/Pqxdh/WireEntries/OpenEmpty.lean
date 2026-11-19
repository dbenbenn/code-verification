/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenEmptyPrefix -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsKeysAddresses
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.StoreNew.Proof
public import LibsignalBinary.Proofs.E2E.Bin.Hooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenBase
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib
open ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.InMem

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64

theorem stackAt_160_eq_cells_8_12 (sp : BitVec 64) :
    stackAt sp 160 = cells (sp - 160#64) 8 ∗ cells (sp - 96#64) 12 := by
  dsimp only [stackAt]
  rw [memRegion_split' (b := sp - 160#64) (b' := sp - 96#64)
        (N := 160) (n := 64) (k := 96) (by decide) (by bv_lin) (by decide),
      ProofLib.memRegion_cells (sp - 160#64) 8 (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]

theorem memRegion_32_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ d0 d1 d2 d3 : BitVec 64,
      m ⊨ ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3)) ∗ R := by
  rw [memRegion_32_four_64 a] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc] at hm ⊢
  rcases hm with ⟨d3, d2, d1, d0, hm⟩
  exact ⟨d0, d1, d2, d3, hm⟩

theorem memRegion_64_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 64 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64,
      m ⊨ ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ∗
            ((a + 32#64) ↦₆₄ d4) ∗ ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗ ((a + 56#64)
              ↦₆₄ d7)) ∗ R := by
  rw [memRegion_split' (b := a) (b' := a + 32#64)
    (N := 64) (n := 32) (k := 32) (by decide) rfl (by decide),
      sepConj_assoc] at hm
  obtain ⟨d0, d1, d2, d3, hm1⟩ := memRegion_32_elim a hm
  have hm2 : m ⊨ memRegion (a + 32#64) 32 ∗
      (((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3)) ∗ R) := by
    ac_sat hm1
  obtain ⟨d4, d5, d6, d7, hm3⟩ := memRegion_32_elim (a + 32#64) hm2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm3
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, by ac_sat hm3⟩

theorem exists_words8_of_length_64 {bs : List (BitVec 8)} (hlen : bs.length = 64) :
    ∃ k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ k0) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ k2) ∗ ((a + 24#64) ↦₆₄ k3) ∗
        ((a + 32#64) ↦₆₄ k4) ∗ ((a + 40#64) ↦₆₄ k5) ∗ ((a + 48#64) ↦₆₄ k6) ∗ ((a + 56#64) ↦₆₄
          k7) := by
  obtain ⟨k0, k1, k2, k3, _, h1⟩ := exists_unpack64_of_length_32 (bs := bs.take 32) (by simp [hlen])
  obtain ⟨k4, k5, k6, k7, _, h2⟩ := exists_unpack64_of_length_32 (bs := bs.drop 32) (by simp [hlen])
  refine ⟨k0, k1, k2, k3, k4, k5, k6, k7, fun a => ?_⟩
  rw [pointsToBytes_take_drop a 32 bs (by omega), h1 a, h2 (a + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion_32_addr_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ (m0 m1 m2 : BitVec 64) (mb : BitVec 8),
      m ⊨ ((a ↦₆₄ m0) ∗ ((a + 8#64) ↦₆₄ m1) ∗ ((a + 16#64) ↦₆₄ m2) ∗
            ((a + 24#64) ↦₈ mb) ∗ memRegion (a + 25#64) 7) ∗ R := by
  rw [memRegion_split' (b := a) (b' := a + 8#64)
    (N := 32) (n := 8) (k := 24) (by decide) rfl (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64)
        (N := 24) (n := 8) (k := 16) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64)
        (N := 16) (n := 8) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := a + 24#64) (b' := a + 25#64)
        (N := 8) (n := 1) (k := 7) (by decide) (by bv_lin) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_one (a + 24#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc] at hm ⊢
  rcases hm with ⟨mb, m2, m1, m0, hm⟩
  exact ⟨m0, m1, m2, mb, hm⟩

theorem memRegion_openP_0x450_split (sp : BitVec 64) :
    memRegion sp 0x450 =
      memRegion sp 8 ∗
      memRegion (sp + 0x008#64) 32 ∗
      memRegion (sp + 0x028#64) 32 ∗
      memRegion (sp + 0x048#64) 48 ∗
      memRegion (sp + 0x078#64) 120 ∗
      memRegion (sp + 240#64) 32 ∗
      memRegion (sp + 272#64) 336 ∗
      memRegion (sp + 608#64) 65 ∗
      memRegion (sp + 673#64) 367 ∗
      memRegion (sp + 1040#64) 64 := by
  rw [memRegion_split' (b := sp) (b' := sp + 0x008#64)
    (N := 0x450) (n := 8) (k := 1096) (by decide) rfl (by decide),
      memRegion_split' (b := sp + 0x008#64) (b' := sp + 0x028#64)
        (N := 1096) (n := 32) (k := 1064) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x028#64) (b' := sp + 0x048#64)
        (N := 1064) (n := 32) (k := 1032) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x048#64) (b' := sp + 0x078#64)
        (N := 1032) (n := 48) (k := 984) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x078#64) (b' := sp + 240#64)
        (N := 984) (n := 120) (k := 864) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 240#64) (b' := sp + 272#64)
        (N := 864) (n := 32) (k := 832) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 272#64) (b' := sp + 608#64)
        (N := 832) (n := 336) (k := 496) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 608#64) (b' := sp + 673#64)
        (N := 496) (n := 65) (k := 431) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 673#64) (b' := sp + 1040#64)
        (N := 431) (n := 367) (k := 64) (by decide) (by bv_lin) (by decide)]

theorem memRegion_openP_0x0f0_join (sp : BitVec 64) (bs32 bs64_1 bs64_2 : List (BitVec 8))
    (b0 : BitVec 8) (h32 : bs32.length = 32) (h64_1 : bs64_1.length = 64) (h64_2 : bs64_2.length =
      64) :
    (((sp + 240#64) ↦ₛ bs32) ∗
     memRegion (sp + 272#64) 336 ∗
     ((sp + 608#64) ↦₈ b0) ∗ ((sp + 609#64) ↦ₛ bs64_1) ∗
     memRegion (sp + 673#64) 367 ∗
     ((sp + 1040#64) ↦ₛ bs64_2)) ⊢
      memRegion (sp + 0x0f0#64) 0x360 := by
  have he1 : ((sp + 240#64) ↦ₛ bs32) ⊢ memRegion (sp + 240#64) 32 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 240#64) bs32; rwa [h32] at h
  have he2 : (((sp + 608#64) ↦₈ b0) ∗ ((sp + 609#64) ↦ₛ bs64_1)) ⊢ memRegion (sp + 608#64) 65 := by
    have h1 := pointsTo8_entails_memRegion (sp + 608#64) b0
    have h2 : ((sp + 609#64) ↦ₛ bs64_1) ⊢ memRegion (sp + 609#64) 64 := by
      have h := ProofLib.pointsToBytes_entails_memRegion (sp + 609#64) bs64_1; rwa [h64_1] at h
    rw [memRegion_split' (b := sp + 608#64) (b' := sp + 609#64)
      (N := 65) (n := 1) (k := 64) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono h1 h2
  have he3 : ((sp + 1040#64) ↦ₛ bs64_2) ⊢ memRegion (sp + 1040#64) 64 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 1040#64) bs64_2; rwa [h64_2] at h
  change _ ⊢ memRegion (sp + 240#64) 864
  rw [memRegion_split' (b := sp + 240#64) (b' := sp + 272#64)
    (N := 864) (n := 32) (k := 832) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 272#64) (b' := sp + 608#64)
        (N := 832) (n := 336) (k := 496) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 608#64) (b' := sp + 673#64)
        (N := 496) (n := 65) (k := 431) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 673#64) (b' := sp + 1040#64)
        (N := 431) (n := 367) (k := 64) (by decide) (by bv_lin) (by decide)]
  refine sepConj_mono he1 (sepConj_mono (Entails.refl _) ?_)
  rw [← sepConj_assoc ((sp + 608#64) ↦₈ b0)]
  exact sepConj_mono he2 (sepConj_mono (Entails.refl _) he3)

theorem protocolAddressAt_of_addr_write (A : RustAlloc) (r : Role) (ptr a : BitVec 64)
    (hptr : ptr ≠ 0#64) :
    ((a ↦₆₄ 36#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗
     ((a + 24#64) ↦₈ 1#8) ∗ memRegion (a + 25#64) 7 ∗
     (ptr ↦ₛ r.nameBytes) ∗ A.live ptr 36 1) ⊢
      protocolAddressAt A ⟨⟨36#64, ptr, r.nameBytes⟩, 1#8⟩ a := by
  have hlen : r.nameBytes.length = 36 := role_nameBytes_length r
  have hcap_ne : (36#64 : BitVec 64) ≠ 0#64 := by decide
  unfold protocolAddressAt vecGhostAt vecU8At RustHeap.vecHeader
  simp only [hlen, hcap_ne, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜36 ≤ 36 ∧ 36 < 9223372036854775808 ∧ ptr ≠ 0#64⌝ ∗
      ((a ↦₆₄ 36#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗
       ((a + 24#64) ↦₈ 1#8) ∗ memRegion (a + 25#64) 7 ∗
       (ptr ↦ₛ r.nameBytes) ∗ A.live ptr 36 1) = _ by ac_rfl))
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)

theorem memRegion_openP_0x450_epilogue_join (sp : BitVec 64) :
    memRegion sp 8 ∗ memRegion (sp + 0x008#64) 232 ∗ memRegion (sp + 0x0f0#64) 0x360 =
      memRegion sp 0x450 := by
  rw [← memRegion_split' (b := sp + 0x008#64) (b' := sp + 0x0f0#64)
        (N := 1096) (n := 232) (k := 0x360) (by decide) (by bv_lin) (by decide),
      ← memRegion_split' (b := sp) (b' := sp + 0x008#64)
        (N := 0x450) (n := 8) (k := 1096) (by decide) rfl (by decide)]

theorem who_ne_of_ofWho_none {who : BitVec 32} (h : Role.ofWho who = none) :
    who ≠ 0#32 ∧ who ≠ 1#32 := by
  unfold Role.ofWho at h
  split_ifs at h with h0 h1
  exact ⟨h0, h1⟩

end CryptoVerification.E2E.Pqxdh.WireEntries
