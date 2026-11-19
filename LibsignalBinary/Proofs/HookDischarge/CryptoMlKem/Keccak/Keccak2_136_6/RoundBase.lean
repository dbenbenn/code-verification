/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base

/-!
# `B02` (`keccak2::<136, 6>`): shared round invariants and lemmas

Shared definitions and helper lemmas for the two inlined `keccak_f1600` loops of `mlkemBlk02`:
- Preserved scalar register bundles (`AbsorbRegsPreserved`, `TailRegsPreserved`).
- Bitwise and Keccak round normalization helpers (`d_dir_eq`, `d_comm_eq`, `theta_dir_eq`,
  `theta_comm_eq`, `rhopi_of_theta`, `rhopi0_of_theta`, `chi_lane_eq`, `chi0_lane_eq`),
  countdown branch lemmas (`bne192_target_eq`, `bne_k_target_eq`), and `SepProp` cell-to-region
  collapse lemmas (`cells128_entails_memRegion`, `cells96_entails_memRegion64_32`).
- Mid-round register and spill-memory invariants (`Loop1MidMem`, `Round1RegsA/B`, `Round1MidA/B`,
  `Round1Post` for loop 1; `Loop2MidMem`, `Round2RegsA/B`, `Round2MidA/B`, `Round2Post` for
  loop 2).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600Round
  keccakRhoOffset
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (keccak2Lane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakC
  keccakD
  keccakF1600Round_getD
  keccakRhoPi
  keccakRhoPiSrc
  keccakRoundLane
  keccakTheta
  rotateLeft_zero_64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base (
  Loop1Regs
  Loop1SpillMem
  Loop2Regs
  Loop2SpillMem
)

/-! ## Preserved scalar registers -/

/-- Scalar registers (`sp, x19..x23, x25, fp`) preserved across Loop 1 (`+0x00b0 → +0x0428`). -/
@[expose] def AbsorbRegsPreserved (s sf : State) : Prop :=
  sf.sp = s.sp ∧
  sf.readReg64 .x19 = s.readReg64 .x19 ∧
  sf.readReg64 .x20 = s.readReg64 .x20 ∧
  sf.readReg64 .x21 = s.readReg64 .x21 ∧
  sf.readReg64 .x22 = s.readReg64 .x22 ∧
  sf.readReg64 .x23 = s.readReg64 .x23 ∧
  sf.readReg64 .x25 = s.readReg64 .x25 ∧
  sf.readReg64 .fp = s.readReg64 .fp

theorem AbsorbRegsPreserved.refl (s : State) : AbsorbRegsPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem AbsorbRegsPreserved.trans {s1 s2 s3 : State}
    (h12 : AbsorbRegsPreserved s1 s2) (h23 : AbsorbRegsPreserved s2 s3) :
    AbsorbRegsPreserved s1 s3 :=
  ⟨h23.1.trans h12.1,
   h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

/-- Scalar registers (`sp, x9, x19, x20, x25, fp`) preserved across Loop 2 (`+0x05e4 → +0x08cc`). -/
@[expose] def TailRegsPreserved (s sf : State) : Prop :=
  sf.sp = s.sp ∧
  sf.readReg64 .x9 = s.readReg64 .x9 ∧
  sf.readReg64 .x19 = s.readReg64 .x19 ∧
  sf.readReg64 .x20 = s.readReg64 .x20 ∧
  sf.readReg64 .x25 = s.readReg64 .x25 ∧
  sf.readReg64 .fp = s.readReg64 .fp

theorem TailRegsPreserved.refl (s : State) : TailRegsPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem TailRegsPreserved.trans {s1 s2 s3 : State}
    (h12 : TailRegsPreserved s1 s2) (h23 : TailRegsPreserved s2 s3) :
    TailRegsPreserved s1 s3 :=
  ⟨h23.1.trans h12.1,
   h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.trans h12.2.2.2.2.2⟩

/-! ## Bitwise, round, branch, and cell normalization helpers -/

theorem orr_self_64 (v : BitVec 64) : (v ||| v) = v :=
  BitVec.or_self

theorem col_parity_eq (x0 x1 x2 x3 x4 : BitVec 64) :
    (((x1 ^^^ x0) ^^^ (x2 ^^^ x3)) ^^^ x4) =
      ((((x0 ^^^ x1) ^^^ x2) ^^^ x3) ^^^ x4) := by
  rw [BitVec.xor_comm x1 x0, ← BitVec.xor_assoc (x0 ^^^ x1) x2 x3]

theorem d_dir_eq (s : KeccakState) (x : Nat)
    {cPrev cNext a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64}
    (hp : (((a1 ^^^ a0) ^^^ (a2 ^^^ a3)) ^^^ a4) = cPrev)
    (hn : (((b1 ^^^ b0) ^^^ (b2 ^^^ b3)) ^^^ b4) = cNext)
    (ha0 : s.getD ((x + 4) % 5) 0#64 = a0)
    (ha1 : s.getD (5 + (x + 4) % 5) 0#64 = a1)
    (ha2 : s.getD (10 + (x + 4) % 5) 0#64 = a2)
    (ha3 : s.getD (15 + (x + 4) % 5) 0#64 = a3)
    (ha4 : s.getD (20 + (x + 4) % 5) 0#64 = a4)
    (hb0 : s.getD ((x + 1) % 5) 0#64 = b0)
    (hb1 : s.getD (5 + (x + 1) % 5) 0#64 = b1)
    (hb2 : s.getD (10 + (x + 1) % 5) 0#64 = b2)
    (hb3 : s.getD (15 + (x + 1) % 5) 0#64 = b3)
    (hb4 : s.getD (20 + (x + 1) % 5) 0#64 = b4) :
    cPrev ^^^ cNext.rotateLeft 1 = keccakD s x := by
  subst hp hn ha0 ha1 ha2 ha3 ha4 hb0 hb1 hb2 hb3 hb4
  unfold keccakD keccakC
  rw [col_parity_eq, col_parity_eq]

theorem d_comm_eq (s : KeccakState) (x : Nat)
    {cPrev cNext a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64}
    (hp : (((a1 ^^^ a0) ^^^ (a2 ^^^ a3)) ^^^ a4) = cPrev)
    (hn : (((b1 ^^^ b0) ^^^ (b2 ^^^ b3)) ^^^ b4) = cNext)
    (ha0 : s.getD ((x + 4) % 5) 0#64 = a0)
    (ha1 : s.getD (5 + (x + 4) % 5) 0#64 = a1)
    (ha2 : s.getD (10 + (x + 4) % 5) 0#64 = a2)
    (ha3 : s.getD (15 + (x + 4) % 5) 0#64 = a3)
    (ha4 : s.getD (20 + (x + 4) % 5) 0#64 = a4)
    (hb0 : s.getD ((x + 1) % 5) 0#64 = b0)
    (hb1 : s.getD (5 + (x + 1) % 5) 0#64 = b1)
    (hb2 : s.getD (10 + (x + 1) % 5) 0#64 = b2)
    (hb3 : s.getD (15 + (x + 1) % 5) 0#64 = b3)
    (hb4 : s.getD (20 + (x + 1) % 5) 0#64 = b4) :
    cNext.rotateLeft 1 ^^^ cPrev = keccakD s x := by
  rw [BitVec.xor_comm]
  exact d_dir_eq s x hp hn ha0 ha1 ha2 ha3 ha4 hb0 hb1 hb2 hb3 hb4

theorem theta_comm_eq (s : KeccakState) (idx : Nat) {d a : BitVec 64}
    (hd : d = keccakD s (idx % 5)) (ha : s.getD idx 0#64 = a) :
    d ^^^ a = keccakTheta s idx := by
  subst hd ha
  unfold keccakTheta
  exact BitVec.xor_comm _ _

theorem theta_dir_eq (s : KeccakState) (idx : Nat) {d a : BitVec 64}
    (hd : d = keccakD s (idx % 5)) (ha : s.getD idx 0#64 = a) :
    a ^^^ d = keccakTheta s idx := by
  subst hd ha
  rfl

theorem rhopi_of_theta (s : KeccakState) (idx src sh : Nat) {t : BitVec 64}
    (hsrc : keccakRhoPiSrc idx = src := by decide)
    (hsh : keccakRhoOffset src = sh := by decide)
    (ht : t = keccakTheta s src) :
    t.rotateLeft sh = keccakRhoPi s idx := by
  subst ht hsrc hsh
  rfl

theorem rhopi0_of_theta (s : KeccakState) {t : BitVec 64}
    (ht : t = keccakTheta s 0) :
    t = keccakRhoPi s 0 := by
  subst ht
  dsimp only [keccakRhoPi, keccakRhoPiSrc, keccakRhoOffset]
  exact (rotateLeft_zero_64 _).symm

theorem lane_round_eq {s : KeccakState} {rc lhs : BitVec 64} (idx : Nat)
    (hidx : idx < 25 := by decide)
    (heq : lhs = keccakRoundLane s rc idx) :
    lhs = (keccakF1600Round s rc).getD idx 0#64 :=
  heq.trans (keccakF1600Round_getD s rc hidx).symm

theorem chi_lane_eq (s : KeccakState) (rc : BitVec 64) (idx i0 i1 i2 : Nat)
    {b0 b1 b2 : BitVec 64}
    (h0 : (idx == 0) = false := by decide)
    (h25 : idx < 25 := by decide)
    (hi0 : 5 * (idx / 5) + idx % 5 = i0 := by decide)
    (hi1 : 5 * (idx / 5) + (idx % 5 + 1) % 5 = i1 := by decide)
    (hi2 : 5 * (idx / 5) + (idx % 5 + 2) % 5 = i2 := by decide)
    (hb0 : b0 = keccakRhoPi s i0)
    (hb1 : b1 = keccakRhoPi s i1)
    (hb2 : b2 = keccakRhoPi s i2) :
    (~~~b1 &&& b2) ^^^ b0 = (keccakF1600Round s rc).getD idx 0#64 := by
  subst hb0 hb1 hb2 hi0 hi1 hi2
  rw [BitVec.xor_comm]
  exact lane_round_eq idx h25 (by simp only [keccakRoundLane, h0]; rfl)

theorem chi0_lane_eq (s : KeccakState) (rc : BitVec 64) {b0 b1 b2 : BitVec 64}
    (hb0 : b0 = keccakRhoPi s 0)
    (hb1 : b1 = keccakRhoPi s 1)
    (hb2 : b2 = keccakRhoPi s 2) :
    (~~~b1 &&& b2) ^^^ (rc ^^^ b0) = (keccakF1600Round s rc).getD 0 0#64 := by
  subst hb0 hb1 hb2
  have h : (~~~keccakRhoPi s 1 &&& keccakRhoPi s 2) ^^^ (rc ^^^ keccakRhoPi s 0) =
      (keccakRhoPi s 0 ^^^ (~~~keccakRhoPi s 1 &&& keccakRhoPi s 2)) ^^^ rc := by
    ext i hi
    simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
    cases (keccakRhoPi s 0)[i] <;> cases (keccakRhoPi s 1)[i] <;>
      cases (keccakRhoPi s 2)[i] <;> cases rc[i] <;> rfl
  exact lane_round_eq 0 (by decide) h

theorem add8_eq_ofNat (r : Nat) :
    BitVec.ofNat 64 (8 * r) + 8#64 = BitVec.ofNat 64 (8 * (r + 1)) := by
  rw [show 8 * (r + 1) = 8 * r + 8 by omega, BitVec.ofNat_add]

theorem cmp192_ne_of_lt {r : Nat} (hlt : r + 1 < 24) :
    BitVec.ofNat 64 (8 * r) + 8#64 ≠ 192#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [add8_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (r + 1) < 2 ^ 64)] at h
  omega

theorem cmp192_eq_of_ge {r : Nat} (hr : r < 24) (hge : ¬ (r + 1 < 24)) :
    BitVec.ofNat 64 (8 * r) + 8#64 = 192#64 := by
  have hr23 : r = 23 := by omega
  subst hr23
  decide

theorem bne192_target_eq {r : Nat} (hr : r < 24) (t1 t2 : BitVec 64) :
    (if (BitVec.ofNat 64 (8 * r) + 8#64 != 192#64) = true then t1 else t2) =
      (if r + 1 < 24 then t1 else t2) := by
  by_cases hlt : r + 1 < 24
  · simp [hlt, bne_iff_ne, cmp192_ne_of_lt hlt]
  · simp [hlt, cmp192_eq_of_ge hr hlt]

theorem add1_eq_ofNat (k : Nat) :
    BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.ofNat_add]

theorem cmp_k_ne_of_lt {k nBlocks : Nat} (hlt : k + 1 < nBlocks) (hn : nBlocks < 2 ^ 64) :
    BitVec.ofNat 64 k + 1#64 ≠ BitVec.ofNat 64 nBlocks := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [add1_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
    Nat.mod_eq_of_lt hn] at h
  omega

theorem cmp_k_eq_of_ge {k nBlocks : Nat} (hk : k < nBlocks) (hge : ¬ (k + 1 < nBlocks)) :
    BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 nBlocks := by
  have heq : k + 1 = nBlocks := by omega
  rw [add1_eq_ofNat, heq]

theorem bne_k_target_eq {k nBlocks : Nat} (hk : k < nBlocks) (hn : nBlocks < 2 ^ 64)
    (t1 t2 : BitVec 64) :
    (if (BitVec.ofNat 64 k + 1#64 != BitVec.ofNat 64 nBlocks) = true then t1 else t2) =
      (if k + 1 < nBlocks then t1 else t2) := by
  by_cases hlt : k + 1 < nBlocks
  · simp [hlt, bne_iff_ne, cmp_k_ne_of_lt hlt hn]
  · simp [hlt, cmp_k_eq_of_ge hk hlt]

theorem cells128_entails_memRegion (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    (((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
       (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
      ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
       (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗
     (((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
       (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))) ∗
      ((((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13)) ∗
       (((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15))))) ⊢
      memRegion a 128 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 120) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 16#64) (n := 8) (k := 112) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 24#64) (n := 8) (k := 104) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 32#64) (n := 8) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 40#64) (n := 8) (k := 88) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 48#64) (n := 8) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 56#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 64#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 72#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 80#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 88#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 96#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 104#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 112#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 120#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (sepConj_mono (pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (pointsTo64_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (pointsTo64_entails_memRegion _ _)))))))))))))))

theorem cells96_entails_memRegion64_32 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    (((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
       (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
      ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
       (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗
     ((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
      (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11)))) ⊢
      memRegion a 64 ∗ memRegion (a + 64#64) 32 := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 40#64) (b' := a + 48#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 48#64) (b' := a + 56#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 64#64) (b' := a + 72#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 72#64) (b' := a + 80#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 80#64) (b' := a + 88#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (pointsTo64_entails_memRegion _ _)))))))))))

theorem writeVReg128_eq_self {s : State} {idx : BitVec 5} {val : BitVec 128}
    (h : s.readVReg128 idx = val) :
    s.writeVReg128 idx val = s := by
  have hv : s.vregs.write idx val = s.vregs := by
    rcases hvregs : s.vregs with ⟨f⟩
    dsimp only [State.readVReg128, VRegFile.read, VRegFile.write] at h ⊢
    rw [hvregs] at h
    congr 1
    funext i
    split
    · simp_all
    · rfl
  cases s
  dsimp only [State.writeVReg128] at hv ⊢
  rw [hv]

theorem spAligned_of_sp_eq {s1 s2 : State} (hsp : s2.sp = s1.sp) (ha : s1.spAligned = true) :
    s2.spAligned = true := by
  simpa only [State.spAligned, hsp] using ha

macro "reg64_lhs" : tactic => `(tactic| (
  conv =>
    lhs
    simp (config := { decide := true }) only [
      State.readReg64_writeVReg128,
      State.readReg64_writeReg64_same,
      State.readReg64_writeReg64,
      State.readReg64_advancePC,
      State.readReg64_setPC,
      State.readReg64_setMem,
      State.readReg64_setPState]
  try rfl))

macro "vreg_lhs" : tactic => `(tactic| (
  conv =>
    lhs
    simp only [
      State.readVReg128_writeVReg128_same,
      State.readVReg128_writeVReg128,
      State.readVReg128_writeReg64,
      State.readVReg128_writeReg32,
      State.readVReg128_advancePC,
      State.readVReg128_setPC,
      State.readVReg128_setMem,
      State.readVReg128_setPState,
      BitVec.reduceEq,
      ite_true,
      ite_false]
  try rfl))

/-! ## 2-way lane projections and loop 1 mid-round invariants -/

@[expose] def laneTheta (st0 st1 : KeccakState) (idx : Nat) : BitVec 128 :=
  keccakTheta st1 idx ++ keccakTheta st0 idx

@[expose] def laneD (st0 st1 : KeccakState) (x : Nat) : BitVec 128 :=
  keccakD st1 x ++ keccakD st0 x

@[expose] def laneRhoPi (st0 st1 : KeccakState) (idx : Nat) : BitVec 128 :=
  keccakRhoPi st1 idx ++ keccakRhoPi st0 idx

@[expose] def laneShlTheta (st0 st1 : KeccakState) (idx sh : Nat) : BitVec 128 :=
  (keccakTheta st1 idx <<< sh) ++ (keccakTheta st0 idx <<< sh)

/-- Stack spill layout at `+0x01d4` and `+0x02dc` (`176` bytes at `sp`). -/
@[expose] def Loop1MidMem (sp : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  (((((sp ↦₆₄ st0.getD 11 0#64) ∗ ((sp + 8#64) ↦₆₄ st1.getD 11 0#64)) ∗
     (((sp + 16#64) ↦₆₄ st0.getD 23 0#64) ∗ ((sp + 24#64) ↦₆₄ st1.getD 23 0#64))) ∗
    ((((sp + 32#64) ↦₆₄ st0.getD 24 0#64) ∗ ((sp + 40#64) ↦₆₄ st1.getD 24 0#64)) ∗
     (((sp + 48#64) ↦₆₄ st0.getD 13 0#64) ∗ ((sp + 56#64) ↦₆₄ st1.getD 13 0#64)))) ∗
   (((((sp + 64#64) ↦₆₄ st0.getD 19 0#64) ∗ ((sp + 72#64) ↦₆₄ st1.getD 19 0#64)) ∗
     (((sp + 80#64) ↦₆₄ st0.getD 18 0#64) ∗ ((sp + 88#64) ↦₆₄ st1.getD 18 0#64))) ∗
    ((((sp + 96#64) ↦₆₄ st0.getD 9 0#64) ∗ ((sp + 104#64) ↦₆₄ st1.getD 9 0#64)) ∗
     (((sp + 112#64) ↦₆₄ st0.getD 4 0#64) ∗ ((sp + 120#64) ↦₆₄ st1.getD 4 0#64))))) ∗
  (((sp + 128#64) ↦₆₄ st0.getD 7 0#64) ∗ ((sp + 136#64) ↦₆₄ st1.getD 7 0#64)) ∗
  (((sp + 144#64) ↦₆₄ st0.getD 8 0#64) ∗ ((sp + 152#64) ↦₆₄ st1.getD 8 0#64)) ∗
  (((sp + 160#64) ↦₆₄ st0.getD 14 0#64) ∗ ((sp + 168#64) ↦₆₄ st1.getD 14 0#64))

/-- Live vector registers at `+0x01d4` (after Loop 1 Part A). -/
@[expose] def Round1RegsA (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 0#5 = keccak2Lane st0 st1 11 ∧
  s.readVReg128 2#5 = laneTheta st0 st1 5 ∧
  s.readVReg128 4#5 = laneTheta st0 st1 10 ∧
  s.readVReg128 5#5 = laneTheta st0 st1 15 ∧
  s.readVReg128 6#5 = laneTheta st0 st1 1 ∧
  s.readVReg128 7#5 = laneTheta st0 st1 6 ∧
  s.readVReg128 8#5 = laneShlTheta st0 st1 5 36 ∧
  s.readVReg128 9#5 = keccak2Lane st0 st1 0 ∧
  s.readVReg128 11#5 = laneShlTheta st0 st1 10 3 ∧
  s.readVReg128 12#5 = laneTheta st0 st1 20 ∧
  s.readVReg128 13#5 = laneD st0 st1 0 ∧
  s.readVReg128 14#5 = laneD st0 st1 1 ∧
  s.readVReg128 15#5 = laneD st0 st1 2 ∧
  s.readVReg128 16#5 = keccak2Lane st0 st1 3 ∧
  s.readVReg128 17#5 = keccak2Lane st0 st1 22 ∧
  s.readVReg128 18#5 = keccak2Lane st0 st1 12 ∧
  s.readVReg128 21#5 = keccak2Lane st0 st1 17 ∧
  s.readVReg128 22#5 = keccak2Lane st0 st1 7 ∧
  s.readVReg128 23#5 = keccak2Lane st0 st1 16 ∧
  s.readVReg128 25#5 = laneD st0 st1 4 ∧
  s.readVReg128 26#5 = keccak2Lane st0 st1 2 ∧
  s.readVReg128 28#5 = keccak2Lane st0 st1 21 ∧
  s.readVReg128 30#5 = laneD st0 st1 3

@[expose] def Round1MidA (s : State) (sp rcBase : BitVec 64) (r : Nat)
    (st0 st1 : KeccakState) (F : SepProp) : State → SepProp → Prop :=
  fun sm Pm =>
    AbsorbRegsPreserved s sm ∧
    sm.readReg64 .x24 = s.readReg64 .x24 ∧
    sm.spAligned = true ∧
    sm.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
    sm.readReg64 .x9 = rcBase + BitVec.ofNat 64 (8 * r) ∧
    sm.pstate = subsPState64 (BitVec.ofNat 64 (8 * r) + 8#64) 192#64 ∧
    Round1RegsA sm st0 st1 ∧
    (Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1MidMem sp st0 st1 ∗ F)

/-- Live vector registers at `+0x02dc` (after Loop 1 Part B). -/
@[expose] def Round1RegsB (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 0#5 = laneShlTheta st0 st1 9 20 ∧
  s.readVReg128 3#5 = laneShlTheta st0 st1 4 27 ∧
  s.readVReg128 6#5 = laneRhoPi st0 st1 21 ∧
  s.readVReg128 7#5 = laneTheta st0 st1 9 ∧
  s.readVReg128 8#5 = laneRhoPi st0 st1 16 ∧
  s.readVReg128 9#5 = laneRhoPi st0 st1 0 ∧
  s.readVReg128 10#5 = laneRhoPi st0 st1 24 ∧
  s.readVReg128 11#5 = laneRhoPi st0 st1 7 ∧
  s.readVReg128 12#5 = laneRhoPi st0 st1 18 ∧
  s.readVReg128 14#5 = laneRhoPi st0 st1 4 ∧
  s.readVReg128 15#5 = laneRhoPi st0 st1 12 ∧
  s.readVReg128 16#5 = laneRhoPi st0 st1 2 ∧
  s.readVReg128 17#5 = laneRhoPi st0 st1 19 ∧
  s.readVReg128 18#5 = laneRhoPi st0 st1 11 ∧
  s.readVReg128 19#5 = laneRhoPi st0 st1 3 ∧
  s.readVReg128 20#5 = laneRhoPi st0 st1 8 ∧
  s.readVReg128 21#5 = laneTheta st0 st1 4 ∧
  s.readVReg128 22#5 = laneRhoPi st0 st1 9 ∧
  s.readVReg128 23#5 = laneRhoPi st0 st1 5 ∧
  s.readVReg128 24#5 = laneRhoPi st0 st1 1 ∧
  s.readVReg128 25#5 = laneTheta st0 st1 19 ∧
  s.readVReg128 26#5 = laneRhoPi st0 st1 20 ∧
  s.readVReg128 27#5 = laneRhoPi st0 st1 10 ∧
  s.readVReg128 28#5 = laneRhoPi st0 st1 17 ∧
  s.readVReg128 29#5 = laneRhoPi st0 st1 14 ∧
  s.readVReg128 30#5 = laneTheta st0 st1 14 ∧
  s.readVReg128 31#5 = laneRhoPi st0 st1 23

@[expose] def Round1MidB (s : State) (sp rcBase : BitVec 64) (r : Nat)
    (st0 st1 : KeccakState) (F : SepProp) : State → SepProp → Prop :=
  fun sm Pm =>
    AbsorbRegsPreserved s sm ∧
    sm.readReg64 .x24 = s.readReg64 .x24 ∧
    sm.spAligned = true ∧
    sm.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
    sm.readReg64 .x9 = rcBase + BitVec.ofNat 64 (8 * r) ∧
    sm.pstate = subsPState64 (BitVec.ofNat 64 (8 * r) + 8#64) 192#64 ∧
    Round1RegsB sm st0 st1 ∧
    (Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1MidMem sp st0 st1 ∗ F)

/-- Postcondition of `round1_step` after round `r < 24`. -/
@[expose] def Round1Post (s : State) (sp rcBase : BitVec 64) (r : Nat)
    (st0 st1 : KeccakState) (F : SepProp) : State → SepProp → Prop :=
  let st0' := keccakF1600Round st0 (keccakRcAt r)
  let st1' := keccakF1600Round st1 (keccakRcAt r)
  fun sf Q =>
    AbsorbRegsPreserved s sf ∧
    sf.readReg64 .x24 = s.readReg64 .x24 ∧
    sf.spAligned = true ∧
    sf.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
    Loop1Regs sf st0' st1' ∧
    (Q ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1SpillMem sp st0' st1' ∗ F)

/-! ## Loop 2 mid-round invariants (`+0x05e4 → +0x06c4 → +0x07c8 → +0x08cc`) -/

/-- Stack spill layout at `+0x06c4` and `+0x07c8` (`176` bytes at `sp`). -/
@[expose] def Loop2MidMem (sp : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  (((((sp ↦₆₄ st0.getD 19 0#64) ∗ ((sp + 8#64) ↦₆₄ st1.getD 19 0#64)) ∗
     (((sp + 16#64) ↦₆₄ st0.getD 24 0#64) ∗ ((sp + 24#64) ↦₆₄ st1.getD 24 0#64))) ∗
    ((((sp + 32#64) ↦₆₄ st0.getD 23 0#64) ∗ ((sp + 40#64) ↦₆₄ st1.getD 23 0#64)) ∗
     (((sp + 48#64) ↦₆₄ st0.getD 18 0#64) ∗ ((sp + 56#64) ↦₆₄ st1.getD 18 0#64)))) ∗
   ((((sp + 64#64) ↦₆₄ st0.getD 13 0#64) ∗ ((sp + 72#64) ↦₆₄ st1.getD 13 0#64)) ∗
    (((sp + 80#64) ↦₆₄ st0.getD 14 0#64) ∗ ((sp + 88#64) ↦₆₄ st1.getD 14 0#64)))) ∗
  (((sp + 96#64) ↦₆₄ st0.getD 7 0#64) ∗ ((sp + 104#64) ↦₆₄ st1.getD 7 0#64)) ∗
  (((sp + 112#64) ↦₆₄ st0.getD 6 0#64) ∗ ((sp + 120#64) ↦₆₄ st1.getD 6 0#64)) ∗
  (((sp + 128#64) ↦₆₄ st0.getD 9 0#64) ∗ ((sp + 136#64) ↦₆₄ st1.getD 9 0#64)) ∗
  (((sp + 144#64) ↦₆₄ st0.getD 8 0#64) ∗ ((sp + 152#64) ↦₆₄ st1.getD 8 0#64)) ∗
  (((sp + 160#64) ↦₆₄ st0.getD 4 0#64) ∗ ((sp + 168#64) ↦₆₄ st1.getD 4 0#64))

/-- Live vector registers at `+0x06c4` (after Loop 2 Part A). -/
@[expose] def Round2RegsA (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 0#5 = laneTheta st0 st1 11 ∧
  s.readVReg128 1#5 = laneTheta st0 st1 16 ∧
  s.readVReg128 2#5 = laneTheta st0 st1 5 ∧
  s.readVReg128 4#5 = laneTheta st0 st1 10 ∧
  s.readVReg128 5#5 = laneTheta st0 st1 15 ∧
  s.readVReg128 6#5 = laneTheta st0 st1 1 ∧
  s.readVReg128 7#5 = laneTheta st0 st1 6 ∧
  s.readVReg128 8#5 = keccak2Lane st0 st1 20 ∧
  s.readVReg128 11#5 = laneShlTheta st0 st1 10 3 ∧
  s.readVReg128 13#5 = laneD st0 st1 0 ∧
  s.readVReg128 14#5 = laneD st0 st1 1 ∧
  s.readVReg128 15#5 = laneD st0 st1 2 ∧
  s.readVReg128 16#5 = keccak2Lane st0 st1 2 ∧
  s.readVReg128 17#5 = keccak2Lane st0 st1 3 ∧
  s.readVReg128 19#5 = keccak2Lane st0 st1 7 ∧
  s.readVReg128 21#5 = keccak2Lane st0 st1 22 ∧
  s.readVReg128 22#5 = laneD st0 st1 4 ∧
  s.readVReg128 24#5 = keccak2Lane st0 st1 12 ∧
  s.readVReg128 25#5 = keccak2Lane st0 st1 17 ∧
  s.readVReg128 27#5 = keccak2Lane st0 st1 21 ∧
  s.readVReg128 28#5 = laneD st0 st1 3 ∧
  s.readVReg128 30#5 = laneShlTheta st0 st1 15 41 ∧
  s.readVReg128 31#5 = keccak2Lane st0 st1 0

@[expose] def Round2MidA (s : State) (sp rcBase : BitVec 64) (r : Nat)
    (st0 st1 : KeccakState) (F : SepProp) : State → SepProp → Prop :=
  fun sm Pm =>
    TailRegsPreserved s sm ∧
    sm.spAligned = true ∧
    sm.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
    sm.readReg64 .x10 = rcBase + BitVec.ofNat 64 (8 * r) ∧
    sm.pstate = subsPState64 (BitVec.ofNat 64 (8 * r) + 8#64) 192#64 ∧
    Round2RegsA sm st0 st1 ∧
    (Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop2MidMem sp st0 st1 ∗ F)

/-- Live vector registers at `+0x07c8` (after Loop 2 Part B). -/
@[expose] def Round2RegsB (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 0#5 = laneShlTheta st0 st1 9 20 ∧
  s.readVReg128 2#5 = laneRhoPi st0 st1 2 ∧
  s.readVReg128 5#5 = laneTheta st0 st1 23 ∧
  s.readVReg128 6#5 = laneRhoPi st0 st1 21 ∧
  s.readVReg128 7#5 = laneShlTheta st0 st1 23 56 ∧
  s.readVReg128 8#5 = laneRhoPi st0 st1 16 ∧
  s.readVReg128 9#5 = laneRhoPi st0 st1 14 ∧
  s.readVReg128 10#5 = laneRhoPi st0 st1 24 ∧
  s.readVReg128 11#5 = laneRhoPi st0 st1 7 ∧
  s.readVReg128 12#5 = laneRhoPi st0 st1 18 ∧
  s.readVReg128 13#5 = laneShlTheta st0 st1 14 39 ∧
  s.readVReg128 14#5 = laneRhoPi st0 st1 4 ∧
  s.readVReg128 15#5 = laneRhoPi st0 st1 12 ∧
  s.readVReg128 17#5 = laneTheta st0 st1 9 ∧
  s.readVReg128 18#5 = laneRhoPi st0 st1 1 ∧
  s.readVReg128 19#5 = laneTheta st0 st1 4 ∧
  s.readVReg128 20#5 = laneRhoPi st0 st1 11 ∧
  s.readVReg128 21#5 = laneRhoPi st0 st1 3 ∧
  s.readVReg128 22#5 = laneTheta st0 st1 19 ∧
  s.readVReg128 23#5 = laneRhoPi st0 st1 8 ∧
  s.readVReg128 24#5 = laneRhoPi st0 st1 20 ∧
  s.readVReg128 25#5 = laneRhoPi st0 st1 9 ∧
  s.readVReg128 26#5 = laneRhoPi st0 st1 10 ∧
  s.readVReg128 27#5 = laneRhoPi st0 st1 17 ∧
  s.readVReg128 28#5 = laneTheta st0 st1 14 ∧
  s.readVReg128 29#5 = laneRhoPi st0 st1 5 ∧
  s.readVReg128 30#5 = laneRhoPi st0 st1 23 ∧
  s.readVReg128 31#5 = laneRhoPi st0 st1 0

@[expose] def Round2MidB (s : State) (sp rcBase : BitVec 64) (r : Nat)
    (st0 st1 : KeccakState) (F : SepProp) : State → SepProp → Prop :=
  fun sm Pm =>
    TailRegsPreserved s sm ∧
    sm.spAligned = true ∧
    sm.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
    sm.readReg64 .x10 = rcBase + BitVec.ofNat 64 (8 * r) ∧
    sm.pstate = subsPState64 (BitVec.ofNat 64 (8 * r) + 8#64) 192#64 ∧
    Round2RegsB sm st0 st1 ∧
    (Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop2MidMem sp st0 st1 ∗ F)

/-- Postcondition of `round2_step` after round `r < 24`. -/
@[expose] def Round2Post (s : State) (sp rcBase : BitVec 64) (r : Nat)
    (st0 st1 : KeccakState) (F : SepProp) : State → SepProp → Prop :=
  let st0' := keccakF1600Round st0 (keccakRcAt r)
  let st1' := keccakF1600Round st1 (keccakRcAt r)
  fun sf Q =>
    TailRegsPreserved s sf ∧
    sf.spAligned = true ∧
    sf.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
    Loop2Regs sf st0' st1' ∧
    (Q ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop2SpillMem sp st0' st1' ∗ F)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase

