/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Extra

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 4×4 `SampleNTT` Matrix `aTrans`

Proves `seg5_sample_matrix_safe_ok` (`SafeSepWP`, zero termination hypotheses) and
`seg5_sample_matrix_ok` (`SepWP` under `Shake128MatrixTerminates rho 4`) across
`+0x40f0 .. +0x76a8`, populating the 16 transposed `SampleNTT` polynomials `aTrans[0..3][0..3]`
at `[sp + 14432 .. sp + 22624)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes mlkemData10Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_zero_reloc_cancel fetch_rebase_ldst128Lo12_site mlkemMpl
  resolve_ro01 resolve_ro02 resolve_ro03 resolve_ro04 resolve_ro10)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk SepWP.roDataAt_intro cst16_0_vec cst16_1_vec cst16_2_vec cst16_8_vec
  mlkemData01Bytes_length mlkemData02Bytes_length mlkemData03Bytes_length mlkemData04Bytes_length
  mlkemData10Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128MatrixTerminates Shake128SeedTerminates sampleMatrixWith sampleNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  allLanesDone sampleNttRow_safeSepWP sampleNttRow_sepWP)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepStore128 polyVecNat step_stpQ128 step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (rhoW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (BTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMemFrom BTreeMemFrom_eq_bytes BTreeMem_entails_memRegion
  SepWP.of_memRegion_btreeMem btreeBytesFrom_length btreeBytesFrom_split
  sepLoad64_btreeMem sepStore128_btreeMem sepStore64_btreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowExtraState06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA (
  RowEntryGprs06 RowInitAPre06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init (seg5_init_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Extra (
  seg5_extra_bodyA_ok seg5_extra_bodyB_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi (
  EpiPreservedGprs06 RowPolyOut06 off4158 seg5_epi_ok)

@[simp, arm64_norm, wp_norm] abbrev off40f0 : BitVec 64 := 16624#64
@[simp, arm64_norm, wp_norm] private abbrev off412c : BitVec 64 := 16684#64
@[simp, arm64_norm, wp_norm] private abbrev off4130 : BitVec 64 := 16688#64
@[simp, arm64_norm, wp_norm] private abbrev off4138 : BitVec 64 := 16696#64
@[simp, arm64_norm, wp_norm] private abbrev off413c : BitVec 64 := 16700#64
@[simp, arm64_norm, wp_norm] private abbrev off4144 : BitVec 64 := 16708#64
@[simp, arm64_norm, wp_norm] private abbrev off414c : BitVec 64 := 16716#64
@[simp, arm64_norm, wp_norm] abbrev off4170 : BitVec 64 := 16752#64
@[simp, arm64_norm, wp_norm] abbrev off76a8 : BitVec 64 := 30376#64

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06
  [0x40f0 → 0x4128, 0x4130 → 0x4134, 0x413c → 0x4140, 0x4148 → 0x4148, 0x4150 → 0x416c]
gen_placed_odd_sites blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06
  [0x40f0 → 0x40f0, 0x4100 → 0x4100, 0x4130 → 0x4130, 0x413c → 0x413c]

@[simp, arm64_norm]
private theorem blkPC06_rebase_cst16_0_ldr [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + off412c) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.0")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 16684)
    (r := { off := 16684, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16684)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4171) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC06_rebase_cst16_1_ldr [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + off4138) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.1")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 16696)
    (r := { off := 16696, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16696)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4174) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC06_rebase_cst16_2_ldr [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + off4144) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.2")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 16708)
    (r := { off := 16708, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16708)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4177) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC06_rebase_cst16_8_ldr [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + off414c) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.8")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 16716)
    (r := { off := 16716, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.8" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 16716)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 4179) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local simp] resolve_ro01 resolve_ro02 resolve_ro03 resolve_ro04 resolve_ro10
attribute [local irreducible] blkPC06 sampleNtt polyVecNat

/-! ## 1. Transposed `SampleNTT` Matrix Predicates & `BTreeMem` Entry Assembly -/

@[expose] noncomputable def ATransMem06 (sp : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  RowPolyOut06 sp rho 0 ∗ RowPolyOut06 sp rho 1 ∗
  RowPolyOut06 sp rho 2 ∗ RowPolyOut06 sp rho 3

theorem sampleMatrixWith_false_getD_06 {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row col : Nat} (hr : row < 4) (hc : col < 4) :
    ((sampleMatrixWith sampleNtt 4 rho false).getD row #[]).getD col zeroPoly =
      sampleNtt (rowSeed rho row col) := by
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  simp [sampleMatrixWith, rowSeed, Array.getD, hr, hc, htake]

theorem shake128MatrixTerminates_row_06 {rho : List (BitVec 8)} (_hrho : rho.length = 32)
    (hTerm : Shake128MatrixTerminates rho 4) {row col : Nat} (hr : row < 4) (hc : col < 4) :
    Shake128SeedTerminates (rowSeed rho row col) :=
  hTerm row col hr hc

private theorem btreeMemFrom_split (ptr : BitVec 64) (start a b : Nat) (t : BTree (BitVec 64) 9) :
    BTreeMemFrom ptr start (a + b) t =
      BTreeMemFrom ptr start a t ∗
      BTreeMemFrom (ptr + BitVec.ofNat 64 (8 * a)) (start + a) b t := by
  rw [BTreeMemFrom_eq_bytes, BTreeMemFrom_eq_bytes, BTreeMemFrom_eq_bytes,
    btreeBytesFrom_split, pointsToBytes_append, btreeBytesFrom_length]

private theorem btreeMemFrom_shift_congr :
    ∀ (cnt s1 s2 : Nat) (ptr : BitVec 64) {t1 t2 : BTree (BitVec 64) 9},
      (∀ k, k < cnt → t1.get (s1 + k) = t2.get (s2 + k)) →
      BTreeMemFrom ptr s1 cnt t1 = BTreeMemFrom ptr s2 cnt t2
  | 0, _, _, _, _, _, _ => rfl
  | c + 1, s1, s2, ptr, t1, t2, h => by
      simp only [BTreeMemFrom]
      have h0 : t1.get s1 = t2.get s2 := by simpa using h 0 (Nat.zero_lt_succ c)
      rw [h0,
        btreeMemFrom_shift_congr c (s1 + 1) (s2 + 1) (ptr + 8#64) fun k hk => by
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) (Nat.succ_lt_succ hk)]

private theorem entry_btree_join_06 (sp : BitVec 64) (tLo tHi : BTree (BitVec 64) 9) :
    ∃ tInit : BTree (BitVec 64) 9,
      tInit.get 9 = sp + 30712#64 ∧
      (BTreeMem (sp + 144#64) 9 tLo ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
        BTreeMem (sp + 224#64) 276 tHi = BTreeMem (sp + 144#64) 286 tInit) := by
  let tInit : BTree (BitVec 64) 9 := BTree.ofFn 9 fun i =>
    if i < 9 then tLo.get i else if i = 9 then sp + 30712#64 else tHi.get (i - 10)
  have ht9 : tInit.get 9 = sp + 30712#64 := by simp [tInit, BTree.get_ofFn 9 _ 9 (by decide)]
  refine ⟨tInit, ht9, ?_⟩
  have hsplit1 : BTreeMem (sp + 144#64) 286 tInit =
      BTreeMemFrom (sp + 144#64) 0 9 tInit ∗ BTreeMemFrom (sp + 216#64) 9 277 tInit := by
    have h := btreeMemFrom_split (sp + 144#64) 0 9 277 tInit
    have ha : sp + 144#64 + BitVec.ofNat 64 (8 * 9) = sp + 216#64 := by bv_omega
    rw [ha] at h; exact h
  have hsplit2 : BTreeMemFrom (sp + 216#64) 9 277 tInit =
      ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗ BTreeMemFrom (sp + 224#64) 10 276 tInit := by
    have h := btreeMemFrom_split (sp + 216#64) 9 1 276 tInit
    have ha : sp + 216#64 + BitVec.ofNat 64 (8 * 1) = sp + 224#64 := by bv_omega
    rw [ha] at h
    have h1 : BTreeMemFrom (sp + 216#64) 9 1 tInit = ((sp + 216#64) ↦₆₄ (sp + 30712#64)) := by
      simp [BTreeMemFrom, ht9]
    rwa [h1] at h
  have hlo : BTreeMemFrom (sp + 144#64) 0 9 tInit = BTreeMem (sp + 144#64) 9 tLo :=
    btreeMemFrom_shift_congr 9 0 0 (sp + 144#64) fun k hk => by
      simp [tInit, BTree.get_ofFn 9 _ k (by omega), hk]
  have hhi : BTreeMemFrom (sp + 224#64) 10 276 tInit = BTreeMem (sp + 224#64) 276 tHi :=
    btreeMemFrom_shift_congr 276 10 0 (sp + 224#64) fun k hk => by
      simp [tInit, BTree.get_ofFn 9 _ (10 + k) (by omega), show ¬(10 + k < 9) by omega,
        show 10 + k ≠ 9 by omega]
  rw [hsplit1, hsplit2, hlo, hhi]

/-! ## 2. Entry Setup (`+0x40f0 → +0x4170`) & Row Loop-Back (`+0x4158 → +0x4170 / +0x76a8`) -/

private theorem seq_env_ro [MlKemPlacement] {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → MlKemRoOk mlkemMpl sm.mem →
      SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        (mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ MlKemRoOk mlkemMpl sm.mem) ∧
        (mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → MlKemRoOk mlkemMpl sm.mem →
          SepWP prog target sm Pm post))
      (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h
      (fun _ _ _ _ ⟨hc, hr⟩ hk => ⟨⟨hc, hr⟩, hk⟩))
    (fun _ _ _ _ ⟨⟨hc, hr⟩, hk⟩ => hk hc hr)

set_option maxHeartbeats 800000 in
private theorem seg5_entry_ok [MlKemPlacement] {sp fpVal : BitVec 64}
    (_hb : MlKemBase blkPl06 blkPl06.base) {rho : List (BitVec 8)}
    {tInit : BTree (BitVec 64) 9} {Rest : SepProp} {s : State}
    (hpc : s.pc = blkPl06.base + off40f0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = sp + 30459#64) (hx20 : s.readReg64 .x20 = sp + 28379#64)
    (hx22 : s.readReg64 .x22 = sp + 4160#64) (hx23 : s.readReg64 .x23 = sp + 24576#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 0)
    (hv1 : s.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2)
    (ht9 : tInit.get 9 = sp + 30712#64) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off4170) s
      (BTreeMem (sp + 144#64) 286 tInit ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        RowEntryGprs06 sp rcBase fpVal sf ∧ sf.readReg64 .x1 = 0#64 ∧
        ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk06 sp rho tA ∧
          (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗ Rest)) := by
  intro rcBase
  refine seq_env_ro (mid := blkPl06.base + BitVec.ofNat 64 16684) hcl hro ?_
  dsimp only [off40f0, off412c, off4138, off4144, off414c, off4170] at hpc ⊢
  wp_step; wp_step; wp_step
  refine SepWP.step_stp64 (wb := none) (ea := sp + 200#64) (ea2 := sp + 208#64)
    (v1 := sp + 28379#64) (v2 := sp + 30459#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp]) (by bv_omega) (by simp [hx20]) (by simp [hx9])
    (sepStore64_btreeMem (k := 7) (by decide) (by decide) (by bv_omega)).left
    (sepStore64_btreeMem (k := 8) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m1
  wp_steps 7
  refine step_stpQ128 (wb := none) (ea := sp + 304#64) (ea16 := sp + 320#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp]) (by bv_omega)
    (v1 := rhoW rho 1 ++ rhoW rho 1) (v2 := rhoW rho 0 ++ rhoW rho 0)
    (by simp; bv_bits) (by simp; bv_bits)
    (sepStore128_btreeMem (k := 20) (by decide) (by decide) (by bv_omega)).left
    (sepStore128_btreeMem (k := 22) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m2
  wp_steps 3
  refine step_stpQ128 (wb := none) (ea := sp + 272#64) (ea16 := sp + 288#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp]) (by bv_omega)
    (v1 := rhoW rho 3 ++ rhoW rho 3) (v2 := rhoW rho 2 ++ rhoW rho 2)
    (by simp; bv_bits) (by simp; bv_bits)
    (sepStore128_btreeMem (k := 16) (by decide) (by decide) (by bv_omega)).left
    (sepStore128_btreeMem (k := 18) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hcl1 hro1 => ?_
  refine seq_env_ro (mid := blkPl06.base + off4138) hcl1 hro1 ?_
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun])
    (by simp [wp_norm, arm64_norm, blkPC06_rebase_cst16_0_ldr]; exact ⟨rfl, rfl⟩) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0")
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    (by simpa using hro1.cst16_0) mlkemData02Bytes_length cst16_0_vec (by wp_norm_lhs) ?_
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 256#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp])
    (val := 0xffffffffffffffff#64 ++ 0xffffffffff0000ff#64) (by simp)
    (sepStore128_btreeMem (k := 14) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hcl2 hro2 => ?_
  refine seq_env_ro (mid := blkPl06.base + off4144) hcl2 hro2 ?_
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun])
    (by simp [wp_norm, arm64_norm, blkPC06_rebase_cst16_1_ldr]; exact ⟨rfl, rfl⟩) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.1")
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    (by simpa using hro2.cst16_1) mlkemData03Bytes_length cst16_1_vec (by wp_norm_lhs) ?_
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 176#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp])
    (val := 0#64 ++ 0x00000000001f0100#64) (by simp)
    (sepStore128_btreeMem (k := 4) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m5
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hcl3 hro3 => ?_
  refine seq_env_ro (mid := blkPl06.base + off414c) hcl3 hro3 ?_
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun])
    (by simp [wp_norm, arm64_norm, blkPC06_rebase_cst16_2_ldr]; exact ⟨rfl, rfl⟩) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.2")
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    (by simpa using hro3.cst16_2) mlkemData04Bytes_length cst16_2_vec (by wp_norm_lhs) ?_
  refine step_strQ128 (wb := none) (ea := sp + 160#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp])
    (val := 0#64 ++ 0x00000000001f0200#64) (by simp)
    (sepStore128_btreeMem (k := 2) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m6
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hcl4 hro4 => ?_
  refine seq_env_ro (mid := blkPl06.base + off4170) hcl4 hro4 ?_
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun])
    (by simp [wp_norm, arm64_norm, blkPC06_rebase_cst16_8_ldr]; exact ⟨rfl, rfl⟩) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.8")
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    (by simpa using hro4.cst16_8) mlkemData10Bytes_length cst16_8_vec (by wp_norm_lhs) ?_
  refine step_strQ128 (wb := none) (ea := sp + 144#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp])
    (val := 0#64 ++ 0x00000000001f0300#64) (by simp)
    (sepStore128_btreeMem (k := 0) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  intro m7
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hclF hroF => ?_
  refine SepWP.roDataAt_intro (by simpa using hroF.keccakRc)
    (by rw [mlkemData01Bytes_length]; decide) ?_
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), hsp16, hclF, hroF,
      ⟨by simp, by simp [hx20], by simp [hx22],
        by simp, by simp,
        by simp [hx25], by simp [hx26],
        by simp [rcBase], by simp [hfp]⟩,
      by simp, _, ?_, by sep_frame⟩
  simp [MemAHeaderOk06, BTree.get_set, ht9]

private theorem seg5_loopback_ok [MlKemPlacement] {sp rcBase fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} (hrow : row < 4)
    {tA : BTree (BitVec 64) 9} {Rest : SepProp} {s : State}
    (hpc : s.pc = blkPl06.base + off4158) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hg : EpiPreservedGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (if row == 3 then blkPl06.base + off76a8 else blkPl06.base + off4170) s
      (BTreeMem (sp + 144#64) 286 tA ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        RowEntryGprs06 sp rcBase fpVal sf ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
        (Pf ⊢ BTreeMem (sp + 144#64) 286 tA ∗ Rest)) := by
  rcases hg with ⟨hx1, hx19, hx22, hx23, hx26, hx28, hfp⟩
  have ht7 : tA.get 7 = sp + 28379#64 := hhdr.2.2.2.2.2.2.1
  wp_step
  refine SepWP.step_ldr64 (wb := none) (ea := sp + 200#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp16])
    (by simp [evalAddrMode, hsp])
    (sepLoad64_btreeMem (k := 7) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) ?_
  rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2 ∨ row = 3) with rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceAdd] at hx1 ⊢
    wp_steps 4
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        ⟨by simp [hx19], by simp [*], by simp [hx22], by simp [hx23],
          by simp, by simp [*], by simp [hx26],
          by simp [hx28], by simp [hfp]⟩,
        by simp [hx1], Entails.refl _⟩

/-! ## 3. Single-Row (`+0x4170 → +0x4170 / +0x76a8`) & 4-Row `SafeSepWP` / `SepWP` Composition -/

@[expose] def Seg5RowPost06 [MlKemPlacement] (b sp rcBase fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.pc = (if row == 3 then b + off76a8 else b + off4170) ∧
  sf.status = .Running ∧
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  RowEntryGprs06 sp rcBase fpVal sf ∧
  sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk06 sp rho tA ∧
    (Pf ⊢ RowPolyOut06 sp rho row ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗ memRegion (sp + 26320#64) 32 ∗
      memRegion (sp + 4160#64) 2176 ∗ memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 30448#64) 2016 ∗ Rest)

private theorem seg5_epi_and_loopback_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hrow : row < 4)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 7235)) (hrun : s.status = .Running)
    (hexit : Seg5Defs.RowExitState06 sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if row == 3 then b + off76a8 else b + off4170) s P
      (Seg5RowPost06 b sp rcBase fpVal rho row Rest) := by
  subst hbase
  refine SepWP.seq (seg5_epi_ok hb rfl hrow hpc hrun hexit) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hsp16, hcl1, hro1, hg1, tA, hhdr, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show _ ⊢ BTreeMem (sp + 144#64) 286 tA ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg5_loopback_ok hrow hpc1 hrun1 hsp1 hspA1 hsp16 hg1 hhdr) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hgF, hx1F, hPf⟩
  exact SepWP.done hpcf hrunf ⟨hpcf, hrunf, hspf, hspAf, hsp16, hclf, hrof, hgF, hx1F,
    tA, hhdr, Entails.trans hPf (by sep_frame)⟩

theorem seg5_row_safe_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4) {s : State} {P : SepProp}
    (hpc : s.pc = b + off4170) (hrun : s.status = .Running)
    (hpre : RowInitAPre06 sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SafeSepWP (blkPC06.rebase b (fun _ => none)) s P
      (Seg5RowPost06 b sp rcBase fpVal rho row Rest) := by
  have hpc' : s.pc = b + BitVec.ofNat 64 (4 * 4188) := by simpa [off4170] using hpc
  have hrowCore : SafeSepWP (blkPC06.rebase b (fun _ => none)) s P
      (fun sE PE => sE.pc = b + BitVec.ofNat 64 (4 * 7235) ∧ sE.status = .Running ∧
        Seg5Defs.RowExitState06 sp rcBase fpVal rho row
          (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) sE PE) := by
    refine sampleNttRow_safeSepWP
      (N := 4) (seeds := fun c => rowSeed rho row c)
      (loopHead := b + BitVec.ofNat 64 (4 * 6354))
      (midPC := Poly.SampleNttLoop.ChunkInstrs.pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4)
      (exitPC := b + BitVec.ofNat 64 (4 * 7235))
      (Inv := RowExtraState06 b sp rcBase fpVal rho row
        (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest))
      (Mid := Seg5Defs.RowMidState06 sp rcBase fpVal rho row
        (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest))
      (by dsimp only [Poly.SampleNttLoop.ChunkInstrs.pcAt]; bv_omega)
      (fun _ _ _ hInv => hInv.1)
      ((seg5_init_ok hb hbase hrho hrow hpc' hrun hpre).mono fun sf Pf hpcf hrunf hpost => by
        by_cases hd : allLanesDone 4 (fun c => rowSeed rho row c) 0 = true
        · simp only [hd, ↓reduceIte] at hpcf hpost ⊢; exact ⟨hpcf, hrunf, hpost⟩
        · simp only [hd] at hpost ⊢; exact hpost)
      (fun _ _ _ hInv => seg5_extra_bodyA_ok hb hrho hInv)
      (fun extra sm Pm hmpc hmrun hMid =>
        (seg5_extra_bodyB_ok hb hmpc hmrun hMid).mono fun sf Pf hpcf hrunf hpost => by
          by_cases hd : allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1) = true
          · simp only [hd, ↓reduceIte] at hpcf hpost ⊢; exact ⟨hpcf, hrunf, hpost⟩
          · simp only [hd] at hpost ⊢; exact hpost)
  exact SafeSepWP.bind hrowCore fun sE PE ⟨hpcE, hrunE, hexE⟩ =>
    SafeSepWP.of_total (seg5_epi_and_loopback_ok hb hbase hrow hpcE hrunE hexE)

theorem seg5_row_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4)
    (hTerm : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho row c))
    {s : State} {P : SepProp}
    (hpc : s.pc = b + off4170) (hrun : s.status = .Running)
    (hpre : RowInitAPre06 sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if row == 3 then b + off76a8 else b + off4170) s P
      (Seg5RowPost06 b sp rcBase fpVal rho row Rest) := by
  have hpc' : s.pc = b + BitVec.ofNat 64 (4 * 4188) := by simpa [off4170] using hpc
  have hrowCore : SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 7235)) s P
      (Seg5Defs.RowExitState06 sp rcBase fpVal rho row
        (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest)) :=
    sampleNttRow_sepWP
      (N := 4) (seeds := fun c => rowSeed rho row c)
      (loopHead := b + BitVec.ofNat 64 (4 * 6354))
      (midPC := Poly.SampleNttLoop.ChunkInstrs.pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4)
      (exitPC := b + BitVec.ofNat 64 (4 * 7235))
      (Inv := RowExtraState06 b sp rcBase fpVal rho row
        (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest))
      (Mid := Seg5Defs.RowMidState06 sp rcBase fpVal rho row
        (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest))
      hTerm (seg5_init_ok hb hbase hrho hrow hpc' hrun hpre)
      (fun _ _ _ hInv => seg5_extra_bodyA_ok hb hrho hInv)
      (fun extra sm Pm hmpc hmrun hMid => seg5_extra_bodyB_ok hb hmpc hmrun hMid)
  exact SepWP.seq hrowCore fun sE PE hpcE hrunE hexE =>
    seg5_epi_and_loopback_ok hb hbase hrow hpcE hrunE hexE

@[expose] def Seg5MatrixPost06 [MlKemPlacement] (b sp fpVal : BitVec 64)
    (rho : List (BitVec 8)) (Rest : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.pc = b + off76a8 ∧ sf.status = .Running ∧
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  sf.readReg64 .x20 = sp + 28379#64 ∧ sf.readReg64 .x22 = sp + 4160#64 ∧
  sf.readReg64 .x23 = sp + 26320#64 ∧ sf.readReg64 .x25 = sp + 28368#64 ∧
  sf.readReg64 .x26 = sp + 28632#64 ∧ sf.readReg64 .fp = fpVal ∧
  (Pf ⊢ ATransMem06 sp rho ∗ memRegion (sp + 144#64) 2288 ∗
    memRegion (sp + 4160#64) 2176 ∗ memRegion (sp + 26320#64) 32 ∗
    memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)

private theorem sepWP_drop_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {A Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s Q post oom) :
    SepWP prog target_pc s (A ∗ Q) post oom := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm))

private theorem seg5_regions_8192_06 (sp : BitVec 64) :
    memRegion (sp + 14432#64) 8192 =
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 0)) 2048 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 1)) 2048 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 := by
  rw [show sp + 14432#64 + BitVec.ofNat 64 (2048 * 0) = sp + 14432#64 from by bv_omega,
    memRegion_split' (b := sp + 14432#64) (b' := sp + 14432#64 + BitVec.ofNat 64 (2048 * 1))
      (n := 2048) (k := (6144 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 14432#64 + BitVec.ofNat 64 (2048 * 1))
      (b' := sp + 14432#64 + BitVec.ofNat 64 (2048 * 2))
      (n := 2048) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 14432#64 + BitVec.ofNat 64 (2048 * 2))
      (b' := sp + 14432#64 + BitVec.ofNat 64 (2048 * 3))
      (n := 2048) (k := (2048 : Nat)) rfl (by bv_omega) (by decide)]

private theorem seg5_exit_finish_06 [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    {rho : List (BitVec 8)} {Rest : SepProp} {sm : State} {Pm : SepProp}
    (hpost3 : Seg5RowPost06 b sp rcBase fpVal rho 3
      (RowPolyOut06 sp rho 0 ∗ RowPolyOut06 sp rho 1 ∗ RowPolyOut06 sp rho 2 ∗ Rest) sm Pm) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off76a8) sm Pm
      (Seg5MatrixPost06 b sp fpVal rho Rest) := by
  rcases hpost3 with ⟨hpc, hrun, hsp, hspA, h16, hcl, hro, hg, _, tA, _, hPm⟩
  have hbt : BTreeMem (sp + 144#64) 286 tA ⊢ memRegion (sp + 144#64) 2288 := by
    simpa using BTreeMem_entails_memRegion (sp + 144#64) 286 tA
  have hEnt : Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      (ATransMem06 sp rho ∗ memRegion (sp + 144#64) 2288 ∗
        memRegion (sp + 4160#64) 2176 ∗ memRegion (sp + 26320#64) 32 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest) := by
    unfold ATransMem06
    refine Entails.trans hPm ?_
    refine Entails.trans (Q := BTreeMem (sp + 144#64) 286 tA ∗
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗ RowPolyOut06 sp rho 0 ∗ RowPolyOut06 sp rho 1 ∗
          RowPolyOut06 sp rho 2 ∗ RowPolyOut06 sp rho 3 ∗ memRegion (sp + 4160#64) 2176 ∗
          memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 28368#64) 672 ∗
          memRegion (sp + 30448#64) 2016 ∗ Rest)) (by sep_frame) ?_
    exact Entails.trans (sepConj_mono_left hbt) (by sep_frame)
  rcases hg with ⟨_, hx20, hx22, hx23, _, hx25, hx26, _, hfp⟩
  have hpc' : sm.pc = b + off76a8 := by simpa using hpc
  exact SepWP.weaken_pre hEnt (sepWP_drop_left (SepWP.done hpc' hrun
    ⟨hpc', hrun, hsp, hspA, h16, hcl, hro, hx20, hx22, hx23, hx25, hx26, hfp, Entails.refl _⟩))

private theorem seg5_row_reframe_06 [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} {Rin Rout : SepProp} {sm : State} {Pm : SepProp}
    (hrow : row < 3)
    (hR : Rin ⊢ memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * (row + 1))) 2048 ∗ Rout)
    (hp : Seg5RowPost06 b sp rcBase fpVal rho row Rin sm Pm) :
    sm.pc = b + off4170 ∧ sm.status = .Running ∧
      RowInitAPre06 sp rcBase fpVal rho (row + 1)
        (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * (row + 1))) 2048 ∗
          (RowPolyOut06 sp rho row ∗ Rout)) sm Pm := by
  rcases hp with ⟨hpc, hrun, hsp, hspA, h16, hcl, hro, hg, hx1, tA, hhdr, hPm⟩
  have hne3 : (row == 3) = false := by
    rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2) with rfl | rfl | rfl <;> decide
  rw [hne3] at hpc
  refine ⟨by simpa using hpc, hrun, hsp, hspA, h16, hcl, hro, hg, hx1, tA, hhdr, ?_⟩
  exact Entails.trans hPm (entails_sub hR (by sep_frame) (by sep_frame))

private theorem seg5_entry_prep_06 [MlKemPlacement] {b sp fpVal : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {Rest : SepProp} {s : State}
    (hpc : s.pc = b + off40f0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = sp + 30459#64) (hx20 : s.readReg64 .x20 = sp + 28379#64)
    (hx22 : s.readReg64 .x22 = sp + 4160#64) (hx23 : s.readReg64 .x23 = sp + 24576#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 0)
    (hv1 : s.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    let RAll := memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 0)) 2048 ∗
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 1)) 2048 ∗
        memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
        memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off4170) s
      (memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 14432#64) 8192 ∗ memRegion (sp + 26320#64) 32 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)
      (fun sf Pf => sf.pc = b + off4170 ∧ sf.status = .Running ∧
        RowInitAPre06 sp rcBase fpVal rho 0 RAll sf Pf) := by
  intro rcBase RAll
  subst hbase
  rw [seg5_regions_8192_06 sp]
  refine SepWP.weaken_pre (P' := memRegion (sp + 144#64) 72 ∗
    (memRegion (sp + 224#64) 2208 ∗ (((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
      (memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ RAll))))
    (by dsimp only [RAll]; sep_frame) ?_
  refine SepWP.of_memRegion_btreeMem 9 (sp + 144#64) (by decide) (by decide) rfl fun tLo => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 224#64) 2208 ∗
    (BTreeMem (sp + 144#64) 9 tLo ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
      (memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ RAll)))
    (by sep_frame) ?_
  refine SepWP.of_memRegion_btreeMem 276 (sp + 224#64) (by decide) (by decide) rfl fun tHi => ?_
  rcases entry_btree_join_06 sp tLo tHi with ⟨tInit, ht9, hjoin⟩
  refine SepWP.weaken_pre (P' := BTreeMem (sp + 144#64) 286 tInit ∗
    (memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 4160#64) 2176 ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ RAll))
    (by rw [← hjoin]; sep_frame) ?_
  refine (seg5_entry_ok _hb hpc hrun hsp hspA hsp16 hcl hro hx9 hx20 hx22 hx23 hx25 hx26 hfp
    hv0 hv1 ht9).mono fun sf Pf hpcf hrunf ⟨hspf, hspAf, h16f, hclf, hrof, hgf, hx1f, tA, hhdr, hPf⟩ =>
    ⟨hpcf, hrunf, hspf, hspAf, h16f, hclf, hrof, hgf, hx1f, tA, hhdr,
      Entails.trans hPf (by sep_frame)⟩

theorem seg5_sample_matrix_safe_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {Rest : SepProp} (hrho : rho.length = 32) {s : State}
    (hpc : s.pc = b + off40f0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = sp + 30459#64) (hx20 : s.readReg64 .x20 = sp + 28379#64)
    (hx22 : s.readReg64 .x22 = sp + 4160#64) (hx23 : s.readReg64 .x23 = sp + 24576#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 0)
    (hv1 : s.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2) :
    SafeSepWP (blkPC06.rebase b (fun _ => none)) s
      (memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 14432#64) 8192 ∗ memRegion (sp + 26320#64) 32 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)
      (Seg5MatrixPost06 b sp fpVal rho Rest) := by
  refine SafeSepWP.bind (SafeSepWP.of_total
    (seg5_entry_prep_06 hb hbase hpc hrun hsp hspA hsp16 hcl hro hx9 hx20 hx22 hx23 hx25 hx26 hfp hv0 hv1)) ?_
  rintro s0 P0 ⟨hpc0, hrun0, hpre0⟩
  refine SafeSepWP.bind (seg5_row_safe_ok hb hbase hrho (row := 0) (by decide) hpc0 hrun0 hpre0) ?_
  rintro sm0 Pm0 hp0
  rcases seg5_row_reframe_06 (row := 0) (Rout := memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
    (by decide) (by sep_frame) hp0 with ⟨hpc1, hrun1, hpre1⟩
  refine SafeSepWP.bind (seg5_row_safe_ok hb hbase hrho (row := 1) (by decide) hpc1 hrun1 hpre1) ?_
  rintro sm1 Pm1 hp1
  rcases seg5_row_reframe_06 (row := 1) (Rout := RowPolyOut06 sp rho 0 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
    (by decide) (by sep_frame) hp1 with ⟨hpc2, hrun2, hpre2⟩
  refine SafeSepWP.bind (seg5_row_safe_ok hb hbase hrho (row := 2) (by decide) hpc2 hrun2 hpre2) ?_
  rintro sm2 Pm2 hp2
  rcases seg5_row_reframe_06 (row := 2) (Rout := RowPolyOut06 sp rho 0 ∗ RowPolyOut06 sp rho 1 ∗ Rest)
    (by decide) (by sep_frame) hp2 with ⟨hpc3, hrun3, hpre3⟩
  refine SafeSepWP.bind (seg5_row_safe_ok hb hbase hrho (row := 3) (by decide) hpc3 hrun3 hpre3) ?_
  rintro sm3 Pm3 hp3
  rcases hp3 with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, tA, hhdr, hP⟩
  exact SafeSepWP.of_total (seg5_exit_finish_06
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, tA, hhdr, Entails.trans hP (by sep_frame)⟩)

theorem seg5_sample_matrix_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {Rest : SepProp}
    (hrho : rho.length = 32) (hTerm : Shake128MatrixTerminates rho 4) {s : State}
    (hpc : s.pc = b + off40f0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp16 : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = sp + 30459#64) (hx20 : s.readReg64 .x20 = sp + 28379#64)
    (hx22 : s.readReg64 .x22 = sp + 4160#64) (hx23 : s.readReg64 .x23 = sp + 24576#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 0)
    (hv1 : s.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off76a8) s
      (memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 14432#64) 8192 ∗ memRegion (sp + 26320#64) 32 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)
      (Seg5MatrixPost06 b sp fpVal rho Rest) := by
  have hT (row : Nat) (hr : row < 4) : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho row c) :=
    fun c hc => shake128MatrixTerminates_row_06 hrho hTerm hr hc
  refine SepWP.seq
    (seg5_entry_prep_06 hb hbase hpc hrun hsp hspA hsp16 hcl hro hx9 hx20 hx22 hx23 hx25 hx26 hfp hv0 hv1) ?_
  rintro s0 P0 _ _ ⟨hpc0, hrun0, hpre0⟩
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 0) (by decide) (hT 0 (by decide)) hpc0 hrun0 hpre0) ?_
  rintro sm0 Pm0 _ _ hp0
  rcases seg5_row_reframe_06 (row := 0) (Rout := memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
    (by decide) (by sep_frame) hp0 with ⟨hpc1, hrun1, hpre1⟩
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 1) (by decide) (hT 1 (by decide)) hpc1 hrun1 hpre1) ?_
  rintro sm1 Pm1 _ _ hp1
  rcases seg5_row_reframe_06 (row := 1) (Rout := RowPolyOut06 sp rho 0 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
    (by decide) (by sep_frame) hp1 with ⟨hpc2, hrun2, hpre2⟩
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 2) (by decide) (hT 2 (by decide)) hpc2 hrun2 hpre2) ?_
  rintro sm2 Pm2 _ _ hp2
  rcases seg5_row_reframe_06 (row := 2) (Rout := RowPolyOut06 sp rho 0 ∗ RowPolyOut06 sp rho 1 ∗ Rest)
    (by decide) (by sep_frame) hp2 with ⟨hpc3, hrun3, hpre3⟩
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 3) (by decide) (hT 3 (by decide)) hpc3 hrun3 hpre3) ?_
  rintro sm3 Pm3 _ _ hp3
  rcases hp3 with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, tA, hhdr, hP⟩
  exact seg5_exit_finish_06
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, tA, hhdr, Entails.trans hP (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix
