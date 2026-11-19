/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
meta import ProofLib.GenPlacedOddSites
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Extra
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Epi

/-!
# `kyber_encapsulate` (`B07`) — Segment 2: 4-Row `SampleNTT` Matrix `Âᵀ` (`+0x0758 .. +0x3d0c`)

Composes the `+0x0758 → +0x07d8` header initialization, 4 iterations of `Seg2Init` + `Seg2Extra` +
`Seg2Epi` + `+0x07c0 → +0x07d8 / +0x3d0c` loop header into `seg2_safeSepWP` (unconditional) and
`seg2_sepWP` (under `Kyber1024EncapsTerminates pk`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes
  mlkemData04Bytes mlkemData10Bytes mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemBlockPlacement_ρ mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk SepWP.roDataAt_intro cst16Vec cst16_0_vec cst16_1_vec cst16_2_vec cst16_8_vec
  mlkemData01Bytes_length mlkemData02Bytes_length mlkemData03Bytes_length mlkemData04Bytes_length
  mlkemData10Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024EncapsTerminates Poly Poly16 Shake128MatrixTerminates Shake128SeedTerminates
  sampleMatrixWith sampleNtt sha3_256List sha3_512List zeroPoly
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  allLanesDone sampleNttRow_safeSepWP sampleNttRow_sepWP
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldrQ128 step_stpQ128 step_strQ128
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07 blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (SpilledMsgWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho pkRho_len rhoW tHatModPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b (
  Seg1bPost Seg1bSpatial
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (BTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMemFrom BTreeMemFrom_eq_bytes BTreeMem_entails_memRegion
  SepWP.of_memRegion_btreeMem btreeBytesFrom_length btreeBytesFrom_split
  pointsToBytes_eq_btreeMem sepLoad64_btreeMem sepStore128_btreeMem sepStore64_btreeMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  MemAHeaderOk RowExitState RowExtraState RowMidState rcSym
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (
  RowEntryGprs RowInitAPre
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Init (seg2_init_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Extra (
  seg2_extra_bodyA_ok seg2_extra_bodyB_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Epi (
  EpiPreservedGprs RowPolyOut off07c0 seg2_epi_ok
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x0758 → 0x07d4]
gen_placed_odd_sites blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07
  [0x0758 → 0x0758, 0x0760 → 0x0760, 0x0794 → 0x0794, 0x07a4 → 0x07a4]

@[simp, arm64_norm]
private theorem blkPC07_rebase_ldst128_cst16_0 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC07.rebase b X).fetch (b + BitVec.ofNat 64 1936) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl07.ρ "libcrux_ml_kem:.rodata.cst16.0")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib07) (prog := blkPC07) (pl := blkPl07) (b := b) (X := X) (off := 1936)
    (r := { off := 1936, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" })
    rfl blkPlaceable07 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 1936)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 484) blk07_code_eq blk07_tree_size rfl)
    rfl rfl rfl rfl (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC07_rebase_ldst128_cst16_1 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC07.rebase b X).fetch (b + BitVec.ofNat 64 1952) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl07.ρ "libcrux_ml_kem:.rodata.cst16.1")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib07) (prog := blkPC07) (pl := blkPl07) (b := b) (X := X) (off := 1952)
    (r := { off := 1952, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" })
    rfl blkPlaceable07 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 1952)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 488) blk07_code_eq blk07_tree_size rfl)
    rfl rfl rfl rfl (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC07_rebase_ldst128_cst16_2 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC07.rebase b X).fetch (b + BitVec.ofNat 64 1964) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl07.ρ "libcrux_ml_kem:.rodata.cst16.2")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib07) (prog := blkPC07) (pl := blkPl07) (b := b) (X := X) (off := 1964)
    (r := { off := 1964, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" })
    rfl blkPlaceable07 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 1964)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 491) blk07_code_eq blk07_tree_size rfl)
    rfl rfl rfl rfl (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC07_rebase_ldst128_cst16_8 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC07.rebase b X).fetch (b + BitVec.ofNat 64 1972) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl07.ρ "libcrux_ml_kem:.rodata.cst16.8")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib07) (prog := blkPC07) (pl := blkPl07) (b := b) (X := X) (off := 1972)
    (r := { off := 1972, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.8" })
    rfl blkPlaceable07 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 1972)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 493) blk07_code_eq blk07_tree_size rfl)
    rfl rfl rfl rfl (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end
@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

/-! ## 1. Transposed `SampleNTT` Matrix Predicates (`ATransRowMem`, `ATransMem`) & `BTreeMem` Join -/

@[expose] noncomputable def aTransPoly (rho : List (BitVec 8)) (row col : Nat) : Poly :=
  sampleNtt (rowSeed rho row col)

@[expose] noncomputable def aTransPoly16 (rho : List (BitVec 8)) (row col : Nat) : Poly16 :=
  (aTransPoly rho row col).map (BitVec.ofNat 16)

theorem sampleMatrixWith_false_getD {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row col : Nat} (hr : row < 4) (hc : col < 4) :
    ((sampleMatrixWith sampleNtt 4 rho false).getD row #[]).getD col zeroPoly =
      aTransPoly rho row col := by
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  simp [sampleMatrixWith, aTransPoly, rowSeed, Array.getD, hr, hc, htake]

private theorem shake128MatrixTerminates_row {rho : List (BitVec 8)}
    (hTerm : Shake128MatrixTerminates rho 4) {row col : Nat} (hr : row < 4) (hc : col < 4) :
    Shake128SeedTerminates (rowSeed rho row col) :=
  hTerm row col hr hc

@[expose] noncomputable def ATransRowMem (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) : SepProp :=
  PolyMem (sp + 12832#64 + BitVec.ofNat 64 (2048 * row)) (polyVecNat (aTransPoly16 rho row 0)) ∗
  PolyMem (sp + 12832#64 + BitVec.ofNat 64 (2048 * row + 512)) (polyVecNat (aTransPoly16 rho row 1)) ∗
  PolyMem (sp + 12832#64 + BitVec.ofNat 64 (2048 * row + 1024)) (polyVecNat (aTransPoly16 rho row 2)) ∗
  PolyMem (sp + 12832#64 + BitVec.ofNat 64 (2048 * row + 1536)) (polyVecNat (aTransPoly16 rho row 3))

private theorem rowPolyOut_eq_aTransRowMem (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) :
    RowPolyOut sp rho row = ATransRowMem sp rho row := rfl

@[expose] noncomputable def ATransMem (sp : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  ATransRowMem sp rho 0 ∗ ATransRowMem sp rho 1 ∗ ATransRowMem sp rho 2 ∗ ATransRowMem sp rho 3

attribute [local simp, local arm64_norm, local wp_norm] off07c0
attribute [local irreducible] blkPC07 SpilledMsgWords sha3_256List sha3_512List sampleNtt polyVecNat
set_option maxRecDepth 100000

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

private theorem btreeMem286_of_parts (sp v9 : BitVec 64) (tLo tHi : BTree (BitVec 64) 9) :
    ∃ t0 : BTree (BitVec 64) 9, t0.get 9 = v9 ∧
      BTreeMem (sp + 144#64) 9 tLo ∗ ((sp + 216#64) ↦₆₄ v9) ∗ BTreeMem (sp + 224#64) 276 tHi =
        BTreeMem (sp + 144#64) 286 t0 := by
  let t0 : BTree (BitVec 64) 9 :=
    BTree.ofFn 9 (fun i => if i < 9 then tLo.get i else if i = 9 then v9 else tHi.get (i - 10))
  have ht9 : t0.get 9 = v9 := by simp [t0, BTree.get_ofFn 9 _ 9 (by decide)]
  refine ⟨t0, ht9, ?_⟩
  have hsplit1 : BTreeMem (sp + 144#64) 286 t0 =
      BTreeMemFrom (sp + 144#64) 0 9 t0 ∗ BTreeMemFrom (sp + 216#64) 9 277 t0 := by
    have h := btreeMemFrom_split (sp + 144#64) 0 9 277 t0
    have ha : sp + 144#64 + BitVec.ofNat 64 (8 * 9) = sp + 216#64 := by bv_omega
    simpa [BTreeMem, ha] using h
  have hsplit2 : BTreeMemFrom (sp + 216#64) 9 277 t0 =
      ((sp + 216#64) ↦₆₄ v9) ∗ BTreeMemFrom (sp + 224#64) 10 276 t0 := by
    change ((sp + 216#64) ↦₆₄ t0.get 9) ∗ BTreeMemFrom (sp + 216#64 + 8#64) 10 276 t0 = _
    rw [ht9, show sp + 216#64 + 8#64 = sp + 224#64 by bv_omega]
  have hlo : BTreeMemFrom (sp + 144#64) 0 9 t0 = BTreeMem (sp + 144#64) 9 tLo :=
    btreeMemFrom_shift_congr 9 0 0 (sp + 144#64) fun k hk => by
      simp [t0, BTree.get_ofFn 9 _ k (by omega), hk]
  have hhi : BTreeMemFrom (sp + 224#64) 10 276 t0 = BTreeMem (sp + 224#64) 276 tHi :=
    btreeMemFrom_shift_congr 276 10 0 (sp + 224#64) fun k hk => by
      simp [t0, BTree.get_ofFn 9 _ (10 + k) (by omega), show ¬(10 + k < 9) by omega,
        show 10 + k ≠ 9 by omega]
  rw [hsplit1, hsplit2, hlo, hhi]

attribute [local irreducible] BTreeMem BTreeMemFrom
  mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes mlkemData10Bytes

/-! ## 2. Entry Header Initialization (`+0x0758 → +0x07d8`) & Loop Header (`+0x07c0`) -/

private theorem sepWP_drop_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {A Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s Q post oom) :
    SepWP prog target_pc s (A ∗ Q) post oom := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm))

private theorem with_frozen_env [MlKemPlacement] {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog target s P (fun sf Pf =>
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem → MlKemRoOk mlkemMpl sf.mem → post sf Pf)) :
    SepWP prog target s P post :=
  SepWP.mono_frozen (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
    ⟨hcl, hro⟩ h (fun _ _ _ _ ⟨hc, hr⟩ hp => hp hc hr)

private theorem sepLoad128_ro {roAddr : BitVec 64} {bs : List (BitVec 8)} {v : BitVec 128}
    (hlen : bs.length = 16) (hv : cst16Vec bs = v) (F : SepProp) :
    SepLoad128 roAddr ((roAddr ↦ᵣ bs) ∗ F) v := by
  subst hv; unfold cst16Vec
  refine ⟨?_, ?_⟩
  · have he : (ByteSlice.readLE bs 8 8 ++ ByteSlice.readLE bs 0 8).extractLsb' 0 64 =
        ByteSlice.readLE bs 0 8 := by bv_bits
    rw [he, ← ByteSlice.pack64_eq_readLE_8]
    exact SepLoad64.of_pointsToBytesRO (off := 0) rfl (by omega) (by simp)
  · have he : (ByteSlice.readLE bs 8 8 ++ ByteSlice.readLE bs 0 8).extractLsb' 64 64 =
        ByteSlice.readLE bs 8 8 := by bv_bits
    rw [he, ← ByteSlice.pack64_eq_readLE_8]
    exact SepLoad64.of_pointsToBytesRO (off := 8) rfl (by omega) rfl

private theorem step_str64_btree {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {ptr : BitVec 64} {k : Nat} {val : BitVec 64}
    {t : BTree (BitVec 64) 9} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hk : k < 286) (hea : ptr + BitVec.ofNat 64 (8 * k) = ea)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (BTreeMem ptr 286 (t.set k val) ∗ Rest) post oom) :
    SepWP prog target_pc s (BTreeMem ptr 286 t ∗ Rest) post oom := by
  have hs : SepStore64 ea val (BTreeMem ptr 286 t ∗ Rest)
      (BTreeMem ptr 286 (t.set k val) ∗ Rest) :=
    (sepStore64_btreeMem hk (by decide) hea).left
  exact SepWP.step_str64 hpc hrun hfetch hsp haddr hval hs hexec hnext

private theorem step_ldr64_btree {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {ptr : BitVec 64} {k : Nat}
    {t : BTree (BitVec 64) 9} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hk : k < 286) (hea : ptr + BitVec.ofNat 64 (8 * k) = ea)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .X64 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hexec : ((applyWriteback s wb).writeReg64 rt (t.get k)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (BTreeMem ptr 286 t ∗ Rest) post oom) :
    SepWP prog target_pc s (BTreeMem ptr 286 t ∗ Rest) post oom := by
  have hl : SepLoad64 ea (BTreeMem ptr 286 t ∗ Rest) (t.get k) :=
    (sepLoad64_btreeMem hk (by decide) hea).left
  exact SepWP.step_ldr64 hpc hrun hfetch hsp haddr hl hexec hnext

private theorem seg2_entry_ok [MlKemPlacement] {b sp : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {t0 : BTree (BitVec 64) 9} {Rest : SepProp}
    (ht9 : t0.get 9 = sp + 29112#64)
    {s : State} (hpc : s.pc = b + 0x0758#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (_hspA : s.spAligned = true) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = sp + 28859#64)
    (hx19 : s.readReg64 .x19 = sp + 2560#64)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hx23 : s.readReg64 .x23 = sp + 26779#64)
    (hx24 : s.readReg64 .x24 = sp + 27032#64)
    (hfp : s.readReg64 .fp = sp + 33008#64)
    (hv0 : s.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 1)
    (hv1 : s.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2)
    (hv2 : s.readVReg128 2#5 = rhoW rho 0 ++ rhoW rho 0) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 2008) s
      ((mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 t0 ∗
        memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest)
      (fun sf Pf => RowInitAPre sp (mlkemMpl.ρ rcSym) rho 0 Rest sf Pf) := by
  subst hbase
  refine with_frozen_env hcl hro ?_
  refine SepWP.roDataAt_intro hro.cst16_0 (by rw [mlkemData02Bytes_length]; decide) ?_
  refine SepWP.roDataAt_intro hro.cst16_1 (by rw [mlkemData03Bytes_length]; decide) ?_
  refine SepWP.roDataAt_intro hro.cst16_2 (by rw [mlkemData04Bytes_length]; decide) ?_
  refine SepWP.roDataAt_intro hro.cst16_8 (by rw [mlkemData10Bytes_length]; decide) ?_
  let RoCsts : SepProp :=
    (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0" ↦ᵣ mlkemData02Bytes) ∗
    (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.1" ↦ᵣ mlkemData03Bytes) ∗
    (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.2" ↦ᵣ mlkemData04Bytes) ∗
    (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.8" ↦ᵣ mlkemData10Bytes)
  let R0 : SepProp := (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗
    memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
    memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest
  refine SepWP.weaken_pre (P' := BTreeMem (sp + 144#64) 286 t0 ∗
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0" ↦ᵣ mlkemData02Bytes) ∗
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.1" ↦ᵣ mlkemData03Bytes) ∗
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.2" ↦ᵣ mlkemData04Bytes) ∗
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.8" ↦ᵣ mlkemData10Bytes) ∗ R0)
    (by dsimp only [R0]; sep_frame) ?_
  wp_steps 1
  refine step_str64_btree (ea := sp + 208#64) (wb := none) (val := sp + 28859#64) (k := 8) (by decide) (by bv_omega)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp [hx9]) (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  wp_step; wp_step
  refine step_stpQ128 (ea := sp + 304#64) (wb := none)
    (v1 := rhoW rho 1 ++ rhoW rho 1) (v2 := rhoW rho 0 ++ rhoW rho 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by simp [hv0]) (by simp [hv2])
    (sepStore128_btreeMem (k := 20) (by decide) (by decide) (by bv_omega)).left
    (sepStore128_btreeMem (k := 22) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  wp_steps 9
  refine step_stpQ128 (ea := sp + 272#64) (wb := none)
    (v1 := rhoW rho 3 ++ rhoW rho 3) (v2 := rhoW rho 2 ++ rhoW rho 2)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl
    (by simp) (by simp)
    (sepStore128_btreeMem (k := 16) (by decide) (by decide) (by bv_omega)).left
    (sepStore128_btreeMem (k := 18) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  refine step_ldrQ128 (ea := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0") (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, Arm64.Obj.pageOf_add_lo12Of])
    (sepLoad128_ro mlkemData02Bytes_length cst16_0_vec _).right (by wp_norm_lhs) ?_
  wp_steps 1
  refine step_str64_btree (ea := sp + 200#64) (wb := none) (val := sp + 26779#64) (k := 7) (by decide) (by bv_omega)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp [hx23]) (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  refine step_strQ128 (ea := sp + 256#64) (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (val := 0xffffffffffffffff#64 ++ 0xffffffffff0000ff#64) rfl
    (sepStore128_btreeMem (k := 14) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  refine step_ldrQ128 (ea := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.1") (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, Arm64.Obj.pageOf_add_lo12Of])
    (sepLoad128_ro mlkemData03Bytes_length cst16_1_vec _).right.right (by wp_norm_lhs) ?_
  wp_steps 1
  refine step_strQ128 (ea := sp + 176#64) (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (val := 0#64 ++ 0x00000000001f0100#64) rfl
    (sepStore128_btreeMem (k := 4) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  refine step_ldrQ128 (ea := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.2") (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, Arm64.Obj.pageOf_add_lo12Of])
    (sepLoad128_ro mlkemData04Bytes_length cst16_2_vec _).right.right.right (by wp_norm_lhs) ?_
  refine step_strQ128 (ea := sp + 160#64) (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (val := 0#64 ++ 0x00000000001f0200#64) rfl
    (sepStore128_btreeMem (k := 2) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  refine step_ldrQ128 (ea := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.8") (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, Arm64.Obj.pageOf_add_lo12Of])
    ((sepLoad128_ro mlkemData10Bytes_length cst16_8_vec R0).right.right.right.right) (by wp_norm_lhs) ?_
  refine step_strQ128 (ea := sp + 144#64) (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (val := 0#64 ++ 0x00000000001f0300#64) rfl
    (sepStore128_btreeMem (k := 0) (by decide) (by decide) (by bv_omega)).left
    (by wp_norm_lhs) fun _ => ?_
  try rw [setPC_setMem_collapse]
  wp_steps 1
  refine SepWP.weaken_pre (P' := RoCsts ∗ (BTreeMem (sp + 144#64) 286 _ ∗ R0))
    (by dsimp only [RoCsts]; sep_frame) (sepWP_drop_left ?_)
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hclF hroF => ?_
  refine ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], hsp_chk, hclF, hroF,
    ⟨by simp [hx19], by simp [rcSym],
      by simp [hx22], by simp [hx23],
      by simp [hx24], by simp, by simp, by simp, by simp [hfp]⟩,
    by simp, _, ?_, by dsimp only [R0]; sep_frame⟩
  have hgs : ∀ (t : BTree (BitVec 64) 9) (k : Nat) (x : BitVec 64) (i : Nat),
      k < 512 → i < 512 → (t.set k x).get i = if i = k then x else t.get i :=
    fun t k x i hk hi => BTree.get_set t k x hk i hi
  unfold MemAHeaderOk
  repeat rw [hgs _ _ _ _ (by decide) (by decide)]
  simp [ht9]

@[simp, arm64_norm, wp_norm] abbrev off3d0c : BitVec 64 := BitVec.ofNat 64 (4 * 3907)

private theorem seg2_loop_hdr_next [MlKemPlacement] {b sp rcBase : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (_hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {row : Nat} {tA : BTree (BitVec 64) 9} {Rest : SepProp}
    (hrow : row < 3) (hhdr : MemAHeaderOk sp rho tA)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + off07c0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hg : EpiPreservedGprs sp rcBase row s)
    (hP : P ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 2008) s P
      (fun sf Pf => RowInitAPre sp rcBase rho (row + 1) Rest sf Pf) := by
  rcases hg with ⟨hx1, hx19, hx21, hx24, hx26, hx27, hfp⟩
  have ht7 : tA.get 7 = sp + 26779#64 := hhdr.2.2.2.2.2.2.1
  refine with_frozen_env hcl hro ?_
  refine SepWP.weaken_pre (Entails.trans hP (show _ ⊢ BTreeMem (sp + 144#64) 286 tA ∗
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ memRegion (sp + 24720#64) 32 ∗
        memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
        memRegion (sp + 28848#64) 2016 ∗ Rest) by sep_frame)) ?_
  refine step_ldr64_btree (ea := sp + 200#64) (wb := none) (k := 7) (by decide) (by bv_omega)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode, hsp]) (by wp_norm_lhs) ?_
  have hne4 : BitVec.ofNat 64 (row + 1) ≠ 4#64 := by bv_omega
  wp_steps 5
  refine SepWP.done (by simp [hne4]) (by simp [hrun]) fun hclF hroF => ?_
  refine ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], hsp_chk, hclF, hroF,
    ⟨by simp [hx19], by simp [hx21], by simp, by simp,
      by simp [hx24], by simp, by simp [hx26], by simp [hx27], by simp [hfp]⟩,
    by simp [hx1], tA, hhdr, by sep_frame⟩

private theorem seg2_loop_hdr_done [MlKemPlacement] {b sp rcBase : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (_hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {tA : BTree (BitVec 64) 9} {Rest : SepProp}
    (hhdr : MemAHeaderOk sp rho tA)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + off07c0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hg : EpiPreservedGprs sp rcBase 3 s)
    (hP : P ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗ Rest) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off3d0c) s P
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        sf.readReg64 .x19 = sp + 2560#64 ∧ sf.readReg64 .x21 = rcBase ∧
        sf.readReg64 .x22 = sp + 26768#64 ∧ sf.readReg64 .x23 = sp + 26779#64 ∧
        sf.readReg64 .x24 = sp + 27032#64 ∧ sf.readReg64 .x26 = sp + 24720#64 ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ BTreeMem (sp + 144#64) 286 tA ∗ Rest)) := by
  rcases hg with ⟨hx1, hx19, hx21, hx24, hx26, _, hfp⟩
  have ht7 : tA.get 7 = sp + 26779#64 := hhdr.2.2.2.2.2.2.1
  refine with_frozen_env hcl hro ?_
  refine SepWP.weaken_pre (Entails.trans hP (show _ ⊢ BTreeMem (sp + 144#64) 286 tA ∗
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ Rest) by sep_frame)) ?_
  refine step_ldr64_btree (ea := sp + 200#64) (wb := none) (k := 7) (by decide) (by bv_omega)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode, hsp]) (by wp_norm_lhs) ?_
  wp_steps 5
  refine SepWP.weaken_pre (P' := (rcBase ↦ᵣ mlkemData01Bytes) ∗
      (BTreeMem (sp + 144#64) 286 tA ∗ Rest)) (by sep_frame) (sepWP_drop_left ?_)
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun hclF hroF => ?_
  exact ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], hsp_chk, hclF, hroF,
    by simp [hx19], by simp [hx21], by simp, by simp,
    by simp [hx24], by simp [hx26], by simp [hfp], Entails.refl _⟩


/-! ## 3. Single-Row & Full 4-Row `Seg2` Composition (`+0x0758 .. +0x3d0c`) -/

private def RowDone [MlKemPlacement] (b sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.pc = b + off07c0 ∧ sf.status = .Running ∧
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  EpiPreservedGprs sp rcBase row sf ∧
  ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk sp rho tA ∧
    (Pf ⊢ ATransRowMem sp rho row ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗ memRegion (sp + 24720#64) 32 ∗
      memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ Rest)

private theorem seg2_row_safeSepWP [MlKemPlacement] {b sp rcBase : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4) {s : State} {P : SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 2008) (hrun : s.status = .Running)
    (hpre : RowInitAPre sp rcBase rho row
      (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SafeSepWP (blkPC07.rebase b (fun _ => none)) s P (RowDone b sp rcBase rho row Rest) := by
  have hne : b + BitVec.ofNat 64 (4 * 2667) ≠ pcAt (b + BitVec.ofNat 64 (4 * 3289)) 4 := by
    dsimp only [pcAt]; bv_omega
  refine SafeSepWP.bind
    (sampleNttRow_safeSepWP
      (Q := fun sm Pm => sm.pc = b + BitVec.ofNat 64 (4 * 3548) ∧ sm.status = .Running ∧
        RowExitState sp rcBase rho row
          (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) sm Pm)
      hne (fun _ _ _ hI => hI.1)
      (SepWP.mono (seg2_init_ok hb hbase hrho hrow hpc hrun hpre) fun sf Pf hpcF hrunF h => by
        by_cases hc : allLanesDone 4 (fun c => rowSeed rho row c) 0
        · simp only [hc, ↓reduceIte] at hpcF h ⊢; exact ⟨hpcF, hrunF, h⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h)
      (fun _ _ _ hI => seg2_extra_bodyA_ok hb hrho hI)
      (fun extra _ _ hpcM hrunM hm =>
        SepWP.mono (seg2_extra_bodyB_ok hb hpcM hrunM hm) fun sf Pf hpcF hrunF h => by
          by_cases hc : allLanesDone 4 (fun c => rowSeed rho row c) (extra + 1)
          · simp only [hc, ↓reduceIte] at hpcF h ⊢; exact ⟨hpcF, hrunF, h⟩
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h)) ?_
  rintro sm Pm ⟨hpcM, hrunM, hexit⟩
  refine SafeSepWP.of_sepWP (SepWP.mono (seg2_epi_ok hb hbase hrow hpcM hrunM hexit) ?_)
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, hsp16, hclf, hrof, hgf, tA, hhdr, hPf⟩
  rw [rowPolyOut_eq_aTransRowMem] at hPf
  exact SafeSepWP.done ⟨hpcf, hrunf, hspf, hspAf, hsp16, hclf, hrof, hgf, tA, hhdr, hPf⟩

private theorem seg2_row_sepWP [MlKemPlacement] {b sp rcBase : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4)
    (hTerm : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho row c))
    {s : State} {P : SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 2008) (hrun : s.status = .Running)
    (hpre : RowInitAPre sp rcBase rho row
      (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off07c0) s P
      (RowDone b sp rcBase rho row Rest) := by
  refine SepWP.seq
    (sampleNttRow_sepWP hTerm
      (seg2_init_ok hb hbase hrho hrow hpc hrun hpre)
      (fun _ _ _ hI => seg2_extra_bodyA_ok hb hrho hI)
      (fun _ _ _ hpcM hrunM hm => seg2_extra_bodyB_ok hb hpcM hrunM hm)) ?_
  rintro sm Pm hpcM hrunM hexit
  refine SepWP.mono (seg2_epi_ok hb hbase hrow hpcM hrunM hexit) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, hsp16, hclf, hrof, hgf, tA, hhdr, hPf⟩
  rw [rowPolyOut_eq_aTransRowMem] at hPf
  exact ⟨hpcf, hrunf, hspf, hspAf, hsp16, hclf, hrof, hgf, tA, hhdr, hPf⟩

/-- Canonical spatial invariant at `+0x3d0c` (`Seg3` entry). -/
@[expose] noncomputable def Seg2Spatial (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) : SepProp :=
  (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗
  stackAt sp 1136 ∗
  memRegion sp 8 ∗
  ((sp + 8#64) ↦₆₄ ret) ∗
  SpilledMsgWords sp (sha3_256List rand) ∗
  memRegion (sp + 144#64) 2352 ∗
  ((sp + 2496#64) ↦ₛ sha3_512List (sha3_256List rand ++ sha3_256List pk)) ∗
  memRegion (sp + 2560#64) 10272 ∗
  ATransMem sp (pkRho pk) ∗
  PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
  PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
  PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
  PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
  ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗
  memRegion (sp + 23104#64) 9840 ∗
  SavedFrame07 sp0 s0

/-- Register + spatial postcondition at `+0x3d0c` (`Seg3` entry). -/
@[expose] def Seg2Post [MlKemPlacement] (b sp0 : BitVec 64) (s0 : State)
    (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := sp0 - 33104#64
  sf.pc = b + off3d0c ∧ sf.status = .Running ∧
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  sf.readReg64 .x19 = sp + 2560#64 ∧ sf.readReg64 .x21 = mlkemMpl.ρ rcSym ∧
  sf.readReg64 .x22 = sp + 26768#64 ∧ sf.readReg64 .x23 = sp + 26779#64 ∧
  sf.readReg64 .x24 = sp + 27032#64 ∧ sf.readReg64 .x26 = sp + 24720#64 ∧
  sf.readReg64 .fp = sp + 33008#64 ∧
  (Pf ⊢ Seg2Spatial sp0 s0 sp ret pkA rA pk rand ∗ Rest)


private theorem seg2_regions_eq (sp : BitVec 64) :
    (memRegion (sp + 224#64) 2272 =
      memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2432#64) 64) ∧
    (memRegion (sp + 144#64) 2352 =
      memRegion (sp + 144#64) 2288 ∗ memRegion (sp + 2432#64) 64) ∧
    (memRegion (sp + 2560#64) 10272 =
      memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 4736#64) 8096) ∧
    (memRegion (sp + 12832#64) 8192 =
      memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 0)) 2048 ∗
      memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 1)) 2048 ∗
      memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
      memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048) ∧
    (memRegion (sp + 23104#64) 9840 =
      memRegion (sp + 23104#64) 1616 ∗ memRegion (sp + 24720#64) 32 ∗
      memRegion (sp + 24752#64) 2016 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 27440#64) 1408 ∗ memRegion (sp + 28848#64) 2016 ∗
      memRegion (sp + 30864#64) 2080) := by
  refine ⟨memRegion_split' (b := sp + 224#64) (b' := sp + 2432#64) (n := 2208) (k := (64 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 144#64) (b' := sp + 2432#64) (n := 2288) (k := (64 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2560#64) (b' := sp + 4736#64) (n := 2176) (k := (8096 : Nat))
      rfl (by bv_omega) (by decide), ?_, ?_⟩
  · rw [show sp + 12832#64 + BitVec.ofNat 64 (2048 * 0) = sp + 12832#64 from by bv_omega,
      memRegion_split' (b := sp + 12832#64) (b' := sp + 12832#64 + BitVec.ofNat 64 (2048 * 1))
        (n := 2048) (k := (6144 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12832#64 + BitVec.ofNat 64 (2048 * 1))
        (b' := sp + 12832#64 + BitVec.ofNat 64 (2048 * 2))
        (n := 2048) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12832#64 + BitVec.ofNat 64 (2048 * 2))
        (b' := sp + 12832#64 + BitVec.ofNat 64 (2048 * 3))
        (n := 2048) (k := (2048 : Nat)) rfl (by bv_omega) (by decide)]
  · rw [memRegion_split' (b := sp + 23104#64) (b' := sp + 24720#64) (n := 1616) (k := (8224 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24720#64) (b' := sp + 24752#64) (n := 32) (k := (8192 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24752#64) (b' := sp + 26768#64) (n := 2016) (k := (6176 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 26768#64) (b' := sp + 27440#64) (n := 672) (k := (5504 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 27440#64) (b' := sp + 28848#64) (n := 1408) (k := (4096 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28848#64) (b' := sp + 30864#64) (n := 2016) (k := (2080 : Nat))
        rfl (by bv_omega) (by decide)]

private def Seg2Frame (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp) : SepProp :=
  (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗
  stackAt sp 1136 ∗
  memRegion sp 8 ∗
  ((sp + 8#64) ↦₆₄ ret) ∗
  SpilledMsgWords sp (sha3_256List rand) ∗
  memRegion (sp + 2432#64) 64 ∗
  ((sp + 2496#64) ↦ₛ sha3_512List (sha3_256List rand ++ sha3_256List pk)) ∗
  memRegion (sp + 4736#64) 8096 ∗
  PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
  PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
  PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
  PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
  ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗
  memRegion (sp + 23104#64) 1616 ∗
  memRegion (sp + 24752#64) 2016 ∗
  memRegion (sp + 27440#64) 1408 ∗
  memRegion (sp + 30864#64) 2080 ∗
  SavedFrame07 sp0 s0 ∗
  Rest

private theorem seg2_exit_to_seg2Spatial (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (tA : BTree (BitVec 64) 9) :
    BTreeMem (sp + 144#64) 286 tA ∗
      (memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗
        ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
        ATransRowMem sp (pkRho pk) 2 ∗ ATransRowMem sp (pkRho pk) 3 ∗
        Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest) ⊢
      Seg2Spatial sp0 s0 sp ret pkA rA pk rand ∗ Rest := by
  have hbt := BTreeMem_entails_memRegion (sp + 144#64) 286 tA
  rw [show 8 * 286 = 2288 from rfl] at hbt
  rcases seg2_regions_eq sp with ⟨_, hr144, hr2560, _, hr23104⟩
  unfold Seg2Spatial Seg2Frame ATransMem
  rw [hr144, hr2560, hr23104]
  exact Entails.trans (sepConj_mono_left hbt) (by sep_frame)


private theorem seg2_entry_prep [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp0 : BitVec 64) (s0 : State) (ret pkA rA : BitVec 64)
    (pk rand : List (BitVec 8)) (Rest : SepProp)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + 0x0758#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpre : Seg1bPost sp0 s0 ret pkA rA pk rand Rest s P) :
    let sp := sp0 - 33104#64
    let RAll := memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 0)) 2048 ∗
      (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 1)) 2048 ∗
        memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
        memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
        Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 2008) s P
      (fun sf Pf => sf.pc = b + BitVec.ofNat 64 2008 ∧ sf.status = .Running ∧
        RowInitAPre sp (mlkemMpl.ρ rcSym) (pkRho pk) 0 RAll sf Pf) := by
  intro sp RAll
  rcases hpre with ⟨hsp, hspA, hsp_chk, hx9, hx19, _, hx22, hx23, hx24, _, hfp, hv0, hv1, hv2, hP⟩
  rcases seg2_regions_eq sp with ⟨hr224, _, hr2560, hr12832, hr23104⟩
  have hsplit : Seg1bSpatial sp0 s0 sp ret pkA rA pk rand ∗ Rest ⊢
      memRegion (sp + 144#64) 72 ∗
      (memRegion (sp + 224#64) 2208 ∗
        (((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
          memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
          memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ RAll)) := by
    dsimp only [RAll]
    unfold Seg1bSpatial Seg2Frame
    rw [hr224, hr2560, hr12832, hr23104]; sep_frame
  refine SepWP.weaken_pre (Entails.trans hP hsplit) ?_
  refine SepWP.of_memRegion_btreeMem 9 (sp + 144#64) (by decide) (by decide) rfl fun tLo => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 224#64) 2208 ∗
      (BTreeMem (sp + 144#64) 9 tLo ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
        memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ RAll)) (by sep_frame) ?_
  refine SepWP.of_memRegion_btreeMem 276 (sp + 224#64) (by decide) (by decide) rfl fun tHi => ?_
  rcases btreeMem286_of_parts sp (sp + 29112#64) tLo tHi with ⟨t0, ht9, hjoin⟩
  refine SepWP.roDataAt_intro hro.keccakRc (by rw [mlkemData01Bytes_length]; decide) ?_
  have hent : (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗
      (BTreeMem (sp + 224#64) 276 tHi ∗
        (BTreeMem (sp + 144#64) 9 tLo ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
          memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
          memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ RAll)) ⊢
      (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 t0 ∗
        memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ RAll := by
    rw [← hjoin]; sep_frame
  refine SepWP.weaken_pre hent ?_
  refine SepWP.mono (seg2_entry_ok hb hbase ht9 hpc hrun hsp hspA hsp_chk hcl hro
    hx9 hx19 hx22 hx23 hx24 hfp hv0 hv1 hv2) ?_
  exact fun _ _ hpcF hrunF hp => ⟨hpcF, hrunF, hp⟩

theorem seg2_safeSepWP [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp0 : BitVec 64) (s0 : State) (ret pkA rA : BitVec 64)
    (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568)
    (s : State) (P : SepProp)
    (hpc : s.pc = b + 0x0758#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpre : Seg1bPost sp0 s0 ret pkA rA pk rand Rest s P) :
    SafeSepWP (blkPC07.rebase b (fun _ => none)) s P
      (Seg2Post b sp0 s0 ret pkA rA pk rand Rest) := by
  let sp := sp0 - 33104#64
  have hrho : (pkRho pk).length = 32 := pkRho_len hpk
  refine SafeSepWP.of_sepWP (SepWP.mono
    (seg2_entry_prep hb hbase sp0 s0 ret pkA rA pk rand Rest hpc hrun hcl hro hpre) ?_)
  rintro s0' P0' _ _ ⟨hpc0, hrun0, hpre0⟩
  refine SafeSepWP.bind (seg2_row_safeSepWP hb hbase hrho (row := 0) (by decide) hpc0 hrun0 hpre0) ?_
  rintro sm0 Pm0 ⟨hpcM0, hrunM0, hspM0, hspAM0, h16M0, hclM0, hroM0, hgM0, tA0, hhdr0, hPM0⟩
  refine SafeSepWP.of_sepWP (SepWP.mono (seg2_loop_hdr_next hb hbase (by decide) hhdr0
    hpcM0 hrunM0 hspM0 hspAM0 h16M0 hclM0 hroM0 hgM0
    (Entails.trans hPM0 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 1)) 2048 ∗
        (ATransRowMem sp (pkRho pk) 0 ∗ memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
          memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
          Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)) by sep_frame))) ?_)
  rintro s1' P1' hpc1 hrun1 hpre1
  refine SafeSepWP.bind (seg2_row_safeSepWP hb hbase hrho (row := 1) (by decide) hpc1 hrun1 hpre1) ?_
  rintro sm1 Pm1 ⟨hpcM1, hrunM1, hspM1, hspAM1, h16M1, hclM1, hroM1, hgM1, tA1, hhdr1, hPM1⟩
  refine SafeSepWP.of_sepWP (SepWP.mono (seg2_loop_hdr_next hb hbase (by decide) hhdr1
    hpcM1 hrunM1 hspM1 hspAM1 h16M1 hclM1 hroM1 hgM1
    (Entails.trans hPM1 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA1 ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
        (ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
          memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
          Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)) by sep_frame))) ?_)
  rintro s2' P2' hpc2 hrun2 hpre2
  refine SafeSepWP.bind (seg2_row_safeSepWP hb hbase hrho (row := 2) (by decide) hpc2 hrun2 hpre2) ?_
  rintro sm2 Pm2 ⟨hpcM2, hrunM2, hspM2, hspAM2, h16M2, hclM2, hroM2, hgM2, tA2, hhdr2, hPM2⟩
  refine SafeSepWP.of_sepWP (SepWP.mono (seg2_loop_hdr_next hb hbase (by decide) hhdr2
    hpcM2 hrunM2 hspM2 hspAM2 h16M2 hclM2 hroM2 hgM2
    (Entails.trans hPM2 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA2 ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
        (ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
          ATransRowMem sp (pkRho pk) 2 ∗ Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)) by sep_frame))) ?_)
  rintro s3' P3' hpc3 hrun3 hpre3
  refine SafeSepWP.bind (seg2_row_safeSepWP hb hbase hrho (row := 3) (by decide) hpc3 hrun3 hpre3) ?_
  rintro sm3 Pm3 ⟨hpcM3, hrunM3, hspM3, hspAM3, h16M3, hclM3, hroM3, hgM3, tA3, hhdr3, hPM3⟩
  refine SafeSepWP.of_sepWP (SepWP.mono (seg2_loop_hdr_done hb hbase hhdr3
    hpcM3 hrunM3 hspM3 hspAM3 h16M3 hclM3 hroM3 hgM3
    (Entails.trans hPM3 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA3 ∗
      (memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗
        ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
        ATransRowMem sp (pkRho pk) 2 ∗ ATransRowMem sp (pkRho pk) 3 ∗
        Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest) by sep_frame))) ?_)
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, h16f, hclf, hrof, hx19f, hx21f, hx22f, hx23f, hx24f, hx26f, hfpf, hPf⟩
  exact SafeSepWP.done ⟨hpcf, hrunf, hspf, hspAf, h16f, hclf, hrof, hx19f, hx21f, hx22f, hx23f, hx24f, hx26f, hfpf,
    Entails.trans hPf (seg2_exit_to_seg2Spatial sp0 s0 sp ret pkA rA pk rand Rest tA3)⟩


theorem seg2_sepWP [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp0 : BitVec 64) (s0 : State) (ret pkA rA : BitVec 64)
    (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568) (hTerm : Kyber1024EncapsTerminates pk)
    (s : State) (P : SepProp)
    (hpc : s.pc = b + 0x0758#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpre : Seg1bPost sp0 s0 ret pkA rA pk rand Rest s P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off3d0c) s P
      (Seg2Post b sp0 s0 ret pkA rA pk rand Rest) := by
  let sp := sp0 - 33104#64
  have hrho : (pkRho pk).length = 32 := pkRho_len hpk
  have hT (row : Nat) (hr : row < 4) : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed (pkRho pk) row c) :=
    fun c hc => shake128MatrixTerminates_row hTerm hr hc
  refine SepWP.seq (seg2_entry_prep hb hbase sp0 s0 ret pkA rA pk rand Rest hpc hrun hcl hro hpre) ?_
  rintro s0' P0' _ _ ⟨hpc0, hrun0, hpre0⟩
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 0) (by decide) (hT 0 (by decide)) hpc0 hrun0 hpre0) ?_
  rintro sm0 Pm0 _ _ ⟨hpcM0, hrunM0, hspM0, hspAM0, h16M0, hclM0, hroM0, hgM0, tA0, hhdr0, hPM0⟩
  refine SepWP.seq (seg2_loop_hdr_next hb hbase (by decide) hhdr0
    hpcM0 hrunM0 hspM0 hspAM0 h16M0 hclM0 hroM0 hgM0
    (Entails.trans hPM0 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 1)) 2048 ∗
        (ATransRowMem sp (pkRho pk) 0 ∗ memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
          memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
          Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)) by sep_frame))) ?_
  rintro s1' P1' hpc1 hrun1 hpre1
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 1) (by decide) (hT 1 (by decide)) hpc1 hrun1 hpre1) ?_
  rintro sm1 Pm1 _ _ ⟨hpcM1, hrunM1, hspM1, hspAM1, h16M1, hclM1, hroM1, hgM1, tA1, hhdr1, hPM1⟩
  refine SepWP.seq (seg2_loop_hdr_next hb hbase (by decide) hhdr1
    hpcM1 hrunM1 hspM1 hspAM1 h16M1 hclM1 hroM1 hgM1
    (Entails.trans hPM1 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA1 ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
        (ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
          memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
          Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)) by sep_frame))) ?_
  rintro s2' P2' hpc2 hrun2 hpre2
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 2) (by decide) (hT 2 (by decide)) hpc2 hrun2 hpre2) ?_
  rintro sm2 Pm2 _ _ ⟨hpcM2, hrunM2, hspM2, hspAM2, h16M2, hclM2, hroM2, hgM2, tA2, hhdr2, hPM2⟩
  refine SepWP.seq (seg2_loop_hdr_next hb hbase (by decide) hhdr2
    hpcM2 hrunM2 hspM2 hspAM2 h16M2 hclM2 hroM2 hgM2
    (Entails.trans hPM2 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA2 ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗ memRegion (sp + 26768#64) 672 ∗
      memRegion (sp + 28848#64) 2016 ∗ (memRegion (sp + 12832#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗
        (ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
          ATransRowMem sp (pkRho pk) 2 ∗ Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest)) by sep_frame))) ?_
  rintro s3' P3' hpc3 hrun3 hpre3
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 3) (by decide) (hT 3 (by decide)) hpc3 hrun3 hpre3) ?_
  rintro sm3 Pm3 _ _ ⟨hpcM3, hrunM3, hspM3, hspAM3, h16M3, hclM3, hroM3, hgM3, tA3, hhdr3, hPM3⟩
  refine SepWP.mono (seg2_loop_hdr_done hb hbase hhdr3
    hpcM3 hrunM3 hspM3 hspAM3 h16M3 hclM3 hroM3 hgM3
    (Entails.trans hPM3 (show _ ⊢ (mlkemMpl.ρ rcSym ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA3 ∗
      (memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗
        ATransRowMem sp (pkRho pk) 0 ∗ ATransRowMem sp (pkRho pk) 1 ∗
        ATransRowMem sp (pkRho pk) 2 ∗ ATransRowMem sp (pkRho pk) 3 ∗
        Seg2Frame sp0 s0 sp ret pkA rA pk rand Rest) by sep_frame))) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, h16f, hclf, hrof, hx19f, hx21f, hx22f, hx23f, hx24f, hx26f, hfpf, hPf⟩
  exact ⟨hpcf, hrunf, hspf, hspAf, h16f, hclf, hrof, hx19f, hx21f, hx22f, hx23f, hx24f, hx26f, hfpf,
    Entails.trans hPf (seg2_exit_to_seg2Spatial sp0 s0 sp ret pkA rA pk rand Rest tA3)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2
