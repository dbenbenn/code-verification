/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Uhat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Decrypt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Extra
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs

/-!
# Operational Divergence of Stuck `mlkem1024::kyber::decapsulate` (`B23` → `B06`)

Proves that when `¬ KemDecapsStateTerminates u` holds at the entry of `lsKyber1024DecapsSym`
(`B23`, calling `B06` `neon::kyber_decapsulate` with `¬ Kyber1024DecapsTerminates sk`), every
state `v` reachable in the real 0-hook program (`cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
and `Placed.cliProgPlacedSig mpl mmpl W`) has `v.status = .Running` (and a next step
`∃ w, Step P_real v w`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Kyber1024Decaps

open Arm64 ProofLib SepProp BitVec
open Arm64.Obj (MultiPlacement MultiPlacedLib lo12Of pageOf_add_lo12Of)
open CryptoVerification.E2E (PqxdhPrims)
open CryptoVerification.SignalSession (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges (KemDecapsCall)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  kemDecapsAtSpec withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  SavedFrame06 blk06_code_eq blk06_tree_size blk23_code_eq blk23_tree_size
  blkLib06 blkLib23 blkPC06 blkPC23 blkPl06 blkPl23 blkPlaceable06 blkPlaceable23
  blkTree06 blkTree23 safeSepWP_of_sepWP_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SpillSliceMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1a (
  Seg1aSpatial seg1a_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (
  cst16_3_val seg1b_ok sk_pointsTo_split uHatZetaSpill40
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1c (
  seg1c_ok sepWP_elim_poly32 sepWP_elim_vec128At spillSliceMem_entails_memRegion
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Uhat (seg2_uhat_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Decrypt (seg3_decrypt_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 (SpilledDecapsWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b2 (seg4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowExtraState06 RowMidState06
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi (RowPolyOut06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Extra (
  seg5_extra_bodyA_ok seg5_extra_bodyB_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Init (seg5_init_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA (
  RowEntryGprs06 RowInitAPre06
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix (
  Seg5RowPost06 off40f0 off4170 off76a8 seg5_row_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMemFrom BTreeMemFrom_eq_bytes SepWP.of_memRegion_btreeMem
  btreeBytesFrom_length btreeBytesFrom_split sepStore128_btreeMem sepStore64_btreeMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (BTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho rhoW tHatModPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env step_ldrQ128_ro
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At polyVecNat step_stpQ128 step_strQ128
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockSafeOk MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemMpl
  mlkemSafeCall_of_blockSafeOk mlkemSafeCaller_ok
  resolve_ro01 resolve_ro02 resolve_ro03 resolve_ro04 resolve_ro10
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes mlkemData10Bytes mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk SepWP.roDataAt_intro cst16_0_vec cst16_1_vec cst16_2_vec cst16_8_vec
  mlkemData01Bytes_length mlkemData02Bytes_length mlkemData03Bytes_length mlkemData04Bytes_length
  mlkemData10Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024DecapsTerminates Poly Shake128MatrixTerminates Shake128SeedTerminates
  bitsToBytes byteEncode compressAndEncode indCpaDecrypt sampleNtt sha3_512List shake256List
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2_resolve_kyber1024Decaps_eq lsKyber1024DecapsSym
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers (
  KemDecapsStateTerminates allLanesDone_eq_false_of_exists_not_terminates
  kemDecapsStateTerminates_iff_of_atSpec_pre sampleNttRow_diverge_safeSepWP
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common (
  c2_mlkem_diverge_of_blockSafeOk_false falsePostSpec
  safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  kemDecapsTightStack
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

/-! ## 1. `B06` (`neon::kyber_decapsulate`) Segment 5 Divergence (`¬ Shake128MatrixTerminates rho 4`) -/

section Blk06Seg5Diverge

attribute [local simp, local arm64_norm, local wp_norm] off40f0 off4170 off76a8
@[local simp, local arm64_norm, local wp_norm] private abbrev off412c : BitVec 64 := 16684#64
@[local simp, local arm64_norm, local wp_norm] private abbrev off4138 : BitVec 64 := 16696#64
@[local simp, local arm64_norm, local wp_norm] private abbrev off4144 : BitVec 64 := 16708#64
@[local simp, local arm64_norm, local wp_norm] private abbrev off414c : BitVec 64 := 16716#64

section
set_option linter.literalFetch false

@[local simp, local arm64_norm]
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

@[local simp, local arm64_norm]
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

@[local simp, local arm64_norm]
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

@[local simp, local arm64_norm]
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

@[local simp, local arm64_norm, local wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local simp] resolve_ro01 resolve_ro02 resolve_ro03 resolve_ro04 resolve_ro10
attribute [local irreducible] blkPC06 sampleNtt polyVecNat

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

private theorem seg5_row_diverge_safe_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp}
    (hrho : rho.length = 32) (hrow : row < 4)
    (hNotTerm : ¬ ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho row c))
    {s : State} {P : SepProp}
    (hpc : s.pc = b + off4170) (hrun : s.status = .Running)
    (hpre : RowInitAPre06 sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SafeSepWP (blkPC06.rebase b (fun _ => none)) s P (fun _ _ => False) := by
  have hpc' : s.pc = b + BitVec.ofNat 64 (4 * 4188) := by simpa [off4170] using hpc
  have hbad : ∃ c, c < 4 ∧ ¬ Shake128SeedTerminates (rowSeed rho row c) := by
    classical
    by_contra hall
    exact hNotTerm fun c hc => by by_contra hnt; exact hall ⟨c, hc, hnt⟩
  have hNever : ∀ extra, allLanesDone 4 (fun c => rowSeed rho row c) extra = false :=
    allLanesDone_eq_false_of_exists_not_terminates hbad
  have hne : b + BitVec.ofNat 64 (4 * 6354) ≠ pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4 := by
    dsimp only [pcAt]; bv_omega
  exact sampleNttRow_diverge_safeSepWP
    (N := 4) (seeds := fun c => rowSeed rho row c)
    (loopHead := b + BitVec.ofNat 64 (4 * 6354))
    (midPC := pcAt (b + BitVec.ofNat 64 (4 * 6976)) 4)
    (exitPC := b + BitVec.ofNat 64 (4 * 7235))
    (Inv := RowExtraState06 b sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest))
    (Mid := RowMidState06 sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest))
    hne (fun _ _ _ hInv => hInv.1) hNever
    (SepWP.mono (seg5_init_ok hb hbase hrho hrow hpc' hrun hpre) fun _ _ _ _ h => by
      simp only [hNever 0] at h ⊢; exact h)
    (fun _ _ _ hInv => seg5_extra_bodyA_ok hb hrho hInv)
    (fun extra _ _ hmpc hmrun hMid =>
      SepWP.mono (seg5_extra_bodyB_ok hb hmpc hmrun hMid) fun _ _ _ _ h => by
        simp only [hNever (extra + 1)] at h ⊢; exact h)

private theorem not_row3_of_not_matrixTerminates4 {rho : List (BitVec 8)}
    (hNotMat : ¬ Shake128MatrixTerminates rho 4)
    (hT0 : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 0 c))
    (hT1 : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 1 c))
    (hT2 : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 2 c)) :
    ¬ ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 3 c) := by
  intro hT3
  apply hNotMat
  intro i j hi hj
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · exact hT0 j hj
  · exact hT1 j hj
  · exact hT2 j hj
  · exact hT3 j hj

private theorem seg5_sample_matrix_diverge_safe_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {Rest : SepProp}
    (hrho : rho.length = 32) (hNotMat : ¬ Shake128MatrixTerminates rho 4) {s : State}
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
      (fun _ _ => False) := by
  refine SafeSepWP.of_sepWP (SepWP.mono
    (seg5_entry_prep_06 hb hbase hpc hrun hsp hspA hsp16 hcl hro
      hx9 hx20 hx22 hx23 hx25 hx26 hfp hv0 hv1) ?_)
  rintro s0 P0 _ _ ⟨hpc0, hrun0, hpre0⟩
  by_cases hT0 : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 0 c)
  · refine SafeSepWP.of_sepWP (SepWP.mono
      (seg5_row_ok hb hbase hrho (row := 0) (by decide) hT0 hpc0 hrun0 hpre0) ?_)
    rintro sm0 Pm0 _ _ hp0
    rcases seg5_row_reframe_06 (row := 0)
        (Rout := memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 2)) 2048 ∗
          memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
        (by decide) (by sep_frame) hp0 with ⟨hpc1, hrun1, hpre1⟩
    by_cases hT1 : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 1 c)
    · refine SafeSepWP.of_sepWP (SepWP.mono
        (seg5_row_ok hb hbase hrho (row := 1) (by decide) hT1 hpc1 hrun1 hpre1) ?_)
      rintro sm1 Pm1 _ _ hp1
      rcases seg5_row_reframe_06 (row := 1)
          (Rout := RowPolyOut06 sp rho 0 ∗
            memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * 3)) 2048 ∗ Rest)
          (by decide) (by sep_frame) hp1 with ⟨hpc2, hrun2, hpre2⟩
      by_cases hT2 : ∀ c, c < 4 → Shake128SeedTerminates (rowSeed rho 2 c)
      · refine SafeSepWP.of_sepWP (SepWP.mono
          (seg5_row_ok hb hbase hrho (row := 2) (by decide) hT2 hpc2 hrun2 hpre2) ?_)
        rintro sm2 Pm2 _ _ hp2
        rcases seg5_row_reframe_06 (row := 2)
            (Rout := RowPolyOut06 sp rho 0 ∗ RowPolyOut06 sp rho 1 ∗ Rest)
            (by decide) (by sep_frame) hp2 with ⟨hpc3, hrun3, hpre3⟩
        exact seg5_row_diverge_safe_ok hb hbase hrho (row := 3) (by decide)
          (not_row3_of_not_matrixTerminates4 hNotMat hT0 hT1 hT2) hpc3 hrun3 hpre3
      · exact seg5_row_diverge_safe_ok hb hbase hrho (row := 2) (by decide) hT2 hpc2 hrun2 hpre2
    · exact seg5_row_diverge_safe_ok hb hbase hrho (row := 1) (by decide) hT1 hpc1 hrun1 hpre1
  · exact seg5_row_diverge_safe_ok hb hbase hrho (row := 0) (by decide) hT0 hpc0 hrun0 hpre0

/-! ## 2. `B06` Prefix (`Seg1a .. Seg4`, `0x0000 → 0x40f0`) -/

private theorem sk_tail_split (skA : BitVec 64) {sk : List (BitVec 8)} (hsk : sk.length = 3168) :
    ((skA + 1536#64) ↦ₛ sk.drop 1536) =
      ((skA + 1536#64) ↦ₛ (sk.drop 1536).take 1568) ∗
      ((skA + 3104#64) ↦ₛ (sk.drop 3104).take 32) ∗
      ((skA + 3136#64) ↦ₛ (sk.drop 3136).take 32) := by
  have h1 : sk.drop 1536 = (sk.drop 1536).take 1568 ++ sk.drop 3104 := by
    conv_lhs => rw [← List.take_append_drop 1568 (sk.drop 1536)]
    rw [List.drop_drop]
  have h2 : sk.drop 3104 = (sk.drop 3104).take 32 ++ (sk.drop 3136).take 32 := by
    have hd3136 : (sk.drop 3104).drop 32 = sk.drop 3136 := by rw [List.drop_drop]
    have hdrop : sk.drop 3136 = (sk.drop 3136).take 32 := by
      symm; apply List.take_of_length_le; simp [hsk]
    conv_lhs => rw [← List.take_append_drop 32 (sk.drop 3104)]
    rw [hd3136, ← hdrop]
  have hl1 : ((sk.drop 1536).take 1568).length = 1568 := by simp [hsk]
  have hl2 : ((sk.drop 3104).take 32).length = 32 := by simp [hsk]
  conv_lhs => rw [h1]
  rw [pointsToBytes_append, hl1]
  conv_lhs => rw [h2]
  rw [pointsToBytes_append, hl2]
  simp only [
    show skA + 1536#64 + BitVec.ofNat 64 1568 = skA + 3104#64 by bv_omega,
    show skA + 3104#64 + BitVec.ofNat 64 32 = skA + 3136#64 by bv_omega]

private theorem pkRho_sk_eq (sk : List (BitVec 8)) :
    pkRho ((sk.drop 1536).take 1568) = (sk.drop 3072).take 32 := by
  have h : ((sk.drop 1536).take 1568).drop 1536 = (sk.drop 3072).take 32 := by
    rw [List.drop_take, List.drop_drop]
  unfold pkRho
  rw [h, List.take_take, Nat.min_self]

private theorem pkRho_sk_len {sk : List (BitVec 8)} (hsk : sk.length = 3168) :
    (pkRho ((sk.drop 1536).take 1568)).length = 32 := by
  rw [pkRho_sk_eq sk]; simp [hsk]

private theorem dup4hLow_3329_trunc64 :
    (dup4hLow 3329#16).truncate 64 = 0x0d010d010d010d01#64 := by decide

private theorem sp_aligned_chk {s : State} {sp : BitVec 64}
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    (sp &&& 15#64 == 0#64) = true := by
  unfold State.spAligned at hspA; rwa [hsp] at hspA

private theorem mr_split (sp : BitVec 64) (o1 n k o2 : Nat)
    (ho : sp + BitVec.ofNat 64 o1 + BitVec.ofNat 64 n = sp + BitVec.ofNat 64 o2 := by bv_omega)
    (hk : n + k ≤ 2 ^ 64 := by decide) :
    memRegion (sp + BitVec.ofNat 64 o1) (n + k) =
      memRegion (sp + BitVec.ofNat 64 o1) n ∗ memRegion (sp + BitVec.ofNat 64 o2) k :=
  memRegion_split' rfl ho.symm hk

private theorem vec128At_entails_memRegion16 (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v ⊢ memRegion ptr 16 := by
  unfold Vec128At
  rw [memRegion_split' (b := ptr) (b' := ptr + 8#64) (n := 8) (k := (8 : Nat)) rfl rfl (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _)

private theorem seg1a_split_28952 (sp : BitVec 64) :
    memRegion (sp + 2008#64) 28952 =
      memRegion (sp + 2008#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗ memRegion (sp + 2024#64) 8 ∗
      memRegion (sp + 2032#64) 8 ∗ memRegion (sp + 2040#64) 8 ∗ memRegion (sp + 2048#64) 16 ∗
      memRegion (sp + 2064#64) 336 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
      memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ∗ memRegion (sp + 2432#64) 1728 ∗
      memRegion (sp + 4160#64) 2048 ∗ memRegion (sp + 6208#64) 8224 ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1536 ∗
      memRegion (sp + 16480#64) 8224 ∗ memRegion (sp + 24704#64) 1616 ∗
      memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 26832#64) 1536 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 28400#64) 480 ∗
      memRegion (sp + 28880#64) 1568 ∗ memRegion (sp + 30448#64) 512 := by
  rw [mr_split sp 2008 8 28944 2016, mr_split sp 2016 8 28936 2024,
    mr_split sp 2024 8 28928 2032, mr_split sp 2032 8 28920 2040,
    mr_split sp 2040 8 28912 2048, mr_split sp 2048 16 28896 2064,
    mr_split sp 2064 336 28560 2400, mr_split sp 2400 8 28552 2408,
    mr_split sp 2408 8 28544 2416, mr_split sp 2416 8 28536 2424,
    mr_split sp 2424 8 28528 2432, mr_split sp 2432 1728 26800 4160,
    mr_split sp 4160 2048 24752 6208, mr_split sp 6208 8224 16528 14432,
    mr_split sp 14432 512 16016 14944, mr_split sp 14944 1536 14480 16480,
    mr_split sp 16480 8224 6256 24704, mr_split sp 24704 1616 4640 26320,
    mr_split sp 26320 512 4128 26832, mr_split sp 26832 1536 2592 28368,
    mr_split sp 28368 32 2560 28400, mr_split sp 28400 480 2080 28880,
    mr_split sp 28880 1568 512 30448]

private theorem seg1a_split_30960 (sp : BitVec 64) :
    memRegion (sp + 30960#64) 1536 =
      memRegion (sp + 30960#64) 512 ∗ memRegion (sp + 31472#64) 512 ∗ memRegion (sp + 31984#64) 512 := by
  rw [mr_split sp 30960 512 1024 31472, mr_split sp 31472 512 512 31984]

private theorem seg2_to_seg3_2064 (sp : BitVec 64) :
    SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
      memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ⊢
      memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 := by
  have h1 : SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ⊢ memRegion (sp + 2064#64) 336 :=
    spillSliceMem_entails_memRegion 21 (sp + 2064#64) uHatZetaSpill40
  have h2 : memRegion (sp + 2064#64) 368 =
      memRegion (sp + 2064#64) 336 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
        memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 := by
    rw [mr_split sp 2064 336 32 2400, mr_split sp 2400 8 24 2408,
      mr_split sp 2408 8 16 2416, mr_split sp 2416 8 8 2424]
  rw [← mr_split sp 2064 32 336 2096, h2]
  exact entails_sub h1 (by sep_frame) (by sep_frame)

private theorem seg4_collapse_224 (sp : BitVec 64) (p1 p2 p3 p4 : BitVec 64) (v : BitVec 128) :
    memRegion (sp + 224#64) 1760 ∗ ((sp + 1984#64) ↦₆₄ p1) ∗ memRegion (sp + 1992#64) 8 ∗
      ((sp + 2000#64) ↦₆₄ p2) ∗ memRegion (sp + 2008#64) 8 ∗ ((sp + 2016#64) ↦₆₄ p3) ∗
      memRegion (sp + 2024#64) 8 ∗ ((sp + 2032#64) ↦₆₄ p4) ∗ memRegion (sp + 2040#64) 8 ∗
      Vec128At (sp + 2048#64) v ∗ memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 ⊢
      memRegion (sp + 224#64) 2208 := by
  have heq : memRegion (sp + 224#64) 2208 =
      memRegion (sp + 224#64) 1760 ∗ memRegion (sp + 1984#64) 8 ∗ memRegion (sp + 1992#64) 8 ∗
      memRegion (sp + 2000#64) 8 ∗ memRegion (sp + 2008#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗
      memRegion (sp + 2024#64) 8 ∗ memRegion (sp + 2032#64) 8 ∗ memRegion (sp + 2040#64) 8 ∗
      memRegion (sp + 2048#64) 16 ∗ memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 := by
    rw [mr_split sp 224 1760 448 1984, mr_split sp 1984 8 440 1992,
      mr_split sp 1992 8 432 2000, mr_split sp 2000 8 424 2008,
      mr_split sp 2008 8 416 2016, mr_split sp 2016 8 408 2024,
      mr_split sp 2024 8 400 2032, mr_split sp 2032 8 392 2040,
      mr_split sp 2040 8 384 2048, mr_split sp 2048 16 368 2064,
      mr_split sp 2064 32 336 2096]
  rw [heq]
  have hsub := sepConj_mono (cell_entails_memRegion8 (sp + 1984#64) p1)
    (sepConj_mono (cell_entails_memRegion8 (sp + 2000#64) p2)
      (sepConj_mono (cell_entails_memRegion8 (sp + 2016#64) p3)
        (sepConj_mono (cell_entails_memRegion8 (sp + 2032#64) p4)
          (vec128At_entails_memRegion16 (sp + 2048#64) v))))
  exact entails_sub hsub (by sep_frame) (by sep_frame)

private theorem seg4_repartition_upper (sp : BitVec 64) :
    memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 4672#64) 1536 ∗
      memRegion (sp + 6208#64) 8224 ∗
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 2016 ∗
      memRegion (sp + 32496#64) 1936 =
    memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 2176 ∗
      memRegion (sp + 6336#64) 8096 ∗
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 32 ∗
      memRegion (sp + 26352#64) 2016 ∗ memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 30448#64) 2016 ∗
      memRegion (sp + 32464#64) 1968 := by
  have hA1 : memRegion (sp + 2560#64) 11872 =
      memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 4672#64) 1536 ∗
        memRegion (sp + 6208#64) 8224 := by
    rw [mr_split sp 2560 2112 9760 4672, mr_split sp 4672 1536 8224 6208]
  have hA2 : memRegion (sp + 2560#64) 11872 =
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 6336#64) 8096 := by
    rw [mr_split sp 2560 1600 10272 4160, mr_split sp 4160 2176 8096 6336]
  have hB1 : memRegion (sp + 24704#64) 9728 =
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 2016 ∗
      memRegion (sp + 32496#64) 1936 := by
    rw [mr_split sp 24704 1616 8112 26320, mr_split sp 26320 512 7600 26832,
      mr_split sp 26832 1536 6064 28368, mr_split sp 28368 32 6032 28400,
      mr_split sp 28400 480 5552 28880, mr_split sp 28880 1568 3984 30448,
      mr_split sp 30448 32 3952 30480, mr_split sp 30480 2016 1936 32496]
  have hB2 : memRegion (sp + 24704#64) 9728 =
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 32 ∗
      memRegion (sp + 26352#64) 2016 ∗ memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 30448#64) 2016 ∗
      memRegion (sp + 32464#64) 1968 := by
    rw [mr_split sp 24704 1616 8112 26320, mr_split sp 26320 32 8080 26352,
      mr_split sp 26352 2016 6064 28368, mr_split sp 28368 672 5392 29040,
      mr_split sp 29040 1408 3984 30448, mr_split sp 30448 2016 1968 32464]
  calc _ = memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 4672#64) 1536 ∗
          memRegion (sp + 6208#64) 8224 ∗ memRegion (sp + 24704#64) 9728 := by
          rw [hB1]
    _ = memRegion (sp + 2560#64) 11872 ∗ memRegion (sp + 24704#64) 9728 := by
          rw [hA1]; sep_ac_rfl
    _ = _ := by rw [hA2, hB2]; sep_ac_rfl

private theorem seg2_to_seg3_regions (sp : BitVec 64) :
    SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
      memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ∗
      memRegion (sp + 14432#64) 2048 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 28400#64) 480 ⊢
      memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1536 ∗
      memRegion (sp + 28368#64) 512 := by
  rw [mr_split sp 14432 512 1536 14944, ← mr_split sp 28368 32 480 28400]
  exact entails_sub (seg2_to_seg3_2064 sp) (by sep_frame) (by sep_frame)

private theorem seg3_to_seg4_regions (sp : BitVec 64) :
    memRegion (sp + 2432#64) 1728 ∗ memRegion (sp + 4160#64) 2048 ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1536 ∗
      memRegion (sp + 16480#64) 8224 ∗ memRegion (sp + 30448#64) 2048 ∗
      memRegion (sp + 32496#64) 2176 =
    memRegion (sp + 2432#64) 2240 ∗ memRegion (sp + 4672#64) 1536 ∗
      memRegion (sp + 14432#64) 10272 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 2016 ∗
      memRegion (sp + 32496#64) 1936 ∗ memRegion (sp + 34432#64) 32 ∗
      memRegion (sp + 34464#64) 208 := by
  rw [mr_split sp 4160 512 1536 4672, mr_split sp 2432 1728 512 4160,
    mr_split sp 14432 2048 8224 16480, mr_split sp 14432 512 1536 14944,
    mr_split sp 30448 32 2016 30480,
    mr_split sp 32496 1936 240 34432, mr_split sp 34432 32 208 34464]
  sep_ac_rfl

private theorem compressAndEncode_len (d : Nat) (f : Poly) :
    (compressAndEncode d f).length = (256 * d) / 8 := by
  simp [compressAndEncode, byteEncode, bitsToBytes]

private theorem indCpaDecrypt_length (k dU dV : Nat) (skPke ct : List (BitVec 8)) :
    (indCpaDecrypt k dU dV skPke ct).length = 32 := by
  unfold indCpaDecrypt; exact compressAndEncode_len 1 _

private def Rest5Spatial (s0 : State) (ret skA ctA : BitVec 64)
    (sk ct : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 34832#64
  let m := indCpaDecrypt 4 11 5 (sk.take 1536) ct
  let pk := (sk.drop 1536).take 1568
  let hPk := (sk.drop 3104).take 32
  let z := (sk.drop 3136).take 32
  stackAt sp 1136 ∗ SavedFrame06 s0.sp s0 ∗ SpilledDecapsWords sp m ∗
    ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
    memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
    memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 6336#64) 8096 ∗
    PolyMem (sp + 22624#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
    PolyMem (sp + 23136#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
    PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
    PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
    ((sp + 24672#64) ↦ₛ List.replicate 32 0#8) ∗
    memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26352#64) 2016 ∗
    memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 32464#64) 1968 ∗
    ((sp + 34432#64) ↦ₛ shake256List 32 (z ++ ct)) ∗ memRegion (sp + 34464#64) 208 ∗
    (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ F

attribute [local irreducible] tHatModPoly16 indCpaDecrypt sha3_512List shake256List in
set_option maxHeartbeats 800000 in
private theorem seg1_to_4_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (sk ct : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = skA) (hx2 : s0.readReg64 .x2 = ctA)
    (hsk : sk.length = 3168) (hct : ct.length = 1568) :
    let sp := s0.sp - 34832#64
    let pk := (sk.drop 1536).take 1568
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off40f0) s0
      (stackAt s0.sp 35968 ∗ (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = sp + 30459#64 ∧ sf.readReg64 .x20 = sp + 28379#64 ∧
        sf.readReg64 .x22 = sp + 4160#64 ∧ sf.readReg64 .x23 = sp + 24576#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧ sf.readReg64 .x26 = sp + 28632#64 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readVReg128 0#5 = rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0 ∧
        sf.readVReg128 1#5 = rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2 ∧
        (Pf ⊢ memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
          memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 4160#64) 2176 ∗
          memRegion (sp + 14432#64) 8192 ∗ memRegion (sp + 26320#64) 32 ∗
          memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗
          Rest5Spatial s0 ret skA ctA sk ct F)) := by
  intro sp pk
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl0 hro0
      (seg1a_ok hb hbase s0 ret skA ctA ((skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ F)
        hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hP1⟩
  have hP1' : P1 ⊢ memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 2048#64) 16 ∗
      (memRegion (sp + 2032#64) 8 ∗ memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 512 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
        (memRegion (sp + 136#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗ memRegion (sp + 2064#64) 336 ∗
          memRegion (sp + 14944#64) 1536 ∗ memRegion (sp + 31472#64) 512 ∗
          memRegion (sp + 31984#64) 512 ∗ ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
          ((skA + 1536#64) ↦ₛ sk.drop 1536) ∗ stackAt sp 1136 ∗ SavedFrame06 s0.sp s0 ∗
          memRegion sp 128 ∗ ((sp + 128#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 72 ∗
          ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗ memRegion (sp + 224#64) 1760 ∗
          ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ memRegion (sp + 1992#64) 8 ∗
          ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2008#64) 8 ∗
          memRegion (sp + 2024#64) 8 ∗ memRegion (sp + 2040#64) 8 ∗
          memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
          memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ∗
          memRegion (sp + 2432#64) 1728 ∗ memRegion (sp + 4160#64) 2048 ∗
          memRegion (sp + 6208#64) 8224 ∗ memRegion (sp + 16480#64) 8224 ∗
          memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 512 ∗
          memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 32 ∗
          memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
          memRegion (sp + 32496#64) 2176 ∗ (ctA ↦ₛ ct) ∗ F)) := by
    refine Entails.trans hP1 ?_
    dsimp only [Seg1aSpatial]
    rw [mr_split sp 136 8 72 144, seg1a_split_28952 sp, seg1a_split_30960 sp,
      sk_pointsTo_split skA hsk]
    sep_frame
  refine SepWP.weaken_pre hP1' ?_
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 14432#64)); intro vInit
  sep_frame_apply (sepWP_elim_vec128At (a := sp + 2048#64)); intro v2048
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl1 hro1
      (seg1b_ok hb hbase s1 sp skA ctA vInit v2048 sk _
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx26_1 hsk) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, _, hx20_2, hx22_2, hx25_2, hx26_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (sepWP_seq_env hcl2 hro2
      (seg1c_ok hb hbase s2 sp skA ctA sk _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx20_2 hx22_2 hx25_2 hx26_2 hsk) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3,
      hx27_3, hx28_3, hv8_3, _, hP3⟩
  have hv8_3' : (s3.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 := by
    rw [hv8_3, dup4hLow_3329_trunc64]
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg2_uhat_ok hb hbase s3 sp ctA ct _
        hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx0_3 hx19_3 hx22_3 hx23_3 hx24_3 hx27_3 hx28_3 hv8_3' hct) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hfp4, hx25_4, hx26_4, _, _, hP4⟩
  let Rest3 : SepProp :=
    SavedFrame06 s0.sp s0 ∗ memRegion sp 128 ∗ ((sp + 128#64) ↦₆₄ ret) ∗
      memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
      memRegion (sp + 224#64) 1760 ∗
      ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ memRegion (sp + 1992#64) 8 ∗
      ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2008#64) 8 ∗
      ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ memRegion (sp + 2024#64) 8 ∗
      ((sp + 2032#64) ↦₆₄ skA) ∗ memRegion (sp + 2040#64) 8 ∗
      Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 2064#64) 32 ∗
      memRegion (sp + 2432#64) 1728 ∗ memRegion (sp + 6208#64) 8224 ∗
      memRegion (sp + 14944#64) 1536 ∗ memRegion (sp + 16480#64) 8224 ∗
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26832#64) 1536 ∗
      memRegion (sp + 28880#64) 1568 ∗ memRegion (sp + 32496#64) 2176 ∗
      (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
      ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
      ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
      ((skA + 1536#64) ↦ₛ sk.drop 1536) ∗ F
  refine SepWP.weaken_pre ?_
    (sepWP_seq_env hcl4 hro4
      (seg3_decrypt_ok hb hbase s4 sp ctA (sk := sk) hct Rest3
        hpc4 hrun4 hsp4 hspA4 hcl4 hro4) ?_)
  · exact Entails.trans hP4
      (entails_sub (seg2_to_seg3_regions sp)
        (by dsimp only [sp]; sep_frame) (by dsimp only [sp, Rest3]; sep_frame))
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, hx23_5, hx25_5, hx26_5, hfp5, hP5⟩
  dsimp only [Rest3] at hP5
  set m := indCpaDecrypt 4 11 5 (sk.take 1536) ct
  set hPk := (sk.drop 3104).take 32
  set z := (sk.drop 3136).take 32
  have hm : m.length = 32 := indCpaDecrypt_length 4 11 5 (sk.take 1536) ct
  have hpk : pk.length = 1568 := by simp [pk, hsk]
  have hhPk : hPk.length = 32 := by simp [hPk, hsk]
  have hz : z.length = 32 := by simp [z, hsk]
  have h4_pre : P5 ⊢ stackAt sp 1136 ∗ memRegion sp 128 ∗
      ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
      ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
      Vec128At (sp + 2048#64) cst16_3_val ∗
      memRegion (sp + 2432#64) 2240 ∗ memRegion (sp + 14432#64) 10272 ∗
      ((sp + 28368#64) ↦ₛ m) ∗ memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
      ((skA + 1536#64) ↦ₛ pk) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
      ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗
      (SavedFrame06 s0.sp s0 ∗ ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
        memRegion (sp + 224#64) 1760 ∗ memRegion (sp + 1992#64) 8 ∗
        memRegion (sp + 2008#64) 8 ∗ memRegion (sp + 2024#64) 8 ∗
        memRegion (sp + 2040#64) 8 ∗ memRegion (sp + 2064#64) 32 ∗
        memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 4672#64) 1536 ∗
        memRegion (sp + 6208#64) 8224 ∗ memRegion (sp + 24704#64) 1616 ∗
        memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 26832#64) 1536 ∗
        memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
        memRegion (sp + 30480#64) 2016 ∗ memRegion (sp + 32496#64) 1936 ∗
        memRegion (sp + 34464#64) 208 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
        ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ F) := by
    refine Entails.trans hP5 ?_
    rw [sk_tail_split skA hsk]
    exact entails_sub (Entails.of_eq (seg3_to_seg4_regions sp))
      (by dsimp only [sp]; sep_frame) (by dsimp only [sp, pk, hPk, z]; sep_frame)
  refine SepWP.weaken_pre h4_pre
    (sepWP_seq_env hcl5 hro5
      (seg4_ok hb hbase s5 sp skA ctA m pk hPk z ct _
        hm hpk hhPk hz hct hpc5 hrun5 hsp5 hspA5 hcl5 hro5 hx23_5) ?_)
  rintro sf Pf hpc_f hrun_f _ _
    ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f, hx25_f, hx26_f, hfp_f, hv0_f, hv1_f, hPf⟩
  refine SepWP.done hpc_f hrun_f
    ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f,
      hx25_f.trans (hx25_5.trans (hx25_4.trans hx25_3)),
      hx26_f.trans (hx26_5.trans (hx26_4.trans hx26_3)),
      hfp_f.trans (hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1)))),
      hv0_f, hv1_f, ?_⟩
  refine Entails.trans hPf ?_
  dsimp only [Rest5Spatial]
  have hsk_join : (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
      ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
      ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
      ((skA + 1536#64) ↦ₛ pk) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗ ((skA + 3136#64) ↦ₛ z) =
      (skA ↦ₛ sk) := by
    rw [sk_pointsTo_split skA hsk, sk_tail_split skA hsk]
  refine entails_sub (seg4_collapse_224 sp (skA + 3104#64) (skA + 3136#64) (skA + 384#64) skA cst16_3_val)
    (by sep_frame) ?_
  refine entails_sub (Entails.of_eq hsk_join) (by sep_frame) ?_
  exact entails_sub (Entails.of_eq (seg4_repartition_upper sp)) (by sep_frame) (by sep_frame)

end Blk06Seg5Diverge

/-! ## 3. `B06` Core & `B23` (`mlkem1024::kyber::decapsulate`) Wrapper Divergence Contracts -/

private def blk06DecapsDivPre :
    (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) → State → SepProp :=
  fun (ret, skA, sk, ctA, ct) s0 =>
    ⌜s0.readReg64 .x0 = ret ∧ s0.readReg64 .x1 = skA ∧ s0.readReg64 .x2 = ctA ∧
      sk.length = 3168 ∧ ct.length = 1568 ∧ ¬ Kyber1024DecapsTerminates sk⌝ ∗
      (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968

private theorem blk06_decaps_diverge_safe_ok :
    MlKemBlockSafeOk 6 (fun mpl => withMlKemRoOk mpl (falsePostSpec blk06DecapsDivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC06 blkPl06 rfl rfl fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
    fun ⟨ret, skA, sk, ctA, ct⟩ s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, blk06DecapsDivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx0, hx1, hx2, hsk, hct, hNotTerm⟩ => ?_
  have hNotMat : ¬ Shake128MatrixTerminates (pkRho ((sk.drop 1536).take 1568)) 4 := by
    rw [pkRho_sk_eq sk]; exact hNotTerm
  refine SafeSepWP.weaken_pre
    (safeSepWP_of_sepWP_env hcl0 hro0
      (seg1_to_4_ok hb hbase s0 ret skA ctA sk ct (memRegion ret 32 ∗ emp)
        hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hsk hct) ?_)
    (by sep_frame)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx9_4, hx20_4, hx22_4, hx23_4, hx25_4, hx26_4, hfp4, hv0_4, hv1_4, hP4⟩
  exact SafeSepWP.weaken_pre
    (seg5_sample_matrix_diverge_safe_ok hb hbase (pkRho_sk_len hsk) hNotMat
      hpc4 hrun4 hsp4 hspA4 (sp_aligned_chk hsp4 hspA4) hcl4 hro4
      hx9_4 hx20_4 hx22_4 hx23_4 hx25_4 hx26_4 hfp4 hv0_4 hv1_4)
    hP4

section Blk23Fetches
set_option linter.literalFetch false
gen_placed_fetches blkPC23 blkLib23 blkTree23 blk23_code_eq blk23_tree_size
  via_placement blkPl23 blkPlaceable23 [0x0 → 0xc]
end Blk23Fetches

private theorem blk23_prologue_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl23 b) (hbase : blkPl23.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (P : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = ret) (hx0 : s0.readReg64 .x0 = skA)
    (hx1 : s0.readReg64 .x1 = ctA) :
    SepWP (blkPC23.rebase b (fun _ => none)) (mlkemMpl.base 6) s0 P
      (sepPost (fun s1 =>
        s1.mem = s0.mem ∧ s1.sp = s0.sp ∧ s1.spAligned = s0.spAligned ∧
        s1.readReg64 .lr = s0.readReg64 .lr ∧
        s1.readReg64 .x0 = ret ∧ s1.readReg64 .x1 = skA ∧
        s1.readReg64 .x2 = ctA ∧
        CalleeSavedPreserved s0 s1) P) := by
  have _ := hb
  subst hbase
  simp only [Reg.x8, Reg.x0, Reg.x1] at hx8 hx0 hx1
  wp_steps 4
  refine SepWP.done
    (by simp [wp_norm, arm64_norm, blkPl23, MultiPlacedLib.blockPlacement])
    (by simp [hrun]) ?_
  rw [sepPost_apply]
  refine ⟨⟨rfl, by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [CalleeSavedPreserved, wp_norm, arm64_norm]⟩, Entails.refl P⟩

private def kyberDecapsDivPre :
    (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) → State → SepProp :=
  fun (ret, skA, sk, ctA, ct) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = skA ∧ s0.readReg64 .x1 = ctA ∧
      sk.length = 3168 ∧ ct.length = 1568 ∧ ¬ Kyber1024DecapsTerminates sk⌝ ∗
      (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968

private theorem blk23_kyber_decaps_diverge_safe_ok :
    MlKemBlockSafeOk 23 (fun mpl => withMlKemRoOk mpl (falsePostSpec kyberDecapsDivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC23 blkPl23 rfl rfl fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
    fun ⟨ret, skA, sk, ctA, ct⟩ s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, kyberDecapsDivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx8, hx0, hx1, hsk, hct, hNotTerm⟩ => ?_
  refine SafeSepWP.of_sepWP (SepWP.mono
    (blk23_prologue_wp hb hbase s0 ret skA ctA
      ((skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968)
      hpc hrun hx8 hx0 hx1) ?_)
  intro s1 P1 hpc1 hrun1 hp1; rw [sepPost_apply] at hp1
  rcases hp1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, _hcs1⟩, hP1⟩
  refine SafeSepWP.weaken_pre
    (SafeSepWP.call_subroutine_frame
      (mlkemSafeCall_of_blockSafeOk (blkPC23.rebase b (fun _ => none)) blk06_decaps_diverge_safe_ok)
      (x := (ret, skA, sk, ctA, ct))
      (P := (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968)
      (F := emp)
      hpc1 hrun1 (hspA1.trans hsp0) hlr1
      (fun R1 hm1 => by
        dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
          falsePostSpec, blk06DecapsDivPre]
        rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
            satisfies_pure_sepConj]
        refine ⟨hmem1 ▸ hcl0, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨hmem1 ▸ hro0, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0_1, hx1_1, hx2_1, hsk, hct, hNotTerm⟩, ?_⟩
        rw [hsp1, emp_sepConj]
        exact Satisfies.mono (by sep_frame) hm1)
      (fun _sf _ _ _ _ _R1 hm_false => False.elim (not_satisfies_false_sepConj (by
        dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
          falsePostSpec] at hm_false
        rw [sepConj_assoc] at hm_false
        exact hm_false))))
    (Entails.trans hP1 (by sep_frame))

/-! ## 4. Layer 1 Real-ELF Divergence Theorems for `lsKyber1024DecapsSym` -/

/-- Step-witnessed operational divergence for `lsKyber1024DecapsSym` (`B23`,
    `mlkem1024::kyber::decapsulate`) under `kemDecapsAtSpec` when
    `¬ KemDecapsStateTerminates u`. -/
theorem kemDecaps_diverge_of_not_stateTerminates_step
    {stk : Nat} (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : KemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (kemDecapsAtSpec stk Q)).pre x u ∗ R)
    (hNotTerm : ¬ KemDecapsStateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) := by
  have hpre_at : u.mem ⊨ (kemDecapsAtSpec stk Q).pre x u ∗ R := by
    simpa only [keepsFs] using hpre
  rcases x with ⟨skA, sk, ctA, ct, ret⟩
  have hNotCall : ¬ Kyber1024DecapsTerminates sk.toList := by
    intro hCall
    exact hNotTerm ((kemDecapsStateTerminates_iff_of_atSpec_pre hpre_at).mpr hCall)
  dsimp only [kemDecapsAtSpec, withStack] at hpre_at
  simp only [sepConj_assoc] at hpre_at
  rw [satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx0, hx1, hx8⟩, hspat⟩ := hpre_at
  have hstk35968 : 35968 ≤ stk := hstk
  rw [stackAt_shrink u.sp stk 35968 hstk35968 hfit] at hspat
  set slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 35968)
  have hpre_div : u.mem ⊨
      kyberDecapsDivPre (ret, skA, sk.toList, ctA, ct.toList) u ∗ (slack ∗ R) := by
    dsimp only [kyberDecapsDivPre]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, sk.toList_length, ct.toList_length, hNotCall⟩,
      Satisfies.mono (by sep_frame) hspat⟩
  exact c2_mlkem_diverge_of_blockSafeOk_false (by decide) blk23_kyber_decaps_diverge_safe_ok
    (by rintro ⟨_, _, _, _, _⟩ s _; cases s; rfl)
    hLs hExt (c2_resolve_kyber1024Decaps_eq hLs) W hpc hrun hsp hInv hFr hpre_div

/-- Layer 1 operational divergence for `lsKyber1024DecapsSym` (`B23`,
    `mlkem1024::kyber::decapsulate`): every state `v` reachable from a stuck entry `u` has
    `v.status = .Running`. -/
theorem kemDecaps_diverge_of_not_stateTerminates
    {stk : Nat} (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : KemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (kemDecapsAtSpec stk Q)).pre x u ∗ R)
    (hNotTerm : ¬ KemDecapsStateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running) := by
  have ⟨h1, h2⟩ := kemDecaps_diverge_of_not_stateTerminates_step hstk hfit hLs hExt W
    hpc hrun hsp hInv hFr hpre hNotTerm
  exact ⟨fun v hv => (h1 v hv).1, fun v hv => (h2 v hv).1⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Kyber1024Decaps
