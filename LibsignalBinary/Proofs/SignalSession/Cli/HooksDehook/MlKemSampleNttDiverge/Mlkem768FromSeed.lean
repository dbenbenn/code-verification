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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
meta import ProofLib.GenPlacedFetches

/-!
# Per-Row Real-Run Divergence for `B10` → `B05` (`<KeyPairCompressedBytes>::from_seed`)

Proves `mlkemFromSeed_diverge_of_not_stateTerminates` (and `_step`): when execution enters
`lsMlkem768FromSeedSym` (`B10`, `33,664` B tight stack) at `u` with `(keepsFs (mlkemFromSeedAtSpec stk
mlkem768Incremental)).pre x u ∗ R` and `¬ MlkemFromSeedStateTerminates u`, every reachable state `v` on
both `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `Placed.cliProgPlacedSig mpl mmpl W`
has `v.status = .Running` (and a `Step` successor).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768FromSeed

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open CryptoVerification.LibsignalSpqrV1 (MlKem MlkemFromSeedCall)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  mlkemFromSeedAtSpec withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem memRegion_entails_exists_treeMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 SavedFrame10 blk10_code_eq blk10_tree_size blkLib10 blkPC05 blkPC10
  blkPl05 blkPl10 blkPlaceable10 blkTree10 cell_entails_memRegion8
  mlkem768FromSeedTerminates_iff_list sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (BTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG (
  Seg1Post Seg1Spatial seg1_prologue_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  B05LateSlots Seg2ConstSlots entails_sub sepWP_elim_cell8
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi (
  RowPolyOut seg2_epi_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  Seg2ConstWordsInv Seg2RegInv Seg2RowDone entry_treeMem_join seg2_row_header_lt3
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowLoop (
  seg2_row_safe_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockSafeOk MlKemPlacement mlkemCall_of_blockOk mlkemMpl
  mlkemSafeCall_of_blockSafeOk mlkemSafeCaller_ok resolve_blk05 resolve_blk29 seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Shake128MatrixTerminates mlkem768Incremental sha3_512List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakSponge)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2_resolve_mlkem768FromSeed_eq lsMlkem768FromSeedSym
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers (
  MlkemFromSeedStateTerminates mlkemFromSeedStateTerminates_iff_of_atSpec_pre
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Common (
  c2_mlkem_diverge_of_blockSafeOk_false falsePostSpec matrixTerminates3_of_rows_ij
  safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  mlkemFromSeedTightStack
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

section Blk05Seg2Diverge
attribute [local irreducible] blkPC05 TreeMem RowPolyOut

/-! ## 1. `B05` (`generate_keypair_compressed`) Segment 2 Matrix Divergence (`¬ Shake128MatrixTerminates`) -/

private theorem sha3_512List_take32_len (msg : List (BitVec 8)) :
    ((sha3_512List msg).take 32).length = 32 := by
  have h64 : (sha3_512List msg).length = 64 := by simp [sha3_512List, keccakSponge]
  simp [h64]

private theorem sepWP_elim_treeMem {prog : Program} {tgt : BitVec 64} {s : State}
    {ptr : BitVec 64} {len : Nat} (hlen : len ≤ 512) {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ t : BTree (BitVec 64) 9, SepWP prog tgt s (TreeMem ptr len t ∗ R) post oom) :
    SepWP prog tgt s (memRegion ptr (8 * len) ∗ R) post oom :=
  SepWP.weaken_pre (sepConj_mono_left (memRegion_entails_exists_treeMem hlen))
    (SepWP.of_sepExists_left h)

private theorem memRegion_432_split (sp : BitVec 64) :
    memRegion (sp + 432#64) 3312 =
      memRegion (sp + 432#64) (8 * 222) ∗ memRegion (sp + 2208#64) 1536 :=
  memRegion_split' (b := sp + 432#64) (b' := sp + 2208#64) (n := 1776) (k := (1536 : Nat))
    rfl (by bv_omega) (by decide)

private def RowCells (sp : BitVec 64) (row : Nat) : SepProp :=
  memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗
  memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗
  memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512

private theorem memRegion_3744_split9 (sp : BitVec 64) :
    memRegion (sp + 3744#64) 4608 =
      RowCells sp 0 ∗ RowCells sp 1 ∗ RowCells sp 2 := by
  unfold RowCells
  have split1536 (base : BitVec 64) :
      memRegion base 1536 =
        memRegion (base + 0#64) 512 ∗ memRegion (base + 512#64) 512 ∗
          memRegion (base + 1024#64) 512 := by
    rw [BitVec.add_zero,
      memRegion_split' (b := base) (b' := base + 512#64) (n := 512) (k := (1024 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := base + 512#64) (b' := base + 1024#64) (n := 512) (k := (512 : Nat))
        rfl (by bv_omega) (by decide)]
  rw [memRegion_split' (b := sp + 3744#64) (b' := sp + 5280#64) (n := 1536) (k := (3072 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5280#64) (b' := sp + 6816#64) (n := 1536) (k := (1536 : Nat))
        rfl (by bv_omega) (by decide),
      split1536 (sp + 3744#64), split1536 (sp + 5280#64), split1536 (sp + 6816#64)]
  simp only [show sp + 5280#64 + 0#64 = sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0) by bv_omega,
    show sp + 5280#64 + 512#64 = sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 1) by bv_omega,
    show sp + 5280#64 + 1024#64 = sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 2) by bv_omega,
    show sp + 6816#64 + 0#64 = sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0) by bv_omega,
    show sp + 6816#64 + 512#64 = sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 1) by bv_omega,
    show sp + 6816#64 + 1024#64 = sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 2) by bv_omega,
    show sp + 3744#64 + 0#64 = sp + 3744#64 + BitVec.ofNat 64 (512 * 0) from rfl,
    show sp + 3744#64 + 512#64 = sp + 3744#64 + BitVec.ofNat 64 (512 * 1) from rfl,
    show sp + 3744#64 + 1024#64 = sp + 3744#64 + BitVec.ofNat 64 (512 * 2) from rfl]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private def Seg2ScratchIdle (sp : BitVec 64) : SepProp :=
  memRegion (sp + 8352#64) 1632 ∗
  memRegion (sp + 11496#64) 5880 ∗
  memRegion (sp + 19008#64) 8832 ∗
  memRegion (sp + 28360#64) 664 ∗
  memRegion (sp + 29048#64) 360

private theorem memRegion_8352_split (sp : BitVec 64) :
    memRegion (sp + 8352#64) 21056 =
      memRegion (sp + 9984#64) 1512 ∗
      memRegion (sp + 17376#64) 1632 ∗
      memRegion (sp + 27840#64) 504 ∗
      memRegion (sp + 28344#64) 16 ∗
      memRegion (sp + 29024#64) 24 ∗
      Seg2ScratchIdle sp := by
  unfold Seg2ScratchIdle
  rw [memRegion_split' (b := sp + 8352#64) (b' := sp + 9984#64) (n := 1632) (k := (19424 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 9984#64) (b' := sp + 11496#64) (n := 1512) (k := (17912 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11496#64) (b' := sp + 17376#64) (n := 5880) (k := (12032 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 17376#64) (b' := sp + 19008#64) (n := 1632) (k := (10400 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19008#64) (b' := sp + 27840#64) (n := 8832) (k := (1568 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 27840#64) (b' := sp + 28344#64) (n := 504) (k := (1064 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28344#64) (b' := sp + 28360#64) (n := 16) (k := (1048 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28360#64) (b' := sp + 29024#64) (n := 664) (k := (384 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 29024#64) (b' := sp + 29048#64) (n := 24) (k := (360 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem constWords_t5 {sp : BitVec 64} {rho : List (BitVec 8)} {tA : BTree (BitVec 64) 9}
    (h : Seg2ConstWordsInv sp rho tA) : tA.get 5 = sp + 27851#64 := by
  rcases h with ⟨_, _, _, _, h5, _⟩; exact h5

private theorem seg1Post_to_seg2 [MlKemPlacement] {s0 s : State} (hp : Seg1Post s0 s) :
    Seg2RegInv (s0.sp - 30080#64) (s0.sp - 96#64) s ∧ s.readReg64 .x1 = 0#64 := by
  rcases hp with ⟨hsp, hal, hfp, hx1, hx19, hx20, hx21, hx23, hx24, hx26, hx27, hx28⟩
  exact ⟨⟨⟨hsp, hal, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩, hx20, hx23⟩, hx1⟩

private def Seg2IdlePassthrough (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗
    (sp ↦ₛ g.take 32) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
    memRegion (sp + 2208#64) 1536 ∗ Seg2ScratchIdle sp ∗
    ((sp + 29408#64) ↦ₛ g.drop 32) ∗ memRegion (sp + 29440#64) 480 ∗ F

private theorem entry_spatial_prep (s0 : State) (seedA outPtr w4 : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) (tMid tHi : BTree (BitVec 64) 9) :
    let sp := s0.sp - 30080#64
    let rho := (sha3_512List (seed.take 32 ++ [3#8])).take 32
    ∃ tA0 : BTree (BitVec 64) 9,
      Seg2ConstWordsInv sp rho tA0 ∧
      (TreeMem (sp + 432#64) 222 tHi ∗ TreeMem (sp + 144#64) 26 tMid ∗ ((sp + 96#64) ↦₆₄ w4) ∗
        (SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗
          ((sp ↦ₛ rho) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
            ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
            ((sp + 29408#64) ↦ₛ (sha3_512List (seed.take 32 ++ [3#8])).drop 32) ∗
            memRegion (sp + 29440#64) 480) ∗
          Seg2ConstSlots sp rho ∗ memRegion (sp + 2208#64) 1536 ∗
          memRegion (sp + 3744#64) 4608 ∗ memRegion (sp + 8352#64) 21056 ∗ F) ⊢
        TreeMem (sp + 64#64) 268 tA0 ∗ memRegion (sp + 9984#64) 1512 ∗
          memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
          memRegion (sp + 29024#64) 24 ∗
          (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
            memRegion (sp + 28344#64) 16 ∗
            memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * 0)) 512 ∗
            memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0)) 512 ∗
            memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0)) 512 ∗
            (RowCells sp 1 ∗ RowCells sp 2 ∗ Seg2IdlePassthrough s0 seedA outPtr seed F))) := by
  intro sp rho
  rcases entry_treeMem_join sp w4 rho tMid tHi with ⟨tA0, htA0, hjoin⟩
  refine ⟨tA0, htA0, ?_⟩
  rw [memRegion_3744_split9 sp]
  unfold RowCells Seg2IdlePassthrough
  rw [memRegion_8352_split sp]
  exact entails_sub
    (A := Seg2ConstSlots sp rho ∗ ((sp + 96#64) ↦₆₄ w4) ∗ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
      TreeMem (sp + 144#64) 26 tMid ∗ TreeMem (sp + 432#64) 222 tHi)
    (B := ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
      TreeMem (sp + 64#64) 268 tA0)
    (by rw [hjoin]; exact Entails.refl _) (by sep_frame) (by sep_frame)

private theorem seg2_epi_lt3_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hr2 : row < 2)
    {s : State} {P : SepProp}
    (hexit : Seg2RowDone b sp fpVal rho row
      (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
        memRegion (sp + 28344#64) 16 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512 ∗ Rest) s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02b8#64) s P
      (fun sf Pf =>
        sf.pc = b + 0x02b8#64 ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2RegInv sp fpVal sf ∧ sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
        ∃ tA : BTree (BitVec 64) 9, Seg2ConstWordsInv sp rho tA ∧
          (Pf ⊢ TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
            memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
            memRegion (sp + 29024#64) 24 ∗
            (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
              memRegion (sp + 28344#64) 16 ∗ RowPolyOut sp rho row ∗ Rest))) := by
  refine SepWP.seq (seg2_epi_ok hb hbase (by omega) hexit) ?_
  rintro sh Ph hpch hrunh ⟨hclh, hroh, hgbh, hx1h, tA, htA, hPh⟩
  refine sepWP_seq_env hclh hroh
    (SepWP.weaken_pre
      (Entails.trans hPh (show _ ⊢ TreeMem (sp + 64#64) 268 tA ∗ _ by sep_frame))
      (seg2_row_header_lt3 hb hbase sh sp fpVal (row + 1) tA _ (by omega) (constWords_t5 htA)
        hpch hrunh hgbh hx1h)) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hregf, hx1f, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hpcf, hrunf, hclf, hrof, hregf, hx1f, tA, htA, Entails.trans hPf (by sep_frame)⟩

private theorem seg2_matrix_diverge_safe_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    (hNotMat : ¬ Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3)
    (hpc : s.pc = b + 0x02b8#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpost : Seg1Post s0 s) :
    SafeSepWP (blkPC05.rebase b (fun _ => none)) s
      (Seg1Spatial s0 seedA outPtr seed F)
      (fun _ _ => False) := by
  let sp := s0.sp - 30080#64
  let rho := (sha3_512List (seed.take 32 ++ [3#8])).take 32
  have hrho : rho.length = 32 := sha3_512List_take32_len _
  rcases seg1Post_to_seg2 hpost with ⟨hreg0, hx1_0⟩
  refine SafeSepWP.of_sepWP (mid := s.pc) ?_
  dsimp only [Seg1Spatial, B05LateSlots]
  rw [memRegion_432_split sp, show (208 : Nat) = 8 * 26 from rfl]
  refine SepWP.weaken_pre (P' := memRegion (sp + 96#64) 8 ∗
    (memRegion (sp + 144#64) (8 * 26) ∗ memRegion (sp + 432#64) (8 * 222) ∗ _)) (by sep_frame) ?_
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 96#64)); intro w4
  refine SepWP.weaken_pre (P' := memRegion (sp + 144#64) (8 * 26) ∗ _) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 26) (by decide) fun tMid => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 432#64) (8 * 222) ∗ _) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 222) (by decide) fun tHi => ?_
  rcases entry_spatial_prep s0 seedA outPtr w4 seed F tMid tHi with ⟨tA0, htA0, hprep⟩
  refine SepWP.done rfl hrun ?_
  let idle := Seg2IdlePassthrough s0 seedA outPtr seed F
  let FRow (r : Nat) (R : SepProp) : SepProp :=
    ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
      memRegion (sp + 28344#64) 16 ∗
      memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * r)) 512 ∗
      memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * r)) 512 ∗
      memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * r)) 512 ∗ R
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safe_ok hb hbase hrho (row := 0) (by decide) htA0
      (F := FRow 0 (RowCells sp 1 ∗ RowCells sp 2 ∗ idle)) hpc hrun hcl hro hreg0 hx1_0)
    fun sm0 Pm0 hex0 => ?_)
    (Entails.trans (by sep_frame) hprep)
  obtain ⟨e0, _, _, _, hd0, _⟩ := hex0.2.2.2.2.2.2.2
  refine SafeSepWP.of_sepWP <| SepWP.mono
    (seg2_epi_lt3_ok hb hbase (row := 0) (Rest := RowCells sp 1 ∗ RowCells sp 2 ∗ idle) (by decide) hex0) ?_
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx1_1, tA1, htA1, hP1⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safe_ok hb hbase hrho (row := 1) (by decide) htA1
      (F := FRow 1 (RowPolyOut sp rho 0 ∗ RowCells sp 2 ∗ idle)) hpc1 hrun1 hcl1 hro1 hreg1 hx1_1)
    fun sm1 Pm1 hex1 => ?_)
    (Entails.trans hP1 (by dsimp only [FRow, RowCells]; sep_frame))
  obtain ⟨e1, _, _, _, hd1, _⟩ := hex1.2.2.2.2.2.2.2
  refine SafeSepWP.of_sepWP <| SepWP.mono
    (seg2_epi_lt3_ok hb hbase (row := 1) (Rest := RowPolyOut sp rho 0 ∗ RowCells sp 2 ∗ idle) (by decide) hex1) ?_
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx1_2, tA2, htA2, hP2⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safe_ok hb hbase hrho (row := 2) (by decide) htA2
      (F := FRow 2 (RowPolyOut sp rho 1 ∗ RowPolyOut sp rho 0 ∗ idle)) hpc2 hrun2 hcl2 hro2 hreg2 hx1_2)
    fun _ _ hex2 => ?_)
    (Entails.trans hP2 (by dsimp only [FRow, RowCells]; sep_frame))
  obtain ⟨e2, _, _, _, hd2, _⟩ := hex2.2.2.2.2.2.2.2
  exact False.elim (hNotMat (matrixTerminates3_of_rows_ij hd0 hd1 hd2))

end Blk05Seg2Diverge

/-! ## 2. `B05` & `B10` Block-Level Divergence Contracts (`MlKemBlockSafeOk`) -/

private def mlkemGenKeypairDivPre :
    (BitVec 64 × List (BitVec 8) × BitVec 64) → State → SepProp :=
  fun (seedA, seed, outPtr) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x1 = outPtr ∧
      seed.length = 64 ∧
      ¬ Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion outPtr 2400 ∗ stackAt s0.sp 31216

private theorem blk05_generate_keypair_diverge_safe_ok :
    MlKemBlockSafeOk 5 (fun mpl => withMlKemRoOk mpl (falsePostSpec mlkemGenKeypairDivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC05 blkPl05 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨seedA, seed, outPtr⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    falsePostSpec, mlkemGenKeypairDivPre] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hseed, hNotMat⟩, hspat⟩ := hpre
  refine ⟨stackAt s0.sp 31216 ∗ (seedA ↦ₛ seed) ∗ memRegion outPtr 2400,
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine SafeSepWP.of_sepWP (mid := b + 0x02b8#64) <| sepWP_seq_env hcl0 hro0
    (seg1_prologue_ok hb hbase s0 seedA outPtr seed (memRegion outPtr 2400)
      hseed hpc hrun hsp0 hx0 hx1 hcl0 hro0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hpost1, hP1⟩
  refine SepWP.done hpc1 hrun1 ?_
  exact SafeSepWP.weaken_pre
    ((seg2_matrix_diverge_safe_ok hb hbase s0 s1 seedA outPtr seed (memRegion outPtr 2400)
        hNotMat hpc1 hrun1 hcl1 hro1 hpost1).mono fun _ _ hf => False.elim hf)
    hP1

private theorem blk10_hP [MlKemPlacement] :
    blkPC10 = (mlkemMultiLib.blockLib 10).program blkPl10 := rfl

section
set_option linter.literalFetch false
gen_placed_fetches blkPC10 blkLib10 blkTree10 blk10_code_eq blk10_tree_size
  via_placement blkPl10 blkPlaceable10 [0 → 92]
end

@[local simp, local arm64_norm, local wp_norm]
private theorem blkPl10_ρ [MlKemPlacement] (sym : String) :
    blkPl10.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkLib10

private theorem stackAt33664_split (sp0 : BitVec 64) :
    stackAt sp0 33664 =
      stackAt (sp0 - 2448#64) 31216 ∗
      memRegion (sp0 - 2448#64) 2400 ∗
      memRegion (sp0 - 48#64) 48 := by
  dsimp only [stackAt]
  have hsub : sp0 - 2448#64 - 31216#64 = sp0 - 33664#64 := by bv_omega
  change memRegion (sp0 - 33664#64) 33664 =
    memRegion (sp0 - 2448#64 - 31216#64) 31216 ∗
    memRegion (sp0 - 2448#64) 2400 ∗
    memRegion (sp0 - 48#64) 48
  rw [hsub,
    memRegion_split' (b := sp0 - 33664#64) (b' := sp0 - 2448#64) (n := 31216) (k := (2448 : Nat))
      rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp0 - 2448#64) (b' := sp0 - 48#64) (n := 2400) (k := 48)
      rfl (by bv_omega) (by omega)]

private theorem replicate_entails_memRegion (a : BitVec 64) (n : Nat) :
    (a ↦ₛ List.replicate n 0#8) ⊢ memRegion a n := by
  have h := pointsToBytes_entails_memRegion a (List.replicate n 0#8)
  rwa [List.length_replicate] at h

private theorem memRegion48_save_split (sp0 : BitVec 64) :
    memRegion (sp0 - 48#64) 48 =
      memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
      memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
      memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
  rw [memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]

private theorem blk10_pre_b05_wp [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl10 b) (hbase : blkPl10.base = b)
    (s0 : State) (seedA kpA : BitVec 64) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = seedA) (hx8 : s0.readReg64 .x8 = kpA)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) :
    SepWP (blkPC10.rebase b (fun _ => none)) (mlkemMpl.base 5) s0
      (memRegion (s0.sp - 2448#64) 2400 ∗ memRegion (s0.sp - 48#64) 48 ∗ F)
      (fun s1 P1 =>
        s1.sp = s0.sp - 2448#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .lr = b + 0x003c#64 ∧
        s1.readReg64 .x0 = seedA ∧
        s1.readReg64 .x1 = s0.sp - 2448#64 ∧
        (P1 ⊢ memRegion (s0.sp - 2448#64) 2400 ∗ SavedFrame10 s0.sp s0 ∗ F)) := by
  subst hbase
  have hsp1_chk : ((s0.sp - 2448#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub s0.sp 2448#64 hsp0 (by decide)
  rw [memRegion48_save_split s0.sp,
    memRegion_split' (b := s0.sp - 2448#64) (b' := s0.sp - 2440#64) (n := 8) (k := (2392 : Nat))
      rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 2448#64)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 48#64)); intro cfp
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 40#64)); intro clr
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 32#64)); intro c28
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 16#64)); intro c20
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 8#64)); intro c19
  wp_cut_codeLoaded
  wp_steps 12
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun]
  intro hcl_pre
  have hfold2400 : ((s0.sp - 2448#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 2440#64) 2392 ⊢
      memRegion (s0.sp - 2448#64) 2400 := by
    rw [memRegion_split' (b := s0.sp - 2448#64) (b' := s0.sp - 2440#64) (n := 8) (k := (2392 : Nat))
      rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 _ _)
  refine SepWP.weaken_pre (entails_sub hfold2400 (by sep_frame) (by sep_frame)) ?_
  wp_mlkem_call blk29_memset_ok (s0.sp - 2448#64, 0#8, 2400)
  have hsp_sf_al : sf.spAligned = true := by simpa [State.spAligned, hsp_sf] using hsp1_chk
  refine SepWP.weaken_pre
    (entails_sub (replicate_entails_memRegion (s0.sp - 2448#64) 2400) (by sep_frame) (by sep_frame)) ?_
  wp_steps 3
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun_sf]
  refine ⟨by simpa using hsp_sf, hsp_sf_al, rfl, rfl, rfl, ?_⟩
  dsimp only [SavedFrame10]
  have ha48 : s0.sp + 0xffffffffffffffd0#64 = s0.sp - 48#64 := by bv_omega
  have ha40 : s0.sp + 0xffffffffffffffd0#64 + 8#64 = s0.sp - 40#64 := by bv_omega
  have ha32 : s0.sp + 0xffffffffffffffd0#64 + 16#64 = s0.sp - 32#64 := by bv_omega
  have ha16 : s0.sp + 0xffffffffffffffd0#64 + 32#64 = s0.sp - 16#64 := by bv_omega
  have ha8  : s0.sp + 0xffffffffffffffd0#64 + 40#64 = s0.sp - 8#64 := by bv_omega
  sep_frame

private def mlkemFromSeedDivPre :
    (BitVec 64 × List (BitVec 8) × BitVec 64) → State → SepProp :=
  fun (seedA, seed, kpA) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x8 = kpA ∧
      seed.length = 64 ∧
      ¬ Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion kpA 2400 ∗ stackAt s0.sp 33664

private theorem blk10_from_seed_diverge_safe_ok :
    MlKemBlockSafeOk 10 (fun mpl => withMlKemRoOk mpl (falsePostSpec mlkemFromSeedDivPre)) := by
  intro _
  refine mlkemSafeCaller_ok blkPC10 blkPl10 rfl blk10_hP fun b hb hbase => ?_
  refine safe_subroutine_ok_withMlKemRoOk_falsePostSpec_of_safeSepWP
    fun ⟨seedA, seed, kpA⟩ s0 hpc hrun hsp0 hcl0 => ?_
  dsimp only [ToBaseSpec.toSpec, withMlKemRoOk, falsePostSpec, mlkemFromSeedDivPre]
  refine SafeSepWP.pure_elim fun hro0 => ?_
  refine SafeSepWP.pure_elim fun ⟨hx0, hx8, hseed, hNotMat⟩ => ?_
  rw [stackAt33664_split s0.sp]
  set F0 : SepProp :=
    (seedA ↦ₛ seed) ∗ stackAt (s0.sp - 2448#64) 31216 ∗ memRegion kpA 2400
  refine SafeSepWP.weaken_pre (P := memRegion (s0.sp - 2448#64) 2400 ∗ memRegion (s0.sp - 48#64) 48 ∗ F0)
    ?_ (by dsimp only [F0]; sep_frame)
  refine SafeSepWP.of_sepWP (mid := mlkemMpl.base 5) <| sepWP_seq_env hcl0 hro0
    (blk10_pre_b05_wp hb hbase s0 seedA kpA F0 hpc hrun hsp0 hx0 hx8 hcl0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hlr1, hx0_1, hx1_1, hP1⟩
  refine SepWP.done hpc1 hrun1 ?_
  refine SafeSepWP.weaken_pre
    (SafeSepWP.call_subroutine_frame
      (mlkemSafeCall_of_blockSafeOk (blkPC10.rebase b (fun _ => none))
        blk05_generate_keypair_diverge_safe_ok)
      (x := (seedA, seed, s0.sp - 2448#64))
      (F := memRegion kpA 2400 ∗ SavedFrame10 s0.sp s0)
      (ret_pc := b + 0x003c#64) hpc1 hrun1 hspA1 hlr1
      (fun R1 hm1 => ?_)
      (fun sf _ _ _ _ R1 hm_false => False.elim (not_satisfies_false_sepConj (by
        dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
          falsePostSpec] at hm_false
        rw [sepConj_assoc] at hm_false
        exact hm_false))))
    hP1
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    falsePostSpec, mlkemGenKeypairDivPre, F0] at hm1 ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
  refine ⟨hcl1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hro1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_1, hx1_1, hseed, hNotMat⟩, ?_⟩
  rw [hsp1]
  exact Satisfies.mono (by sep_frame) hm1

/-! ## 3. Layer 1 Real-ELF Divergence Theorems for `lsMlkem768FromSeedSym` -/

/-- Step-witnessed operational divergence for `lsMlkem768FromSeedSym` (`B10`, `<KeyPairCompressedBytes>::from_seed`)
    when `¬ MlkemFromSeedStateTerminates u`. -/
theorem mlkemFromSeed_diverge_of_not_stateTerminates_step
    {stk : Nat} (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : MlkemFromSeedCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (mlkemFromSeedAtSpec stk K)).pre x u ∗ R)
    (hNotTerm : ¬ MlkemFromSeedStateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) v w) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running ∧
        ∃ w : State, Step (cliProgPlacedSig mpl mmpl W) v w) := by
  have hpre_at : u.mem ⊨ (mlkemFromSeedAtSpec stk K).pre x u ∗ R := by
    simpa only [keepsFs] using hpre
  have hNotCall : ¬ Shake128MatrixTerminates ((sha3_512List (x.seed.toList.take 32 ++ [3#8])).take 32) 3 := by
    intro hMat
    exact hNotTerm ((mlkemFromSeedStateTerminates_iff_of_atSpec_pre hpre_at).mpr
      (mlkem768FromSeedTerminates_iff_list.mpr hMat))
  dsimp only [mlkemFromSeedAtSpec] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx0, hx8⟩, hspat⟩ := hpre_at
  have hstk33664 : 33664 ≤ stk := hstk
  rw [stackAt_shrink u.sp stk 33664 hstk33664 hfit] at hspat
  set slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 33664)
  have hpre_div : u.mem ⊨ mlkemFromSeedDivPre (x.seedA, x.seed.toList, x.kpA) u ∗ (slack ∗ R) := by
    dsimp only [mlkemFromSeedDivPre]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, x.seed.toList_length, hNotCall⟩, Satisfies.mono (by sep_frame) hspat⟩
  exact c2_mlkem_diverge_of_blockSafeOk_false (by decide) blk10_from_seed_diverge_safe_ok
    (by intro ⟨_, _, _⟩ s _; cases s; rfl)
    hLs hExt (c2_resolve_mlkem768FromSeed_eq hLs) W hpc hrun hsp hInv hFr hpre_div

/-- Layer 1 operational divergence for `lsMlkem768FromSeedSym` (`B10`, `<KeyPairCompressedBytes>::from_seed`):
    every state `v` reachable from a stuck entry `u` has `v.status = .Running`. -/
theorem mlkemFromSeed_diverge_of_not_stateTerminates
    {stk : Nat} (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks)
    {x : MlkemFromSeedCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hpre : u.mem ⊨ (keepsFs (mlkemFromSeedAtSpec stk K)).pre x u ∗ R)
    (hNotTerm : ¬ MlkemFromSeedStateTerminates u) :
    (∀ v : State, Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      v.status = .Running) ∧
    (∀ v : State, Steps (cliProgPlacedSig mpl mmpl W) u v →
      v.status = .Running) := by
  have ⟨h1, h2⟩ := mlkemFromSeed_diverge_of_not_stateTerminates_step hstk hfit hLs hExt W
    hpc hrun hsp hInv hFr hpre hNotTerm
  exact ⟨fun v hv => (h1 v hv).1, fun v hv => (h2 v hv).1⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge.Mlkem768FromSeed
