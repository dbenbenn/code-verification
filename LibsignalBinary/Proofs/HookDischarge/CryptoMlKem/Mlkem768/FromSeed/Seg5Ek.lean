/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3

/-!
# `generate_keypair_compressed` (`B05`) — Segment 5a `ek` Assembly & `SHA3-256(ek)` (`+0x60fc .. +0x666c`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl
  resolve_blk02 resolve_blk28 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6 (blk02_keccak2_136_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (memRegion32_cells)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteEncode polyAdd polyNtt sampleMatrixWith sampleNtt sampleVecCbd2
  sha3_256List sha3_512List shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdDup_8h_gpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At VecRangeMem bytesToVecNat pointsToBytes_eq_vecRangeMem polyVecNat
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  entails_sub sepWP_elim_bytes sepWP_elim_cell8 sepWP_elim_vec128 vec128At_entails_memRegion16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi (RowPolyOut)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix (AMatrixMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (SHatMem cbdNttPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3 (EHatMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec (
  Seg4Exit THatMem off60fc tHatPoly16 tHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser (
  orr_12_eq_add_12 polyAdd_canonical polyBounded16_mono ser12Prefix
  ser12Prefix_16_eq_byteEncode step_dead_stpQ_reg)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops (
  LoopPres seg5_loop1 seg5_loop2 seg5_loop3)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [24828 → 25188, 25344 → 25396]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local irreducible] blkLib05 dup8x16 polyVecNat ser12Prefix
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 svc_simdDup_8h_gpr

@[simp, arm64_norm, wp_norm] abbrev off666c : BitVec 64 := BitVec.ofNat 64 26220

theorem spAligned_mod16 {s : State} {sp : BitVec 64} (hsp : s.sp = sp) (hal : s.spAligned = true) :
    sp.toNat % 16 = 0 := by
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hal
  have hand : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hchk
  have hnat := congrArg BitVec.toNat hand
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at hnat
  change sp.toNat &&& (2 ^ 4 - 1) = 0 at hnat
  rwa [Nat.and_two_pow_sub_one_eq_mod] at hnat

theorem spAligned_of_chk {s : State} {sp : BitVec 64}
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true) : s.spAligned = true := by
  simpa [State.spAligned, hsp] using hchk

theorem setPC_setMem_self {s : State} {p : BitVec 64} (hpc : s.pc = p) :
    (s.setPC p).setMem s.mem = s := by
  cases s; subst hpc; rfl

theorem step_dead_strQ_sp {prog : Program} {b target_pc sp : BitVec 64}
    {s : State} {m : Memory} {Rest : SepProp} {post : State → SepProp → Prop}
    (baseOff total pcOff nextOff subOff offLit : Nat) (vt : BitVec 5)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 offLit))))
    (hnextOff : pcOff + 4 = nextOff) (hoff : baseOff + subOff = offLit)
    (hbounds : subOff + 16 ≤ total) (htotal : total ≤ 2 ^ 64)
    (hcont : ∀ m' : Memory,
      SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
        (memRegion (sp + BitVec.ofNat 64 baseOff) total ∗ Rest) post) :
    SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (memRegion (sp + BitVec.ofNat 64 baseOff) total ∗ Rest) post := by
  have hea : (sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 subOff =
      sp + BitVec.ofNat 64 offLit := by subst hoff; bv_omega
  have hpc_next : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine step_strQ128_region (pc := b + BitVec.ofNat 64 pcOff)
    rfl hrun hfetch hspA (by simp [evalAddrMode, hsp]) hbounds htotal hea fun m' => ?_
  rw [hpc_next]; exact hcont m'

theorem polyMem_entails_memRegion512 (ptr : BitVec 64) (f : Nat → BitVec 128) :
    PolyMem ptr f ⊢ memRegion ptr 512 :=
  vecRangeMem_entails_memRegion 32 ptr f

theorem cells32_entails_memRegion (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      memRegion a 32 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := (24 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := a + 16#64) (n := 8) (k := (16 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := a + 24#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by omega)]
  exact entails_sub (cell_entails_memRegion8 a v0) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (a + 8#64) v1) (by sep_frame)
      (entails_sub (cell_entails_memRegion8 (a + 16#64) v2) (by sep_frame)
        (entails_sub (cell_entails_memRegion8 (a + 24#64) v3) (by sep_frame) (by sep_frame))))

theorem vec2_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    let v0 := bytesToVecNat bs 0
    let v1 := bytesToVecNat bs 1
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1
  rw [pointsToBytes_eq_vecRangeMem 2 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, Nat.zero_add]
  rw [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

theorem stackAt_1136_split_1040 (sp : BitVec 64) :
    stackAt sp 1136 = stackAt sp 1040 ∗ memRegion (sp - 1136#64) 96 := by
  unfold stackAt
  have hb : sp - BitVec.ofNat 64 1136 = sp - 1136#64 := rfl
  have hb' : sp - BitVec.ofNat 64 1040 = sp - 1040#64 := rfl
  rw [hb, hb', memRegion_split' (b := sp - 1136#64) (b' := sp - 1040#64) (n := 96) (k := (1040 : Nat))
    rfl (by bv_omega) (by omega)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

theorem eHatMem_entails_memRegion (sp : BitVec 64) (sigma : List (BitVec 8)) :
    EHatMem sp sigma ⊢ memRegion (sp + 17376#64) 1536 := by
  unfold EHatMem
  rw [memRegion_split' (b := sp + 17376#64) (b' := sp + 17888#64) (n := 512) (k := (1024 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 17888#64) (b' := sp + 18400#64) (n := 512) (k := (512 : Nat))
        rfl (by bv_omega) (by decide)]
  exact entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
    (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
      (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame) (by sep_frame)))

theorem aMatrixMem_entails_memRegion (sp : BitVec 64) (rho : List (BitVec 8)) :
    AMatrixMem sp rho ⊢ memRegion (sp + 3744#64) 4608 := by
  unfold AMatrixMem RowPolyOut
  have h00 : sp + 3744#64 + BitVec.ofNat 64 (512 * 0) = sp + 3744#64 := by bv_omega
  have h10 : sp + 3744#64 + BitVec.ofNat 64 (512 * 1) = sp + 4256#64 := by bv_omega
  have h20 : sp + 3744#64 + BitVec.ofNat 64 (512 * 2) = sp + 4768#64 := by bv_omega
  have h01 : sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0) = sp + 5280#64 := by bv_omega
  have h11 : sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 1) = sp + 5792#64 := by bv_omega
  have h21 : sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 2) = sp + 6304#64 := by bv_omega
  have h02 : sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0) = sp + 6816#64 := by bv_omega
  have h12 : sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 1) = sp + 7328#64 := by bv_omega
  have h22 : sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 2) = sp + 7840#64 := by bv_omega
  rw [h00, h10, h20, h01, h11, h21, h02, h12, h22]
  rw [memRegion_split' (b := sp + 3744#64) (b' := sp + 4256#64) (n := 512) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4256#64) (b' := sp + 4768#64) (n := 512) (k := (3584 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4768#64) (b' := sp + 5280#64) (n := 512) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5280#64) (b' := sp + 5792#64) (n := 512) (k := (2560 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5792#64) (b' := sp + 6304#64) (n := 512) (k := (2048 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 6304#64) (b' := sp + 6816#64) (n := 512) (k := (1536 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 6816#64) (b' := sp + 7328#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 7328#64) (b' := sp + 7840#64) (n := 512) (k := (512 : Nat)) rfl (by bv_omega) (by decide)]
  exact entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
    (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
      (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
        (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
          (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
            (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
              (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
                (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
                  (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame) (by sep_frame)))))))))

theorem tHatPoly16_ser12 {rho sigma : List (BitVec 8)}
    (hrho : rho.length = 32) (hsig : sigma.length = 32) {col : Nat} (hcol : col < 3) :
    let aMat := sampleMatrixWith sampleNtt 3 rho true
    let sHat := (sampleVecCbd2 3 sigma 0).map polyNtt
    let eHat := (sampleVecCbd2 3 sigma 3).map polyNtt
    let tPoly := polyAdd (vecDotNtt 3 (aMat.getD col #[]) sHat) (eHat.getD col zeroPoly)
    PolyBounded16 3328 (tHatPoly16 rho sigma col) ∧
    ser12Prefix (tHatPoly16 rho sigma col) 16 = byteEncode 12 tPoly := by
  dsimp only
  obtain ⟨hbnd1664, hrep⟩ := tHatPoly16_spec hrho hsig hcol
  have hbnd3328 : PolyBounded16 3328 (tHatPoly16 rho sigma col) :=
    polyBounded16_mono (by decide : (1664 : Int) ≤ 3328) hbnd1664
  exact ⟨hbnd3328, ser12Prefix_16_eq_byteEncode hbnd3328 hrep (polyAdd_canonical _ _)⟩

theorem replicate_entails_memRegion (a : BitVec 64) (n : Nat) :
    (a ↦ₛ List.replicate n 0#8) ⊢ memRegion a n := by
  simpa [List.length_replicate] using pointsToBytes_entails_memRegion a (List.replicate n 0#8)

theorem call_bytes_memcpy [MlKemPlacement] {b target_pc retPC dst src : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {n : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mlkemMpl.base 28) (hrun : s.status = .Running) (hspA : s.spAligned = true)
    (hlr : s.readReg64 .lr = retPC) (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 n)
    (hlen : bs.length = n) (hn : n < 2 ^ 64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hcont : ∀ sf : State, sf.pc = retPC → sf.status = .Running → LoopPres s sf →
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem →
      SepWP (blkPC05.rebase b (fun _ => none)) target_pc sf
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ Rest) post) :
    SepWP (blkPC05.rebase b (fun _ => none)) target_pc s
      (memRegion dst n ∗ (src ↦ₛ bs) ∗ Rest) post := by
  have hlt : bs.length < 2 ^ 64 := by omega
  have hx2' : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by rw [hlen, hx2]
  refine SepWP.weaken_pre (P' := memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ Rest)
    (by rw [hlen]; sep_frame) ?_
  wp_mlkem_call blk28_memcpy_ok (dst, src, bs)
  have hlp : LoopPres s sf := ⟨hsp_sf, by simp [State.spAligned, hsp_sf], hcs_sf, h, h_1, h_2, h_3⟩
  exact SepWP.weaken_pre (by sep_frame) (hcont sf hpc_sf hrun_sf hlp ‹_›)

theorem call_dead_memcpy [MlKemPlacement] {b target_pc retPC baseD baseS dst src : BitVec 64}
    {s : State} {totD offD totS offS n : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mlkemMpl.base 28) (hrun : s.status = .Running) (hspA : s.spAligned = true)
    (hlr : s.readReg64 .lr = retPC) (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 n)
    (hdst : baseD + BitVec.ofNat 64 offD = dst) (hsrc : baseS + BitVec.ofNat 64 offS = src)
    (hbD : offD + n ≤ totD) (htD : totD ≤ 2 ^ 64) (hbS : offS + n ≤ totS) (htS : totS ≤ 2 ^ 64)
    (hn : n < 2 ^ 64) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hcont : ∀ sf : State, sf.pc = retPC → sf.status = .Running → LoopPres s sf →
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem →
      SepWP (blkPC05.rebase b (fun _ => none)) target_pc sf
        (memRegion baseD totD ∗ memRegion baseS totS ∗ Rest) post) :
    SepWP (blkPC05.rebase b (fun _ => none)) target_pc s
      (memRegion baseD totD ∗ memRegion baseS totS ∗ Rest) post := by
  have hsD1 : memRegion baseD totD =
      memRegion baseD offD ∗ memRegion dst (totD - offD) := by
    rw [← hdst]
    have h := memRegion_split baseD offD (totD - offD) (by omega)
    rwa [Nat.add_sub_of_le (show offD ≤ totD by omega)] at h
  have hsD2 : memRegion dst (totD - offD) =
      memRegion dst n ∗ memRegion (dst + BitVec.ofNat 64 n) (totD - offD - n) := by
    have h := memRegion_split dst n (totD - offD - n) (by omega)
    rwa [show n + (totD - offD - n) = totD - offD by omega] at h
  have hsS1 : memRegion baseS totS =
      memRegion baseS offS ∗ memRegion src (totS - offS) := by
    rw [← hsrc]
    have h := memRegion_split baseS offS (totS - offS) (by omega)
    rwa [Nat.add_sub_of_le (show offS ≤ totS by omega)] at h
  have hsS2 : memRegion src (totS - offS) =
      memRegion src n ∗ memRegion (src + BitVec.ofNat 64 n) (totS - offS - n) := by
    have h := memRegion_split src n (totS - offS - n) (by omega)
    rwa [show n + (totS - offS - n) = totS - offS by omega] at h
  refine SepWP.weaken_pre (show memRegion baseD totD ∗ memRegion baseS totS ∗ Rest ⊢
      memRegion src n ∗ (memRegion dst n ∗ memRegion baseD offD ∗
        memRegion (dst + BitVec.ofNat 64 n) (totD - offD - n) ∗ memRegion baseS offS ∗
        memRegion (src + BitVec.ofNat 64 n) (totS - offS - n) ∗ Rest) by
    rw [hsD1, hsD2, hsS1, hsS2]; sep_frame) ?_
  refine sepWP_elim_bytes n (by omega) fun bs hbs => ?_
  refine SepWP.weaken_pre (show (src ↦ₛ bs) ∗ (memRegion dst n ∗ _) ⊢
      memRegion dst n ∗ (src ↦ₛ bs) ∗ _ by sep_frame) ?_
  refine call_bytes_memcpy hpc hrun hspA hlr hx0 hx1 hx2 hbs hn hcl fun sf hpcsf hrunsf hlp hclsf => ?_
  refine SepWP.weaken_pre ?_ (hcont sf hpcsf hrunsf hlp hclsf)
  rw [hsD1, hsD2, hsS1, hsS2]
  have hmD : (dst ↦ₛ bs) ⊢ memRegion dst n := by rw [← hbs]; exact pointsToBytes_entails_memRegion _ _
  have hmS : (src ↦ₛ bs) ⊢ memRegion src n := by rw [← hbs]; exact pointsToBytes_entails_memRegion _ _
  exact entails_sub hmD (by sep_frame) (entails_sub hmS (by sep_frame) (by sep_frame))

theorem call_dead_memset [MlKemPlacement] {b target_pc retPC baseD dst : BitVec 64}
    {s : State} {totD offD n : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mlkemMpl.base 29) (hrun : s.status = .Running) (hspA : s.spAligned = true)
    (hlr : s.readReg64 .lr = retPC) (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 n)
    (hdst : baseD + BitVec.ofNat 64 offD = dst)
    (hbD : offD + n ≤ totD) (htD : totD ≤ 2 ^ 64) (hn : n < 2 ^ 64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hcont : ∀ sf : State, sf.pc = retPC → sf.status = .Running → LoopPres s sf →
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem →
      SepWP (blkPC05.rebase b (fun _ => none)) target_pc sf
        (memRegion baseD totD ∗ Rest) post) :
    SepWP (blkPC05.rebase b (fun _ => none)) target_pc s
      (memRegion baseD totD ∗ Rest) post := by
  have hsD1 : memRegion baseD totD =
      memRegion baseD offD ∗ memRegion dst (totD - offD) := by
    rw [← hdst]
    have h := memRegion_split baseD offD (totD - offD) (by omega)
    rwa [Nat.add_sub_of_le (show offD ≤ totD by omega)] at h
  have hsD2 : memRegion dst (totD - offD) =
      memRegion dst n ∗ memRegion (dst + BitVec.ofNat 64 n) (totD - offD - n) := by
    have h := memRegion_split dst n (totD - offD - n) (by omega)
    rwa [show n + (totD - offD - n) = totD - offD by omega] at h
  refine SepWP.weaken_pre (show memRegion baseD totD ∗ Rest ⊢
      memRegion dst n ∗ (memRegion baseD offD ∗ memRegion (dst + BitVec.ofNat 64 n) (totD - offD - n) ∗ Rest) by
    rw [hsD1, hsD2]; sep_frame) ?_
  wp_mlkem_call blk29_memset_ok (dst, 0#8, n)
  have hlp : LoopPres s sf := ⟨hsp_sf, by simp [State.spAligned, hsp_sf], hcs_sf, h, h_1, h_2, h_3⟩
  refine SepWP.weaken_pre ?_ (hcont sf hpc_sf hrun_sf hlp ‹_›)
  rw [hsD1, hsD2]
  exact entails_sub (replicate_entails_memRegion dst n) (by sep_frame) (by sep_frame)

@[simp] theorem extractLsb64_lo_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[simp] theorem extractLsb64_hi_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

@[simp] theorem truncate64_append (hi lo : BitVec 64) :
    (hi ++ lo).truncate 64 = lo := by bv_bits

theorem seg5_dead_shuffle [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (rho : List (BitVec 8)) (hrho : rho.length = 32)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 24828) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 25068) s
      ((sp ↦ₛ rho) ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
        memRegion (sp + 8352#64) 32 ∗ memRegion (sp + 17376#64) 4608 ∗
        memRegion (sp + 3744#64) 4608 ∗ memRegion (sp + 9984#64) 1184 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 8352#64 ∧ sf.readReg64 .x20 = sp + 2208#64 ∧
        (Pf ⊢ (sp ↦ₛ rho) ∗ ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
          memRegion (sp + 17376#64) 4608 ∗ memRegion (sp + 3744#64) 4608 ∗
          memRegion (sp + 9984#64) 1184 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine SepWP.weaken_pre (show (sp ↦ₛ rho) ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
        memRegion (sp + 8352#64) 32 ∗ _ ⊢
      memRegion (sp + 8352#64) 32 ∗ ((sp ↦ₛ rho) ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ _) by
    sep_frame) ?_
  apply memRegion32_cells (sp + 8352#64); intro c0 c1 c2 c3
  refine SepWP.weaken_pre
    (P' := ((sp + 8352#64) ↦₆₄ c0) ∗ ((sp + 8360#64) ↦₆₄ c1) ∗
      ((sp + 8368#64) ↦₆₄ c2) ∗ ((sp + 8376#64) ↦₆₄ c3) ∗
      (sp ↦₆₄ (bytesToVecNat rho 0).extractLsb' 0 64) ∗
      ((sp + 8#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 64 64) ∗
      ((sp + 16#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 0 64) ∗
      ((sp + 24#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 64 64) ∗
      ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ memRegion (sp + 17376#64) 4608 ∗
      memRegion (sp + 3744#64) 4608 ∗ memRegion (sp + 9984#64) 1184 ∗ Rest)
    (by rw [← vec2_cells_eq_bytes sp hrho]; simp only [bitvec64_add_add_fold]; sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 14
  apply SepWP.done; · wp_norm_lhs
  · simp [hrun]
  intro hcl0
  refine SepWP.weaken_pre (P' := memRegion (sp + 17376#64) 4608 ∗ memRegion (sp + 3744#64) 4608 ∗
      (memRegion (sp + 9984#64) 1184 ∗ (sp ↦ₛ rho) ∗ ((sp + 8352#64) ↦ₛ rho) ∗
        ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ Rest))
    (by
      rw [← vec2_cells_eq_bytes sp hrho, ← vec2_cells_eq_bytes (sp + 8352#64) hrho]
      simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate]
      sep_frame) ?_
  refine call_dead_memcpy (dst := sp + 17376#64) (src := sp + 3744#64)
    (offD := 0) (offS := 0) (n := 512)
    (by wp_norm_lhs) (by simp [hrun]) (spAligned_of_chk (by simp [hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl0
    fun s1 hpc1 hrun1 hlp1 hcl1 => ?_
  wp_steps 4
  refine call_dead_memcpy (dst := sp + 17888#64) (src := sp + 5280#64)
    (offD := 512) (offS := 1536) (n := 512)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hlp1.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, hlp1.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, hlp1.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have lp2 := hlp1.trans hlp2; wp_steps 5
  refine call_dead_memcpy (dst := sp + 18400#64) (src := sp + 6816#64)
    (offD := 1024) (offS := 3072) (n := 512)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [lp2.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp2.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp2.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl2
    fun s3 hpc3 hrun3 hlp3 hcl3 => ?_
  have lp3 := lp2.trans hlp3; wp_steps 4
  refine call_dead_memcpy (dst := sp + 18912#64) (src := sp + 4256#64)
    (offD := 1536) (offS := 512) (n := 512)
    (by wp_norm_lhs) (by simp [hrun3]) (spAligned_of_chk (by simp [lp3.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp3.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp3.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl3
    fun s4 hpc4 hrun4 hlp4 hcl4 => ?_

  have lp4 := lp3.trans hlp4; wp_steps 4
  refine call_dead_memcpy (dst := sp + 19424#64) (src := sp + 5792#64)
    (offD := 2048) (offS := 2048) (n := 512)
    (by wp_norm_lhs) (by simp [hrun4]) (spAligned_of_chk (by simp [lp4.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp4.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp4.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl4
    fun s5 hpc5 hrun5 hlp5 hcl5 => ?_
  have lp5 := lp4.trans hlp5; wp_steps 5
  refine call_dead_memcpy (dst := sp + 19936#64) (src := sp + 7328#64)
    (offD := 2560) (offS := 3584) (n := 512)
    (by wp_norm_lhs) (by simp [hrun5]) (spAligned_of_chk (by simp [lp5.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp5.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp5.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl5
    fun s6 hpc6 hrun6 hlp6 hcl6 => ?_
  have lp6 := lp5.trans hlp6; wp_steps 4
  refine call_dead_memcpy (dst := sp + 20448#64) (src := sp + 4768#64)
    (offD := 3072) (offS := 1024) (n := 512)
    (by wp_norm_lhs) (by simp [hrun6]) (spAligned_of_chk (by simp [lp6.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp6.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp6.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl6
    fun s7 hpc7 hrun7 hlp7 hcl7 => ?_
  have lp7 := lp6.trans hlp7; wp_steps 4
  refine call_dead_memcpy (dst := sp + 20960#64) (src := sp + 6304#64)
    (offD := 3584) (offS := 2560) (n := 512)
    (by wp_norm_lhs) (by simp [hrun7]) (spAligned_of_chk (by simp [lp7.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp7.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp7.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl7
    fun s8 hpc8 hrun8 hlp8 hcl8 => ?_
  have lp8 := lp7.trans hlp8; wp_steps 5
  refine call_dead_memcpy (dst := sp + 21472#64) (src := sp + 7840#64)
    (offD := 4096) (offS := 4096) (n := 512)
    (by wp_norm_lhs) (by simp [hrun8]) (spAligned_of_chk (by simp [lp8.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp8.2.2.2.2.2.1])
    (by simp [wp_norm, arm64_norm, lp8.2.2.2.2.1]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl8
    fun s9 hpc9 hrun9 hlp9 hcl9 => ?_
  have lp9 := lp8.trans hlp9
  refine SepWP.weaken_pre (show memRegion (sp + 17376#64) 4608 ∗ memRegion (sp + 3744#64) 4608 ∗ _ ⊢
      memRegion (sp + 3744#64) 4608 ∗ memRegion (sp + 17376#64) 4608 ∗ _ by sep_frame) ?_
  wp_steps 5
  refine call_dead_memcpy (dst := sp + 3744#64) (src := sp + 17376#64)
    (offD := 0) (offS := 0) (n := 4608)
    (by wp_norm_lhs) (by simp [hrun9]) (spAligned_of_chk (by simp [lp9.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp9.2.2.2.2.2.2])
    (by simp [wp_norm, arm64_norm, lp9.1, hsp]) (by wp_norm_lhs)
    (by bv_omega) (by bv_omega) (by decide) (by decide) (by decide) (by decide) (by decide) hcl9
    fun s10 hpc10 hrun10 hlp10 hcl10 => ?_
  have lp10 := lp9.trans hlp10
  refine SepWP.weaken_pre (show memRegion (sp + 3744#64) 4608 ∗ memRegion (sp + 17376#64) 4608 ∗
        (memRegion (sp + 9984#64) 1184 ∗ _) ⊢
      memRegion (sp + 9984#64) 1184 ∗ (memRegion (sp + 3744#64) 4608 ∗
        memRegion (sp + 17376#64) 4608 ∗ _) by sep_frame) ?_
  wp_steps 6
  refine call_dead_memset (dst := sp + 10368#64) (offD := 384) (n := 800)
    (by wp_norm_lhs) (by simp [hrun10]) (spAligned_of_chk (by simp [lp10.1, hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm, lp10.1, hsp])
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by bv_omega) (by decide) (by decide) (by decide) hcl10
    fun sf hpcsf hrunsf hlpf _ => ?_
  have lpf := lp10.trans hlpf
  refine SepWP.done hpcsf hrunsf ⟨by simp [lpf.1, hsp],
    spAligned_of_chk (by simp [lpf.1, hsp]) hchk, by simp [lpf.2.2.1, hfp],
    by simp [lpf.2.2.2.1], by simp [lpf.2.2.2.2.1], by sep_frame⟩

theorem enter_mem_block {prog : Program} {target_pc : BitVec 64} (sp p : BitVec 64)
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = p) (hrun : s.status = .Running) (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcont : s.status = .Running → s.sp = sp → s.spAligned = true →
      SepWP prog target_pc ((s.setPC p).setMem s.mem) P post) :
    SepWP prog target_pc s P post := by
  rw [← setPC_setMem_self hpc]
  exact hcont hrun hsp hspA

local macro "step_strQ_sp " baseOff:num total:num pcOff:num nextOff:num subOff:num offLit:num vt:term:arg : tactic => `(tactic| (
  refine step_dead_strQ_sp $baseOff $total $pcOff $nextOff $subOff $offLit $vt
    ‹_› ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) (by omega) ?_
  intro _))

local macro "step_stpQ_reg " rn:term:arg total:num pcOff:num nextOff:num off:num vt1:term:arg vt2:term:arg : tactic => `(tactic| (
  refine step_dead_stpQ_reg $rn $total $pcOff $nextOff $off $vt1 $vt2
    (by decide) ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) ?_
  intro _))

theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h1
      (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

theorem seg5_ek_col0 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x19v : BitVec 64) (p0 : Poly16)
    (hbnd0 : PolyBounded16 3328 p0) (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 25068) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = x19v) (hx20 : s.readReg64 .x20 = sp + 2208#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 25400) s
      (PolyMem (sp + 2208#64) (polyVecNat p0) ∗
        memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 9984#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = x19v ∧ sf.readReg64 .x20 = sp + 27840#64 ∧
        (Pf ⊢ PolyMem (sp + 2208#64) (polyVecNat p0) ∗
          ((sp + 9984#64) ↦ₛ ser12Prefix p0 16) ∗
          memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
          memRegion (sp + 29024#64) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hmod : sp.toNat % 16 = 0 := spAligned_mod16 hsp hspA
  have horr : (sp + 27840#64) ||| 12#64 = sp + 27852#64 := orr_12_eq_add_12 hmod 27840 (by decide)
  refine SepWP.weaken_pre (show PolyMem (sp + 2208#64) (polyVecNat p0) ∗
        memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        (PolyMem (sp + 2208#64) (polyVecNat p0) ∗ _) by sep_frame) ?_
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 25192) hcl ?_
  wp_steps 7
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 25096)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_chk (by simp [hsp]) hchk) ?_
  intro hrun0 hsp0 hspA0
  step_strQ_sp 27840 384 25096 25100 368 28208 1#5; step_strQ_sp 27840 384 25100 25104 352 28192 1#5
  step_strQ_sp 27840 384 25104 25108 336 28176 1#5; step_strQ_sp 27840 384 25108 25112 320 28160 1#5
  step_strQ_sp 27840 384 25112 25116 304 28144 1#5; step_strQ_sp 27840 384 25116 25120 288 28128 1#5
  step_strQ_sp 27840 384 25120 25124 272 28112 1#5; step_strQ_sp 27840 384 25124 25128 256 28096 1#5
  step_strQ_sp 27840 384 25128 25132 240 28080 1#5; step_strQ_sp 27840 384 25132 25136 224 28064 1#5
  step_strQ_sp 27840 384 25136 25140 208 28048 1#5; step_strQ_sp 27840 384 25140 25144 192 28032 1#5
  step_strQ_sp 27840 384 25144 25148 176 28016 1#5; step_strQ_sp 27840 384 25148 25152 160 28000 1#5
  step_strQ_sp 27840 384 25152 25156 144 27984 1#5; step_strQ_sp 27840 384 25156 25160 128 27968 1#5
  step_strQ_sp 27840 384 25160 25164 112 27952 1#5; step_strQ_sp 27840 384 25164 25168 96 27936 1#5
  step_strQ_sp 27840 384 25168 25172 80 27920 1#5; step_strQ_sp 27840 384 25172 25176 64 27904 1#5
  step_strQ_sp 27840 384 25176 25180 48 27888 1#5; step_strQ_sp 27840 384 25180 25184 32 27872 1#5
  step_strQ_sp 27840 384 25184 25188 16 27856 1#5; step_strQ_sp 27840 384 25188 25192 0 27840 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        (PolyMem (sp + 2208#64) (polyVecNat p0) ∗
          memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 9984#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 2208#64) (polyVecNat p0) ∗ memRegion (sp + 27840#64) 384 ∗
        (memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 9984#64) 384 ∗ Rest) by
    sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop1 hb (sp + 2208#64) (sp + 27840#64) p0 hbnd0 _ _ rfl hrun0
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx20]) (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  have hsp1 : s1.sp = sp := by simpa [hsp] using hlp1.1
  have hx19_1 : s1.readReg64 .x19 = x19v := by simpa [hx19] using hlp1.2.2.2.1
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 2208#64) (polyVecNat p0) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 9984#64) 384 ∗ Rest) ⊢
      memRegion (sp + 29024#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + 9984#64) 384 ∗ PolyMem (sp + 2208#64) (polyVecNat p0) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 8
  refine call_bytes_memcpy (dst := sp + 29024#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [Seg5Ser.ser12Prefix_length]) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have hsp2 : s2.sp = sp := by simpa [hsp1] using hlp2.1
  refine SepWP.weaken_pre (show ((sp + 29024#64) ↦ₛ ser12Prefix p0 16) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + 9984#64) 384 ∗ PolyMem (sp + 2208#64) (polyVecNat p0) ∗ Rest) ⊢
      memRegion (sp + 9984#64) 384 ∗ ((sp + 29024#64) ↦ₛ ser12Prefix p0 16) ∗
        (((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗ PolyMem (sp + 2208#64) (polyVecNat p0) ∗ Rest) by
    sep_frame) ?_
  wp_steps 6
  refine call_bytes_memcpy (dst := sp + 9984#64) (src := sp + 29024#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [Seg5Ser.ser12Prefix_length]) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  have hsp_sf : sf.sp = sp := by simpa [hlp2.1, hsp1] using hlpf.1
  have hm29 : ((sp + 29024#64) ↦ₛ ser12Prefix p0 16) ⊢ memRegion (sp + 29024#64) 384 := by
    simpa [Seg5Ser.ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 29024#64) (ser12Prefix p0 16)
  have hm27 : ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ⊢ memRegion (sp + BitVec.ofNat 64 27840) 384 := by
    simpa [Seg5Ser.ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p0 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf,
    spAligned_of_chk hsp_sf hchk,
    by simpa [hlp2.2.2.1, hlp1.2.2.1, hfp] using hlpf.2.2.1,
    by simpa [hlp2.2.2.2.1, hx19_1] using hlpf.2.2.2.1,
    by simpa [hlp2.2.2.2.2.1, wp_norm, arm64_norm, hsp1] using hlpf.2.2.2.2.1,
    entails_sub hm29 (by sep_frame) (entails_sub hm27 (by sep_frame) (by sep_frame))⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek
