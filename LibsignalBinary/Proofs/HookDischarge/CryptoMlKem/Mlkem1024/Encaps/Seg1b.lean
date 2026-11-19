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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b2

/-!
# `kyber_encapsulate` (`B07`) — Segment 1b (`+0x02c0 .. +0x0758`)

- `Seg1bSpatial` and `Seg1bPost`: canonical stack-frame invariant at `+0x0758`, holding
  deserialized `tHat[0..3]` at `[sp + 21024 .. sp + 23072)` and `rho` lane vectors in `v0, v1, v2`.
- `seg1b_ok`: full Segment 1b composition (`+0x02c0 → +0x0758`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_256List sha3_512List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem
  SepWP.of_memRegion_vecRangeMem
  Vec128At
  VecRangeMem
  polyVecNat
  vecRangeMem_entails_memRegion
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07
  blkPC07
  blkPl07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (SpilledMsgWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a (
  Seg1aPost
  Seg1aSpatial
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0
  pkEk0_len
  pkEk1
  pkEk1_len
  pkEk2
  pkEk2_len
  pkEk3
  pkEk3_len
  pkRho
  pkRho_len
  pk_pointsTo_split
  rhoW
  rho_pointsTo_eq_vec128
  tHatModPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1 (
  seg1b_copy0_zero1
  seg1b_copy1
  seg1b_init_zero0
  seg1b_loop0
  seg1b_loop1
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b2 (
  seg1b_copy2_zero3
  seg1b_copy3_rho
  seg1b_loop2
  seg1b_loop3
  seg1b_zero2
)

attribute [local irreducible] blkPC07 SpilledMsgWords sha3_256List sha3_512List

/-- Canonical spatial invariant at `+0x0758` (`Seg2` entry). -/
@[expose] def Seg1bSpatial (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) : SepProp :=
  (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗
  stackAt sp 1136 ∗
  memRegion sp 8 ∗
  ((sp + 8#64) ↦₆₄ ret) ∗
  SpilledMsgWords sp (sha3_256List rand) ∗
  memRegion (sp + 144#64) 72 ∗
  ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
  memRegion (sp + 224#64) 2272 ∗
  ((sp + 2496#64) ↦ₛ sha3_512List (sha3_256List rand ++ sha3_256List pk)) ∗
  memRegion (sp + 2560#64) 10272 ∗
  memRegion (sp + 12832#64) 8192 ∗
  PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
  PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
  PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
  PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
  ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗
  memRegion (sp + 23104#64) 9840 ∗
  SavedFrame07 sp0 s0

/-- Register + spatial postcondition at `+0x0758` (`Seg2` entry). -/
@[expose] def Seg1bPost (sp0 : BitVec 64) (s0 : State)
    (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := sp0 - 33104#64
  sf.sp = sp ∧
  sf.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  sf.readReg64 .x9 = sp + 28859#64 ∧
  sf.readReg64 .x19 = sp + 2560#64 ∧
  sf.readReg64 .x20 = pkA ∧
  sf.readReg64 .x22 = sp + 26768#64 ∧
  sf.readReg64 .x23 = sp + 26779#64 ∧
  sf.readReg64 .x24 = sp + 27032#64 ∧
  sf.readReg64 .x26 = sp + 2560#64 ∧
  sf.readReg64 .fp = sp + 33008#64 ∧
  sf.readVReg128 0#5 = rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 1 ∧
  sf.readVReg128 1#5 = rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2 ∧
  sf.readVReg128 2#5 = rhoW (pkRho pk) 0 ++ rhoW (pkRho pk) 0 ∧
  (Pf ⊢ Seg1bSpatial sp0 s0 sp ret pkA rA pk rand ∗ Rest)

private theorem seg1b_regions_eq (sp : BitVec 64) :
    (memRegion (sp + 224#64) 2272 =
      memRegion (sp + 224#64) 2192 ∗ memRegion (sp + 2416#64) 16 ∗ memRegion (sp + 2432#64) 64) ∧
    (memRegion (sp + 2560#64) 10272 =
      memRegion (sp + 2560#64) 512 ∗ memRegion (sp + 3072#64) 9760) ∧
    (memRegion (sp + 21024#64) 2048 =
      memRegion (sp + 21024#64) 512 ∗ memRegion (sp + 21536#64) 512 ∗
      memRegion (sp + 22048#64) 512 ∗ memRegion (sp + 22560#64) 512) := by
  refine ⟨?_,
    memRegion_split' (b := sp + 2560#64) (b' := sp + 3072#64) (n := 512) (k := (9760 : Nat))
      rfl (by bv_omega) (by decide), ?_⟩
  · rw [memRegion_split' (b := sp + 224#64) (b' := sp + 2416#64) (n := (2192 : Nat)) (k := 80)
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2416#64) (b' := sp + 2432#64) (n := 16) (k := 64)
        rfl (by bv_omega) (by decide)]
  · rw [memRegion_split' (b := sp + 21024#64) (b' := sp + 21536#64) (n := 512) (k := (1536 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 21536#64) (b' := sp + 22048#64) (n := 512) (k := (1024 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22048#64) (b' := sp + 22560#64) (n := 512) (k := 512)
        rfl (by bv_omega) (by decide)]

private theorem vec128At_entails_memRegion16 (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v ⊢ memRegion ptr 16 := by
  have h := vecRangeMem_entails_memRegion 1 ptr (fun _ => v)
  simpa [VecRangeMem, sepConj_emp] using h

private theorem pk_split_rho_vec {pkA : BitVec 64} {pk : List (BitVec 8)} (hpk : pk.length = 1568) :
    (pkA ↦ₛ pk) =
      (pkA ↦ₛ pkEk0 pk) ∗ ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
      ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
      Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
      Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) := by
  have ha : (pkA + 1536#64) + 16#64 = pkA + 1552#64 := by bv_omega
  rw [pk_pointsTo_split hpk, rho_pointsTo_eq_vec128 (pkRho_len hpk), ha]

private def Seg1bFrame (sp0 : BitVec 64) (s0 : State)
    (sp ret rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp) : SepProp :=
  (rA ↦ₛ rand) ∗
  stackAt sp 1136 ∗
  memRegion sp 8 ∗
  ((sp + 8#64) ↦₆₄ ret) ∗
  SpilledMsgWords sp (sha3_256List rand) ∗
  memRegion (sp + 144#64) 72 ∗
  ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
  memRegion (sp + 224#64) 2192 ∗
  memRegion (sp + 2432#64) 64 ∗
  ((sp + 2496#64) ↦ₛ sha3_512List (sha3_256List rand ++ sha3_256List pk)) ∗
  memRegion (sp + 3072#64) 9760 ∗
  memRegion (sp + 12832#64) 8192 ∗
  ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗
  memRegion (sp + 23104#64) 9840 ∗
  SavedFrame07 sp0 s0 ∗
  Rest

private theorem seg1aSpatial_to_seg1b (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568) :
    Seg1aSpatial sp0 s0 sp ret pkA rA pk rand ∗ Rest ⊢
      memRegion (sp + 2560#64) 512 ∗
      ((pkA ↦ₛ pkEk0 pk) ∗ ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
        Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
        memRegion (sp + 2416#64) 16 ∗
        memRegion (sp + 21024#64) 512 ∗ memRegion (sp + 21536#64) 512 ∗
        memRegion (sp + 22048#64) 512 ∗ memRegion (sp + 22560#64) 512 ∗
        Seg1bFrame sp0 s0 sp ret rA pk rand Rest) := by
  unfold Seg1aSpatial Seg1bFrame
  obtain ⟨hr1, hr2, hr3⟩ := seg1b_regions_eq sp
  rw [pk_split_rho_vec hpk, hr1, hr2, hr3]
  sep_frame

private theorem seg1b_to_seg1bSpatial (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568) :
    Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
      Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
      PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
      memRegion (sp + 2560#64) 512 ∗
      (((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
        PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗
        PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (pkA ↦ₛ pkEk0 pk) ∗
        Seg1bFrame sp0 s0 sp ret rA pk rand Rest) ⊢
      Seg1bSpatial sp0 s0 sp ret pkA rA pk rand ∗ Rest := by
  have hv := vec128At_entails_memRegion16 (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hv)))))) ?_
  unfold Seg1bSpatial Seg1bFrame
  obtain ⟨hr1, hr2, _⟩ := seg1b_regions_eq sp
  rw [pk_split_rho_vec hpk, hr1, hr2]
  sep_frame

attribute [local irreducible] Seg1bFrame

theorem seg1b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp0 : BitVec 64) (s0 : State) (ret pkA rA : BitVec 64)
    (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568)
    (s : State) (P : SepProp)
    (hpc : s.pc = b + 0x02c0#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hpre : Seg1aPost sp0 s0 ret pkA rA pk rand Rest s P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0758#64) s P
      (Seg1bPost sp0 s0 ret pkA rA pk rand Rest) := by
  let sp := sp0 - 33104#64
  rcases hpre with ⟨hsp, _hspA, hsp_chk, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hfp, hP⟩
  refine SepWP.weaken_pre (Entails.trans hP
    (seg1aSpatial_to_seg1b sp0 s0 sp ret pkA rA pk rand Rest hpk)) ?_
  refine sepWP_seq_env hcl hro (seg1b_init_zero0 hb hbase s sp pkA _ hpc hrun hsp hsp_chk hcl hro hx20) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hfp1,
      hv0_1, hv1_1, hv6_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 2560#64) (by decide) rfl ?_
  intro f0
  refine SepWP.weaken_pre (show PolyMem (sp + 2560#64) f0 ∗ _ ⊢
      (pkA ↦ₛ pkEk0 pk) ∗ PolyMem (sp + 2560#64) f0 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1 (seg1b_loop0 hb pkA (sp + 2560#64) (pkEk0 pk) _
    (pkEk0_len hpk) 15 0 rfl s1 f0 hpc1 hrun1 hspA1
    (by simp [hx9_1]) (by simp [hx8_1]) (hx23_1.trans hx23)
    hv1_1 hv0_1 hv6_1 (fun _ hj => by omega)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, _hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx26_2, hfp2, hv6_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢ memRegion (sp + 2416#64) 16 ∗
      (memRegion (sp + 21024#64) 512 ∗ PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (((pkA + 384#64) ↦ₛ pkEk1 pk) ∗ ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗
          ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
          Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
          Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
          memRegion (sp + 21536#64) 512 ∗ memRegion (sp + 22048#64) 512 ∗
          memRegion (sp + 22560#64) 512 ∗ (pkA ↦ₛ pkEk0 pk) ∗
          Seg1bFrame sp0 s0 sp ret rA pk rand Rest)) by sep_frame)) ?_
  refine SepWP.of_memRegion_vecRangeMem 1 (sp + 2416#64) (by decide) rfl ?_
  intro f2416
  have hv2416 : VecRangeMem 1 (sp + 2416#64) f2416 = Vec128At (sp + 2416#64) (f2416 0) := by
    simp [VecRangeMem, sepConj_emp]
  rw [hv2416]
  refine sepWP_seq_env hcl2 hro2 (seg1b_copy0_zero1 hb hbase s2 sp pkA (f2416 0) (pkEk0 pk) _
    hpc2 hrun2 (hsp2.trans hsp1) hsp_chk hcl2
    (hx19_2.trans (hx19_1.trans hx19)) (hx26_2.trans (hx26_1.trans hx26)) hv6_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hfp3,
      hv0_3, hv1_3, hv6_3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢ memRegion (sp + 2560#64) 512 ∗
      (((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 21536#64) 512 ∗
        (((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
          Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
          Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
          memRegion (sp + 22048#64) 512 ∗ memRegion (sp + 22560#64) 512 ∗
          PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
          (pkA ↦ₛ pkEk0 pk) ∗ Seg1bFrame sp0 s0 sp ret rA pk rand Rest)) by sep_frame)) ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 2560#64) (by decide) rfl ?_
  intro f1
  refine SepWP.weaken_pre (show PolyMem (sp + 2560#64) f1 ∗ _ ⊢
      ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗ PolyMem (sp + 2560#64) f1 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl3 hro3 (seg1b_loop1 hb (pkA + 384#64) (sp + 2560#64) (pkEk1 pk) _
    (pkEk1_len hpk) 15 0 rfl s3 f1 hpc3 hrun3 hspA3
    (by simp [hx21_3, hx21_2, hx21_1, hx21]) (by simp [hx8_3]) hx26_3
    hv0_3 hv1_3 hv6_3 (fun _ hj => by omega)) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, _hspA4, hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx26_4, hfp4, _hv6_4, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (show _ ⊢ memRegion (sp + 21536#64) 512 ∗
      PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
      (Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
        ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
        Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
        memRegion (sp + 22048#64) 512 ∗ memRegion (sp + 22560#64) 512 ∗
        ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (pkA ↦ₛ pkEk0 pk) ∗ Seg1bFrame sp0 s0 sp ret rA pk rand Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl4 hro4 (seg1b_copy1 hb hbase s4 sp (pkEk1 pk) _
    hpc4 hrun4 (hsp4.trans hsp3) hsp_chk hcl4) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, _hspA5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx26_5, hfp5, hP5⟩
  refine SepWP.weaken_pre (Entails.trans hP5 (show _ ⊢ memRegion (sp + 2560#64) 512 ∗
      Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
      (((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ memRegion (sp + 22048#64) 512 ∗
        ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
        Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
        memRegion (sp + 22560#64) 512 ∗
        PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (pkA ↦ₛ pkEk0 pk) ∗ Seg1bFrame sp0 s0 sp ret rA pk rand Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl5 hro5 (seg1b_zero2 hb hbase s5 sp pkA _
    hpc5 hrun5 hsp5 hsp_chk (hx19_5.trans (hx19_4.trans hx19_3))) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6
    ⟨hsp6, hspA6, hx8_6, hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx26_6, hfp6,
      hv0_6, hv1_6, hv6_6, hP6⟩
  refine SepWP.weaken_pre hP6 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 2560#64) (by decide) rfl ?_
  intro f2
  refine SepWP.weaken_pre (show PolyMem (sp + 2560#64) f2 ∗ _ ⊢
      ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ PolyMem (sp + 2560#64) f2 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl6 hro6 (seg1b_loop2 hb (pkA + 768#64) (sp + 2560#64) (pkEk2 pk) _
    (pkEk2_len hpk) 15 0 rfl s6 f2 hpc6 hrun6 hspA6
    (by simp [hx23_6, hx23_5, hx23_4, hx23_3]) (by simp [hx8_6]) (hx21_6.trans hx21_5)
    hv1_6 hv0_6 hv6_6 (fun _ hj => by omega)) ?_
  rintro s7 P7 hpc7 hrun7 hcl7 hro7
    ⟨hsp7, _hspA7, hx19_7, hx20_7, _hx21_7, hx22_7, hx24_7, hx26_7, hfp7, _hv6_7, hP7⟩
  refine SepWP.weaken_pre (Entails.trans hP7 (show _ ⊢
      Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
      memRegion (sp + 22048#64) 512 ∗
      PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
      (((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
        Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
        memRegion (sp + 22560#64) 512 ∗
        ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗
        PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (pkA ↦ₛ pkEk0 pk) ∗ Seg1bFrame sp0 s0 sp ret rA pk rand Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl7 hro7 (seg1b_copy2_zero3 hb hbase s7 sp (pkEk2 pk) _
    hpc7 hrun7 (hsp7.trans hsp6) hsp_chk hcl7) ?_
  rintro s8 P8 hpc8 hrun8 hcl8 hro8
    ⟨hsp8, hspA8, hx8_8, hx19_8, hx20_8, hx21_8, hx22_8, hx24_8, hx26_8, hfp8,
      hv0_8, hv1_8, hv6_8, hP8⟩
  refine SepWP.weaken_pre (Entails.trans hP8 (show _ ⊢ memRegion (sp + 2560#64) 512 ∗
      (((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
        Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
        memRegion (sp + 22560#64) 512 ∗
        Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
        PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗
        PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (pkA ↦ₛ pkEk0 pk) ∗ Seg1bFrame sp0 s0 sp ret rA pk rand Rest) by sep_frame)) ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 2560#64) (by decide) rfl ?_
  intro f3
  refine SepWP.weaken_pre (show PolyMem (sp + 2560#64) f3 ∗ _ ⊢
      ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗ PolyMem (sp + 2560#64) f3 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl8 hro8 (seg1b_loop3 hb (pkA + 1152#64) (sp + 2560#64) (pkEk3 pk) _
    (pkEk3_len hpk) 15 0 rfl s8 f3 hpc8 hrun8 hspA8
    (by simp [hx19_8, hx19_7, hx19_6]) (by simp [hx8_8]) hx21_8
    hv1_8 hv0_8 hv6_8 (fun _ hj => by omega)) ?_
  rintro s9 P9 hpc9 hrun9 hcl9 _hro9
    ⟨hsp9, _hspA9, hx20_9, _hx21_9, hx22_9, hx24_9, hx26_9, _hx27_9, hfp9, _hv6_9, hP9⟩
  refine SepWP.weaken_pre (Entails.trans hP9 (show _ ⊢
      Vec128At (pkA + 1536#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
      Vec128At (pkA + 1552#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
      memRegion (sp + 22560#64) 512 ∗
      PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
      (((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
        Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
        PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗
        PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
        PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        (pkA ↦ₛ pkEk0 pk) ∗ Seg1bFrame sp0 s0 sp ret rA pk rand Rest) by sep_frame)) ?_
  have hx20_all : s9.readReg64 .x20 = pkA := by
    simp [hx20_9, hx20_8, hx20_7, hx20_6, hx20_5, hx20_4, hx20_3, hx20_2, hx20_1]
  refine SepWP.mono (seg1b_copy3_rho hb hbase s9 sp pkA (pkEk3 pk) (pkRho pk) _
    hpc9 hrun9 (hsp9.trans hsp8) hsp_chk hcl9 hx20_all) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx9_f, hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx26_f, hfp_f,
    hv0_f, hv1_f, hv2_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hsp_chk, hx9_f, hx19_f, hx20_f,
    by simp [hx22_f, hx22_9, hx22_8, hx22_7, hx22_6, hx22_5, hx22_4, hx22_3, hx22_2, hx22_1, hx22],
    hx23_f,
    by simp [hx24_f, hx24_9, hx24_8, hx24_7, hx24_6, hx24_5, hx24_4, hx24_3, hx24_2, hx24_1, hx24],
    by simp [hx26_f, hx26_9, hx26_8, hx26_7, hx26_6, hx26_5, hx26_4, hx26_3, sp],
    by simp [hfp_f, hfp9, hfp8, hfp7, hfp6, hfp5, hfp4, hfp3, hfp2, hfp1, hfp],
    hv0_f, hv1_f, hv2_f,
    Entails.trans hPf (seg1b_to_seg1bSpatial sp0 s0 sp ret pkA rA pk rand Rest hpk)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b
