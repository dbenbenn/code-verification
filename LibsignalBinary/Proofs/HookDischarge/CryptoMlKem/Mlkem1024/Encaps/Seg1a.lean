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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a3

/-!
# `kyber_encapsulate` (`B07`) — Segment 1a (`+0x0000 .. +0x02c0`)

- `Seg1aSpatial` and `Seg1aPost`: canonical stack-frame invariant at `+0x02c0` (`sp = s0.sp - 33104#64`).
- `seg1a_ok`: full Segment 1a composition (`+0x0000 → +0x02c0`) over `stackAt s0.sp 34240`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07
  blkPC07
  blkPl07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  SpilledMsgWords
  seg1a_prologue
  seg1a_setup_hash_rand
  sha3_256List_len
  sha3_512List_len
  stackAt_34240_split
  stackProbe8_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2 (
  keccak2SlicesRW_entails_memRegion32
  seg1a2_hash_pk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a3 (
  seg1a3_copy_memset
  seg1a3_hash_g
)

attribute [local irreducible] blkPC07 SpilledMsgWords sha3_256List sha3_512List

/-- Canonical spatial invariant at `+0x02c0` (`sp = sp0 - 33104#64`, `34,240`-byte frame). -/
@[expose] def Seg1aSpatial (sp0 : BitVec 64) (s0 : State)
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
  memRegion (sp + 21024#64) 2048 ∗
  ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗
  memRegion (sp + 23104#64) 9840 ∗
  SavedFrame07 sp0 s0

/-- Register + spatial postcondition at `+0x02c0` (`Seg1b` entry). -/
@[expose] def Seg1aPost (sp0 : BitVec 64) (s0 : State)
    (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := sp0 - 33104#64
  sf.sp = sp ∧
  sf.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  sf.readReg64 .x19 = pkA + 384#64 ∧
  sf.readReg64 .x20 = pkA ∧
  sf.readReg64 .x21 = pkA + 384#64 ∧
  sf.readReg64 .x22 = sp + 26768#64 ∧
  sf.readReg64 .x23 = sp + 2560#64 ∧
  sf.readReg64 .x24 = sp + 27032#64 ∧
  sf.readReg64 .x26 = sp + 12832#64 ∧
  sf.readReg64 .fp = sp + 33008#64 ∧
  (Pf ⊢ Seg1aSpatial sp0 s0 sp ret pkA rA pk rand ∗ Rest)

private theorem memRegion_176_32768_join (sp0 : BitVec 64) :
    let sp := sp0 - 33104#64
    memRegion sp 176 ∗ memRegion (sp0 - 32928#64) 32768 = memRegion sp 32944 := by
  intro sp
  exact (memRegion_split' (b := sp) (b' := sp0 - 32928#64) (n := 176) (k := (32768 : Nat))
    rfl (by dsimp only [sp]; bv_omega) (by decide)).symm

private theorem memRegion_32944_seg1a_split (sp : BitVec 64) :
    memRegion sp 32944 =
      memRegion sp 8 ∗ memRegion (sp + 8#64) 8 ∗ memRegion (sp + 16#64) 128 ∗
      memRegion (sp + 144#64) 72 ∗ memRegion (sp + 216#64) 8 ∗
      memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2432#64) 32 ∗
      memRegion (sp + 2464#64) 32 ∗ memRegion (sp + 2496#64) 64 ∗
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 2592#64) 32 ∗
      memRegion (sp + 2624#64) 10208 ∗ memRegion (sp + 12832#64) 32 ∗
      memRegion (sp + 12864#64) 32 ∗ memRegion (sp + 12896#64) 10176 ∗
      memRegion (sp + 23072#64) 32 ∗ memRegion (sp + 23104#64) 5744 ∗
      memRegion (sp + 28848#64) 32 ∗ memRegion (sp + 28880#64) 4016 ∗
      memRegion (sp + 32896#64) 32 ∗ memRegion (sp + 32928#64) 16 := by
  rw [memRegion_split' (b' := sp + 8#64) (n := 8) (k := (32936 : Nat)) rfl rfl (by decide),
    memRegion_split' (b := sp + 8#64) (b' := sp + 16#64) (n := 8) (k := (32928 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16#64) (b' := sp + 144#64) (n := 128) (k := (32800 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 144#64) (b' := sp + 216#64) (n := 72) (k := (32728 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 216#64) (b' := sp + 224#64) (n := 8) (k := (32720 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 224#64) (b' := sp + 2432#64) (n := (2208 : Nat)) (k := (30512 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2432#64) (b' := sp + 2464#64) (n := 32) (k := (30480 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2464#64) (b' := sp + 2496#64) (n := 32) (k := (30448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2496#64) (b' := sp + 2560#64) (n := 64) (k := (30384 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2560#64) (b' := sp + 2592#64) (n := 32) (k := (30352 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2592#64) (b' := sp + 2624#64) (n := 32) (k := (30320 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2624#64) (b' := sp + 12832#64) (n := (10208 : Nat)) (k := (20112 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12832#64) (b' := sp + 12864#64) (n := 32) (k := (20080 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12864#64) (b' := sp + 12896#64) (n := 32) (k := (20048 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12896#64) (b' := sp + 23072#64) (n := (10176 : Nat)) (k := (9872 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 23072#64) (b' := sp + 23104#64) (n := 32) (k := (9840 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 23104#64) (b' := sp + 28848#64) (n := (5744 : Nat)) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28848#64) (b' := sp + 28880#64) (n := 32) (k := (4064 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28880#64) (b' := sp + 32896#64) (n := (4016 : Nat)) (k := 48) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 32896#64) (b' := sp + 32928#64) (n := 32) (k := 16) rfl (by bv_omega) (by decide)]
private theorem seg1a_join_2560_64 (sp : BitVec 64) :
    memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 2592#64) 32 = memRegion (sp + 2560#64) 64 :=
  (memRegion_split' (b := sp + 2560#64) (b' := sp + 2592#64) (n := 32) (k := 32)
    rfl (by bv_omega) (by decide)).symm

private theorem seg1a_join_12832_64 (sp : BitVec 64) :
    memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 12864#64) 32 = memRegion (sp + 12832#64) 64 :=
  (memRegion_split' (b := sp + 12832#64) (b' := sp + 12864#64) (n := 32) (k := 32)
    rfl (by bv_omega) (by decide)).symm

private theorem seg1a_join_12832_10240 (sp : BitVec 64) :
    memRegion (sp + 12832#64) 64 ∗ memRegion (sp + 12896#64) 10176 = memRegion (sp + 12832#64) 10240 :=
  (memRegion_split' (b := sp + 12832#64) (b' := sp + 12896#64) (n := 64) (k := (10176 : Nat))
    rfl (by bv_omega) (by decide)).symm

private theorem seg1a_join_post (sp : BitVec 64) :
    (memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2432#64) 64 = memRegion (sp + 224#64) 2272) ∧
    (memRegion (sp + 2560#64) 64 ∗ memRegion (sp + 2624#64) 10208 = memRegion (sp + 2560#64) 10272) ∧
    (memRegion (sp + 23104#64) 9840 =
      memRegion (sp + 23104#64) 5744 ∗ memRegion (sp + 28848#64) 32 ∗
      memRegion (sp + 28880#64) 4016 ∗ memRegion (sp + 32896#64) 32 ∗
      memRegion (sp + 32928#64) 16) := by
  refine ⟨(memRegion_split' (b := sp + 224#64) (b' := sp + 2432#64) (n := (2208 : Nat)) (k := 64)
      rfl (by bv_omega) (by decide)).symm,
    (memRegion_split' (b := sp + 2560#64) (b' := sp + 2624#64) (n := 64) (k := (10208 : Nat))
      rfl (by bv_omega) (by decide)).symm, ?_⟩
  rw [memRegion_split' (b := sp + 23104#64) (b' := sp + 28848#64) (n := (5744 : Nat)) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28848#64) (b' := sp + 28880#64) (n := 32) (k := (4064 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28880#64) (b' := sp + 32896#64) (n := (4016 : Nat)) (k := 48) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 32896#64) (b' := sp + 32928#64) (n := 32) (k := 16) rfl (by bv_omega) (by decide)]

theorem seg1a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 : State) (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568) (hrnd : rand.length = 32)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = pkA) (hx2 : s0.readReg64 .x2 = rA) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x02c0#64) s0
      ((pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt s0.sp 34240 ∗ Rest)
      (Seg1aPost s0.sp s0 ret pkA rA pk rand Rest) := by
  let sp := s0.sp - 33104#64
  have hsp_chk : (sp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 33104#64 hsp0 (by decide)
  have hfp_val : s0.sp - 96#64 = sp + 33008#64 := by dsimp only [sp]; clear * -; bv_omega
  have hsp_probe : s0.sp - 160#64 = (s0.sp - 32928#64) + BitVec.ofNat 64 (4096 * 8) := by
    clear * -; bv_omega
  have hsp_176 : s0.sp - 32928#64 = sp + 176#64 := by dsimp only [sp]; clear * -; bv_omega
  rw [stackAt_34240_split s0.sp]
  refine SepWP.weaken_pre (show _ ⊢ memRegion (s0.sp - 160#64) 160 ∗
      ((pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗ memRegion sp 176 ∗
        memRegion (s0.sp - 32928#64) 32768 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg1a_prologue hb hbase s0 ret pkA rA _ hpc hrun hsp0 hx0 hx1 hx2) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx9_1, hfp1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢ memRegion (s0.sp - 32928#64) (4096 * 8) ∗
      (SavedFrame07 s0.sp s0 ∗ (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗
        memRegion sp 176 ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1 (stackProbe8_ok hb hbase (s0.sp - 32928#64) _ 8 (by decide) (by decide)
    s1 hpc1 hrun1 (hsp1.trans hsp_probe) hspA1 hx9_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, _, hx0_2, hx1_2, hx2_2, hfp2, hP2⟩
  have hjoin32944 : memRegion sp 176 ∗ memRegion (s0.sp - 32928#64) (4096 * 8) =
      memRegion sp 32944 := memRegion_176_32768_join s0.sp
  have hP2' : P2 ⊢ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗
      memRegion (sp + 8#64) 8 ∗ memRegion (sp + 216#64) 8 ∗
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
      memRegion (sp + 28848#64) 32 ∗
      ((pkA ↦ₛ pk) ∗ SavedFrame07 s0.sp s0 ∗ memRegion sp 8 ∗
        memRegion (sp + 16#64) 128 ∗ memRegion (sp + 144#64) 72 ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2432#64) 32 ∗
        memRegion (sp + 2464#64) 32 ∗ memRegion (sp + 2496#64) 64 ∗
        memRegion (sp + 2592#64) 32 ∗ memRegion (sp + 2624#64) 10208 ∗
        memRegion (sp + 12864#64) 32 ∗ memRegion (sp + 12896#64) 10176 ∗
        memRegion (sp + 23072#64) 32 ∗ memRegion (sp + 23104#64) 5744 ∗
        memRegion (sp + 28880#64) 4016 ∗ memRegion (sp + 32896#64) 32 ∗
        memRegion (sp + 32928#64) 16 ∗ Rest) := by
    refine Entails.trans hP2 ?_
    refine Entails.trans (Q := memRegion sp 32944 ∗
      (SavedFrame07 s0.sp s0 ∗ (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗ Rest))
      (by rw [← hjoin32944]; sep_frame) ?_
    rw [memRegion_32944_seg1a_split sp]
    sep_frame
  refine SepWP.weaken_pre hP2' ?_
  refine sepWP_seq_env hcl2 hro2 (seg1a_setup_hash_rand hb hbase s2 sp (sp + 33008#64) ret pkA rA
    rand _ hrnd hpc2 hrun2 (hsp2.trans hsp_176) hsp_chk hcl2 hro2
    (hx0_2.trans hx0_1) (hx1_2.trans hx1_1) (hx2_2.trans hx2_1)
    (hfp2.trans (hfp1.trans hfp_val))) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hfp3, hP3⟩
  have hs3 := keccak2SlicesRW_entails_memRegion32 (sp + 12832#64) rA rA 32 32
  have hP3' : P3 ⊢ (pkA ↦ₛ pk) ∗ stackAt sp 1136 ∗
      memRegion (sp + 16#64) 128 ∗ memRegion (sp + 2432#64) 32 ∗
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
      ((sp + 28848#64) ↦ₛ sha3_256List rand) ∗ memRegion (sp + 32896#64) 32 ∗
      ((rA ↦ₛ rand) ∗ SavedFrame07 s0.sp s0 ∗ memRegion sp 8 ∗ ((sp + 8#64) ↦₆₄ ret) ∗
        memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2464#64) 32 ∗
        memRegion (sp + 2496#64) 64 ∗ memRegion (sp + 2592#64) 32 ∗
        memRegion (sp + 2624#64) 10208 ∗ memRegion (sp + 12864#64) 32 ∗
        memRegion (sp + 12896#64) 10176 ∗ memRegion (sp + 23072#64) 32 ∗
        memRegion (sp + 23104#64) 5744 ∗ memRegion (sp + 28880#64) 4016 ∗
        memRegion (sp + 32928#64) 16 ∗ Rest) := by
    refine Entails.trans hP3 ?_
    refine Entails.trans (Q := (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗
      ((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
      ((sp + 28848#64) ↦ₛ sha3_256List rand) ∗ _)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hs3)))))) ?_
    sep_frame
  refine SepWP.weaken_pre hP3' ?_
  refine sepWP_seq_env hcl3 hro3 (seg1a2_hash_pk hb hbase s3 sp pkA pk (sha3_256List rand) _
    hpk (sha3_256List_len rand) hpc3 hrun3 hsp3 hsp_chk hcl3 hro3
    hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hfp3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, _, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hfp4, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (by
    show _ ⊢ stackAt sp 1136 ∗ ((sp + 2432#64) ↦ₛ sha3_256List rand) ∗
      memRegion (sp + 2464#64) 32 ∗ memRegion (sp + 2560#64) 64 ∗
      memRegion (sp + 12832#64) 64 ∗ memRegion (sp + 28848#64) 32 ∗
      ((sp + 32896#64) ↦ₛ sha3_256List pk) ∗
      ((pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ SavedFrame07 s0.sp s0 ∗ memRegion sp 8 ∗
        ((sp + 8#64) ↦₆₄ ret) ∗ SpilledMsgWords sp (sha3_256List rand) ∗
        memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2496#64) 64 ∗
        memRegion (sp + 2624#64) 10208 ∗ memRegion (sp + 12896#64) 10176 ∗
        memRegion (sp + 23072#64) 32 ∗ memRegion (sp + 23104#64) 5744 ∗
        memRegion (sp + 28880#64) 4016 ∗ memRegion (sp + 32928#64) 16 ∗ Rest)
    rw [← seg1a_join_2560_64 sp, ← seg1a_join_12832_64 sp]
    sep_frame)) ?_
  refine sepWP_seq_env hcl4 hro4 (seg1a3_hash_g hb hbase s4 sp pkA
    (sha3_256List rand) (sha3_256List pk) _
    (sha3_256List_len rand) (sha3_256List_len pk) hpc4 hrun4 hsp4 hsp_chk hcl4 hro4
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hfp4) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, _, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx26_5, hfp5, hP5⟩
  refine SepWP.weaken_pre (Entails.trans hP5 (by
    show _ ⊢ memRegion (sp + 2496#64) 64 ∗
      ((sp + 2560#64) ↦ₛ sha3_512List (sha3_256List rand ++ sha3_256List pk)) ∗
      memRegion (sp + 12832#64) 10240 ∗ memRegion (sp + 23072#64) 32 ∗
      ((pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗ SavedFrame07 s0.sp s0 ∗
        memRegion sp 8 ∗ ((sp + 8#64) ↦₆₄ ret) ∗ SpilledMsgWords sp (sha3_256List rand) ∗
        memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
        memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 2432#64) 64 ∗
        memRegion (sp + 2624#64) 10208 ∗ memRegion (sp + 23104#64) 5744 ∗
        memRegion (sp + 28848#64) 32 ∗ memRegion (sp + 28880#64) 4016 ∗
        memRegion (sp + 32896#64) 32 ∗ memRegion (sp + 32928#64) 16 ∗ Rest)
    rw [← seg1a_join_12832_10240 sp]
    sep_frame)) ?_
  refine SepWP.mono (seg1a3_copy_memset hb hbase s5 sp pkA
    (sha3_512List (sha3_256List rand ++ sha3_256List pk)) _
    (sha3_512List_len _) hpc5 hrun5 hsp5 hsp_chk hcl5 hro5
    hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx26_5 hfp5) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx26_f, hfp_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hsp_chk, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx26_f, hfp_f, ?_⟩
  refine Entails.trans hPf ?_
  unfold Seg1aSpatial
  obtain ⟨hj1, hj2, hj3⟩ := seg1a_join_post sp
  rw [← hj1, ← hj2, hj3]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a
