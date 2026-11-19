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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2 -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Prf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E1Prf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E1

/-!
# `kyber_encapsulate` (`B07`) — Segment 3 Top-Level Composition (`+0x3d0c .. +0x59d0`) (`Seg3`)

Composes `Seg3Cbd.seg3_entry_ops`, `Seg3Prf.seg3_prf_calls`, `Seg3Prf.seg3_copy_and_zetas`,
`Seg3Rhat.seg3_rhat_loop_ok`, `Seg3E1Prf.seg3_memset_e1`, `Seg3E1Prf.seg3_e1_prf_calls`,
`Seg3E1Prf.seg3_e1_copy_prf`, `Seg3E1.seg3_e1_ok`, and `Seg3E2.seg3_e2_ok` into `seg3_ok`
(`+0x3d0c → +0x59d0`, establishing `Seg3Post`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  sha3_256List sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  sha3_512List_length shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem bytesToVecNat oct8Mem_entails_memRegion polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SpillSliceMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07 blkPC07 blkPl07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (SpilledMsgWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2 (
  ATransMem Seg2Post Seg2Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd (
  ATransAt PublicKeyStateAt aTransAt_12832_eq off3d0c seg3_entry_ops)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Prf (
  off3ec8 pointsToBytes128_eq_oct8Mem seg3_copy_and_zetas seg3_prf_calls)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat (
  offSeg3RhatEnd rHatPoly16 seg3_rhat_loop_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E1Prf (
  off5254 off53b8 offSeg3E1 offSeg3E1Setup seg3_e1_copy_prf seg3_e1_prf_calls seg3_memset_e1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E1 (seg3_e1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2 (
  offSeg3E2 offSeg4Start seg3_e2_ok)

attribute [local irreducible] blkPC07 sha3_256List sha3_512List shake256List neonCbd2Poly16
  polyVecNat PolyMem SpillSliceMem SpilledMsgWords SavedFrame07

/-- Spatial invariant at `+0x59d0` (`Seg4` entry). -/
@[expose] noncomputable def Seg3Spatial (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) : SepProp :=
  let hashed := sha3_512List (sha3_256List rand ++ sha3_256List pk)
  let coins := hashed.drop 32
  (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗
  stackAt sp 1136 ∗ memRegion sp 8 ∗ ((sp + 8#64) ↦₆₄ ret) ∗
  SpilledMsgWords sp (sha3_256List rand) ∗
  memRegion (sp + 144#64) 1344 ∗
  PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [8#8])))) ∗
  memRegion (sp + 2000#64) 496 ∗
  ((sp + 2496#64) ↦ₛ hashed) ∗
  PublicKeyStateAt (sp + 2560#64) pk ∗
  memRegion (sp + 12832#64) 11888 ∗
  PolyMem (sp + 24720#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [0#8])))) ∗
  PolyMem (sp + 25232#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [1#8])))) ∗
  PolyMem (sp + 25744#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [2#8])))) ∗
  PolyMem (sp + 26256#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [3#8])))) ∗
  PolyMem (sp + 26768#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8])))) ∗
  PolyMem (sp + 27280#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
  PolyMem (sp + 27792#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [6#8])))) ∗
  PolyMem (sp + 28304#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [7#8])))) ∗
  memRegion (sp + 28816#64) 32 ∗
  PolyMem (sp + 28848#64) (fun _ => 0#128) ∗
  PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
  PolyMem (sp + 29872#64) (fun _ => 0#128) ∗
  PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
  memRegion (sp + 30896#64) 2048 ∗
  SavedFrame07 sp0 s0

/-- Register + spatial postcondition at `+0x59d0` (`Seg4` entry). -/
@[expose] def Seg3Post [MlKemPlacement] (b sp0 : BitVec 64) (s0 : State)
    (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := sp0 - 33104#64
  sf.pc = b + offSeg4Start ∧ sf.status = .Running ∧
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  sf.readReg64 .x20 = sp + 28848#64 ∧
  sf.readReg64 .fp = sp + 33008#64 ∧
  (Pf ⊢ Seg3Spatial sp0 s0 sp ret pkA rA pk rand ∗ Rest)

attribute [local irreducible] PublicKeyStateAt

private theorem pointsToBytes128_entails_memRegion (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) ⊢ memRegion ptr 128 := by
  rw [pointsToBytes128_eq_oct8Mem ptr h]
  exact oct8Mem_entails_memRegion ptr _

private theorem prf4_entails_memRegion512 (sp : BitVec 64)
    {p0 p1 p2 p3 : List (BitVec 8)}
    (h0 : p0.length = 128) (h1 : p1.length = 128) (h2 : p2.length = 128) (h3 : p3.length = 128) :
    ((sp + 28848#64) ↦ₛ p0) ∗ ((sp + 28976#64) ↦ₛ p1) ∗
      ((sp + 29104#64) ↦ₛ p2) ∗ ((sp + 29232#64) ↦ₛ p3) ⊢
      memRegion (sp + 28848#64) 512 := by
  have hm : memRegion (sp + 28848#64) 512 =
      memRegion (sp + 28848#64) 128 ∗ memRegion (sp + 28976#64) 128 ∗
        memRegion (sp + 29104#64) 128 ∗ memRegion (sp + 29232#64) 128 := by
    rw [memRegion_split' (b := sp + 28848#64) (b' := sp + 28976#64) (n := 128) (k := (384 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 28976#64) (b' := sp + 29104#64) (n := 128) (k := (256 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 29104#64) (b' := sp + 29232#64) (n := 128) (k := (128 : Nat))
          rfl (by bv_omega) (by decide)]
  rw [hm]
  exact entails_sub (pointsToBytes128_entails_memRegion _ h0) (by sep_frame)
    (entails_sub (pointsToBytes128_entails_memRegion _ h1) (by sep_frame)
      (entails_sub (pointsToBytes128_entails_memRegion _ h2) (by sep_frame)
        (entails_sub (pointsToBytes128_entails_memRegion _ h3) (by sep_frame) (by sep_frame))))

section
unseal PublicKeyStateAt in
private theorem publicKeyStateAt_12832_eq (sp : BitVec 64) (pk : List (BitVec 8)) :
    ATransMem sp (pkRho pk) ∗
      PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
      PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
      PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
      PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
      ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) =
      PublicKeyStateAt (sp + 12832#64) pk := by
  dsimp only [PublicKeyStateAt]
  rw [aTransAt_12832_eq]
  have h0 : sp + 12832#64 + 8192#64 = sp + 21024#64 := by bv_omega
  have h1 : sp + 12832#64 + 8704#64 = sp + 21536#64 := by bv_omega
  have h2 : sp + 12832#64 + 9216#64 = sp + 22048#64 := by bv_omega
  have h3 : sp + 12832#64 + 9728#64 = sp + 22560#64 := by bv_omega
  have h4 : sp + 12832#64 + BitVec.ofNat 64 10240 = sp + 23072#64 := by bv_omega
  rw [h0, h1, h2, h3, h4]
end

private theorem seg3_regions_eq (sp : BitVec 64) :
    (memRegion (sp + 144#64) 2352 =
      memRegion (sp + 144#64) 1648 ∗ memRegion (sp + 1792#64) 640 ∗ memRegion (sp + 2432#64) 64) ∧
    (memRegion (sp + 144#64) 2352 =
      memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 2000#64) 496) ∧
    (memRegion (sp + 12832#64) 10272 =
      memRegion (sp + 12832#64) 128 ∗ memRegion (sp + 12960#64) 384 ∗
      memRegion (sp + 13344#64) 9760) ∧
    (memRegion (sp + 12832#64) 512 =
      memRegion (sp + 12832#64) 128 ∗ memRegion (sp + 12960#64) 384) ∧
    (memRegion (sp + 12832#64) 10272 =
      memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 13344#64) 9760) ∧
    (memRegion (sp + 28848#64) 512 =
      memRegion (sp + 28848#64) 32 ∗ memRegion (sp + 28880#64) 480) := by
  refine ⟨?_, ?_, ?_,
    memRegion_split' (b := sp + 12832#64) (b' := sp + 12960#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12832#64) (b' := sp + 13344#64) (n := 512) (k := (9760 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28848#64) (b' := sp + 28880#64) (n := 32) (k := (480 : Nat))
      rfl (by bv_omega) (by decide)⟩
  · rw [memRegion_split' (b := sp + 144#64) (b' := sp + 1792#64) (n := 1648) (k := (704 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 1792#64) (b' := sp + 2432#64) (n := 640) (k := (64 : Nat))
          rfl (by bv_omega) (by decide)]
  · rw [memRegion_split' (b := sp + 144#64) (b' := sp + 1488#64) (n := 1344) (k := (1008 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 1488#64) (b' := sp + 2000#64) (n := 512) (k := (496 : Nat))
          rfl (by bv_omega) (by decide)]
  · rw [memRegion_split' (b := sp + 12832#64) (b' := sp + 12960#64) (n := 128) (k := (10144 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 12960#64) (b' := sp + 13344#64) (n := 384) (k := (9760 : Nat))
          rfl (by bv_omega) (by decide)]
private theorem seg3_part1a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + off3d0c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off3ec8) s
      (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 2560#64) 10272 ∗
       PublicKeyStateAt (sp + 12832#64) pk ∗ memRegion (sp + 23104#64) 1568 ∗
       memRegion (sp + 24672#64) 33 ∗ memRegion (sp + 24720#64) 2048 ∗
       memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 28848#64) 32 ∗
       memRegion (sp + 31408#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
       memRegion (sp + 32288#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 12832#64 ∧
        s2.readReg64 .x21 = sp + 24720#64 ∧ s2.readReg64 .x22 = sp + 28848#64 ∧
        s2.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s2.mem ∧ MlKemRoOk mlkemMpl s2.mem ∧
        (P2 ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 2560#64) pk ∗
          memRegion (sp + 12960#64) 384 ∗ memRegion (sp + 13344#64) 9760 ∗
          memRegion (sp + 23104#64) 1568 ∗ ((sp + 24672#64) ↦ₛ hashed.drop 32) ∗
          ((sp + 24704#64) ↦₈ 0#8) ∗
          PolyMem (sp + 24720#64) (fun _ => 0#128) ∗ PolyMem (sp + 25232#64) (fun _ => 0#128) ∗
          PolyMem (sp + 25744#64) (fun _ => 0#128) ∗ PolyMem (sp + 26256#64) (fun _ => 0#128) ∗
          memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 28848#64) 32 ∗
          ((sp + 31936#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [0#8])) ∗
          ((sp + 32288#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [1#8])) ∗
          ((sp + 31408#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [2#8])) ∗
          ((sp + 12832#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [3#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  have hc : (hashed.drop 32).length = 32 := by simp [List.length_drop, hh]
  rcases seg3_regions_eq sp with ⟨_, _, hr12832, _, _, _⟩
  refine SepWP.weaken_pre (by sep_frame : _ ⊢
    ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 2560#64) 10272 ∗
      PublicKeyStateAt (sp + 12832#64) pk ∗ memRegion (sp + 23104#64) 1568 ∗
      memRegion (sp + 24672#64) 33 ∗ memRegion (sp + 24720#64) 2048 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 28848#64) 32 ∗
        memRegion (sp + 31408#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
        memRegion (sp + 32288#64) 128 ∗ Rest)) ?_
  refine sepWP_seq_env hcl hro
    (seg3_entry_ops hb hbase s sp pk hashed _ hh hpc hrun hsp hspA hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hx21_1, hx22_1, hfp1, hP1⟩
  rw [hx22] at hx22_1
  refine SepWP.weaken_pre hP1 ?_
  rw [hr12832]
  refine SepWP.weaken_pre (by sep_frame : _ ⊢
    ((sp + 24672#64) ↦ₛ hashed.drop 32) ∗ memRegion (sp + 12832#64) 128 ∗
      memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 28848#64) 32 ∗
      memRegion (sp + 31408#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
      memRegion (sp + 32288#64) 128 ∗ stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_prf_calls hb hbase s1 sp (hashed.drop 32) _ hc hpc1 hrun1 hsp1 hspA1
      hx19_1 hx20_1 hx21_1 hx22_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hP2⟩
  rw [hfp1] at hfp2
  exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hcl2, hro2,
    Entails.trans hP2 (by sep_frame)⟩

private theorem seg3_part1b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (prf0 prf1 prf2 prf3 : List (BitVec 8)) (Rest : SepProp)
    (hp0 : prf0.length = 128) (hp1 : prf1.length = 128)
    (hp2 : prf2.length = 128) (hp3 : prf3.length = 128)
    (hpc : s.pc = b + off3ec8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64) (hx20 : s.readReg64 .x20 = sp + 12832#64)
    (hx21 : s.readReg64 .x21 = sp + 24720#64) (hx22 : s.readReg64 .x22 = sp + 28848#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg3RhatEnd) s
      (((sp + 31936#64) ↦ₛ prf0) ∗ ((sp + 32288#64) ↦ₛ prf1) ∗
       ((sp + 31408#64) ↦ₛ prf2) ∗ ((sp + 12832#64) ↦ₛ prf3) ∗
       memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 1792#64) 640 ∗
       memRegion (sp + 12960#64) 384 ∗
       PolyMem (sp + 24720#64) (fun _ => 0#128) ∗ PolyMem (sp + 25232#64) (fun _ => 0#128) ∗
       PolyMem (sp + 25744#64) (fun _ => 0#128) ∗ PolyMem (sp + 26256#64) (fun _ => 0#128) ∗
       Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 1792#64) 640 ∗
          memRegion (sp + 12832#64) 512 ∗
          PolyMem (sp + 24720#64) (polyVecNat (rHatPoly16 prf0)) ∗
          PolyMem (sp + 25232#64) (polyVecNat (rHatPoly16 prf1)) ∗
          PolyMem (sp + 25744#64) (polyVecNat (rHatPoly16 prf2)) ∗
          PolyMem (sp + 26256#64) (polyVecNat (rHatPoly16 prf3)) ∗
          memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
          memRegion (sp + 31408#64) 128 ∗ Rest)) := by
  rcases seg3_regions_eq sp with ⟨_, _, _, hr512, _, _⟩
  refine sepWP_seq_env hcl hro
    (seg3_copy_and_zetas hb hbase s sp prf0 prf1 prf2 prf3 _ hp0 hp1 hp2 hp3
      hpc hrun hsp hspA hx19 hx20 hx21 hx22) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, _, hfp3, rv3, t0, ht0, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hr512.symm) (by sep_frame) (by sep_frame) : _ ⊢
      ((sp + 28848#64) ↦ₛ prf0) ∗ ((sp + 28976#64) ↦ₛ prf1) ∗
      ((sp + 29104#64) ↦ₛ prf2) ∗ ((sp + 29232#64) ↦ₛ prf3) ∗
      memRegion (sp + 12832#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t0 ∗
      PolyMem (sp + 24720#64) (fun _ => 0#128) ∗ PolyMem (sp + 25232#64) (fun _ => 0#128) ∗
      PolyMem (sp + 25744#64) (fun _ => 0#128) ∗ PolyMem (sp + 26256#64) (fun _ => 0#128) ∗ _) ?_
  refine sepWP_seq_env hcl3 hro3
    (seg3_rhat_loop_ok hb hbase s3 sp prf0 prf1 prf2 prf3 t0 ht0 _ _ _ _ _
      hp0 hp1 hp2 hp3 hpc3 hrun3 hsp3 hspA3 hcl3 hro3
      r0 r1 r2 r3 r5 r7 r9 r10 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 rv3) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hx19f, _, _, hfp_f, hclf, hrof, hPf⟩
  rw [hfp3] at hfp_f
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hx19f, hfp_f, hclf, hrof,
    Entails.trans hPf (entails_sub (prf4_entails_memRegion512 sp hp0 hp1 hp2 hp3)
      (by sep_frame) (by sep_frame))⟩

private theorem seg3_regions2_eq (sp : BitVec 64) :
    (memRegion (sp + 31408#64) 132 =
      memRegion (sp + 31408#64) 128 ∗ memRegion (sp + 31536#64) 4) ∧
    (memRegion (sp + 31408#64) 132 =
      memRegion (sp + 31408#64) 32 ∗ memRegion (sp + 31440#64) 100) ∧
    (memRegion (sp + 26768#64) 2048 =
      memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 26900#64) 1916) ∧
    (memRegion (sp + 28848#64) 2048 =
      memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 29360#64) 1536) ∧
    (memRegion (sp + 12832#64) 11888 =
      memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 13344#64) 9760 ∗
      memRegion (sp + 23104#64) 1568 ∗ memRegion (sp + 24672#64) 33 ∗
      memRegion (sp + 24705#64) 15) := by
  refine ⟨memRegion_split' (b := sp + 31408#64) (b' := sp + 31536#64) (n := 128) (k := (4 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 31408#64) (b' := sp + 31440#64) (n := 32) (k := (100 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 26768#64) (b' := sp + 26900#64) (n := 132) (k := (1916 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28848#64) (b' := sp + 29360#64) (n := 512) (k := (1536 : Nat))
      rfl (by bv_omega) (by decide), ?_⟩
  rw [memRegion_split' (b := sp + 12832#64) (b' := sp + 13344#64) (n := 512) (k := (11376 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 13344#64) (b' := sp + 23104#64) (n := 9760) (k := (1616 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 23104#64) (b' := sp + 24672#64) (n := 1568) (k := (48 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24672#64) (b' := sp + 24705#64) (n := 33) (k := (15 : Nat))
        rfl (by bv_omega) (by decide)]

private theorem seg3_regions3_eq (sp : BitVec 64) :
    (memRegion (sp + 23104#64) 9840 =
      memRegion (sp + 23104#64) 1568 ∗ memRegion (sp + 24672#64) 33 ∗
      memRegion (sp + 24705#64) 15 ∗ memRegion (sp + 24720#64) 2048 ∗
      memRegion (sp + 26768#64) 2048 ∗ memRegion (sp + 28816#64) 32 ∗
      memRegion (sp + 28848#64) 2048 ∗ memRegion (sp + 30896#64) 2048) ∧
    (memRegion (sp + 30896#64) 2048 =
      memRegion (sp + 30896#64) 512 ∗ memRegion (sp + 31408#64) 132 ∗
      memRegion (sp + 31540#64) 396 ∗ memRegion (sp + 31936#64) 128 ∗
      memRegion (sp + 32064#64) 224 ∗ memRegion (sp + 32288#64) 128 ∗
      memRegion (sp + 32416#64) 320 ∗ memRegion (sp + 32736#64) 128 ∗
      memRegion (sp + 32864#64) 80) := by
  constructor
  · rw [memRegion_split' (b := sp + 23104#64) (b' := sp + 24672#64) (n := 1568) (k := (8272 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 24672#64) (b' := sp + 24705#64) (n := 33) (k := (8239 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 24705#64) (b' := sp + 24720#64) (n := 15) (k := (8224 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 24720#64) (b' := sp + 26768#64) (n := 2048) (k := (6176 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 26768#64) (b' := sp + 28816#64) (n := 2048) (k := (4128 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 28816#64) (b' := sp + 28848#64) (n := 32) (k := (4096 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 28848#64) (b' := sp + 30896#64) (n := 2048) (k := (2048 : Nat))
          rfl (by bv_omega) (by decide)]
  · rw [memRegion_split' (b := sp + 30896#64) (b' := sp + 31408#64) (n := 512) (k := (1536 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 31408#64) (b' := sp + 31540#64) (n := 132) (k := (1404 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 31540#64) (b' := sp + 31936#64) (n := 396) (k := (1008 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 31936#64) (b' := sp + 32064#64) (n := 128) (k := (880 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 32064#64) (b' := sp + 32288#64) (n := 224) (k := (656 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 32288#64) (b' := sp + 32416#64) (n := 128) (k := (528 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 32416#64) (b' := sp + 32736#64) (n := 320) (k := (208 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 32736#64) (b' := sp + 32864#64) (n := 128) (k := (80 : Nat))
          rfl (by bv_omega) (by decide)]

private theorem seg3_part2a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg3E1Setup) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg3E1) s
      (((sp + 24672#64) ↦ₛ coins) ∗ memRegion (sp + 26768#64) 2048 ∗
       memRegion (sp + 31408#64) 132 ∗ memRegion (sp + 28848#64) 512 ∗
       memRegion (sp + 12832#64) 128 ∗ memRegion (sp + 32736#64) 128 ∗
       memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 28849#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 26768#64 ∧
        sf.readReg64 .x21 = sp + 12832#64 ∧ sf.readReg64 .x22 = sp + 28848#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧ sf.readVReg128 3#5 = 0#128 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 24672#64) ↦ₛ coins) ∗ memRegion (sp + 31408#64) 132 ∗
          PolyMem (sp + 26768#64) (fun _ => 0#128) ∗ PolyMem (sp + 27280#64) (fun _ => 0#128) ∗
          PolyMem (sp + 27792#64) (fun _ => 0#128) ∗ PolyMem (sp + 28304#64) (fun _ => 0#128) ∗
          ((sp + 28848#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          ((sp + 28976#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
          ((sp + 29104#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
          ((sp + 29232#64) ↦ₛ shake256List 128 (coins ++ [7#8])) ∗
          memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
          memRegion (sp + 32288#64) 128 ∗ memRegion (sp + 12832#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  rcases seg3_regions_eq sp with ⟨_, _, _, _, _, hr28848⟩
  refine SepWP.weaken_pre (by sep_frame : _ ⊢
    memRegion (sp + 26768#64) 2048 ∗ stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl hro
    (seg3_memset_e1 hb hbase s sp _ hpc hrun hsp hspA hx19 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [hr28848]
  refine SepWP.weaken_pre (by sep_frame : _ ⊢
    ((sp + 24672#64) ↦ₛ coins) ∗ memRegion (sp + 31408#64) 132 ∗
      memRegion (sp + 28848#64) 32 ∗ memRegion (sp + 12832#64) 128 ∗
      memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
      memRegion (sp + 32288#64) 128 ∗ stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_e1_prf_calls hb hbase s1 sp coins _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hr28848.symm) (by sep_frame) (by sep_frame) : _ ⊢
      ((sp + 32736#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
      ((sp + 31936#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
      ((sp + 32288#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
      ((sp + 12832#64) ↦ₛ shake256List 128 (coins ++ [7#8])) ∗
      memRegion (sp + 28848#64) 512 ∗ _) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg3_e1_copy_prf hb hbase s2 sp (shake256List_length 128 _) (shake256List_length 128 _)
      (shake256List_length 128 _) (shake256List_length 128 _) _
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2 hcl2 hro2) ?_
  rintro sf Pf hpcf hrunf hclf hrof
    ⟨hspf, hspAf, hx8f, hx9f, hx19f, hx20f, hx21f, hx22f, hfpf, hv3f, hPf⟩
  rw [hfp2, hfp1] at hfpf
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hx8f, hx9f, hx19f, hx20f, hx21f, hx22f,
    hfpf, hv3f, hclf, hrof, Entails.trans hPf (by sep_frame)⟩

private theorem seg3_part2b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8))
    (z0 z1 z2 z3 : Nat → BitVec 128) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg3E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = sp + 28849#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64) (hx20 : s.readReg64 .x20 = sp + 26768#64)
    (hx21 : s.readReg64 .x21 = sp + 12832#64) (hv3 : s.readVReg128 3#5 = 0#128)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Start) s
      (((sp + 28848#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
       ((sp + 28976#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
       ((sp + 29104#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
       ((sp + 29232#64) ↦ₛ shake256List 128 (coins ++ [7#8])) ∗
       memRegion (sp + 12832#64) 512 ∗
       PolyMem (sp + 26768#64) z0 ∗ PolyMem (sp + 27280#64) z1 ∗
       PolyMem (sp + 27792#64) z2 ∗ PolyMem (sp + 28304#64) z3 ∗
       ((sp + 24704#64) ↦₈ 0#8) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
       memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 29360#64) 1536 ∗
       memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 28848#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [8#8])))) ∗
          PolyMem (sp + 26768#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8])))) ∗
          PolyMem (sp + 27280#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
          PolyMem (sp + 27792#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [6#8])))) ∗
          PolyMem (sp + 28304#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [7#8])))) ∗
          PolyMem (sp + 28848#64) (fun _ => 0#128) ∗ PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29872#64) (fun _ => 0#128) ∗ PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
          memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 24672#64) 33 ∗
          memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  rcases seg3_regions2_eq sp with ⟨_, _, _, hr28848_2048, _⟩
  refine sepWP_seq_env hcl hro
    (seg3_e1_ok hb hbase s sp coins z0 z1 z2 z3 _ hpc hrun hsp hspA hx8 hx9 hx19 hx20 hx21 hv3) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hfp1, _, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hr28848_2048.symm) (by sep_frame) (by sep_frame) : _ ⊢
      ((sp + 24704#64) ↦₈ 0#8) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
      memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 28848#64) 2048 ∗
      memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 32736#64) 128 ∗
      memRegion (sp + 31408#64) 32 ∗ stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_e2_ok hb hbase s1 sp coins 0#8 _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hcl1 hro1) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hx20f, hfpf, hclf, hrof, hPf⟩
  rw [hfp1] at hfpf
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hx20f, hfpf, hclf, hrof,
    Entails.trans hPf (by sep_frame)⟩

private theorem seg3_part1 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + off3d0c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg3RhatEnd) s
      (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
       memRegion (sp + 2560#64) 10272 ∗ PublicKeyStateAt (sp + 12832#64) pk ∗
       memRegion (sp + 23104#64) 1568 ∗ memRegion (sp + 24672#64) 33 ∗
       memRegion (sp + 24720#64) 2048 ∗ memRegion (sp + 26768#64) 132 ∗
       memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 31408#64) 128 ∗
       memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
          PublicKeyStateAt (sp + 2560#64) pk ∗ memRegion (sp + 12832#64) 512 ∗
          memRegion (sp + 13344#64) 9760 ∗ memRegion (sp + 23104#64) 1568 ∗
          ((sp + 24672#64) ↦ₛ hashed.drop 32) ∗ ((sp + 24704#64) ↦₈ 0#8) ∗
          PolyMem (sp + 24720#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [0#8])))) ∗
          PolyMem (sp + 25232#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [1#8])))) ∗
          PolyMem (sp + 25744#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [2#8])))) ∗
          PolyMem (sp + 26256#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [3#8])))) ∗
          memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 28848#64) 512 ∗
          memRegion (sp + 31408#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
          memRegion (sp + 32288#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  rcases seg3_regions_eq sp with ⟨_, _, _, _, _, hr28848⟩
  rw [hr28848]
  refine SepWP.weaken_pre (by sep_frame : _ ⊢
    ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 2560#64) 10272 ∗
      PublicKeyStateAt (sp + 12832#64) pk ∗ memRegion (sp + 23104#64) 1568 ∗
      memRegion (sp + 24672#64) 33 ∗ memRegion (sp + 24720#64) 2048 ∗
      memRegion (sp + 26768#64) 132 ∗ memRegion (sp + 28848#64) 32 ∗
      memRegion (sp + 31408#64) 128 ∗ memRegion (sp + 31936#64) 128 ∗
      memRegion (sp + 32288#64) 128 ∗ stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl hro
    (seg3_part1a hb hbase s sp pk hashed _ hh hpc hrun hsp hspA hx22 hcl hro) ?_
  rintro s2 P2 hpc2 hrun2 _ _ ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hcl2, hro2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hr28848.symm) (by sep_frame) (by sep_frame) : _ ⊢
      ((sp + 31936#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [0#8])) ∗
      ((sp + 32288#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [1#8])) ∗
      ((sp + 31408#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [2#8])) ∗
      ((sp + 12832#64) ↦ₛ shake256List 128 (hashed.drop 32 ++ [3#8])) ∗
      memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 1792#64) 640 ∗
      memRegion (sp + 12960#64) 384 ∗
      PolyMem (sp + 24720#64) (fun _ => 0#128) ∗ PolyMem (sp + 25232#64) (fun _ => 0#128) ∗
      PolyMem (sp + 25744#64) (fun _ => 0#128) ∗ PolyMem (sp + 26256#64) (fun _ => 0#128) ∗ _) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg3_part1b hb hbase s2 sp _ _ _ _ _
      (shake256List_length 128 _) (shake256List_length 128 _)
      (shake256List_length 128 _) (shake256List_length 128 _)
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2 hcl2 hro2) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hx19f, hfpf, hclf, hrof, hPf⟩
  rw [hfp2] at hfpf
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hx19f, hfpf, hclf, hrof,
    Entails.trans hPf (by sep_frame)⟩

private theorem seg3_part2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg3E1Setup) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Start) s
      (((sp + 24672#64) ↦ₛ coins) ∗ ((sp + 24704#64) ↦₈ 0#8) ∗
       memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 12832#64) 512 ∗
       memRegion (sp + 26768#64) 2048 ∗ memRegion (sp + 28848#64) 512 ∗
       memRegion (sp + 29360#64) 1536 ∗ memRegion (sp + 31408#64) 132 ∗
       memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
       memRegion (sp + 32736#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 28848#64 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [8#8])))) ∗
          PolyMem (sp + 26768#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8])))) ∗
          PolyMem (sp + 27280#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
          PolyMem (sp + 27792#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [6#8])))) ∗
          PolyMem (sp + 28304#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [7#8])))) ∗
          PolyMem (sp + 28848#64) (fun _ => 0#128) ∗ PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29872#64) (fun _ => 0#128) ∗ PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
          memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 24672#64) 33 ∗
          memRegion (sp + 31408#64) 132 ∗ memRegion (sp + 31936#64) 128 ∗
          memRegion (sp + 32288#64) 128 ∗ memRegion (sp + 32736#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  rcases seg3_regions_eq sp with ⟨_, _, _, hr512, _, _⟩
  rcases seg3_regions2_eq sp with ⟨_, hr31408_32, _, _, _⟩
  rw [hr512]
  refine SepWP.weaken_pre (by sep_frame : _ ⊢
    ((sp + 24672#64) ↦ₛ coins) ∗ memRegion (sp + 26768#64) 2048 ∗
      memRegion (sp + 31408#64) 132 ∗ memRegion (sp + 28848#64) 512 ∗
      memRegion (sp + 12832#64) 128 ∗ memRegion (sp + 32736#64) 128 ∗
      memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
      stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl hro
    (seg3_part2a hb hbase s sp coins _ hc hpc hrun hsp hspA hx19 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 _ _
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, _, hfp1, hv3_1, hcl1, hro1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [hr31408_32]
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hr512.symm) (by sep_frame) (by sep_frame) : _ ⊢
      ((sp + 28848#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
      ((sp + 28976#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
      ((sp + 29104#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
      ((sp + 29232#64) ↦ₛ shake256List 128 (coins ++ [7#8])) ∗
      memRegion (sp + 12832#64) 512 ∗
      PolyMem (sp + 26768#64) (fun _ => 0#128) ∗ PolyMem (sp + 27280#64) (fun _ => 0#128) ∗
      PolyMem (sp + 27792#64) (fun _ => 0#128) ∗ PolyMem (sp + 28304#64) (fun _ => 0#128) ∗
      ((sp + 24704#64) ↦₈ 0#8) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
      memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 29360#64) 1536 ∗
      memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗
      stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_part2b hb hbase s1 sp coins _ _ _ _ _ hc hpc1 hrun1 hsp1 hspA1
      hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hv3_1 hcl1 hro1) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hx20f, hfpf, hclf, hrof, hPf⟩
  rw [hfp1] at hfpf
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hx20f, hfpf, hclf, hrof,
    Entails.trans hPf (entails_sub (Entails.of_eq hr31408_32.symm) (by sep_frame) (by sep_frame))⟩

private theorem mid144_reframe (sp : BitVec 64) :
    memRegion (sp + 144#64) 1648 ∗ memRegion (sp + 1792#64) 640 ∗ memRegion (sp + 2432#64) 64 =
      memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 2000#64) 496 := by
  rcases seg3_regions_eq sp with ⟨h1, h2, _, _, _, _⟩
  exact h1.symm.trans h2

/-- Segment 3 (`+0x3d0c → +0x59d0`): sample `r̂[0..3]`, `e₁[0..3]`, `e₂`, copy `PublicKeyStateAt`
to `sp + 2560`, and zero `uVec[0..3]` at `sp + 28848`. -/
theorem seg3_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp0 : BitVec 64) (s0 : State) (ret pkA rA : BitVec 64)
    (pk rand : List (BitVec 8)) (Rest : SepProp)
    (s : State) (P : SepProp)
    (hpre : Seg2Post b sp0 s0 ret pkA rA pk rand Rest s P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Start) s P
      (Seg3Post b sp0 s0 ret pkA rA pk rand Rest) := by
  let sp := sp0 - 33104#64
  let hashed := sha3_512List (sha3_256List rand ++ sha3_256List pk)
  have hh : hashed.length = 64 := sha3_512List_length _
  have hc : (hashed.drop 32).length = 32 := by simp [List.length_drop, hh]
  rcases hpre with
    ⟨hpc, hrun, hsp, hspA, h16, hcl, hro, _, _, hx22, _, _, _, hfp, hP⟩
  rcases seg3_regions_eq sp with ⟨hr144a, _, _, _, _, _⟩
  rcases seg3_regions2_eq sp with ⟨hr31408_128, _, hr26768, hr28848_2048, hr11888⟩
  rcases seg3_regions3_eq sp with ⟨hr23104, hr30896⟩
  refine SepWP.weaken_pre hP ?_
  dsimp only [Seg2Spatial]
  have hpk12832 := publicKeyStateAt_12832_eq sp pk
  rw [hr144a, hr23104, hr26768, hr28848_2048, hr30896, hr31408_128]
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hpk12832) (by sep_frame) (by sep_frame) : _ ⊢
      ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
      memRegion (sp + 2560#64) 10272 ∗ PublicKeyStateAt (sp + 12832#64) pk ∗
      memRegion (sp + 23104#64) 1568 ∗ memRegion (sp + 24672#64) 33 ∗
      memRegion (sp + 24720#64) 2048 ∗ memRegion (sp + 26768#64) 132 ∗
      memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 31408#64) 128 ∗
      memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
      stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl hro
    (seg3_part1 hb hbase s sp pk hashed _ hh hpc hrun hsp hspA hx22 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 _ _ ⟨hsp1, hspA1, hx19_1, hfp1, hcl1, hro1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq (mid144_reframe sp)) (by sep_frame)
      (entails_sub (Entails.of_eq hr26768.symm) (by sep_frame)
        (entails_sub (Entails.of_eq hr31408_128.symm) (by sep_frame) (by sep_frame))) : _ ⊢
      ((sp + 24672#64) ↦ₛ hashed.drop 32) ∗ ((sp + 24704#64) ↦₈ 0#8) ∗
      memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 12832#64) 512 ∗
      memRegion (sp + 26768#64) 2048 ∗ memRegion (sp + 28848#64) 512 ∗
      memRegion (sp + 29360#64) 1536 ∗ memRegion (sp + 31408#64) 132 ∗
      memRegion (sp + 31936#64) 128 ∗ memRegion (sp + 32288#64) 128 ∗
      memRegion (sp + 32736#64) 128 ∗ stackAt sp 1136 ∗ _) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_part2 hb hbase s1 sp (hashed.drop 32) _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hcl1 hro1) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hx20f, hfpf, hclf, hrof, hPf⟩
  rw [hfp1, hfp] at hfpf
  refine SepWP.done hpcf hrunf ⟨hpcf, hrunf, hspf, hspAf, h16, hclf, hrof, hx20f, hfpf, ?_⟩
  dsimp only [Seg3Spatial]
  exact Entails.trans hPf
    (entails_sub (Entails.of_eq hr11888.symm) (by sep_frame)
      (entails_sub (Entails.of_eq hr30896.symm) (by sep_frame) (by sep_frame)))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3
