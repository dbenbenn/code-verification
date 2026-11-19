/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner

/-!
# `encapsulate1_serialized` (`B03`) — `Seg2` Symbolic Entry Builder & Clamp Dispatch (`Seg2Clamp`)

Shared symbolic entry state constructor (`mkSegState` / `mkSegEnv`) for `Seg2` ranges and proofs of
both post-`rej_sample` clamp/branch dispatchers (`+0x2500 → +0x026c / +0x2580` for `init3` and
`+0x31b8 → +0x026c / +0x2580` for `extra1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (clampSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2RegInv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem seedConstsWords treeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KConstsLoOpt KStateMatches KSpatial evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (
  readSlot slotHolds slotValid ushr64_truncate64_append vreg128_repack writeSlot)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  inv01Slots inv2Slots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  Seg2LoopState Seg2RowExit cfgClamp clampWord64_of_le271 multiLaneSampled3_eq_treeMem
  raw_sampled_le271 rowPermState rowSeeds)

attribute [local irreducible] keccakF1600 blkPC03

/-! ## 1. Pre-Clamp Slot Tables (`+0x21cc` and `+0x2e84`) & Symbolic Entry State Builder -/

@[expose] def preClamp01Slots : List KSlot :=
  [.vreg 18, .vreg 15, .spillQ 1984, .vreg 10, .vreg 26, .vreg 12, .spillQ 1136, .vreg 21, .vreg 28, .vreg 11,
   .vreg 14, .vreg 25, .vreg 9, .vreg 24, .vreg 5, .spillQ 1792, .vreg 23, .spillQ 1120, .vreg 31, .vreg 27,
   .spillQ 1008, .spillQ 1168, .spillQ 2080, .spillQ 1872, .spillQ 2128]

@[expose] def preClamp2Slots : List KSlot :=
  [.spillD 1456, .spillD 1968, .spillD 1632, .vregLo 0, .vregLo 13, .spillD 1584, .spillD 1600, .spillD 1616,
   .spillD 1888, .spillD 2048, .spillD 1568, .spillD 1728, .spillD 1744, .vregLo 16, .spillD 2032, .spillD 1488,
   .spillD 1712, .spillD 1840, .vregLo 6, .vregLo 8, .spillD 1312, .spillD 1152, .spillD 1184, .spillD 2176,
   .spillD 1952]

@[expose] def preExtra01Slots : List KSlot :=
  [.spillQ 1024, .spillQ 1680, .spillQ 1984, .spillQ 2096, .spillQ 2160, .spillQ 1056, .spillQ 1136, .spillQ 1856,
   .spillQ 1920, .spillQ 1936, .spillQ 1040, .spillQ 1088, .spillQ 1104, .spillQ 1696, .spillQ 2112, .spillQ 1792,
   .spillQ 1072, .spillQ 1120, .spillQ 1904, .spillQ 2064, .spillQ 1008, .spillQ 1168, .spillQ 2080, .spillQ 1872,
   .spillQ 2128]

@[expose] def preExtra2Slots : List KSlot :=
  [.vregLo 18, .spillD 1968, .spillD 1632, .vregLo 0, .vregLo 13, .spillD 1584, .spillD 1600, .vregLo 28,
   .vregLo 15, .vregLo 14, .vregLo 11, .vregLo 23, .vregLo 21, .vregLo 22, .vregLo 12, .vregLo 30,
   .vregLo 24, .vregLo 20, .vregLo 6, .vregLo 5, .vregLo 27, .vregLo 7, .vregLo 29, .spillD 2176, .vregLo 19]

@[expose] def seedConstExprs : List KExpr :=
  [.const64 0xffffffffff0000ff#64, .const64 0xffffffffffffffff#64,
   .var 97, .var 97, .var 98, .var 98, .var 99, .var 99, .var 100, .var 100]

@[expose] def mkSegBaseState (hasSeedConsts : Bool) : KState :=
  { vregs := BTree.ofFn 5 fun vr => (.var (110 + 2 * vr), .var (110 + 2 * vr + 1))
    gprs := BTree.ofFn 5 fun g =>
      if g == 8 then .var 101
      else if g == 19 then .rcAdd 0#64
      else if g == 20 then .spAdd 4272#64
      else if g == 21 then .spAdd 12448#64
      else if g == 22 then .var 96
      else if g == 23 then .spAdd 2456#64
      else if g == 24 then .const64 544#64
      else if g == 25 then .spAdd 14248#64
      else if g == 26 then .spAdd 13995#64
      else if g == 27 then .const64 256#64
      else if g == 28 then .spAdd 13984#64
      else .var (200 + g)
    memA := BTree.ofFn 9 fun i =>
      if hasSeedConsts && (Nat.ble 30 i && Nat.blt i 40) then seedConstExprs.getD (i - 30) (.const64 0#64)
      else .var (300 + i)
    memB := BTree.ofFn 9 fun i => .var (900 + i)
    pstateFlag := none }

@[expose] def writeSlotsPair (cfg : KCfg) (offLo offHi : Nat) : Nat → List KSlot → KState → KState
  | _, [], st => st
  | idx, sl :: rest, st =>
      writeSlotsPair cfg offLo offHi (idx + 1) rest
        (writeSlot cfg st sl (.var (offLo + idx), .var (offHi + idx)))

@[expose] def writeSlotsSingle (cfg : KCfg) (offLo : Nat) : Nat → List KSlot → KState → KState
  | _, [], st => st
  | idx, sl :: rest, st =>
      writeSlotsSingle cfg offLo (idx + 1) rest
        (writeSlot cfg st sl (.var (offLo + idx), .const64 0#64))

@[expose] def mkSegState (cfg : KCfg) (hasSeedConsts : Bool) (slots01 slots2 : List KSlot) : KState :=
  writeSlotsSingle cfg 50 0 slots2 (writeSlotsPair cfg 0 25 0 slots01 (mkSegBaseState hasSeedConsts))

@[expose] def mkSegEnv [MlKemPlacement] (sp : BitVec 64) (row : Nat) (rho : List (BitVec 8))
    (k0 k1 k2 : KeccakState) (s : State) (tA tB : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp
    rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    rLoop := 0
    vars := fun id =>
      if id < 25 then k0.getD id 0#64
      else if id < 50 then k1.getD (id - 25) 0#64
      else if id < 75 then k2.getD (id - 50) 0#64
      else if id == 96 then BitVec.ofNat 64 row
      else if id == 97 then ByteSlice.readLE rho 24 8
      else if id == 98 then ByteSlice.readLE rho 16 8
      else if id == 99 then ByteSlice.readLE rho 8 8
      else if id == 100 then ByteSlice.readLE rho 0 8
      else if id == 101 then s.readReg64 .x8
      else if id < 174 then
        let k := id - 110
        let v := s.readVReg128 (BitVec.ofNat 5 (k / 2))
        if k % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 232 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 200)))
      else if id < 812 then tA.get (id - 300)
      else if id < 1412 then tB.get (id - 900)
      else 0#64 }

private theorem writeSlot_preserves {cfg : KCfg} {env : KEnv} {st : KState} {s : State}
    {tA : BTree (BitVec 64) 9} {sl : KSlot} {p : KExpr × KExpr}
    (hm : KStateMatches env st s) (htA : evalMemTree env st.memA = tA)
    (hsl : slotHolds cfg s tA sl (evalKExpr env p.1) (evalKExpr env p.2)) :
    KStateMatches env (writeSlot cfg st sl p) s ∧
      evalMemTree env (writeSlot cfg st sl p).memA = tA ∧
      (writeSlot cfg st sl p).memB = st.memB := by
  cases sl with
  | vreg r =>
      rcases hsl with ⟨hr, hv⟩; refine ⟨⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpflag⟩, htA, rfl⟩
      intro vr; simp only [writeSlot]; rw [BTree.get_set _ r p hr vr.toNat vr.isLt]
      by_cases heq : vr.toNat = r
      · have hvr : vr = BitVec.ofNat 5 r := BitVec.eq_of_toNat_eq (by simp [heq, Nat.mod_eq_of_lt hr])
        subst hvr; simpa [heq] using hv
      · simp [heq]; exact hm.hvregs vr
  | spillQ off =>
      rcases hsl with ⟨hidx, hlo, hhi⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩, ?_, rfl⟩
      apply Encaps1.Seg2Loop.btree_ext_get; intro j hj
      simp only [writeSlot, evalMemTree, BTree.get_map]
      rw [BTree.get_set _ _ _ hidx j hj]
      by_cases h1 : j = (off - cfg.offA) / 8 + 1
      · subst h1; simpa using hhi.symm
      · simp only [h1, ↓reduceIte]; rw [BTree.get_set _ _ _ (by omega) j hj]
        by_cases h0 : j = (off - cfg.offA) / 8
        · subst h0; simpa using hlo.symm
        · simp only [h0, ↓reduceIte]; rw [← htA, evalMemTree, BTree.get_map]
  | vregLo r =>
      rcases hsl with ⟨hr, hv⟩; refine ⟨⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpflag⟩, htA, rfl⟩
      intro vr; simp only [writeSlot]; rw [BTree.get_set _ r _ hr vr.toNat vr.isLt]
      by_cases heq : vr.toNat = r
      · have hvr : vr = BitVec.ofNat 5 r := BitVec.eq_of_toNat_eq (by simp [heq, Nat.mod_eq_of_lt hr])
        subst hvr; simp only [heq, ↓reduceIte]
        have hold := hm.hvregs (BitVec.ofNat 5 r)
        have hhi : ((s.readVReg128 (BitVec.ofNat 5 r)) >>> 64).truncate 64 =
            evalKExpr env (st.vregs.get r).2 := by
          rw [hold, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, ushr64_truncate64_append]
        calc s.readVReg128 (BitVec.ofNat 5 r)
          _ = ((s.readVReg128 (BitVec.ofNat 5 r)) >>> 64).truncate 64 ++
                (s.readVReg128 (BitVec.ofNat 5 r)).truncate 64 :=
              (vreg128_repack (s.readVReg128 (BitVec.ofNat 5 r))).symm
          _ = evalKExpr env (st.vregs.get r).2 ++ evalKExpr env p.1 := by rw [hhi, hv]
      · simp [heq]; exact hm.hvregs vr
  | spillD off =>
      rcases hsl with ⟨hidx, hlo⟩
      refine ⟨⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩, ?_, rfl⟩
      apply Encaps1.Seg2Loop.btree_ext_get; intro j hj
      simp only [writeSlot, evalMemTree, BTree.get_map]
      rw [BTree.get_set _ _ _ hidx j hj]
      by_cases h0 : j = (off - cfg.offA) / 8
      · subst h0; simpa using hlo.symm
      · simp only [h0, ↓reduceIte]; rw [← htA, evalMemTree, BTree.get_map]

private theorem mkSegBaseState_matches [MlKemPlacement] {sp : BitVec 64} {row : Nat}
    {rho : List (BitVec 8)} {k0 k1 k2 : KeccakState} {s : State} {tA tB : BTree (BitVec 64) 9}
    {hasSeedConsts : Bool} (hreg : Seg2RegInv sp s) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : hasSeedConsts = true → ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) :
    let env := mkSegEnv sp row rho k0 k1 k2 s tA tB
    KStateMatches env (mkSegBaseState hasSeedConsts) s ∧
      evalMemTree env (mkSegBaseState hasSeedConsts).memA = tA ∧
      evalMemTree env (mkSegBaseState hasSeedConsts).memB = tB := by
  intro env
  rcases hreg with ⟨hsp, hspA, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hx28⟩
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_, ?_⟩
  · intro vr
    simp only [mkSegBaseState]; rw [BTree.get_ofFn 5 _ vr.toNat vr.isLt]
    have hlt := vr.isLt
    have hb0 : ¬(110 + 2 * vr.toNat < 25) ∧ ¬(110 + 2 * vr.toNat < 50) ∧ ¬(110 + 2 * vr.toNat < 75) ∧
        110 + 2 * vr.toNat < 174 := ⟨by omega, by omega, by omega, by omega⟩
    have hb1 : ¬(110 + 2 * vr.toNat + 1 < 25) ∧ ¬(110 + 2 * vr.toNat + 1 < 50) ∧
        ¬(110 + 2 * vr.toNat + 1 < 75) ∧ 110 + 2 * vr.toNat + 1 < 174 := ⟨by omega, by omega, by omega, by omega⟩
    have hn0 : ∀ c ∈ [96, 97, 98, 99, 100, 101], (110 + 2 * vr.toNat == c) = false :=
      fun c hc => beq_false_of_ne (by simp at hc; omega)
    have hn1 : ∀ c ∈ [96, 97, 98, 99, 100, 101], (110 + 2 * vr.toNat + 1 == c) = false :=
      fun c hc => beq_false_of_ne (by simp at hc; omega)
    have hd0 : (110 + 2 * vr.toNat - 110) / 2 = vr.toNat := by omega
    have hm0 : ((110 + 2 * vr.toNat - 110) % 2 == 0) = true := beq_iff_eq.mpr (by omega)
    have hd1 : (110 + 2 * vr.toNat + 1 - 110) / 2 = vr.toNat := by omega
    have hm1 : ((110 + 2 * vr.toNat + 1 - 110) % 2 == 0) = false := beq_false_of_ne (by omega)
    simp only [evalKExpr, env, mkSegEnv, hb0.1, hb0.2.1, hb0.2.2.1, hb0.2.2.2,
      hb1.1, hb1.2.1, hb1.2.2.1, hb1.2.2.2,
      hn0 96 (by simp), hn0 97 (by simp), hn0 98 (by simp), hn0 99 (by simp), hn0 100 (by simp), hn0 101 (by simp),
      hn1 96 (by simp), hn1 97 (by simp), hn1 98 (by simp), hn1 99 (by simp), hn1 100 (by simp), hn1 101 (by simp),
      ↓reduceIte, hd0, hm0, hd1, hm1, Bool.false_eq_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (vreg128_repack (s.readVReg128 vr)).symm
  · intro g hg31
    simp only [mkSegBaseState]; rw [BTree.get_ofFn 5 _ g.toNat g.isLt]
    have hlt := g.isLt
    by_cases h8 : g = 8#5; · subst h8; rfl
    by_cases h19 : g = 19#5; · subst h19; simpa [evalKExpr, env, mkSegEnv] using hx19
    by_cases h20 : g = 20#5; · subst h20; exact hx20
    by_cases h21 : g = 21#5; · subst h21; exact hx21
    by_cases h22 : g = 22#5; · subst h22; exact hx22
    by_cases h23 : g = 23#5; · subst h23; exact hx23
    by_cases h24 : g = 24#5; · subst h24; exact hx24
    by_cases h25 : g = 25#5; · subst h25; exact hx25
    by_cases h26 : g = 26#5
    · subst h26; change s.readReg64 (.gpr 26#5) = sp + 13995#64; rw [hx26]; bv_omega
    by_cases h27 : g = 27#5; · subst h27; exact hx27
    by_cases h28 : g = 28#5; · subst h28; exact hx28
    have hne : ∀ c : Fin 32, g ≠ BitVec.ofNat 5 c.1 → (g.toNat == c.1) = false := fun c hc =>
      beq_false_of_ne fun he => hc (BitVec.eq_of_toNat_eq (by simp [he]))
    simp only [hne ⟨8, by decide⟩ h8, hne ⟨19, by decide⟩ h19, hne ⟨20, by decide⟩ h20,
      hne ⟨21, by decide⟩ h21, hne ⟨22, by decide⟩ h22, hne ⟨23, by decide⟩ h23,
      hne ⟨24, by decide⟩ h24, hne ⟨25, by decide⟩ h25, hne ⟨26, by decide⟩ h26,
      hne ⟨27, by decide⟩ h27, hne ⟨28, by decide⟩ h28, Bool.false_eq_true, ↓reduceIte]
    simp only [evalKExpr, env, mkSegEnv, show ¬(200 + g.toNat < 25) by omega,
      show ¬(200 + g.toNat < 50) by omega, show ¬(200 + g.toNat < 75) by omega,
      beq_false_of_ne (show 200 + g.toNat ≠ 96 by omega),
      beq_false_of_ne (show 200 + g.toNat ≠ 97 by omega),
      beq_false_of_ne (show 200 + g.toNat ≠ 98 by omega),
      beq_false_of_ne (show 200 + g.toNat ≠ 99 by omega),
      beq_false_of_ne (show 200 + g.toNat ≠ 100 by omega),
      beq_false_of_ne (show 200 + g.toNat ≠ 101 by omega),
      show ¬(200 + g.toNat < 174) by omega, show 200 + g.toNat < 232 by omega,
      ↓reduceIte, Bool.false_eq_true, show 200 + g.toNat - 200 = g.toNat by omega,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · apply Encaps1.Seg2Loop.btree_ext_get; intro j hj
    simp only [evalMemTree, BTree.get_map, mkSegBaseState]
    rw [BTree.get_ofFn 9 _ j hj]
    cases hasSeedConsts with
    | false =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, evalKExpr, env, mkSegEnv,
          show ¬(300 + j < 25) by omega, show ¬(300 + j < 50) by omega, show ¬(300 + j < 75) by omega,
          beq_false_of_ne (show 300 + j ≠ 96 by omega), beq_false_of_ne (show 300 + j ≠ 97 by omega),
          beq_false_of_ne (show 300 + j ≠ 98 by omega), beq_false_of_ne (show 300 + j ≠ 99 by omega),
          beq_false_of_ne (show 300 + j ≠ 100 by omega), beq_false_of_ne (show 300 + j ≠ 101 by omega),
          show ¬(300 + j < 174) by omega, show ¬(300 + j < 232) by omega,
          show 300 + j < 812 by omega, show 300 + j - 300 = j by omega]
    | true =>
        by_cases h30 : 30 ≤ j ∧ j < 40
        · have hb30 : (Nat.ble 30 j && Nat.blt j 40) = true := by
            simp [Nat.ble_eq, Nat.blt_eq, h30]
          simp only [Bool.true_and, hb30, ↓reduceIte]
          have hi := htA rfl (j - 30) (by omega)
          rw [show 30 + (j - 30) = j by omega] at hi
          rcases (show j - 30 = 0 ∨ j - 30 = 1 ∨ j - 30 = 2 ∨ j - 30 = 3 ∨ j - 30 = 4 ∨
              j - 30 = 5 ∨ j - 30 = 6 ∨ j - 30 = 7 ∨ j - 30 = 8 ∨ j - 30 = 9 by omega) with
            h | h | h | h | h | h | h | h | h | h <;>
            (rw [hi, h]; simp [seedConstExprs, seedConstsWords, evalKExpr, env, mkSegEnv])
        · have hb30 : (Nat.ble 30 j && Nat.blt j 40) = false :=
            Bool.eq_false_iff.mpr (by simp [Nat.ble_eq, Nat.blt_eq]; omega)
          simp only [Bool.true_and, hb30, Bool.false_eq_true, ↓reduceIte, evalKExpr, env, mkSegEnv,
            show ¬(300 + j < 25) by omega, show ¬(300 + j < 50) by omega, show ¬(300 + j < 75) by omega,
            beq_false_of_ne (show 300 + j ≠ 96 by omega), beq_false_of_ne (show 300 + j ≠ 97 by omega),
            beq_false_of_ne (show 300 + j ≠ 98 by omega), beq_false_of_ne (show 300 + j ≠ 99 by omega),
            beq_false_of_ne (show 300 + j ≠ 100 by omega), beq_false_of_ne (show 300 + j ≠ 101 by omega),
            show ¬(300 + j < 174) by omega, show ¬(300 + j < 232) by omega,
            show 300 + j < 812 by omega, show 300 + j - 300 = j by omega]
  · apply Encaps1.Seg2Loop.btree_ext_get; intro j hj
    simp only [evalMemTree, BTree.get_map, mkSegBaseState]
    rw [BTree.get_ofFn 9 _ j hj]
    simp only [evalKExpr, env, mkSegEnv,
      show ¬(900 + j < 25) by omega, show ¬(900 + j < 50) by omega, show ¬(900 + j < 75) by omega,
      beq_false_of_ne (show 900 + j ≠ 96 by omega), beq_false_of_ne (show 900 + j ≠ 97 by omega),
      beq_false_of_ne (show 900 + j ≠ 98 by omega), beq_false_of_ne (show 900 + j ≠ 99 by omega),
      beq_false_of_ne (show 900 + j ≠ 100 by omega), beq_false_of_ne (show 900 + j ≠ 101 by omega),
      show ¬(900 + j < 174) by omega, show ¬(900 + j < 232) by omega, show ¬(900 + j < 812) by omega,
      show 900 + j < 1412 by omega, ↓reduceIte, Bool.false_eq_true, show 900 + j - 900 = j by omega]

private theorem writeSlotsPair_matches {cfg : KCfg} {env : KEnv} {k0 k1 : KeccakState}
    {s : State} {tA : BTree (BitVec 64) 9} {mB0 : BTree KExpr 9}
    (hv0 : ∀ k, k < 25 → evalKExpr env (.var k) = k0.getD k 0#64)
    (hv1 : ∀ k, k < 25 → evalKExpr env (.var (25 + k)) = k1.getD k 0#64)
    (rem : List KSlot) :
    ∀ (k : Nat) (st : KState),
      k + rem.length ≤ 25 →
      (∀ j, j < rem.length →
        slotHolds cfg s tA (rem.getD j (.vreg 0)) (k0.getD (k + j) 0#64) (k1.getD (k + j) 0#64)) →
      KStateMatches env st s → evalMemTree env st.memA = tA → st.memB = mB0 →
      KStateMatches env (writeSlotsPair cfg 0 25 k rem st) s ∧
        evalMemTree env (writeSlotsPair cfg 0 25 k rem st).memA = tA ∧
        (writeSlotsPair cfg 0 25 k rem st).memB = mB0 := by
  induction rem with
  | nil => intro _ _ _ _ hm htA hmB; exact ⟨hm, htA, hmB⟩
  | cons sl rest ih =>
      intro k st hsum hsl hm htA hmB
      have hlen : (sl :: rest).length = rest.length + 1 := rfl
      have hk : k < 25 := by omega
      have hsl0 : slotHolds cfg s tA sl (evalKExpr env (.var (0 + k))) (evalKExpr env (.var (25 + k))) := by
        rw [Nat.zero_add, hv0 k hk, hv1 k hk]
        have h0 := hsl 0 (by omega)
        simpa only [List.getD_cons_zero, Nat.add_zero] using h0
      rcases writeSlot_preserves (p := (.var (0 + k), .var (25 + k))) hm htA hsl0 with ⟨hm1, htA1, hmB1⟩
      exact ih (k + 1) _ (by omega)
        (fun j hj => by
          have hj1 := hsl (j + 1) (by omega)
          rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j by omega] at hj1
          exact hj1)
        hm1 htA1 (hmB1.trans hmB)

private theorem writeSlotsSingle_matches {cfg : KCfg} {env : KEnv} {k2 : KeccakState}
    {s : State} {tA : BTree (BitVec 64) 9} {mB0 : BTree KExpr 9}
    (hv2 : ∀ k, k < 25 → evalKExpr env (.var (50 + k)) = k2.getD k 0#64)
    (rem : List KSlot) :
    ∀ (k : Nat) (st : KState),
      k + rem.length ≤ 25 →
      (∀ j, j < rem.length →
        slotHolds cfg s tA (rem.getD j (.vreg 0)) (k2.getD (k + j) 0#64) 0#64) →
      KStateMatches env st s → evalMemTree env st.memA = tA → st.memB = mB0 →
      KStateMatches env (writeSlotsSingle cfg 50 k rem st) s ∧
        evalMemTree env (writeSlotsSingle cfg 50 k rem st).memA = tA ∧
        (writeSlotsSingle cfg 50 k rem st).memB = mB0 := by
  induction rem with
  | nil => intro _ _ _ _ hm htA hmB; exact ⟨hm, htA, hmB⟩
  | cons sl rest ih =>
      intro k st hsum hsl hm htA hmB
      have hlen : (sl :: rest).length = rest.length + 1 := rfl
      have hk : k < 25 := by omega
      have hsl0 : slotHolds cfg s tA sl (evalKExpr env (.var (50 + k))) (evalKExpr env (.const64 0#64)) := by
        rw [hv2 k hk]; dsimp only [evalKExpr]
        have h0 := hsl 0 (by omega)
        simpa only [List.getD_cons_zero, Nat.add_zero] using h0
      rcases writeSlot_preserves (p := (.var (50 + k), .const64 0#64)) hm htA hsl0 with ⟨hm1, htA1, hmB1⟩
      exact ih (k + 1) _ (by omega)
        (fun j hj => by
          have hj1 := hsl (j + 1) (by omega)
          rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j by omega] at hj1
          exact hj1)
        hm1 htA1 (hmB1.trans hmB)

theorem mkSegState_matches [MlKemPlacement] {cfg : KCfg} {hasSeedConsts : Bool}
    {slots01 slots2 : List KSlot} {sp : BitVec 64} {row : Nat} {rho : List (BitVec 8)}
    {k0 k1 k2 : KeccakState} {s : State} {tA tB : BTree (BitVec 64) 9}
    (hl01 : slots01.length ≤ 25) (hl2 : slots2.length ≤ 25)
    (hreg : Seg2RegInv sp s) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : hasSeedConsts = true → ∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64)
    (hs01 : ∀ idx, idx < slots01.length →
      slotHolds cfg s tA (slots01.getD idx (.vreg 0)) (k0.getD idx 0#64) (k1.getD idx 0#64))
    (hs2 : ∀ idx, idx < slots2.length →
      slotHolds cfg s tA (slots2.getD idx (.vreg 0)) (k2.getD idx 0#64) 0#64) :
    let env := mkSegEnv sp row rho k0 k1 k2 s tA tB
    let st := mkSegState cfg hasSeedConsts slots01 slots2
    KStateMatches env st s ∧ evalMemTree env st.memA = tA ∧ evalMemTree env st.memB = tB := by
  intro env st
  rcases mkSegBaseState_matches (k0 := k0) (k1 := k1) (k2 := k2) (tA := tA) (tB := tB)
    hreg hx22 htA with ⟨hm0, htA0, htB0⟩
  have hv0 : ∀ k, k < 25 → evalKExpr env (.var k) = k0.getD k 0#64 :=
    fun k hk => by simp [evalKExpr, env, mkSegEnv, hk]
  have hv1 : ∀ k, k < 25 → evalKExpr env (.var (25 + k)) = k1.getD k 0#64 := fun k hk => by
    simp [evalKExpr, env, mkSegEnv, show ¬(25 + k < 25) by omega,
      show 25 + k < 50 by omega, show 25 + k - 25 = k by omega]
  have hv2 : ∀ k, k < 25 → evalKExpr env (.var (50 + k)) = k2.getD k 0#64 := fun k hk => by
    simp [evalKExpr, env, mkSegEnv, show ¬(50 + k < 25) by omega,
      show ¬(50 + k < 50) by omega, show 50 + k < 75 by omega, show 50 + k - 50 = k by omega]
  rcases writeSlotsPair_matches (cfg := cfg) hv0 hv1 slots01 0 _ (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hs01 j hj) hm0 htA0 rfl with ⟨hm1, htA1, hmB1⟩
  rcases writeSlotsSingle_matches (cfg := cfg) hv2 slots2 0 _ (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hs2 j hj) hm1 htA1 rfl with ⟨hm2, htA2, hmB2⟩
  exact ⟨hm2, htA2, by dsimp only [st, mkSegState]; rw [hmB2, hmB1, htB0]⟩

/-! ## 2. Clamp Post-State Checker & `+0x2500` / `+0x31b8` Dispatchers -/

@[expose] def checkSegRegGprs (st : KState) (eX8 : KExpr) : Bool :=
  (st.gprs.get 8).beq eX8 &&
  (st.gprs.get 19).beq (.rcAdd 0#64) &&
  (st.gprs.get 20).beq (.spAdd 4272#64) &&
  (st.gprs.get 21).beq (.spAdd 12448#64) &&
  (st.gprs.get 22).beq (.var 96) &&
  (st.gprs.get 23).beq (.spAdd 2456#64) &&
  (st.gprs.get 24).beq (.const64 544#64) &&
  (st.gprs.get 25).beq (.spAdd 14248#64) &&
  (st.gprs.get 26).beq (.spAdd 13995#64) &&
  (st.gprs.get 27).beq (.const64 256#64) &&
  (st.gprs.get 28).beq (.spAdd 13984#64)

@[expose] def checkSeedConstsMemA (st : KState) : Bool :=
  (List.range 10).all fun i => (st.memA.get (30 + i)).beq (seedConstExprs.getD i (.const64 0#64))

@[expose] def checkClampEnd (st : KState) (checkInvSlots : Bool) : Bool :=
  checkSegRegGprs st (.var 101) &&
  checkSeedConstsMemA st &&
  (st.memB.get 0).beq (.clamp64 (.var 900)) &&
  (st.memB.get 1).beq (.clamp64 (.var 901)) &&
  (st.memB.get 2).beq (.clamp64 (.var 902)) &&
  (!checkInvSlots ||
    (((List.range 25).all fun idx =>
        let sl := inv01Slots.getD idx (.vreg 0)
        slotValid cfgClamp sl &&
          (readSlot cfgClamp st sl).1.beq (.var idx) &&
          (readSlot cfgClamp st sl).2.beq (.var (25 + idx))) &&
     ((List.range 25).all fun idx =>
        let sl := inv2Slots.getD idx (.vreg 0)
        slotValid cfgClamp sl &&
          (readSlot cfgClamp st sl).1.beq (.var (50 + idx)) &&
          (readSlot cfgClamp st sl).2.beq (.const64 0#64))))

theorem eq_some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o <;> simp_all

theorem sepWP_drop_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {A Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s Q post oom) :
    SepWP prog target_pc s (A ∗ Q) post oom := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm))

theorem extract_segRegInv [MlKemPlacement] {sp : BitVec 64} {row : Nat} {eX8 : KExpr}
    {env : KEnv} {st : KState} {sf : State}
    (hm : KStateMatches env st sf) (hsp : env.sp = sp)
    (hrc : env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (hv96 : env.vars 96 = BitVec.ofNat 64 row)
    (hchk : checkSegRegGprs st eX8 = true) :
    Seg2RegInv sp sf ∧ sf.readReg64 .x8 = evalKExpr env eX8 ∧
      sf.readReg64 .x22 = BitVec.ofNat 64 row := by
  simp only [checkSegRegGprs, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g8, g19⟩, g20⟩, g21⟩, g22⟩, g23⟩, g24⟩, g25⟩, g26⟩, g27⟩, g28⟩
  have rg : ∀ (g : Fin 32), g.1 ≠ 31 → ∀ {e : KExpr}, (st.gprs.get g.1).beq e = true →
      sf.readReg64 (.gpr (BitVec.ofNat 5 g.1)) = evalKExpr env e := by
    intro g hg e hb
    have r := hm.hgprs (BitVec.ofNat 5 g.1) (by
      intro h; apply hg; have := congrArg BitVec.toNat h
      simpa [Nat.mod_eq_of_lt g.2] using this)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt g.2, KExpr.beq_eq_true hb] at r
    exact r
  refine ⟨⟨hm.hsp.trans hsp, hm.hsp_al, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rg ⟨8, by decide⟩ (by decide) g8, ?_⟩
  · simpa [evalKExpr, hrc] using rg ⟨19, by decide⟩ (by decide) g19
  · simpa [evalKExpr, hsp] using rg ⟨20, by decide⟩ (by decide) g20
  · simpa [evalKExpr, hsp] using rg ⟨21, by decide⟩ (by decide) g21
  · simpa [evalKExpr, hsp] using rg ⟨23, by decide⟩ (by decide) g23
  · simpa [evalKExpr] using rg ⟨24, by decide⟩ (by decide) g24
  · simpa [evalKExpr, hsp] using rg ⟨25, by decide⟩ (by decide) g25
  · have r26 := rg ⟨26, by decide⟩ (by decide) g26
    dsimp only [evalKExpr] at r26; rw [hsp] at r26; rw [r26]; bv_omega
  · simpa [evalKExpr] using rg ⟨27, by decide⟩ (by decide) g27
  · simpa [evalKExpr, hsp] using rg ⟨28, by decide⟩ (by decide) g28
  · simpa [evalKExpr, hv96] using rg ⟨22, by decide⟩ (by decide) g22

theorem extract_seedConsts {rho : List (BitVec 8)} {env : KEnv} {st : KState}
    (hv97 : env.vars 97 = ByteSlice.readLE rho 24 8)
    (hv98 : env.vars 98 = ByteSlice.readLE rho 16 8)
    (hv99 : env.vars 99 = ByteSlice.readLE rho 8 8)
    (hv100 : env.vars 100 = ByteSlice.readLE rho 0 8)
    (hchk : checkSeedConstsMemA st = true) :
    ∀ i, i < 10 → (evalMemTree env st.memA).get (30 + i) = (seedConstsWords rho).getD i 0#64 := by
  intro i hi
  have hall : (st.memA.get (30 + i)).beq (seedConstExprs.getD i (.const64 0#64)) = true :=
    (List.all_eq_true.mp hchk) i (List.mem_range.mpr hi)
  rw [evalMemTree, BTree.get_map, KExpr.beq_eq_true hall]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [seedConstExprs, seedConstsWords, evalKExpr, hv97, hv98, hv99, hv100]

theorem finish_clamp_branch [MlKemPlacement] {b sp : BitVec 64}
    {rho : List (BitVec 8)} {row extra : Nat} {F : SepProp}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    {env : KEnv} {st : KState} {sf : State}
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) extra sampled hws)
    (hm : KStateMatches env st sf) (hsp : env.sp = sp)
    (hrc : env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (hv96 : env.vars 96 = BitVec.ofNat 64 row)
    (hv97 : env.vars 97 = ByteSlice.readLE rho 24 8)
    (hv98 : env.vars 98 = ByteSlice.readLE rho 16 8)
    (hv99 : env.vars 99 = ByteSlice.readLE rho 8 8)
    (hv100 : env.vars 100 = ByteSlice.readLE rho 0 8)
    (hv101 : env.vars 101 = BitVec.ofNat 64 (row + 1))
    (hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 (extra + 2)).getD idx 0#64)
    (hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 (extra + 2)).getD idx 0#64)
    (hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 (extra + 2)).getD idx 0#64)
    (hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0))
    (hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1))
    (hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2))
    (isExit : Bool) (hdone : allLanesDone 3 (rowSeeds rho row) extra = isExit)
    (hpc : sf.pc = if isExit then b + 0x026c#64 else b + 0x2580#64)
    (hrun : sf.status = .Running)
    (hchk : checkClampEnd st (!isExit) = true) :
    let FF := Seg2ConstsLo sp ∗ memRegion (sp + 2192#64) 1512 ∗
      MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ memRegion (sp + 13984#64) 504 ∗ F
    SepWP (blkPC03.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) extra then b + 0x026c#64 else b + 0x2580#64)
      sf (KSpatial cfgClamp env st FF)
      (fun sOut POut => mlkemMultiLib.CodeLoaded mlkemMpl sOut.mem → MlKemRoOk mlkemMpl sOut.mem →
        if allLanesDone 3 (rowSeeds rho row) extra then Seg2RowExit b sp rho row F sOut POut
        else Seg2LoopState b sp rho row F extra sOut POut) := by
  intro FF
  rw [hdone]
  simp only [checkClampEnd, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hregC, hseedC⟩, hm0⟩, hm1⟩, hm2⟩, hslotsC⟩
  rcases extract_segRegInv hm hsp hrc hv96 hregC with ⟨hreg, hx8, hx22⟩
  rw [evalKExpr, hv101] at hx8
  have htA := extract_seedConsts hv97 hv98 hv99 hv100 hseedC
  have hclamp : MultiLaneXofInv 3 (rowSeeds rho row) extra (fun i => clampSampled (sampled i)) hws :=
    hraw.clamp
  have htB : ∀ i, i < 3 →
      (evalMemTree env st.memB).get i = BitVec.ofNat 64 (clampSampled (sampled i)) := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [evalMemTree, BTree.get_map, KExpr.beq_eq_true hm0, evalKExpr, evalKExpr, hb0]
      exact clampWord64_of_le271 (raw_sampled_le271 hraw (by decide))
    · rw [evalMemTree, BTree.get_map, KExpr.beq_eq_true hm1, evalKExpr, evalKExpr, hb1]
      exact clampWord64_of_le271 (raw_sampled_le271 hraw (by decide))
    · rw [evalMemTree, BTree.get_map, KExpr.beq_eq_true hm2, evalKExpr, evalKExpr, hb2]
      exact clampWord64_of_le271 (raw_sampled_le271 hraw (by decide))
  have hsampMem : TreeMem (sp + 12448#64) 3 (evalMemTree env st.memB) =
      MultiLaneSampled (sp + 12448#64) 3 (fun i => clampSampled (sampled i)) :=
    (multiLaneSampled3_eq_treeMem sp _ _
      (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide))).symm
  apply sepWP_drop_left
  cases isExit with
  | true =>
      simp only [↓reduceIte] at hpc ⊢
      refine SepWP.done hpc hrun fun hcl hro => ⟨hpc, hrun, hcl, hro, hreg, hx8, hx22, extra,
        evalMemTree env st.memA, fun i => clampSampled (sampled i), hws, hdone, hclamp, htA, ?_⟩
      dsimp only [KConstsLoOpt, cfgClamp, FF]
      rw [emp_sepConj, hsp, show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
        show sp + BitVec.ofNat 64 12448 = sp + 12448#64 from rfl]
      exact Entails.trans (by sep_frame : _ ⊢ TreeMem (sp + 12448#64) 3 (evalMemTree env st.memB) ∗
          (Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 (evalMemTree env st.memA) ∗
            memRegion (sp + 2192#64) 1512 ∗ MultiLaneSlots (sp + 4272#64) 544 3 hws ∗
            memRegion (sp + 13984#64) 504 ∗ F))
        (Entails.trans (sepConj_mono_left (treeMem_entails_memRegion (evalMemTree env st.memB) (by decide))) (by sep_frame))
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
      simp only [Bool.not_false, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hslotsC
      rcases hslotsC with ⟨hs01, hs2⟩
      refine SepWP.done hpc hrun fun hcl hro => ⟨hpc, hrun, hcl, hro, hreg, hx8, hx22,
        evalMemTree env st.memA, fun i => clampSampled (sampled i), hws, htA, ?_, ?_, hclamp, ?_⟩
      · intro idx hidx
        have hi := (List.all_eq_true.mp hs01) idx (List.mem_range.mpr hidx)
        simp only [Bool.and_eq_true] at hi
        have hsl := Seg2Runner.eval_checked_slot (ok := fun _ => true) (envSpec := env) hm
          (fun _ _ => rfl) _ hi.1.1 _ _ hi.1.2 hi.2 rfl rfl
        simpa [evalKExpr, hv0 idx hidx, hv1 idx hidx] using hsl
      · intro idx hidx
        have hi := (List.all_eq_true.mp hs2) idx (List.mem_range.mpr hidx)
        simp only [Bool.and_eq_true] at hi
        have hsl := Seg2Runner.eval_checked_slot (ok := fun _ => true) (envSpec := env) hm
          (fun _ _ => rfl) _ hi.1.1 _ _ hi.1.2 hi.2 rfl rfl
        simpa [evalKExpr, hv2 idx hidx] using hsl
      · dsimp only [KConstsLoOpt, cfgClamp, FF]
        rw [emp_sepConj, hsp, show sp + BitVec.ofNat 64 96 = sp + 96#64 from rfl,
          show sp + BitVec.ofNat 64 12448 = sp + 12448#64 from rfl, hsampMem]
        sep_frame

theorem with_frozen_env [MlKemPlacement] {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf =>
      mlkemMultiLib.CodeLoaded mlkemMpl sf.mem → MlKemRoOk mlkemMpl sf.mem → post sf Pf)) :
    SepWP prog tgt s P post :=
  SepWP.mono_frozen (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m ∧ MlKemRoOk mlkemMpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
    ⟨hcl, hro⟩ h (fun _ _ _ _ ⟨hc, hr⟩ hp => hp hc hr)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp
