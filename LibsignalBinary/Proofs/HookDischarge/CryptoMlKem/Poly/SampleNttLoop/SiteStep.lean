/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkStep

/-!
# Outer `204`-Instruction `N`-Lane `rej_sample` Site Composition (`SampleNttLoop.SiteStep`)

`204`-instruction (`pcAt pcBase 4 → pcAt pcBase 204`) outer and inner `rej_sample` site theorem
(`step_rej_site_lanes`) shared across all 10 sites in `B03`–`B07`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (parseRej12Candidates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (packHalfwordsLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt brDisp pcAt pcAt_brDisp pcAt_succ rBuf rRem rSampled rSlotBase
  readReg64_writeReg64_ne_of rejClobberedRegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (
  RejVariant rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneRawInv MultiLaneSampled MultiLaneSlots sepLoad64_multiLaneSampled
  sepStore64_multiLaneSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkStep (
  ClobberedPreserved step_rej_chunks_inv)

/-- Per-site register and count configuration for all 10 `B03`–`B07` `rej_sample` sites. -/
structure RejSiteConfig where
  v : RejVariant
  nLanes : Nat
  nChunks : Nat
  slotStride : Nat
  rIdx : Reg
  rSqPtr : Reg
  rPrevIdx : Reg
  rSampArr : Reg
  rSlotStride : Reg
  rSlotsBase : Reg

@[expose] def RejSiteConfig.siteClobberedRegs (cfg : RejSiteConfig) : List Reg :=
  [cfg.rIdx, cfg.rSqPtr, cfg.rPrevIdx, rSlotBase cfg.v.isVarA] ++ rejClobberedRegs cfg.v.isVarA

@[expose] def RejSiteConfig.siteDistinctRegs (cfg : RejSiteConfig) : List Reg :=
  [cfg.rIdx, cfg.rSqPtr, cfg.rPrevIdx, cfg.rSampArr, cfg.rSlotStride, cfg.rSlotsBase,
   rSlotBase cfg.v.isVarA, .sp, .xzr, .gpr 31#5]

@[expose] def RejSiteConfig.Valid (cfg : RejSiteConfig) : Prop :=
  1 ≤ cfg.nLanes ∧ cfg.nLanes < 2 ^ 12 ∧ 1 ≤ cfg.nChunks ∧ 24 * cfg.nChunks < 2 ^ 12 ∧
  cfg.siteDistinctRegs.Nodup ∧
  ∀ r ∈ [cfg.rIdx, cfg.rSqPtr, cfg.rPrevIdx, cfg.rSampArr, cfg.rSlotStride,
         cfg.rSlotsBase, .sp, .xzr, .gpr 31#5], r ∉ rejClobberedRegs cfg.v.isVarA

@[expose] def decMemReg (x : Reg) : (xs : List Reg) → Decidable (x ∈ xs)
  | [] => isFalse List.not_mem_nil
  | y :: ys =>
    letI := decMemReg x ys
    decidable_of_iff (x = y ∨ x ∈ ys) List.mem_cons.symm

@[expose] def decBallNotMem (bad : List Reg) : (xs : List Reg) → Decidable (∀ r ∈ xs, r ∉ bad)
  | [] => isTrue (by intro _ h; cases h)
  | x :: xs =>
    letI := decMemReg x bad
    letI := decBallNotMem bad xs
    decidable_of_iff (x ∉ bad ∧ ∀ r ∈ xs, r ∉ bad)
      ⟨fun ⟨hx, hxs⟩ r hr => by
          rcases List.mem_cons.mp hr with rfl | hrs
          · exact hx
          · exact hxs r hrs,
       fun hall =>
          ⟨hall x (List.mem_cons.mpr (Or.inl rfl)),
           fun r hrs => hall r (List.mem_cons.mpr (Or.inr hrs))⟩⟩

@[expose] def decNodupReg : (xs : List Reg) → Decidable xs.Nodup
  | [] => isTrue List.Pairwise.nil
  | x :: xs =>
    letI := decMemReg x xs
    letI := decNodupReg xs
    decidable_of_iff (x ∉ xs ∧ xs.Nodup) List.nodup_cons.symm

instance (cfg : RejSiteConfig) : Decidable cfg.Valid := by
  unfold RejSiteConfig.Valid
  letI := decNodupReg cfg.siteDistinctRegs
  letI := decBallNotMem (rejClobberedRegs cfg.v.isVarA)
    [cfg.rIdx, cfg.rSqPtr, cfg.rPrevIdx, cfg.rSampArr, cfg.rSlotStride,
     cfg.rSlotsBase, .sp, .xzr, .gpr 31#5]
  infer_instance

@[expose] def SitePreserved (cfg : RejSiteConfig) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp ∧ s.vregs = s0.vregs ∧
  ∀ r, r ∉ cfg.siteClobberedRegs → s.readReg64 r = s0.readReg64 r

theorem SitePreserved.refl {cfg : RejSiteConfig} {s0 : State} (hrun : s0.status = .Running) :
    SitePreserved cfg s0 s0 := ⟨hrun, rfl, rfl, fun _ _ => rfl⟩

theorem SitePreserved.trans {cfg : RejSiteConfig} {s0 s1 s2 : State}
    (h1 : SitePreserved cfg s0 s1) (h2 : SitePreserved cfg s1 s2) : SitePreserved cfg s0 s2 :=
  ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun r hr => (h2.2.2.2 r hr).trans (h1.2.2.2 r hr)⟩

private theorem SitePreserved.of_clobbered {cfg : RejSiteConfig} {s0 s : State}
    (h : ClobberedPreserved cfg.v.isVarA s0 s) : SitePreserved cfg s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r fun hc => hr (by simp [RejSiteConfig.siteClobberedRegs, hc])⟩

theorem SitePreserved.setPState {cfg : RejSiteConfig} {s0 s : State}
    (h : SitePreserved cfg s0 s) (ps : PState) : SitePreserved cfg s0 (s.setPState ps) :=
  ⟨h.1, h.2.1, h.2.2.1, fun r hr => (by cases s; cases r <;> rfl : (s.setPState ps).readReg64 r = s.readReg64 r).trans (h.2.2.2 r hr)⟩

theorem SitePreserved.setMem {cfg : RejSiteConfig} {s0 s : State}
    (h : SitePreserved cfg s0 s) (m : Memory) : SitePreserved cfg s0 (s.setMem m) :=
  ⟨h.1, h.2.1, h.2.2.1, fun r hr => (by cases s; cases r <;> rfl : (s.setMem m).readReg64 r = s.readReg64 r).trans (h.2.2.2 r hr)⟩

theorem SitePreserved.writeClobbered {cfg : RejSiteConfig} {s0 s : State}
    (h : SitePreserved cfg s0 s) (rt : Reg) (val : BitVec 64)
    (hrt : rt ∈ cfg.siteClobberedRegs) (_hsp_ne : rt ≠ .sp) :
    SitePreserved cfg s0 (s.writeReg64 rt val) := by
  refine ⟨h.1, ?_, h.2.2.1, fun r hr => ?_⟩
  · simp [State.writeReg64, h.2.1]
  · have hne : r ≠ rt := by intro heq; subst heq; exact hr hrt
    exact (readReg64_writeReg64_ne_of s hne).trans (h.2.2.2 r hr)

/-- Outer `[0..10]` lane-dispatch & `sampled`-store instructions shared by all 10 `B03`–`B07` sites. -/
@[expose] def rejOuterInstrs (cfg : RejSiteConfig) : List Instr :=
  [.addSubImm .W64 .SUBS .xzr cfg.rIdx (BitVec.ofNat 12 cfg.nLanes) false,
   .addSubImm .W64 .ADD cfg.rSqPtr cfg.rSqPtr (BitVec.ofNat 12 (24 * cfg.nChunks)) false,
   .str .X64 (rSampled cfg.v.isVarA) (.RegOffset cfg.rSampArr cfg.rPrevIdx .UXTX 3),
   .bCond .EQ (brDisp 3 204),
   .dataProc3 .W64 .MADD (rSlotBase cfg.v.isVarA) cfg.rIdx cfg.rSlotStride cfg.rSlotsBase,
   .ldr .W64 .X64 false (rSampled cfg.v.isVarA) (.RegOffset cfg.rSampArr cfg.rIdx .UXTX 3),
   .logicalShift .W64 .ORR cfg.rPrevIdx .xzr cfg.rIdx .LSL 0,
   .addSubImm .W64 .ADD cfg.rIdx cfg.rIdx 1#12 false,
   .logicalShift .W64 .ORR (rBuf cfg.v.isVarA) .xzr cfg.rSqPtr .LSL 0,
   .moveWide .W32 .MOVZ (rRem cfg.v.isVarA) (BitVec.ofNat 16 cfg.nChunks) 0,
   .b (brDisp 10 15)]

/-- Complete `204`-instruction (`[0..203]`) `rej_sample` site instruction list. -/
@[expose] def rejSiteInstrs (cfg : RejSiteConfig) : List Instr := rejOuterInstrs cfg ++ rejInnerInstrs cfg.v

private theorem zext64_ofNat12 {m : Nat} (hm : m < 2 ^ 12) : (BitVec.ofNat 12 m).zeroExtend 64 = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.zeroExtend, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega : m < 2 ^ 64)]

private theorem setWidth64_ofNat16 {n : Nat} (hn : n < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

private theorem shl3_ofNat64 (k : Nat) : (BitVec.ofNat 64 k) <<< 3 = BitVec.ofNat 64 (8 * k) := by bv_omega

private theorem condHolds_cmp64_eq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 12) :
    ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 a) ((BitVec.ofNat 12 b).zeroExtend 64)) =
      decide (a = b) := by
  rw [zext64_ofNat12 hb, conditionHolds_eq_subsPState64]
  by_cases hab : a = b
  · subst hab; simp
  · have hne : (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := beq_false_of_ne fun heq => hab (by
      have hn := congrArg BitVec.toNat heq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)] at hn; exact hn)
    simp [hab, hne]

private theorem mem_of_get? {α : Type} : ∀ {l : List α} {k : Nat} {z : α}, l[k]? = some z → z ∈ l
  | [], k, _, h => by cases k <;> simp at h
  | _ :: _, 0, _, h => by simp at h; exact h ▸ .head _
  | _ :: _, k + 1, _, h => .tail _ (mem_of_get? (by simpa using h))

private theorem nodup_get_ne {α : Type} : ∀ {l : List α} (_ : l.Nodup) {i j : Nat} {x y : α},
    l[i]? = some x → l[j]? = some y → i ≠ j → x ≠ y
  | [], _, i, _, _, _, hi, _, _ => by cases i <;> simp at hi
  | _ :: _, _, 0, 0, _, _, _, _, hne => absurd rfl hne
  | _ :: _, hnd, 0, _ + 1, _, _, hi, hj, _ => by
    simp at hi hj; subst hi; exact fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ mem_of_get? hj)
  | _ :: _, hnd, _ + 1, 0, _, _, hi, hj, _ => by
    simp at hi hj; subst hj; exact fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ mem_of_get? hi)
  | _ :: _, hnd, _ + 1, _ + 1, _, _, hi, hj, hne =>
    nodup_get_ne (List.nodup_cons.mp hnd).2 (by simpa using hi) (by simpa using hj) (by omega)

private theorem not_siteClobbered {cfg : RejSiteConfig} (hv : cfg.Valid) {i : Nat} {r : Reg}
    (hi : cfg.siteDistinctRegs[i]? = some r) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h6 : i ≠ 6)
    (hm : r ∈ [cfg.rIdx, cfg.rSqPtr, cfg.rPrevIdx, cfg.rSampArr, cfg.rSlotStride, cfg.rSlotsBase, .sp, .xzr, .gpr 31#5]) :
    r ∉ cfg.siteClobberedRegs := by
  simp only [RejSiteConfig.siteClobberedRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨⟨nodup_get_ne hv.2.2.2.2.1 hi rfl h0, nodup_get_ne hv.2.2.2.2.1 hi rfl h1,
    nodup_get_ne hv.2.2.2.2.1 hi rfl h2, nodup_get_ne hv.2.2.2.2.1 hi rfl h6⟩, hv.2.2.2.2.2 r hm⟩

private theorem readReg64_writeReg64_self (s : State) {r : Reg} (val : BitVec 64)
    (hxzr : r ≠ .xzr) (h31 : r ≠ .gpr 31#5) : (s.writeReg64 r val).readReg64 r = val := by
  cases r with
  | gpr idx =>
    have hne : (idx == 31#5) = false := beq_false_of_ne fun h => h31 (congrArg Reg.gpr h)
    simp [State.writeReg64, State.readReg64, hne, RegFile.read, RegFile.write]
  | sp => rfl
  | xzr => exact absurd rfl hxzr

@[simp] private theorem setPC_setPC' (s : State) (a b : BitVec 64) : (s.setPC a).setPC b = s.setPC b := by cases s; rfl
@[simp] private theorem readReg64_setPC' (s : State) (a : BitVec 64) (r : Reg) : (s.setPC a).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] private theorem readReg64_setPState' (s : State) (ps : PState) (r : Reg) : (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] private theorem pstate_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).pstate = s.pstate := by cases s; cases r <;> rfl
@[simp] private theorem pstate_setMem' (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by cases s; rfl
@[simp] private theorem setPC_writeReg64_setPC' (s : State) (a b : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).setPC b = (s.writeReg64 r v).setPC b := by cases s; cases r <;> rfl
private theorem advancePC_writeReg64_setPC (s : State) (a : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).advancePC = (s.writeReg64 r v).setPC (a + 4#64) := by cases s; cases r <;> rfl
private theorem advancePC_setPState_setPC (s : State) (a : BitVec 64) (ps : PState) :
    ((s.setPC a).setPState ps).advancePC = (s.setPState ps).setPC (a + 4#64) := by cases s; rfl
private theorem setMem_setPC (s : State) (a : BitVec 64) (m : Memory) : (s.setPC a).setMem m = (s.setMem m).setPC a := by cases s; rfl
private theorem swap_slot_front (Pbuf Psamp Pslot Fslot F : SepProp) :
    Pbuf ∗ (Psamp ∗ ((Pslot ∗ Fslot) ∗ F)) = Pbuf ∗ (Pslot ∗ (Psamp ∗ (Fslot ∗ F))) := by
  simp only [sepConj_assoc]; congr 1; rw [← sepConj_assoc Psamp Pslot, sepConj_comm Psamp Pslot, sepConj_assoc]

private theorem dNe {cfg : RejSiteConfig} (hv : cfg.Valid) {i j : Nat} {x y : Reg}
    (hi : cfg.siteDistinctRegs[i]? = some x) (hj : cfg.siteDistinctRegs[j]? = some y) (hne : i ≠ j) : x ≠ y :=
  nodup_get_ne hv.2.2.2.2.1 hi hj hne

private theorem ne_of_mem_rej {cfg : RejSiteConfig} (hv : cfg.Valid) {r r' : Reg}
    (hm : r ∈ [cfg.rIdx, cfg.rSqPtr, cfg.rPrevIdx, cfg.rSampArr, cfg.rSlotStride, cfg.rSlotsBase, .sp, .xzr, .gpr 31#5])
    (hr' : r' ∈ rejClobberedRegs cfg.v.isVarA) : r ≠ r' :=
  fun heq => hv.2.2.2.2.2 r hm (heq ▸ hr')

private theorem step_site_enter_lane {prog : Program} {target pcBase sqBase sampBase slotsBase : BitVec 64}
    {cfg : RejSiteConfig} {k : Nat} {sampled : Nat → Nat} {s0 s : State} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hv : cfg.Valid) (hk : k < cfg.nLanes) (hf : FetchesInstrsAt prog pcBase 0 (rejOuterInstrs cfg))
    (hp : SitePreserved cfg s0 s) (hsampA : s0.readReg64 cfg.rSampArr = sampBase)
    (hstr : s0.readReg64 cfg.rSlotStride = BitVec.ofNat 64 cfg.slotStride)
    (hslots : s0.readReg64 cfg.rSlotsBase = slotsBase) (hidx : s.readReg64 cfg.rIdx = BitVec.ofNat 64 k)
    (hsq : s.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11))
    (hcont : ∀ sE : State, SitePreserved cfg s0 sE →
      sE.readReg64 (rSlotBase cfg.v.isVarA) = slotsBase + BitVec.ofNat 64 (cfg.slotStride * k) →
      sE.readReg64 (rSampled cfg.v.isVarA) = BitVec.ofNat 64 (sampled k) →
      sE.readReg64 cfg.rPrevIdx = BitVec.ofNat 64 k → sE.readReg64 cfg.rIdx = BitVec.ofNat 64 (k + 1) →
      sE.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11) →
      sE.readReg64 (rBuf cfg.v.isVarA) = (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k)) + 11#64 →
      sE.readReg64 (rRem cfg.v.isVarA) = BitVec.ofNat 64 cfg.nChunks →
      SepWP prog target (sE.setPC (pcAt pcBase 15)) (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗ F)) post oom) :
    SepWP prog target (s.setPC (pcAt pcBase 4)) (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗ F)) post oom := by
  have hrSamp : s.readReg64 cfg.rSampArr = sampBase :=
    (hp.2.2.2 _ (not_siteClobbered hv (i := 3) rfl (by decide) (by decide) (by decide) (by decide) (by simp))).trans hsampA
  have hrStr : s.readReg64 cfg.rSlotStride = BitVec.ofNat 64 cfg.slotStride :=
    (hp.2.2.2 _ (not_siteClobbered hv (i := 4) rfl (by decide) (by decide) (by decide) (by decide) (by simp))).trans hstr
  have hrSlots : s.readReg64 cfg.rSlotsBase = slotsBase :=
    (hp.2.2.2 _ (not_siteClobbered hv (i := 5) rfl (by decide) (by decide) (by decide) (by decide) (by simp))).trans hslots
  have hSmpRej : rSampled cfg.v.isVarA ∈ rejClobberedRegs cfg.v.isVarA := by cases cfg.v <;> simp [rejClobberedRegs]
  have hBufRej : rBuf cfg.v.isVarA ∈ rejClobberedRegs cfg.v.isVarA := by cases cfg.v <;> simp [rejClobberedRegs]
  have hRemRej : rRem cfg.v.isVarA ∈ rejClobberedRegs cfg.v.isVarA := by cases cfg.v <;> simp [rejClobberedRegs]
  let slot_k := slotsBase + BitVec.ofNat 64 (cfg.slotStride * k)
  obtain ⟨s4, hs4⟩ : ∃ st, s.writeReg64 (rSlotBase cfg.v.isVarA) slot_k = st := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ st, s4.writeReg64 (rSampled cfg.v.isVarA) (BitVec.ofNat 64 (sampled k)) = st := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ st, s5.writeReg64 cfg.rPrevIdx (BitVec.ofNat 64 k) = st := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ st, s6.writeReg64 cfg.rIdx (BitVec.ofNat 64 (k + 1)) = st := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ st, s7.writeReg64 (rBuf cfg.v.isVarA) (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11)) = st := ⟨_, rfl⟩
  obtain ⟨s9, hs9⟩ : ∃ st, s8.writeReg64 (rRem cfg.v.isVarA) (BitVec.ofNat 64 cfg.nChunks) = st := ⟨_, rfl⟩
  refine SepWP.step_pure (s' := s4.setPC (pcAt pcBase 5)) rfl hp.1 (hf.get 4) ?_ (by rw [← hs4]; rfl) ?_
  · have hmul : BitVec.ofNat 64 k * BitVec.ofNat 64 cfg.slotStride = BitVec.ofNat 64 (cfg.slotStride * k) := by
      rw [← BitVec.ofNat_mul, Nat.mul_comm]
    simp [Program.evalInst, execInstWithSvc, execDataProc3, hrSlots, hidx, hrStr, hmul,
      State.writeReg, advancePC_writeReg64_setPC, pcAt_succ, hs4, slot_k]
  have hp4 : SitePreserved cfg s0 s4 := hs4 ▸ hp.writeClobbered (rSlotBase cfg.v.isVarA) slot_k
    (by simp [RejSiteConfig.siteClobberedRegs]) (dNe hv (i := 6) (j := 7) rfl rfl (by decide))
  have hidx4 : s4.readReg64 cfg.rIdx = BitVec.ofNat 64 k := by
    rw [← hs4, readReg64_writeReg64_ne_of s (dNe hv (i := 0) (j := 6) rfl rfl (by decide)), hidx]
  have hsamp4 : s4.readReg64 cfg.rSampArr = sampBase := by
    rw [← hs4, readReg64_writeReg64_ne_of s (dNe hv (i := 3) (j := 6) rfl rfl (by decide)), hrSamp]
  refine SepWP.step_ldr64 (s' := s5.setPC (pcAt pcBase 6)) (ea := sampBase + ((BitVec.ofNat 64 k) <<< 3))
    (wb := none) (v := BitVec.ofNat 64 (sampled k)) rfl hp4.1 (hf.get 5)
    (by have := dNe hv (i := 3) (j := 7) rfl rfl (by decide)
        cases h : cfg.rSampArr <;> simp_all [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
    (by simp [evalAddrMode, extendVal, hsamp4, hidx4])
    (sepLoad64_multiLaneSampled hk (by rw [← sepConj_assoc, sepConj_comm Pbuf, sepConj_assoc]) (by rw [shl3_ofNat64]))
    (by simp [applyWriteback, setPC_writeReg64_setPC', pcAt_succ, hs5]) ?_
  have hp5 : SitePreserved cfg s0 s5 := hs5 ▸ hp4.writeClobbered (rSampled cfg.v.isVarA) (BitVec.ofNat 64 (sampled k))
    (by simp [RejSiteConfig.siteClobberedRegs, hSmpRej]) (by cases cfg.v <;> decide)
  have hidx5 : s5.readReg64 cfg.rIdx = BitVec.ofNat 64 k := by
    rw [← hs5, readReg64_writeReg64_ne_of s4 (ne_of_mem_rej hv (by simp) hSmpRej), hidx4]
  refine SepWP.step_pure (s' := s6.setPC (pcAt pcBase 7)) rfl hp5.1 (hf.get 6)
    (by simp [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical, shiftVal, shift64,
        State.readReg, hidx5, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ, hs6]) (by rw [← hs6]; rfl) ?_
  have hp6 : SitePreserved cfg s0 s6 := hs6 ▸ hp5.writeClobbered cfg.rPrevIdx (BitVec.ofNat 64 k)
    (by simp [RejSiteConfig.siteClobberedRegs]) (dNe hv (i := 2) (j := 7) rfl rfl (by decide))
  have hidx6 : s6.readReg64 cfg.rIdx = BitVec.ofNat 64 k := by
    rw [← hs6, readReg64_writeReg64_ne_of s5 (dNe hv (i := 0) (j := 2) rfl rfl (by decide)), hidx5]
  refine SepWP.step_pure (s' := s7.setPC (pcAt pcBase 8)) rfl hp6.1 (hf.get 7)
    (by have hadd1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by bv_omega
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hidx6, hadd1,
          State.writeReg, advancePC_writeReg64_setPC, pcAt_succ, hs7]) (by rw [← hs7]; rfl) ?_
  have hp7 : SitePreserved cfg s0 s7 := hs7 ▸ hp6.writeClobbered cfg.rIdx (BitVec.ofNat 64 (k + 1))
    (by simp [RejSiteConfig.siteClobberedRegs]) (dNe hv (i := 0) (j := 7) rfl rfl (by decide))
  have hsq7 : s7.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11) := by
    rw [← hs7, readReg64_writeReg64_ne_of s6 (dNe hv (i := 1) (j := 0) rfl rfl (by decide)),
      ← hs6, readReg64_writeReg64_ne_of s5 (dNe hv (i := 1) (j := 2) rfl rfl (by decide)),
      ← hs5, readReg64_writeReg64_ne_of s4 (ne_of_mem_rej hv (by simp) hSmpRej),
      ← hs4, readReg64_writeReg64_ne_of s (dNe hv (i := 1) (j := 6) rfl rfl (by decide)), hsq]
  refine SepWP.step_pure (s' := s8.setPC (pcAt pcBase 9)) rfl hp7.1 (hf.get 8)
    (by simp [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical, shiftVal, shift64,
        State.readReg, hsq7, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ, hs8]) (by rw [← hs8]; rfl) ?_
  have hp8 : SitePreserved cfg s0 s8 := hs8 ▸ hp7.writeClobbered (rBuf cfg.v.isVarA) (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11))
    (by simp [RejSiteConfig.siteClobberedRegs, hBufRej]) (by cases cfg.v <;> decide)
  refine SepWP.step_pure (s' := s9.setPC (pcAt pcBase 10)) rfl hp8.1 (hf.get 9)
    (by simp [Program.evalInst, execInstWithSvc, execMoveWide, State.writeReg,
          advancePC_writeReg64_setPC, pcAt_succ]
        rw [setWidth64_ofNat16 (by have := hv.2.2.2.1; omega), hs9]) (by rw [← hs9]; rfl) ?_
  have hp9 : SitePreserved cfg s0 s9 := hs9 ▸ hp8.writeClobbered (rRem cfg.v.isVarA) (BitVec.ofNat 64 cfg.nChunks)
    (by simp [RejSiteConfig.siteClobberedRegs, hRemRej]) (by cases cfg.v <;> decide)
  refine SepWP.step_pure (s' := s9.setPC (pcAt pcBase 15)) rfl hp9.1 (hf.get 10)
    (by simp [Program.evalInst, execInstWithSvc, pcAt_brDisp]) rfl ?_
  refine hcont s9 hp9 ?_ ?_ ?_ ?_ ?_ ?_
    (by rw [← hs9]; exact readReg64_writeReg64_self s8 (BitVec.ofNat 64 cfg.nChunks) (by cases cfg.v <;> decide) (by cases cfg.v <;> decide))
  · rw [← hs9, readReg64_writeReg64_ne_of s8 (by cases cfg.v <;> decide),
      ← hs8, readReg64_writeReg64_ne_of s7 (by cases cfg.v <;> decide),
      ← hs7, readReg64_writeReg64_ne_of s6 (dNe hv (i := 6) (j := 0) rfl rfl (by decide)),
      ← hs6, readReg64_writeReg64_ne_of s5 (dNe hv (i := 6) (j := 2) rfl rfl (by decide)),
      ← hs5, readReg64_writeReg64_ne_of s4 (by cases cfg.v <;> decide), ← hs4]
    exact readReg64_writeReg64_self s _ (dNe hv (i := 6) (j := 8) rfl rfl (by decide)) (dNe hv (i := 6) (j := 9) rfl rfl (by decide))
  · rw [← hs9, readReg64_writeReg64_ne_of s8 (by cases cfg.v <;> decide),
      ← hs8, readReg64_writeReg64_ne_of s7 (by cases cfg.v <;> decide),
      ← hs7, readReg64_writeReg64_ne_of s6 (ne_of_mem_rej hv (by simp) hSmpRej).symm,
      ← hs6, readReg64_writeReg64_ne_of s5 (ne_of_mem_rej hv (by simp) hSmpRej).symm, ← hs5]
    exact readReg64_writeReg64_self s4 (BitVec.ofNat 64 (sampled k)) (by cases cfg.v <;> decide) (by cases cfg.v <;> decide)
  · rw [← hs9, readReg64_writeReg64_ne_of s8 (ne_of_mem_rej hv (by simp) hRemRej),
      ← hs8, readReg64_writeReg64_ne_of s7 (ne_of_mem_rej hv (by simp) hBufRej),
      ← hs7, readReg64_writeReg64_ne_of s6 (dNe hv (i := 2) (j := 0) rfl rfl (by decide)), ← hs6]
    exact readReg64_writeReg64_self s5 _ (dNe hv (i := 2) (j := 8) rfl rfl (by decide)) (dNe hv (i := 2) (j := 9) rfl rfl (by decide))
  · rw [← hs9, readReg64_writeReg64_ne_of s8 (ne_of_mem_rej hv (by simp) hRemRej),
      ← hs8, readReg64_writeReg64_ne_of s7 (ne_of_mem_rej hv (by simp) hBufRej), ← hs7]
    exact readReg64_writeReg64_self s6 _ (dNe hv (i := 0) (j := 8) rfl rfl (by decide)) (dNe hv (i := 0) (j := 9) rfl rfl (by decide))
  · rw [← hs9, readReg64_writeReg64_ne_of s8 (ne_of_mem_rej hv (by simp) hRemRej),
      ← hs8, readReg64_writeReg64_ne_of s7 (ne_of_mem_rej hv (by simp) hBufRej), hsq7]
  · rw [← hs9, readReg64_writeReg64_ne_of s8 (by cases cfg.v <;> decide), ← hs8]
    have hbv : sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11) =
        (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k)) + 11#64 := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (readReg64_writeReg64_self s7 _ (by cases cfg.v <;> decide) (by cases cfg.v <;> decide)).trans hbv

private theorem step_site_finish_lane {prog : Program} {target pcBase sqBase sampBase : BitVec 64}
    {cfg : RejSiteConfig} {k sk' : Nat} {sampled : Nat → Nat} {s0 sF : State} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hv : cfg.Valid) (hk : k < cfg.nLanes) (hf : FetchesInstrsAt prog pcBase 0 (rejOuterInstrs cfg))
    (hp : SitePreserved cfg s0 sF) (hsampA : s0.readReg64 cfg.rSampArr = sampBase)
    (hsampF : sF.readReg64 (rSampled cfg.v.isVarA) = BitVec.ofNat 64 sk')
    (hprevF : sF.readReg64 cfg.rPrevIdx = BitVec.ofNat 64 k)
    (hidxF : sF.readReg64 cfg.rIdx = BitVec.ofNat 64 (k + 1))
    (hsqF : sF.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11))
    (hcont : ∀ sN : State, SitePreserved cfg s0 sN →
      sN.readReg64 cfg.rIdx = BitVec.ofNat 64 (k + 1) →
      sN.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * (k + 1) + 11) →
      SepWP prog target (sN.setPC (if k + 1 = cfg.nLanes then pcAt pcBase 204 else pcAt pcBase 4))
        (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes (fun i => if i = k then sk' else sampled i) ∗ F)) post oom) :
    SepWP prog target (sF.setPC (pcAt pcBase 0)) (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗ F)) post oom := by
  have hSmpRej : rSampled cfg.v.isVarA ∈ rejClobberedRegs cfg.v.isVarA := by cases cfg.v <;> simp [rejClobberedRegs]
  let psC := subsPState64 (BitVec.ofNat 64 (k + 1)) ((BitVec.ofNat 12 cfg.nLanes).zeroExtend 64)
  let sqNext := sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * (k + 1) + 11)
  let s1 := sF.setPState psC
  let s2 := s1.writeReg64 cfg.rSqPtr sqNext
  refine SepWP.step_pure (s' := s1.setPC (pcAt pcBase 1)) rfl hp.1 (hf.get 0)
    (by simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hidxF, State.writeReg,
        advancePC_setPState_setPC, pcAt_succ, s1, psC]) rfl ?_
  refine SepWP.step_pure (s' := s2.setPC (pcAt pcBase 2)) rfl hp.1 (hf.get 1)
    (by have hsq1 : s1.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11) := by
          simpa [s1] using hsqF
        have hsqAdd : (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11)) +
            BitVec.setWidth 64 (BitVec.ofNat 12 (24 * cfg.nChunks)) = sqNext := by
          change (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11)) +
            (BitVec.ofNat 12 (24 * cfg.nChunks)).zeroExtend 64 = sqNext
          rw [zext64_ofNat12 hv.2.2.2.1, BitVec.add_assoc, ← BitVec.ofNat_add]
          have hn : (24 * cfg.nChunks * k + 11) + 24 * cfg.nChunks = 24 * cfg.nChunks * (k + 1) + 11 := by
            rw [Nat.mul_succ]; omega
          rw [hn]
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hsq1, hsqAdd,
          State.writeReg, advancePC_writeReg64_setPC, pcAt_succ, s2]) rfl ?_
  have hp2 := (hp.setPState psC).writeClobbered cfg.rSqPtr sqNext
    (by simp [RejSiteConfig.siteClobberedRegs]) (dNe hv (i := 1) (j := 7) rfl rfl (by decide))
  have hsamp2 : s2.readReg64 cfg.rSampArr = sampBase :=
    (hp2.2.2.2 _ (not_siteClobbered hv (i := 3) rfl (by decide) (by decide) (by decide) (by decide) (by simp))).trans hsampA
  have hprev2 : s2.readReg64 cfg.rPrevIdx = BitVec.ofNat 64 k := by
    rw [show s2 = s1.writeReg64 cfg.rSqPtr sqNext from rfl,
      readReg64_writeReg64_ne_of s1 (dNe hv (i := 2) (j := 1) rfl rfl (by decide))]
    simpa [s1] using hprevF
  have hsval2 : s2.readReg64 (rSampled cfg.v.isVarA) = BitVec.ofNat 64 sk' := by
    rw [show s2 = s1.writeReg64 cfg.rSqPtr sqNext from rfl,
      readReg64_writeReg64_ne_of s1 (ne_of_mem_rej hv (by simp) hSmpRej).symm]
    simpa [s1] using hsampF
  refine SepWP.step_str64 (s' := s2.setPC (pcAt pcBase 3)) (ea := sampBase + ((BitVec.ofNat 64 k) <<< 3))
    (wb := none) (val := BitVec.ofNat 64 sk')
    (P' := Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes (fun i => if i = k then sk' else sampled i) ∗ F))
    rfl hp2.1 (hf.get 2)
    (by have := dNe hv (i := 3) (j := 7) rfl rfl (by decide)
        cases h : cfg.rSampArr <;> simp_all [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
    (by simp [evalAddrMode, extendVal, hsamp2, hprev2]) (by simp [hsval2])
    (sepStore64_multiLaneSampled hk (by rw [← sepConj_assoc, sepConj_comm Pbuf, sepConj_assoc])
      (by rw [← sepConj_assoc, sepConj_comm Pbuf, sepConj_assoc]) (by rw [shl3_ofNat64]))
    (by simp [applyWriteback, pcAt_succ]) fun m' => ?_
  rw [setMem_setPC]
  let s3 := s2.setMem m'
  have hp3 := hp2.setMem m'
  have hpst2 : s2.pstate = psC := by simp [s2, s1]
  have hcond : ConditionHolds .EQ psC = decide (k + 1 = cfg.nLanes) :=
    condHolds_cmp64_eq_ofNat (a := k + 1) (b := cfg.nLanes) (by have := hv.2.1; omega) hv.2.1
  refine SepWP.step_pure (s' := s3.setPC (if k + 1 = cfg.nLanes then pcAt pcBase 204 else pcAt pcBase 4))
    rfl hp3.1 (hf.get 3)
    (by by_cases hlast : k + 1 = cfg.nLanes <;>
        simp [Program.evalInst, execInstWithSvc, s3, hpst2, hcond, hlast, pcAt_brDisp,
          State.advancePC_setPC, pcAt_succ (pcBase := pcBase) (idx := 3)]) rfl ?_
  refine hcont s3 hp3 ?_ ?_
  · rw [show s3 = s2.setMem m' from rfl, readReg64_setMem',
      show s2 = s1.writeReg64 cfg.rSqPtr sqNext from rfl,
      readReg64_writeReg64_ne_of s1 (dNe hv (i := 0) (j := 1) rfl rfl (by decide))]
    simpa [s1] using hidxF
  · rw [show s3 = s2.setMem m' from rfl, readReg64_setMem',
      show s2 = s1.writeReg64 cfg.rSqPtr sqNext from rfl]
    exact readReg64_writeReg64_self s1 sqNext (dNe hv (i := 1) (j := 8) rfl rfl (by decide))
      (dNe hv (i := 1) (j := 9) rfl rfl (by decide))

private theorem step_rej_site_lanes_from {prog : Program} {target pcBase sqBase sampBase slotsBase : BitVec 64}
    {cfg : RejSiteConfig} {bufs : Nat → List (BitVec 8)} {s0 : State} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hv : cfg.Valid) (hfOuter : FetchesInstrsAt prog pcBase 0 (rejOuterInstrs cfg))
    (hfInner : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs cfg.v))
    (hread : ∀ i, i < cfg.nLanes → RejBufReadable (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * i)) (bufs i) cfg.nChunks Pbuf)
    (hbufLen : ∀ i, i < cfg.nLanes → 24 * cfg.nChunks ≤ (bufs i).length)
    (hsampA : s0.readReg64 cfg.rSampArr = sampBase)
    (hstr : s0.readReg64 cfg.rSlotStride = BitVec.ofNat 64 cfg.slotStride)
    (hslots : s0.readReg64 cfg.rSlotsBase = slotsBase) :
    ∀ (rem k : Nat) (cands : Nat → List Nat) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)) (s : State),
      k + (rem + 1) = cfg.nLanes → SitePreserved cfg s0 s →
      MultiLaneRawInv cfg.nLanes cands sampled hws →
      s.readReg64 cfg.rIdx = BitVec.ofNat 64 k →
      s.readReg64 cfg.rSqPtr = sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * k + 11) →
      (∀ (sF : State) (sampled' : Nat → Nat) (hws' : Nat → List (BitVec 16)),
        SitePreserved cfg s0 sF →
        MultiLaneRawInv cfg.nLanes (fun i => if k ≤ i then cands i ++ parseRej12Candidates ((bufs i).take (24 * cfg.nChunks)) else cands i) sampled' hws' →
        SepWP prog target (sF.setPC (pcAt pcBase 204))
          (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled' ∗ (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws' ∗ F))) post oom) →
      SepWP prog target (s.setPC (pcAt pcBase 4))
        (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗ (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws ∗ F))) post oom := by
  intro rem; induction rem with
  | zero =>
    intro k cands sampled hws s hsum hp hinv hidx hsq hcont
    have hk : k < cfg.nLanes := by omega
    refine step_site_enter_lane hv hk hfOuter hp hsampA hstr hslots hidx hsq fun sE hpE hslotE hsampE hprevE hidxE hsqE hbufE hremE => ?_
    rcases MultiLaneSlots.focus (slotsBase := slotsBase) (slotStride := cfg.slotStride) hk hws with ⟨Fslot, hSlotEq, hSlotUpd⟩
    rw [hSlotEq, swap_slot_front]
    refine step_rej_chunks_inv hpE.1 hfInner (hread k hk) hv.2.2.1 (by have := hv.2.2.2.1; omega)
      (hbufLen k hk) (hinv k hk) hslotE hsampE hbufE hremE fun sC sk' hwsk' hclobC hsampC hinvk' => ?_
    rw [← swap_slot_front, hSlotUpd hwsk']
    refine step_site_finish_lane hv hk hfOuter (hpE.trans (SitePreserved.of_clobbered hclobC)) hsampA hsampC
      ((hclobC.2.2.2 _ (hv.2.2.2.2.2 _ (by simp))).trans hprevE)
      ((hclobC.2.2.2 _ (hv.2.2.2.2.2 _ (by simp))).trans hidxE)
      ((hclobC.2.2.2 _ (hv.2.2.2.2.2 _ (by simp))).trans hsqE) fun sN hpN _ _ => ?_
    simpa [show k + 1 = cfg.nLanes by omega] using hcont sN _ _ hpN fun i hi => by
      by_cases hik : i = k
      · subst hik; simpa using hinvk'
      · simp [hik, show ¬ (k ≤ i) by omega]; exact hinv i hi
  | succ rem' ih =>
    intro k cands sampled hws s hsum hp hinv hidx hsq hcont
    have hk : k < cfg.nLanes := by omega
    refine step_site_enter_lane hv hk hfOuter hp hsampA hstr hslots hidx hsq fun sE hpE hslotE hsampE hprevE hidxE hsqE hbufE hremE => ?_
    rcases MultiLaneSlots.focus (slotsBase := slotsBase) (slotStride := cfg.slotStride) hk hws with ⟨Fslot, hSlotEq, hSlotUpd⟩
    rw [hSlotEq, swap_slot_front]
    refine step_rej_chunks_inv hpE.1 hfInner (hread k hk) hv.2.2.1 (by have := hv.2.2.2.1; omega)
      (hbufLen k hk) (hinv k hk) hslotE hsampE hbufE hremE fun sC sk' hwsk' hclobC hsampC hinvk' => ?_
    rw [← swap_slot_front, hSlotUpd hwsk']
    refine step_site_finish_lane hv hk hfOuter (hpE.trans (SitePreserved.of_clobbered hclobC)) hsampA hsampC
      ((hclobC.2.2.2 _ (hv.2.2.2.2.2 _ (by simp))).trans hprevE)
      ((hclobC.2.2.2 _ (hv.2.2.2.2.2 _ (by simp))).trans hidxE)
      ((hclobC.2.2.2 _ (hv.2.2.2.2.2 _ (by simp))).trans hsqE) fun sN hpN hidxN hsqN => ?_
    simp only [show k + 1 ≠ cfg.nLanes by omega, ↓reduceIte]
    refine ih (k + 1) (fun i => if i = k then cands i ++ parseRej12Candidates ((bufs i).take (24 * cfg.nChunks)) else cands i)
      _ _ sN (by omega) hpN
      (fun i hi => by
        by_cases hik : i = k
        · subst hik; simpa using hinvk'
        · simp only [hik, ↓reduceIte]; exact hinv i hi)
      hidxN hsqN
      fun sF sampledF hwsF hpF hinvF => hcont sF sampledF hwsF hpF fun i hi => ?_
    have hF := hinvF i hi
    by_cases hik : i = k
    · subst hik; simpa [show ¬ (i + 1 ≤ i) by omega] using hF
    · simpa [hik, show (k + 1 ≤ i) ↔ (k ≤ i) by omega] using hF

/-- Complete `204`-instruction (`pcAt pcBase 4 → pcAt pcBase 204`) outer+inner `N`-lane
    `rej_sample` site theorem shared by all 10 sites across `B03`–`B07`. -/
theorem step_rej_site_lanes {prog : Program} {target pcBase sqBase sampBase slotsBase : BitVec 64}
    {cfg : RejSiteConfig} {cands : Nat → List Nat} {sampled : Nat → Nat}
    {bufs : Nat → List (BitVec 8)} {hws : Nat → List (BitVec 16)}
    {s0 : State} {Pbuf F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = pcAt pcBase 4) (hrun : s0.status = .Running) (hv : cfg.Valid)
    (hfOuter : FetchesInstrsAt prog pcBase 0 (rejOuterInstrs cfg))
    (hfInner : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs cfg.v))
    (hread : ∀ i, i < cfg.nLanes →
      RejBufReadable (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * i)) (bufs i) cfg.nChunks Pbuf)
    (hbufLen : ∀ i, i < cfg.nLanes → 24 * cfg.nChunks ≤ (bufs i).length)
    (hinv : MultiLaneRawInv cfg.nLanes cands sampled hws)
    (hidx0 : s0.readReg64 cfg.rIdx = 0#64) (hsq0 : s0.readReg64 cfg.rSqPtr = sqBase + 11#64)
    (hsampA : s0.readReg64 cfg.rSampArr = sampBase)
    (hstr : s0.readReg64 cfg.rSlotStride = BitVec.ofNat 64 cfg.slotStride)
    (hslots : s0.readReg64 cfg.rSlotsBase = slotsBase)
    (hcont : ∀ (sF : State) (sampled' : Nat → Nat) (hws' : Nat → List (BitVec 16)),
      SitePreserved cfg s0 sF →
      MultiLaneRawInv cfg.nLanes
        (fun i => cands i ++ parseRej12Candidates ((bufs i).take (24 * cfg.nChunks))) sampled' hws' →
      SepWP prog target (sF.setPC (pcAt pcBase 204))
        (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled' ∗
          (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws' ∗ F))) post oom) :
    SepWP prog target s0
      (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗
        (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws ∗ F))) post oom := by
  have hs0 : s0 = s0.setPC (pcAt pcBase 4) := by cases s0; simp_all [State.setPC]
  rw [hs0]
  exact step_rej_site_lanes_from hv hfOuter hfInner hread hbufLen hsampA hstr hslots
    (cfg.nLanes - 1) 0 cands sampled hws s0 (by have := hv.1; omega) (SitePreserved.refl hrun) hinv
    hidx0 (by simpa [Nat.mul_zero] using hsq0) fun sF sampled' hws' hpF hinvF =>
      hcont sF sampled' hws' hpF fun i hi => by simpa [Nat.zero_le] using hinvF i hi

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep
