/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism

/-!
# Multi-Lane `SampleNTT` Loop and Row Framework (`SampleNttLoop.LoopFramework`)

`SampleNTT` (`sample_from_xof`) XOF invariants, 3-block and 1-block site wrappers, and both
unconditional `SafeSepWP` and conditional total-correctness `SepWP` loop/row combinators for
`B03`–`B07`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Shake128SeedTerminates bytesToPoly16 parseRej12Candidates sampleNttBounded
  shake128BlockAt shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  clampSampled packHalfwordsLE parseRej12Candidates_shake128FirstBlocks_succ
  sampleNttAt sampleNttBounded_eq_some_of_ge256 sampleNttClassical sampler_eq_sampleNttAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism (
  multiLaneMaxExtra multiLane_extra_lt_maxExtra shake128FirstBlocks_take256_toArray_eq_classical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (FetchesInstrsAt pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneClampedInv MultiLaneRawInv MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig SitePreserved rejOuterInstrs step_rej_site_lanes)

/-! ## 1. Pure `SampleNTT` XOF Invariants, Block Transitions, & Exit Slot Bridges -/

@[expose] def MultiLaneRawXofInv (N : Nat) (seeds : Nat → List (BitVec 8)) (extra : Nat)
    (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)) : Prop :=
  MultiLaneRawInv N (fun i => parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))) sampled hws

@[expose] def MultiLaneXofInv (N : Nat) (seeds : Nat → List (BitVec 8)) (extra : Nat)
    (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)) : Prop :=
  MultiLaneClampedInv N (fun i => parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))) sampled hws

theorem MultiLaneXofInv.toRaw {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} (h : MultiLaneXofInv N seeds extra sampled hws) :
    MultiLaneRawXofInv N seeds extra sampled hws := MultiLaneClampedInv.toRaw h

theorem MultiLaneRawXofInv.clamp {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} (h : MultiLaneRawXofInv N seeds extra sampled hws) :
    MultiLaneXofInv N seeds extra (fun i => clampSampled (sampled i)) hws := MultiLaneRawInv.clamp h

@[expose] def allLanesDone (N : Nat) (seeds : Nat → List (BitVec 8)) (extra : Nat) : Bool :=
  (List.range N).all fun i =>
    decide (256 ≤ (parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).length)

theorem allLanesDone_eq_true_iff {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat} :
    allLanesDone N seeds extra = true ↔
      ∀ i, i < N → 256 ≤ (parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).length := by
  simp [allLanesDone]

theorem allLanesDone_eq_false_iff {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat} :
    allLanesDone N seeds extra = false ↔
      ∃ i, i < N ∧ (parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).length < 256 := by
  simp [allLanesDone]

theorem MultiLaneRawXofInv.lt256_iff {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hinv : MultiLaneRawXofInv N seeds extra sampled hws) {i : Nat} (hi : i < N) :
    sampled i < 256 ↔ (parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).length < 256 := by
  have h := hinv i hi; dsimp only at h; rcases h with ⟨_, hcases, _⟩; omega

theorem MultiLaneRawXofInv.ge256_iff {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hinv : MultiLaneRawXofInv N seeds extra sampled hws) {i : Nat} (hi : i < N) :
    256 ≤ sampled i ↔ 256 ≤ (parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).length := by
  have h := hinv i hi; dsimp only at h; rcases h with ⟨_, hcases, _⟩; omega

theorem MultiLaneRawXofInv.allLanesDone_iff_ge256 {N : Nat} {seeds : Nat → List (BitVec 8)}
    {extra : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hinv : MultiLaneRawXofInv N seeds extra sampled hws) :
    allLanesDone N seeds extra = true ↔ ∀ i, i < N → 256 ≤ sampled i := by
  rw [allLanesDone_eq_true_iff]
  exact ⟨fun h i hi => (hinv.ge256_iff hi).mpr (h i hi), fun h i hi => (hinv.ge256_iff hi).mp (h i hi)⟩

theorem MultiLaneXofInv.allLanesDone_iff_sampled {N : Nat} {seeds : Nat → List (BitVec 8)}
    {extra : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hinv : MultiLaneXofInv N seeds extra sampled hws) :
    allLanesDone N seeds extra = true ↔ ∀ i, i < N → sampled i = 256 := by
  rw [allLanesDone_eq_true_iff]
  exact ⟨fun h i hi => (hinv i hi).eq256_iff.mpr (h i hi), fun h i hi => (hinv i hi).eq256_iff.mp (h i hi)⟩

theorem MultiLaneRawXofInv.of_init3 {N : Nat} {seeds bufs : Nat → List (BitVec 8)}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawInv N (fun i => [] ++ parseRej12Candidates ((bufs i).take (24 * 21))) sampled hws)
    (hbufs : ∀ i, i < N → (bufs i).take 504 = shake128FirstBlocks (seeds i) 3) :
    MultiLaneRawXofInv N seeds 0 sampled hws := by
  intro i hi; have hb : (bufs i).take (24 * 21) = shake128FirstBlocks (seeds i) (0 + 3) := hbufs i hi
  simpa [hb] using hraw i hi

theorem MultiLaneXofInv.of_init3 {N : Nat} {seeds bufs : Nat → List (BitVec 8)}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawInv N (fun i => [] ++ parseRej12Candidates ((bufs i).take (24 * 21))) sampled hws)
    (hbufs : ∀ i, i < N → (bufs i).take 504 = shake128FirstBlocks (seeds i) 3) :
    MultiLaneXofInv N seeds 0 (fun i => clampSampled (sampled i)) hws :=
  (MultiLaneRawXofInv.of_init3 hraw hbufs).clamp

theorem MultiLaneRawXofInv.step_extra_block {N : Nat} {seeds bufs : Nat → List (BitVec 8)}
    {extra : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawInv N (fun i =>
        parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3)) ++
          parseRej12Candidates ((bufs i).take (24 * 7))) sampled hws)
    (hbufs : ∀ i, i < N → (bufs i).take 168 = shake128BlockAt (seeds i) (extra + 3)) :
    MultiLaneRawXofInv N seeds (extra + 1) sampled hws := by
  intro i hi
  have hb : (bufs i).take (24 * 7) = shake128BlockAt (seeds i) (extra + 3) := hbufs i hi
  have hsucc : (extra + 1) + 3 = (extra + 3) + 1 := by omega
  dsimp only; rw [hsucc, parseRej12Candidates_shake128FirstBlocks_succ, ← hb]
  exact hraw i hi

theorem MultiLaneXofInv.step_extra_block {N : Nat} {seeds bufs : Nat → List (BitVec 8)}
    {extra : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawInv N (fun i =>
        parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3)) ++
          parseRej12Candidates ((bufs i).take (24 * 7))) sampled hws)
    (hbufs : ∀ i, i < N → (bufs i).take 168 = shake128BlockAt (seeds i) (extra + 3)) :
    MultiLaneXofInv N seeds (extra + 1) (fun i => clampSampled (sampled i)) hws :=
  (MultiLaneRawXofInv.step_extra_block hraw hbufs).clamp

theorem MultiLaneXofInv.exit_poly {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hinv : MultiLaneXofInv N seeds extra sampled hws)
    (hd : allLanesDone N seeds extra = true) {i : Nat} (hi : i < N) :
    sampled i = 256 ∧
    bytesToPoly16 ((packHalfwordsLE (hws i)).take 512) =
      ((parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).take 256).toArray.map (BitVec.ofNat 16) ∧
    bytesToPoly16 ((packHalfwordsLE (hws i)).take 512) =
      (sampleNttClassical (seeds i)).map (BitVec.ofNat 16) := by
  have hge := allLanesDone_eq_true_iff.mp hd i hi
  have hs : sampled i = 256 := (hinv i hi).eq256_iff.mpr hge
  have hp1 := (hinv i hi).bytesToPoly16_take512 hs
  exact ⟨hs, hp1, by rw [hp1, shake128FirstBlocks_take256_toArray_eq_classical hge]⟩

theorem MultiLaneRawXofInv.exit_poly {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hinv : MultiLaneRawXofInv N seeds extra sampled hws)
    (hd : allLanesDone N seeds extra = true) {i : Nat} (hi : i < N) :
    256 ≤ sampled i ∧
    bytesToPoly16 ((packHalfwordsLE (hws i)).take 512) =
      ((parseRej12Candidates (shake128FirstBlocks (seeds i) (extra + 3))).take 256).toArray.map (BitVec.ofNat 16) ∧
    bytesToPoly16 ((packHalfwordsLE (hws i)).take 512) =
      (sampleNttClassical (seeds i)).map (BitVec.ofNat 16) :=
  let ⟨_, hp1, hp2⟩ := hinv.clamp.exit_poly hd hi
  ⟨(hinv.ge256_iff hi).mpr (allLanesDone_eq_true_iff.mp hd i hi), hp1, hp2⟩

theorem MultiLaneXofInv.exit_poly_sampler {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} {sampler : List (BitVec 8) → Poly}
    (hsampler : ∀ s (h : Shake128SeedTerminates s), sampler s = sampleNttAt s (Classical.choose h))
    (hinv : MultiLaneXofInv N seeds extra sampled hws) (hd : allLanesDone N seeds extra = true)
    {i : Nat} (hi : i < N) :
    bytesToPoly16 ((packHalfwordsLE (hws i)).take 512) = (sampler (seeds i)).map (BitVec.ofNat 16) := by
  rw [(hinv.exit_poly hd hi).2.1, sampler_eq_sampleNttAt hsampler (allLanesDone_eq_true_iff.mp hd i hi)]; rfl

theorem MultiLaneRawXofInv.exit_sampleNttBounded {N : Nat} {seeds : Nat → List (BitVec 8)}
    {extra fuel : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (_hinv : MultiLaneRawXofInv N seeds extra sampled hws) (hd : allLanesDone N seeds extra = true)
    (hle : extra ≤ fuel) {i : Nat} (hi : i < N) :
    sampleNttBounded fuel (seeds i) = some (sampleNttClassical (seeds i)) := by
  have hge := allLanesDone_eq_true_iff.mp hd i hi
  rw [sampleNttBounded_eq_some_of_ge256 hle hge, ← shake128FirstBlocks_take256_toArray_eq_classical hge]; rfl

/-! ## 2. Site-Level `3`-Block (`nChunks = 21`) & `1`-Block (`nChunks = 7`) `rej_sample` Steps -/

theorem step_rej_site_init3 {prog : Program} {target pcBase sqBase sampBase slotsBase : BitVec 64}
    {cfg : RejSiteConfig} {seeds bufs : Nat → List (BitVec 8)} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    {s0 : State} {Pbuf F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = pcAt pcBase 4) (hrun : s0.status = .Running) (hv : cfg.Valid) (hnChunks : cfg.nChunks = 21)
    (hfOuter : FetchesInstrsAt prog pcBase 0 (rejOuterInstrs cfg)) (hfInner : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs cfg.v))
    (hread : ∀ i, i < cfg.nLanes → RejBufReadable (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * i)) (bufs i) cfg.nChunks Pbuf)
    (hbufLen : ∀ i, i < cfg.nLanes → 24 * cfg.nChunks ≤ (bufs i).length)
    (hbufs : ∀ i, i < cfg.nLanes → (bufs i).take 504 = shake128FirstBlocks (seeds i) 3)
    (hinv0 : MultiLaneRawInv cfg.nLanes (fun _ => []) sampled hws)
    (hidx0 : s0.readReg64 cfg.rIdx = 0#64) (hsq0 : s0.readReg64 cfg.rSqPtr = sqBase + 11#64)
    (hsampA : s0.readReg64 cfg.rSampArr = sampBase) (hstr : s0.readReg64 cfg.rSlotStride = BitVec.ofNat 64 cfg.slotStride)
    (hslots : s0.readReg64 cfg.rSlotsBase = slotsBase)
    (hcont : ∀ sF sampled' hws', SitePreserved cfg s0 sF → MultiLaneRawXofInv cfg.nLanes seeds 0 sampled' hws' →
      SepWP prog target (sF.setPC (pcAt pcBase 204))
        (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled' ∗ (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws' ∗ F))) post oom) :
    SepWP prog target s0 (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗ (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws ∗ F))) post oom :=
  step_rej_site_lanes hpc hrun hv hfOuter hfInner hread hbufLen hinv0 hidx0 hsq0 hsampA hstr hslots
    fun sF sampled' hws' hp hraw => by rw [hnChunks] at hraw; exact hcont sF sampled' hws' hp (.of_init3 hraw hbufs)

theorem step_rej_site_extra1 {prog : Program} {target pcBase sqBase sampBase slotsBase : BitVec 64}
    {cfg : RejSiteConfig} {seeds bufs : Nat → List (BitVec 8)} {extra : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    {s0 : State} {Pbuf F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = pcAt pcBase 4) (hrun : s0.status = .Running) (hv : cfg.Valid) (hnChunks : cfg.nChunks = 7)
    (hfOuter : FetchesInstrsAt prog pcBase 0 (rejOuterInstrs cfg)) (hfInner : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs cfg.v))
    (hread : ∀ i, i < cfg.nLanes → RejBufReadable (sqBase + BitVec.ofNat 64 (24 * cfg.nChunks * i)) (bufs i) cfg.nChunks Pbuf)
    (hbufLen : ∀ i, i < cfg.nLanes → 24 * cfg.nChunks ≤ (bufs i).length)
    (hbufs : ∀ i, i < cfg.nLanes → (bufs i).take 168 = shake128BlockAt (seeds i) (extra + 3))
    (hinv : MultiLaneRawXofInv cfg.nLanes seeds extra sampled hws)
    (hidx0 : s0.readReg64 cfg.rIdx = 0#64) (hsq0 : s0.readReg64 cfg.rSqPtr = sqBase + 11#64)
    (hsampA : s0.readReg64 cfg.rSampArr = sampBase) (hstr : s0.readReg64 cfg.rSlotStride = BitVec.ofNat 64 cfg.slotStride)
    (hslots : s0.readReg64 cfg.rSlotsBase = slotsBase)
    (hcont : ∀ sF sampled' hws', SitePreserved cfg s0 sF → MultiLaneRawXofInv cfg.nLanes seeds (extra + 1) sampled' hws' →
      SepWP prog target (sF.setPC (pcAt pcBase 204))
        (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled' ∗ (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws' ∗ F))) post oom) :
    SepWP prog target s0 (Pbuf ∗ (MultiLaneSampled sampBase cfg.nLanes sampled ∗ (MultiLaneSlots slotsBase cfg.slotStride cfg.nLanes hws ∗ F))) post oom :=
  step_rej_site_lanes hpc hrun hv hfOuter hfInner hread hbufLen hinv hidx0 hsq0 hsampA hstr hslots
    fun sF sampled' hws' hp hraw => by rw [hnChunks] at hraw; exact hcont sF sampled' hws' hp (.step_extra_block hraw hbufs)

/-! ## 3. Unconditional `SafeSepWP` Loop and Row Combinators (no termination hypothesis) -/

theorem sampleNttWhile_safeSepWP1 {prog : Program}
    {Inv : Nat → State → SepProp → Prop} {Q : State → SepProp → Prop}
    (hStep : ∀ extra st P, Inv extra st P →
      SafeSepWP1 prog st P (fun sf Pf => Inv (extra + 1) sf Pf ∨ Q sf Pf))
    {extra0 : Nat} {s0 : State} {P0 : SepProp} (h0 : Inv extra0 s0 P0) :
    SafeSepWP prog s0 P0 Q := by
  refine SafeSepWP.loop (fun st P => ∃ extra, Inv extra st P) ?_ ⟨extra0, h0⟩
  rintro st Pst ⟨extra, hInv⟩
  exact (hStep extra st Pst hInv).mono fun _ _ h =>
    match h with | .inl hN => .inl ⟨extra + 1, hN⟩ | .inr hE => .inr hE

theorem sampleNttWhile_safeSepWP {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop} {Q : State → SepProp → Prop}
    (hne : loopHead ≠ midPC) (hInvPC : ∀ extra st P, Inv extra st P → st.pc = loopHead)
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra))
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf => if allLanesDone N seeds (extra + 1) then Q sf Pf else Inv (extra + 1) sf Pf))
    {extra0 : Nat} {s0 : State} {P0 : SepProp} (h0 : Inv extra0 s0 P0) :
    SafeSepWP prog s0 P0 Q := by
  refine sampleNttWhile_safeSepWP1 (fun extra st P hInv => ?_) h0
  refine SafeSepWP1.of_sepWP (by rw [hInvPC extra st P hInv]; exact hne) ?_
  refine (hBodyA extra st P hInv).mono fun sm Pm hmpc hmrun hMid => ?_
  refine SafeSepWP.of_total ((hBodyB extra sm Pm hmpc hmrun hMid).mono fun _ _ _ _ hPost => ?_)
  by_cases hd : allLanesDone N seeds (extra + 1) = true
  · simp only [hd, ↓reduceIte] at hPost; exact Or.inr hPost
  · simp only [hd] at hPost; exact Or.inl hPost

theorem sampleNttRow_safeSepWP {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop} {Q : State → SepProp → Prop}
    {sEntry : State} {PEntry : SepProp}
    (hne : loopHead ≠ midPC) (hInvPC : ∀ extra st P, Inv extra st P → st.pc = loopHead)
    (hInit : SepWP prog (if allLanesDone N seeds 0 then exitPC else loopHead) sEntry PEntry
      (fun sf Pf => if allLanesDone N seeds 0 then Q sf Pf else Inv 0 sf Pf))
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra))
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf => if allLanesDone N seeds (extra + 1) then Q sf Pf else Inv (extra + 1) sf Pf)) :
    SafeSepWP prog sEntry PEntry Q := by
  refine SafeSepWP.of_sepWP (hInit.mono fun _ _ _ _ hPost => ?_)
  by_cases hd : allLanesDone N seeds 0 = true
  · simp only [hd, ↓reduceIte] at hPost; exact SafeSepWP.done hPost
  · simp only [hd] at hPost
    exact sampleNttWhile_safeSepWP hne hInvPC hBodyA hBodyB hPost

/-! ## 4. Conditional Total-Correctness `SepWP` Loop and Row Combinators -/

private theorem sampleNttWhile_sepWP_fuel {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hTerm : ∀ i, i < N → Shake128SeedTerminates (seeds i))
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra) oom)
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf =>
          if allLanesDone N seeds (extra + 1) then Q sf Pf else Inv (extra + 1) sf Pf) oom) :
    ∀ (fuel extra : Nat) (st : State) (P : SepProp),
      multiLaneMaxExtra N seeds hTerm - extra ≤ fuel →
      Inv extra st P → SepWP prog exitPC st P Q oom := by
  intro fuel
  induction fuel with
  | zero =>
    intro extra st P hfuel hInv
    have hIter := SepWP.seq (hBodyA extra st P hInv) (hBodyB extra)
    by_cases hd : allLanesDone N seeds (extra + 1) = true
    · simp only [hd, ↓reduceIte] at hIter; exact hIter
    · rcases allLanesDone_eq_false_iff.mp (Bool.eq_false_iff.mpr hd) with ⟨lane, hlt, hcands⟩
      have hltMax := multiLane_extra_lt_maxExtra hTerm hlt hcands
      omega
  | succ fuel' ih =>
    intro extra st P hfuel hInv
    have hIter := SepWP.seq (hBodyA extra st P hInv) (hBodyB extra)
    by_cases hd : allLanesDone N seeds (extra + 1) = true
    · simp only [hd, ↓reduceIte] at hIter; exact hIter
    · simp only [hd] at hIter
      exact SepWP.seq hIter fun sf Pf _ _ hNext => ih (extra + 1) sf Pf (by omega) hNext

theorem sampleNttWhile_sepWP {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hTerm : ∀ i, i < N → Shake128SeedTerminates (seeds i))
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra) oom)
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf =>
          if allLanesDone N seeds (extra + 1) then Q sf Pf else Inv (extra + 1) sf Pf) oom)
    {extra0 : Nat} {s0 : State} {P0 : SepProp} (h0 : Inv extra0 s0 P0) :
    SepWP prog exitPC s0 P0 Q oom :=
  sampleNttWhile_sepWP_fuel hTerm hBodyA hBodyB
    (multiLaneMaxExtra N seeds hTerm - extra0) extra0 s0 P0 (Nat.le_refl _) h0

theorem sampleNttRow_sepWP {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop} {Q : State → SepProp → Prop}
    {oom : State → SepProp} {sEntry : State} {PEntry : SepProp}
    (hTerm : ∀ i, i < N → Shake128SeedTerminates (seeds i))
    (hInit : SepWP prog (if allLanesDone N seeds 0 then exitPC else loopHead) sEntry PEntry
      (fun sf Pf => if allLanesDone N seeds 0 then Q sf Pf else Inv 0 sf Pf) oom)
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra) oom)
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf =>
          if allLanesDone N seeds (extra + 1) then Q sf Pf else Inv (extra + 1) sf Pf) oom) :
    SepWP prog exitPC sEntry PEntry Q oom := by
  by_cases hd : allLanesDone N seeds 0 = true
  · simp only [hd, ↓reduceIte] at hInit; exact hInit
  · simp only [hd] at hInit
    exact SepWP.seq hInit fun _ _ _ _ hInv0 => sampleNttWhile_sepWP hTerm hBodyA hBodyB hInv0

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
