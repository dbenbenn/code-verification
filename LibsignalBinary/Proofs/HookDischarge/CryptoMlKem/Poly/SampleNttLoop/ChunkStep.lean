/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriple0
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples14
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57

/-!
# 24-byte chunk and inner `nChunks` loop composition

Composes `ChunkTriple0`, `ChunkTriples14`, `ChunkTriples57`, and `rejHeadLatchInstrs` across all
3 variants (`varA`, `varB`, `varC`) into `step_rej_chunk24_active`, `step_rej_chunk24`,
`step_rej_chunks_inv`, and `step_cmp64_csel_clamp` (`B03`–`B07`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkStep

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (parseRej12Candidates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  RejSlotClampedInv RejSlotRawInv clampSampled packHalfwordsLE parseRej12Chunk24
  parseRej12Chunk24_length_le_16 parseRej12Triple_length_le_2 rejChunkStepPure
  rejWriteCandidates rejWriteCandidates_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (
  RejBufReadable condHolds_cmp64_1_eq condHolds_cmp64_256_cs csel_clampSampled_eq
  rejChunksFromPure rejChunksFromPure_zero_eq_fold rejWriteCandidates_append subs64_one_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt RejTripleState ScratchPreserved brDisp parseRej12TripleAt pcAt pcAt_brDisp
  pcAt_succ rBuf rCnt rRem rSampled rSlotBase readReg64_writeReg64_ne_of rejClobberedRegs
  rejHeadLatchInstrs rejOutPre24Instrs rejOutPre57Instrs rejScratchRegs rejSpine14Instrs
  rejSpine56Instrs rejStore14Instrs rejStore56Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (
  RejVariant rejInnerInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords.FetchesInstrsAt (slice)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriple0 (
  step_rej_triple0_AB step_rej_triple0_C)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples14 (step_rej_triple_1_4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57 (
  step_rej_triple7 step_rej_triple_5_6)

/-! ## 1. Prefix Candidate Accumulator Across Triples `0..7` -/

@[expose] def parseRej12Prefix (bs : List (BitVec 8)) : Nat → List Nat
  | 0 => [] | t + 1 => parseRej12Prefix bs t ++ parseRej12TripleAt bs t

theorem parseRej12Prefix_length_le (bs : List (BitVec 8)) :
    ∀ t : Nat, (parseRej12Prefix bs t).length ≤ 2 * t
  | 0 => by simp [parseRej12Prefix]
  | t + 1 => by
    simp only [parseRej12Prefix, List.length_append, parseRej12TripleAt]
    have ih := parseRej12Prefix_length_le bs t
    have htr := parseRej12Triple_length_le_2 (bs.getD (3 * t) 0#8) (bs.getD (3 * t + 1) 0#8) (bs.getD (3 * t + 2) 0#8)
    omega

theorem parseRej12Prefix_one (bs : List (BitVec 8)) :
    parseRej12Prefix bs 1 = parseRej12TripleAt bs 0 := by simp [parseRej12Prefix]

theorem parseRej12Prefix_eight (bs : List (BitVec 8)) :
    parseRej12Prefix bs 8 = parseRej12Chunk24 bs := by
  simp [parseRej12Prefix, parseRej12Chunk24, parseRej12TripleAt, List.append_assoc]

private theorem prefix_step_acc (hws : List (BitVec 16)) (chunk : List (BitVec 8))
    (sampled t cnt cnt' : Nat) (hws_t hws' : List (BitVec 16))
    (hc : cnt = (parseRej12Prefix chunk t).length)
    (hh : hws_t = rejWriteCandidates hws sampled (parseRej12Prefix chunk t))
    (hc' : cnt' = cnt + (parseRej12TripleAt chunk t).length)
    (hh' : hws' = rejWriteCandidates hws_t (sampled + cnt) (parseRej12TripleAt chunk t)) :
    cnt' = (parseRej12Prefix chunk (t + 1)).length ∧
    hws' = rejWriteCandidates hws sampled (parseRej12Prefix chunk (t + 1)) := by
  subst hc hh hc'; subst hh'; exact ⟨(List.length_append ..).symm, (rejWriteCandidates_append ..).symm⟩

/-! ## 2. Active 24-Byte Chunk Trellis Composition (`[17..203] → 11`) -/

private def RejPrefixCont (prog : Program) (target pcBase : BitVec 64) (isVarA : Bool) (s0 : State)
    (slotBase : BitVec 64) (sampled : Nat) (hws : List (BitVec 16)) (chunk : List (BitVec 8))
    (Pbuf F : SepProp) (post : State → SepProp → Prop) (oom : State → SepProp) (idx t : Nat) : Prop :=
  ∀ s cnt hws_t, RejTripleState isVarA s0 slotBase sampled cnt s →
    cnt = (parseRej12Prefix chunk t).length →
    hws_t = rejWriteCandidates hws sampled (parseRej12Prefix chunk t) →
    SepWP prog target (s.setPC (pcAt pcBase idx)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws_t) ∗ F)) post oom

private theorem lift_triple_5_6 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {spShift t nChunks chunkIdx sampled : Nat} {s0 : State}
    {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (ht5 : 5 ≤ t) (ht6 : t ≤ 6)
    (hfSp : FetchesInstrsAt prog pcBase (39 - spShift + 10 * (t - 1)) (rejSpine56Instrs isVarA spShift t))
    (hfOut : FetchesInstrsAt prog pcBase (105 + 14 * (t - 1)) (rejOutPre57Instrs isVarA spShift t))
    (hfSt : FetchesInstrsAt prog pcBase (167 + 14 * (t - 5)) (rejStore56Instrs isVarA spShift t))
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256)
    (hNextSp : RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (39 - spShift + 10 * t) (t + 1))
    (hNextOut : RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (105 + 14 * t) (t + 1)) :
    RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (39 - spShift + 10 * (t - 1)) t ∧
    RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (105 + 14 * (t - 1)) t := by
  let chunk := (buf.drop (24 * chunkIdx)).take 24
  have hpair := fun (cnt : Nat) (hws_t : List (BitVec 16))
      (hc : cnt = (parseRej12Prefix chunk t).length) (hh : hws_t = rejWriteCandidates hws sampled (parseRej12Prefix chunk t)) =>
    step_rej_triple_5_6 ht5 ht6 hfSp hfOut hfSt hbuf0 hread hchunk
      (by rw [hh, rejWriteCandidates_length, hlen]) hs (hc ▸ parseRej12Prefix_length_le chunk t)
      (fun s' cnt' hws' hst' hc' hh' => let ⟨h1, h2⟩ := prefix_step_acc hws chunk sampled t cnt cnt' hws_t hws' hc hh hc' hh'; hNextSp s' cnt' hws' hst' h1 h2)
      (fun s' cnt' hws' hst' hc' hh' => let ⟨h1, h2⟩ := prefix_step_acc hws chunk sampled t cnt cnt' hws_t hws' hc hh hc' hh'; hNextOut s' cnt' hws' hst' h1 h2)
  exact ⟨fun s cnt hws_t hst hc hh => (hpair cnt hws_t hc hh).1 s hst, fun s cnt hws_t hst hc hh => (hpair cnt hws_t hc hh).2 s hst⟩

private theorem lift_triple_2_4 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {spShift t nChunks chunkIdx sampled : Nat} {s0 : State}
    {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (ht2 : 2 ≤ t) (ht4 : t ≤ 4)
    (hfSp : FetchesInstrsAt prog pcBase (39 - spShift + 10 * (t - 1)) (rejSpine14Instrs isVarA spShift t))
    (hfOut : FetchesInstrsAt prog pcBase (105 + 14 * (t - 1)) (rejOutPre24Instrs isVarA spShift t))
    (hfSt : FetchesInstrsAt prog pcBase (110 + 14 * (t - 1)) (rejStore14Instrs isVarA spShift t))
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256)
    (hNextSp : RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (39 - spShift + 10 * t) (t + 1))
    (hNextOut : RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (105 + 14 * t) (t + 1)) :
    RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (39 - spShift + 10 * (t - 1)) t ∧
    RejPrefixCont prog target pcBase isVarA s0 slotBase sampled hws ((buf.drop (24 * chunkIdx)).take 24) Pbuf F post oom (105 + 14 * (t - 1)) t := by
  let chunk := (buf.drop (24 * chunkIdx)).take 24
  have hpair := fun (cnt : Nat) (hws_t : List (BitVec 16))
      (hc : cnt = (parseRej12Prefix chunk t).length) (hh : hws_t = rejWriteCandidates hws sampled (parseRej12Prefix chunk t)) =>
    step_rej_triple_1_4 (by omega) ht4 hfSp hfSt hbuf0 hread hchunk
      (by rw [hh, rejWriteCandidates_length, hlen]) hs (hc ▸ parseRej12Prefix_length_le chunk t)
      (fun s' cnt' hws' hst' hc' hh' => let ⟨h1, h2⟩ := prefix_step_acc hws chunk sampled t cnt cnt' hws_t hws' hc hh hc' hh'; hNextSp s' cnt' hws' hst' h1 h2)
      (fun s' cnt' hws' hst' hc' hh' => let ⟨h1, h2⟩ := prefix_step_acc hws chunk sampled t cnt cnt' hws_t hws' hc hh hc' hh'; hNextOut s' cnt' hws' hst' h1 h2)
  exact ⟨fun s cnt hws_t hst hc hh => (hpair cnt hws_t hc hh).1 s hst, fun s cnt hws_t hst hc hh => (hpair cnt hws_t hc hh).2 hfOut ht2 s hst⟩

/-- Complete 24-byte active chunk body (`[17..203] → 11`) across all 3 variants (`varA/B/C`). -/
theorem step_rej_chunk24_active {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {v : RejVariant} {nChunks chunkIdx sampled : Nat} {s0 : State}
    {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s0.status = .Running) (hf : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs v))
    (hslot0 : s0.readReg64 (rSlotBase v.isVarA) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 sampled)
    (hbuf0 : s0.readReg64 (rBuf v.isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256)
    (hcont : ∀ s' cnt' hws', RejTripleState v.isVarA s0 slotBase sampled cnt' s' →
      cnt' = (parseRej12Chunk24 ((buf.drop (24 * chunkIdx)).take 24)).length →
      hws' = rejWriteCandidates hws sampled (parseRej12Chunk24 ((buf.drop (24 * chunkIdx)).take 24)) →
      SepWP prog target (s'.setPC (pcAt pcBase 11)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom) :
    SepWP prog target (s0.setPC (pcAt pcBase 17)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  let chunk := (buf.drop (24 * chunkIdx)).take 24
  have hsh : v.spShift ≤ 7 := by cases v <;> decide
  have hCont8 : RejPrefixCont prog target pcBase v.isVarA s0 slotBase sampled hws chunk Pbuf F post oom 11 8 :=
    fun s' cnt' hws' hst hc hh => by rw [parseRej12Prefix_eight] at hc hh; exact hcont s' cnt' hws' hst hc hh
  have h7 : RejPrefixCont prog target pcBase v.isVarA s0 slotBase sampled hws chunk Pbuf F post oom (39 - v.spShift + 10 * 6) 7 ∧
      RejPrefixCont prog target pcBase v.isVarA s0 slotBase sampled hws chunk Pbuf F post oom (105 + 14 * 6) 7 := by
    rw [show 39 - v.spShift + 10 * 6 = 99 - v.spShift by omega, show 105 + 14 * 6 = 189 from rfl]
    have hpair := fun (cnt : Nat) (hws_7 : List (BitVec 16))
        (hc : cnt = (parseRej12Prefix chunk 7).length) (hh : hws_7 = rejWriteCandidates hws sampled (parseRej12Prefix chunk 7)) =>
      step_rej_triple7 hsh (by cases v <;> exact slice hf (by omega) rfl)
        (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl)
        hbuf0 hread hchunk (by rw [hh, rejWriteCandidates_length, hlen]) hs (hc ▸ parseRej12Prefix_length_le chunk 7)
        (fun s' cnt' hws' hst' hc' hh' => let ⟨h1, h2⟩ := prefix_step_acc hws chunk sampled 7 cnt cnt' hws_7 hws' hc hh hc' hh'; hCont8 s' cnt' hws' hst' h1 h2)
    exact ⟨fun s cnt hws_7 hst hc hh => (hpair cnt hws_7 hc hh).1 s hst, fun s cnt hws_7 hst hc hh => (hpair cnt hws_7 hc hh).2 s hst⟩
  have h6 := lift_triple_5_6 (t := 6) (by omega) (by omega) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) hbuf0 hread hchunk hlen hs h7.1 h7.2
  have h5 := lift_triple_5_6 (t := 5) (by omega) (by omega) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) hbuf0 hread hchunk hlen hs h6.1 h6.2
  have h4 := lift_triple_2_4 (t := 4) (by omega) (by omega) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) hbuf0 hread hchunk hlen hs h5.1 h5.2
  have h3 := lift_triple_2_4 (t := 3) (by omega) (by omega) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) hbuf0 hread hchunk hlen hs h4.1 h4.2
  have h2 := lift_triple_2_4 (t := 2) (by omega) (by omega) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl) hbuf0 hread hchunk hlen hs h3.1 h3.2
  have hSp1 : RejPrefixCont prog target pcBase v.isVarA s0 slotBase sampled hws chunk Pbuf F post oom (39 - v.spShift) 1 :=
    fun s cnt hws_1 hst hc hh =>
      (step_rej_triple_1_4 (t := 1) (spShift := v.spShift) (by omega) (by omega)
        (by cases v <;> exact slice hf (by omega) rfl) (by cases v <;> exact slice hf (by omega) rfl)
        hbuf0 hread hchunk (by rw [hh, rejWriteCandidates_length, hlen]) hs (hc ▸ parseRej12Prefix_length_le chunk 1)
        (fun s' cnt' hws' hst' hc' hh' => let ⟨ha, hb⟩ := prefix_step_acc hws chunk sampled 1 cnt cnt' hws_1 hws' hc hh hc' hh'; h2.1 s' cnt' hws' hst' ha hb)
        (fun s' cnt' hws' hst' hc' hh' => let ⟨ha, hb⟩ := prefix_step_acc hws chunk sampled 1 cnt cnt' hws_1 hws' hc hh hc' hh'; h2.2 s' cnt' hws' hst' ha hb)).1 s hst
  cases v with
  | varA =>
    refine step_rej_triple0_AB (isVarA := true) hrun (slice hf (by omega) rfl)
      hslot0 hsamp0 hbuf0 hread hchunk hlen hs fun s' cnt' hws' hst' hc' hh' => ?_
    rw [← parseRej12Prefix_one] at hc' hh'; exact hSp1 s' cnt' hws' hst' hc' hh'
  | varB =>
    refine step_rej_triple0_AB (isVarA := false) hrun (slice hf (by omega) rfl)
      hslot0 hsamp0 hbuf0 hread hchunk hlen hs fun s' cnt' hws' hst' hc' hh' => ?_
    rw [← parseRej12Prefix_one] at hc' hh'; exact hSp1 s' cnt' hws' hst' hc' hh'
  | varC =>
    refine step_rej_triple0_C hrun (slice hf (by omega) rfl) (slice hf (by omega) rfl)
      hslot0 hsamp0 hbuf0 hread hchunk hlen hs fun s' cnt' hws' hst' hc' hh' => ?_
    rw [← parseRej12Prefix_one] at hc' hh'; exact hSp1 s' cnt' hws' hst' hc' hh'

/-! ## 3. Full Single-Chunk Step (`[15 → 12]`), `nChunks` Loop (`[15 → 0]`), & Clamp -/

@[expose] def ClobberedPreserved (isVarA : Bool) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp ∧ s.vregs = s0.vregs ∧
  ∀ r : Reg, r ∉ rejClobberedRegs isVarA → s.readReg64 r = s0.readReg64 r

theorem ClobberedPreserved.refl {isVarA : Bool} {s0 : State} (hrun : s0.status = .Running) :
    ClobberedPreserved isVarA s0 s0 := ⟨hrun, rfl, rfl, fun _ _ => rfl⟩

theorem ClobberedPreserved.trans {isVarA : Bool} {s0 s1 s2 : State}
    (h1 : ClobberedPreserved isVarA s0 s1) (h2 : ClobberedPreserved isVarA s1 s2) :
    ClobberedPreserved isVarA s0 s2 :=
  ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun r hr => (h2.2.2.2 r hr).trans (h1.2.2.2 r hr)⟩

theorem ClobberedPreserved.of_scratch {isVarA : Bool} {s0 s : State}
    (h : ScratchPreserved isVarA s0 s) : ClobberedPreserved isVarA s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r fun hs =>
    hr (by cases isVarA <;> simp [rejScratchRegs, rejClobberedRegs] at hs ⊢ <;> tauto)⟩

theorem ClobberedPreserved.setPState {isVarA : Bool} {s0 s : State}
    (h : ClobberedPreserved isVarA s0 s) (ps : PState) :
    ClobberedPreserved isVarA s0 (s.setPState ps) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem ClobberedPreserved.writeClobbered {isVarA : Bool} {s0 s : State}
    (h : ClobberedPreserved isVarA s0 s) (rt : Reg) (val : BitVec 64)
    (hrt : rt ∈ rejClobberedRegs isVarA) : ClobberedPreserved isVarA s0 (s.writeReg64 rt val) := by
  rcases h with ⟨hrun, hsp, hv, hregs⟩
  refine ⟨by simp [State.writeReg64, hrun],
    by cases isVarA <;> simp [rejClobberedRegs, rSampled, rBuf, rRem,
         ChunkInstrs.rOut, rCnt, ChunkInstrs.rB1, ChunkInstrs.rS0, ChunkInstrs.rS1] at hrt <;>
       rcases hrt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using hsp,
    by simp [State.writeReg64, hv],
    fun r hr => (readReg64_writeReg64_ne_of s (fun (heq : r = rt) => hr (heq ▸ hrt))).trans (hregs r hr)⟩

theorem ClobberedPreserved.readSlotBase {isVarA : Bool} {s0 s : State}
    (h : ClobberedPreserved isVarA s0 s) : s.readReg64 (rSlotBase isVarA) = s0.readReg64 (rSlotBase isVarA) :=
  h.2.2.2 (rSlotBase isVarA) (by cases isVarA <;> simp [rejClobberedRegs, rSlotBase, rSampled,
    rBuf, rRem, ChunkInstrs.rOut, rCnt, ChunkInstrs.rB1, ChunkInstrs.rS0, ChunkInstrs.rS1])

private theorem setPC_setPC (s : State) (a b : BitVec 64) : (s.setPC a).setPC b = s.setPC b := by cases s; rfl
private theorem setPC_writeReg64_setPC (s : State) (a b : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).setPC b = (s.writeReg64 r v).setPC b := by cases s; cases r <;> rfl
private theorem advancePC_writeReg64_setPC (s : State) (a : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).advancePC = (s.writeReg64 r v).setPC (a + 4#64) := by cases s; cases r <;> rfl
private theorem advancePC_setPState_setPC (s : State) (a : BitVec 64) (ps : PState) :
    ((s.setPC a).setPState ps).advancePC = (s.setPState ps).setPC (a + 4#64) := by cases s; rfl
private theorem advancePC_writeReg64_setPState_setPC (s : State) (a : BitVec 64) (r : Reg) (v : BitVec 64) (ps : PState) :
    (((s.setPC a).writeReg64 r v).setPState ps).advancePC = ((s.writeReg64 r v).setPState ps).setPC (a + 4#64) := by
  cases s; cases r <;> rfl

theorem rejChunkStepPure_bounds {sampled : Nat} {hws : List (BitVec 16)} {c : List (BitVec 8)}
    (hs : sampled ≤ 271) (hlen : hws.length = 272) :
    (rejChunkStepPure sampled hws c).1 ≤ 271 ∧ (rejChunkStepPure sampled hws c).2.length = 272 := by
  have h16 := parseRej12Chunk24_length_le_16 c; unfold rejChunkStepPure
  by_cases hlt : sampled < 256 <;> simp [hlt, rejWriteCandidates_length, hlen] <;> omega

/-- Full single-chunk step `[15 → 12]` matching `rejChunkStepPure`. -/
theorem step_rej_chunk24 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {v : RejVariant} {nChunks chunkIdx sampled : Nat} {s0 : State}
    {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s0.status = .Running) (hf : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs v))
    (hslot0 : s0.readReg64 (rSlotBase v.isVarA) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 sampled)
    (hbuf0 : s0.readReg64 (rBuf v.isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hsb : sampled ≤ 271)
    (hcont : ∀ s1 : State, let res := rejChunkStepPure sampled hws ((buf.drop (24 * chunkIdx)).take 24)
      ClobberedPreserved v.isVarA s0 s1 → s1.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 res.1 →
      s1.readReg64 (rBuf v.isVarA) = s0.readReg64 (rBuf v.isVarA) →
      s1.readReg64 (rRem v.isVarA) = s0.readReg64 (rRem v.isVarA) →
      SepWP prog target (s1.setPC (pcAt pcBase 12)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE res.2) ∗ F)) post oom) :
    SepWP prog target (s0.setPC (pcAt pcBase 15)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  have hfHL : FetchesInstrsAt prog pcBase 11 (rejHeadLatchInstrs v.isVarA) := by cases v <;> exact slice hf (by omega) rfl
  let ps := subsPState64 (BitVec.ofNat 64 sampled) 256#64; let sA := s0.setPState ps
  refine SepWP.step_pure_setPC (s' := sA.setPC (pcAt pcBase 16)) hrun (hfHL.get 4) ?_ rfl ?_
  · simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hsamp0, ps, sA, State.writeReg, advancePC_setPState_setPC, pcAt_succ]
  · refine SepWP.step_pure_setPC (s' := sA.setPC (if ConditionHolds .CS ps then pcAt pcBase 12 else pcAt pcBase 17)) hrun (hfHL.get 5) ?_ rfl ?_
    · by_cases hc : ConditionHolds .CS ps <;> simp [Program.evalInst, execInstWithSvc, hc, ps, sA, pcAt_brDisp, State.advancePC_setPC, setPC_setPC, pcAt_succ (pcBase := pcBase) (idx := 16)]
    · rw [show ConditionHolds .CS ps = decide (¬(sampled < 256)) from condHolds_cmp64_256_cs (by omega)]
      by_cases hs : sampled < 256
      · simp only [hs, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine step_rej_chunk24_active hrun hf hslot0 hsamp0 hbuf0 hread hchunk hlen hs fun s' cnt' hws' hst' hc' hh' => ?_
        let s1 := s'.writeReg64 (rSampled v.isVarA) (BitVec.ofNat 64 (sampled + cnt'))
        have hs'samp : s'.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 sampled := hst'.1.readSampled.trans hsamp0
        refine SepWP.step_pure_setPC (s' := s1.setPC (pcAt pcBase 12)) hst'.1.1 (hfHL.get 0) ?_ rfl ?_
        · have hadd : BitVec.ofNat 64 cnt' + BitVec.ofNat 64 sampled = BitVec.ofNat 64 (sampled + cnt') := by bv_omega
          simp [Program.evalInst, execInstWithSvc, execAddSubShift, State.readReg, hst'.2.2, hs'samp, shiftVal, shift64, hadd, s1, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ]
        · have hres : rejChunkStepPure sampled hws ((buf.drop (24 * chunkIdx)).take 24) = (sampled + cnt', hws') := by simp [rejChunkStepPure, hs, hc', hh']
          have hclob : ClobberedPreserved v.isVarA s0 s1 := ((ClobberedPreserved.refl hrun).setPState ps).trans
            ((ClobberedPreserved.of_scratch hst'.1).writeClobbered (rSampled v.isVarA) (BitVec.ofNat 64 (sampled + cnt')) (by cases v <;> simp [rejClobberedRegs]))
          have hrs1 : s1.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 (sampled + cnt') := by cases v <;> simp [s1, RejVariant.isVarA, rSampled]
          have hrb1 : s1.readReg64 (rBuf v.isVarA) = s0.readReg64 (rBuf v.isVarA) :=
            (readReg64_writeReg64_ne_of s' (by cases v <;> decide)).trans hst'.1.readBuf
          have hrr1 : s1.readReg64 (rRem v.isVarA) = s0.readReg64 (rRem v.isVarA) :=
            (readReg64_writeReg64_ne_of s' (by cases v <;> decide)).trans
              (hst'.1.2.2.2 (rRem v.isVarA) (by cases v <;> simp [rejScratchRegs, RejVariant.isVarA, rRem, ChunkInstrs.rOut, rCnt, ChunkInstrs.rB1, ChunkInstrs.rS0, ChunkInstrs.rS1]))
          have hk := hcont s1 hclob (by rw [hres]; exact hrs1) hrb1 hrr1; rwa [hres] at hk
      · simp only [hs, not_false_eq_true, decide_true, ↓reduceIte]
        have hres : rejChunkStepPure sampled hws ((buf.drop (24 * chunkIdx)).take 24) = (sampled, hws) := by simp [rejChunkStepPure, hs]
        have hk := hcont sA ((ClobberedPreserved.refl hrun).setPState ps) (by rw [hres]; exact hsamp0) rfl rfl
        rwa [hres] at hk

private theorem step_rej_latch {prog : Program} {target pcBase sqBase : BitVec 64}
    {v : RejVariant} {chunkIdx rem : Nat} {s0 s1 : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hfHL : FetchesInstrsAt prog pcBase 11 (rejHeadLatchInstrs v.isVarA))
    (hclob1 : ClobberedPreserved v.isVarA s0 s1) (hremB : rem + 1 < 2 ^ 64)
    (hbuf1 : s1.readReg64 (rBuf v.isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hrem1 : s1.readReg64 (rRem v.isVarA) = BitVec.ofNat 64 (rem + 1))
    (hcont : ∀ s3 : State, ClobberedPreserved v.isVarA s0 s3 →
      s3.readReg64 (rSampled v.isVarA) = s1.readReg64 (rSampled v.isVarA) →
      s3.readReg64 (rBuf v.isVarA) = sqBase + BitVec.ofNat 64 (24 * (chunkIdx + 1) + 11) →
      s3.readReg64 (rRem v.isVarA) = BitVec.ofNat 64 rem →
      SepWP prog target (s3.setPC (if rem = 0 then pcAt pcBase 0 else pcAt pcBase 15)) P post oom) :
    SepWP prog target (s1.setPC (pcAt pcBase 12)) P post oom := by
  let psR := subsPState64 (BitVec.ofNat 64 (rem + 1)) 1#64
  let s2 := (s1.writeReg64 (rRem v.isVarA) (BitVec.ofNat 64 rem)).setPState psR
  let s3 := s2.writeReg64 (rBuf v.isVarA) (sqBase + BitVec.ofNat 64 (24 * (chunkIdx + 1) + 11))
  refine SepWP.step_pure_setPC (s' := s2.setPC (pcAt pcBase 13)) hclob1.1 (hfHL.get 1) ?_ rfl ?_
  · simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hrem1, subs64_one_eq rem, psR, s2, State.writeReg, advancePC_writeReg64_setPState_setPC, pcAt_succ]
  · have hbuf2 : s2.readReg64 (rBuf v.isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11) := (readReg64_writeReg64_ne_of _ (by cases v <;> decide)).trans hbuf1
    have hbufAdd : (sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11)) + 24#64 = sqBase + BitVec.ofNat 64 (24 * (chunkIdx + 1) + 11) := by bv_omega
    refine SepWP.step_pure_setPC (s' := s3.setPC (pcAt pcBase 14)) hclob1.1 (hfHL.get 2) ?_ rfl ?_
    · simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hbuf2, hbufAdd, s3, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ]
    · have hpst3 : s3.pstate = psR := by cases s1; cases v <;> rfl
      have hcond := condHolds_cmp64_1_eq hremB
      refine SepWP.step_pure_setPC (s' := s3.setPC (if rem = 0 then pcAt pcBase 0 else pcAt pcBase 15)) hclob1.1 (hfHL.get 3) ?_ rfl ?_
      · by_cases hr0 : rem = 0 <;> simp [Program.evalInst, execInstWithSvc, hpst3, psR, hcond, hr0, pcAt_brDisp, State.advancePC_setPC, setPC_setPC, pcAt_succ (pcBase := pcBase) (idx := 14)]
      · have hclob3 : ClobberedPreserved v.isVarA s0 s3 :=
            ((hclob1.writeClobbered (rRem v.isVarA) (BitVec.ofNat 64 rem) (by cases v <;> simp [rejClobberedRegs])).setPState psR).writeClobbered
              (rBuf v.isVarA) (sqBase + BitVec.ofNat 64 (24 * (chunkIdx + 1) + 11)) (by cases v <;> simp [rejClobberedRegs])
        exact hcont s3 hclob3
          ((readReg64_writeReg64_ne_of _ (by cases v <;> decide)).trans (readReg64_writeReg64_ne_of _ (by cases v <;> decide)))
          (by cases v <;> simp [s3, RejVariant.isVarA, rBuf])
          ((readReg64_writeReg64_ne_of _ (by cases v <;> decide)).trans (by cases v <;> simp [s2, RejVariant.isVarA, rRem]))

/-- Countdown loop `[15 → 0]` over `rem + 1` remaining 24-byte chunks starting at `chunkIdx`. -/
theorem step_rej_chunks_from {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {v : RejVariant} {nChunks : Nat} {buf : List (BitVec 8)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs v)) (hread : RejBufReadable sqBase buf nChunks Pbuf) :
    ∀ (rem chunkIdx sampled : Nat) (s0 : State) (hws : List (BitVec 16)),
      s0.status = .Running → chunkIdx + (rem + 1) ≤ nChunks → rem + 1 < 2 ^ 64 →
      hws.length = 272 → sampled ≤ 271 →
      s0.readReg64 (rSlotBase v.isVarA) = slotBase →
      s0.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 sampled →
      s0.readReg64 (rBuf v.isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11) →
      s0.readReg64 (rRem v.isVarA) = BitVec.ofNat 64 (rem + 1) →
      (∀ sF : State, let res := rejChunksFromPure buf chunkIdx (rem + 1) sampled hws
        ClobberedPreserved v.isVarA s0 sF → sF.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 res.1 →
        SepWP prog target (sF.setPC (pcAt pcBase 0)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE res.2) ∗ F)) post oom) →
      SepWP prog target (s0.setPC (pcAt pcBase 15)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  have hfHL : FetchesInstrsAt prog pcBase 11 (rejHeadLatchInstrs v.isVarA) := by cases v <;> exact slice hf (by omega) rfl
  intro rem; induction rem with
  | zero =>
    intro chunkIdx sampled s0 hws hrun hfit hremB hlen hsb hslot0 hsamp0 hbuf0 hrem0 hcont
    refine step_rej_chunk24 hrun hf hslot0 hsamp0 hbuf0 hread (by omega) hlen hsb fun s1 hclob1 hs1 hbuf1 hrem1 =>
      step_rej_latch hfHL hclob1 hremB (hbuf1.trans hbuf0) (hrem1.trans hrem0) fun s3 hclob3 hs3 _ _ => by
        simpa [rejChunksFromPure] using hcont s3 hclob3 (hs3.trans hs1)
  | succ rem' ih =>
    intro chunkIdx sampled s0 hws hrun hfit hremB hlen hsb hslot0 hsamp0 hbuf0 hrem0 hcont
    refine step_rej_chunk24 hrun hf hslot0 hsamp0 hbuf0 hread (by omega) hlen hsb fun s1 hclob1 hs1 hbuf1 hrem1 => ?_
    have hbnd1 := rejChunkStepPure_bounds (c := (buf.drop (24 * chunkIdx)).take 24) hsb hlen
    refine step_rej_latch hfHL hclob1 hremB (hbuf1.trans hbuf0) (hrem1.trans hrem0) fun s3 hclob3 hs3 hbuf3 hrem3 => ?_
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    exact ih (chunkIdx + 1) _ s3 _ hclob3.1 (by omega) (by omega) hbnd1.2 hbnd1.1
      (hclob3.readSlotBase.trans hslot0) (hs3.trans hs1) hbuf3 hrem3 fun sF hclobF hsF => hcont sF (hclob3.trans hclobF) hsF

/-- Complete `nChunks`-chunk (`21` or `7`) inner `rej_sample` countdown loop `[15 → 0]` preserving
    `RejSlotRawInv` over `buf.take (24 * nChunks)`. -/
theorem step_rej_chunks_inv {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {v : RejVariant} {nChunks sampled : Nat} {cands : List Nat} {s0 : State}
    {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s0.status = .Running) (hf : FetchesInstrsAt prog pcBase 11 (rejInnerInstrs v))
    (hread : RejBufReadable sqBase buf nChunks Pbuf)
    (hn1 : 1 ≤ nChunks) (hnB : nChunks < 2 ^ 64) (hbufLen : 24 * nChunks ≤ buf.length)
    (hinv : RejSlotRawInv cands sampled hws)
    (hslot0 : s0.readReg64 (rSlotBase v.isVarA) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 sampled)
    (hbuf0 : s0.readReg64 (rBuf v.isVarA) = sqBase + 11#64)
    (hrem0 : s0.readReg64 (rRem v.isVarA) = BitVec.ofNat 64 nChunks)
    (hcont : ∀ (sF : State) (sampled' : Nat) (hws' : List (BitVec 16)),
      ClobberedPreserved v.isVarA s0 sF → sF.readReg64 (rSampled v.isVarA) = BitVec.ofNat 64 sampled' →
      RejSlotRawInv (cands ++ parseRej12Candidates (buf.take (24 * nChunks))) sampled' hws' →
      SepWP prog target (sF.setPC (pcAt pcBase 0)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom) :
    SepWP prog target (s0.setPC (pcAt pcBase 15)) (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  have hsb : sampled ≤ 271 := by rcases hinv with ⟨_, ⟨h, _⟩ | ⟨_, h, _⟩, _⟩ <;> omega
  have hsub : nChunks - 1 + 1 = nChunks := by omega
  refine step_rej_chunks_from hf hread (nChunks - 1) 0 sampled s0 hws hrun (by omega)
    (by omega) hinv.1 hsb hslot0 hsamp0 hbuf0 (by rwa [hsub]) fun sF hclob hsF => ?_
  rw [hsub, rejChunksFromPure_zero_eq_fold] at hsF ⊢
  exact hcont sF _ _ hclob hsF (hinv.step_chunks buf nChunks hbufLen)

/-- Execute `cmp rSrc, #255` (`.addSubImm .W64 .SUBS .xzr rSrc 255#12 false`) at `pc`. -/
theorem step_cmp64_255 {prog : Program} {target pc : BitVec 64} {rSrc : Reg} {sampled : Nat}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf : prog.fetch pc = some (.addSubImm .W64 .SUBS .xzr rSrc 255#12 false))
    (hsrc : s.readReg64 rSrc = BitVec.ofNat 64 sampled)
    (hnext : SepWP prog target ((s.setPState (subsPState64 (BitVec.ofNat 64 sampled) 255#64)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target s P post oom := by
  refine SepWP.step_pure (s' := (s.setPState (subsPState64 (BitVec.ofNat 64 sampled) 255#64)).setPC (pc + 4#64)) hpc hrun hf ?_ rfl hnext
  simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hsrc, State.writeReg, advancePC_setPState_setPC]

/-- Execute `csel rDst, r256, rSrc, hi` at `pc`, clamping `RejSlotRawInv` to `RejSlotClampedInv`. -/
theorem step_csel_clamp {prog : Program} {target pc : BitVec 64} {rDst r256 rSrc : Reg}
    {cands : List Nat} {sampled : Nat} {hws : List (BitVec 16)}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf : prog.fetch pc = some (.condSelect .W64 .CSEL rDst r256 rSrc .HI))
    (hps : s.pstate = subsPState64 (BitVec.ofNat 64 sampled) 255#64)
    (hr256 : s.readReg64 r256 = 256#64) (hsrc : s.readReg64 rSrc = BitVec.ofNat 64 sampled)
    (hinv : RejSlotRawInv cands sampled hws)
    (hnext : RejSlotClampedInv cands (clampSampled sampled) hws →
      SepWP prog target ((s.writeReg64 rDst (BitVec.ofNat 64 (clampSampled sampled))).setPC (pc + 4#64)) P post oom) :
    SepWP prog target s P post oom := by
  have hbnd : sampled < 2 ^ 64 := by rcases hinv with ⟨_, ⟨h, _⟩ | ⟨_, h, _⟩, _⟩ <;> omega
  have hcsel := csel_clampSampled_eq hbnd; simp only [conditionHolds_hi_subsPState64] at hcsel
  refine SepWP.step_pure (s' := (s.writeReg64 rDst (BitVec.ofNat 64 (clampSampled sampled))).setPC (pc + 4#64)) hpc hrun hf ?_ rfl (hnext hinv.clamp)
  simp [Program.evalInst, execInstWithSvc, execCondSelect, State.readReg, hps, hr256, hsrc, hcsel, State.writeReg, advancePC_writeReg64_setPC]

/-- Adjacent `cmp rSrc, #255; csel rDst, r256, rSrc, hi` clamp pair at `pc` and `pc + 4`. -/
theorem step_cmp64_csel_clamp {prog : Program} {target pc : BitVec 64} {rDst r256 rSrc : Reg}
    {cands : List Nat} {sampled : Nat} {hws : List (BitVec 16)}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.addSubImm .W64 .SUBS .xzr rSrc 255#12 false))
    (hf1 : prog.fetch (pc + 4#64) = some (.condSelect .W64 .CSEL rDst r256 rSrc .HI))
    (hr256 : s.readReg64 r256 = 256#64) (hsrc : s.readReg64 rSrc = BitVec.ofNat 64 sampled)
    (hinv : RejSlotRawInv cands sampled hws)
    (hnext : RejSlotClampedInv cands (clampSampled sampled) hws →
      SepWP prog target (((s.setPState (subsPState64 (BitVec.ofNat 64 sampled) 255#64)).writeReg64
        rDst (BitVec.ofNat 64 (clampSampled sampled))).setPC (pc + 8#64)) P post oom) :
    SepWP prog target s P post oom :=
  step_cmp64_255 hpc hrun hf0 hsrc <| step_csel_clamp rfl hrun hf1 rfl hr256 hsrc hinv fun hcl => by
    simpa [setPC_writeReg64_setPC, show (pc + 4#64) + 4#64 = pc + 8#64 by bv_omega] using hnext hcl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkStep
