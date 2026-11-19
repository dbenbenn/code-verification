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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples -- proof-setup: allow-public-import

/-!
# Backwards-Trellis `SepWP` Lemmas for Triples `5..7` (`SampleNttLoop.ChunkTriples57`)

Two-track `SepWP` lemmas for triples `5..7` (`bytes 15..23`) of `rej_sample` across `B03`–`B07`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57
open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkemQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE parseRej12Triple rej12D1 rej12D1W32 rej12D2 rej12D2W32 rejWriteCandidates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (
  RejBufReadable condHolds_cmp32_3328_hi_d1 condHolds_cmp32_3328_hi_d2
  condHolds_cmp32_3328_ls_d1 condHolds_cmp32_3328_ls_d2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt RejTripleState parseRej12TripleAt pcAt rB1 rBuf rCnt rOut rS0 rS1
  readReg64_writeReg64_ne_of read_writeScratch_self rejLoadByte rejOutPre57Instrs
  rejScratchRegs rejSpine56Instrs rejSpine7Instrs rejStore56Instrs rejStore7Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples (
  of_single_scratch step_b_uncond step_bfi_d1 step_cmp32_bCond step_load_chunk_byte
  step_lsr_orr_d2 step_strh_regOff_inc trunc16_d1_reg trunc16_d2_reg writeScratch64)

/-! ## 1. Pure Case Split Helpers for `parseRej12TripleAt` -/

theorem tripleAt_00 {chunk : List (BitVec 8)} {t : Nat} (hws : List (BitVec 16))
    (sampled cnt : Nat)
    (hd1 : ¬(rej12D1 (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8) < mlkemQ))
    (hd2 : ¬(rej12D2 (chunk.getD (3 * t + 1) 0#8) (chunk.getD (3 * t + 2) 0#8) < mlkemQ)) :
    cnt = cnt + (parseRej12TripleAt chunk t).length ∧
    hws = rejWriteCandidates hws (sampled + cnt) (parseRej12TripleAt chunk t) := by
  unfold parseRej12TripleAt parseRej12Triple
  simp only [hd1, hd2, ↓reduceIte, List.append_nil, List.length_nil, Nat.add_zero,
    rejWriteCandidates, and_self]

theorem tripleAt_01 {chunk : List (BitVec 8)} {t : Nat} (hws : List (BitVec 16))
    (sampled cnt : Nat)
    (hd1 : ¬(rej12D1 (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8) < mlkemQ))
    (hd2 : rej12D2 (chunk.getD (3 * t + 1) 0#8) (chunk.getD (3 * t + 2) 0#8) < mlkemQ) :
    cnt + 1 = cnt + (parseRej12TripleAt chunk t).length ∧
    hws.set (sampled + cnt)
      (BitVec.ofNat 16 (rej12D2 (chunk.getD (3 * t + 1) 0#8) (chunk.getD (3 * t + 2) 0#8))) =
      rejWriteCandidates hws (sampled + cnt) (parseRej12TripleAt chunk t) := by
  unfold parseRej12TripleAt parseRej12Triple
  simp only [hd1, hd2, ↓reduceIte, List.nil_append, List.length_singleton, rejWriteCandidates,
    and_self]

theorem tripleAt_10 {chunk : List (BitVec 8)} {t : Nat} (hws : List (BitVec 16))
    (sampled cnt : Nat)
    (hd1 : rej12D1 (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8) < mlkemQ)
    (hd2 : ¬(rej12D2 (chunk.getD (3 * t + 1) 0#8) (chunk.getD (3 * t + 2) 0#8) < mlkemQ)) :
    cnt + 1 = cnt + (parseRej12TripleAt chunk t).length ∧
    hws.set (sampled + cnt)
      (BitVec.ofNat 16 (rej12D1 (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8))) =
      rejWriteCandidates hws (sampled + cnt) (parseRej12TripleAt chunk t) := by
  unfold parseRej12TripleAt parseRej12Triple
  simp only [hd1, hd2, ↓reduceIte, List.append_nil, List.length_singleton, rejWriteCandidates,
    and_self]

theorem tripleAt_11 {chunk : List (BitVec 8)} {t : Nat} (hws : List (BitVec 16))
    (sampled cnt : Nat)
    (hd1 : rej12D1 (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8) < mlkemQ)
    (hd2 : rej12D2 (chunk.getD (3 * t + 1) 0#8) (chunk.getD (3 * t + 2) 0#8) < mlkemQ) :
    cnt + 2 = cnt + (parseRej12TripleAt chunk t).length ∧
    (hws.set (sampled + cnt)
      (BitVec.ofNat 16 (rej12D1 (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8)))).set
        (sampled + (cnt + 1))
        (BitVec.ofNat 16 (rej12D2 (chunk.getD (3 * t + 1) 0#8) (chunk.getD (3 * t + 2) 0#8))) =
      rejWriteCandidates hws (sampled + cnt) (parseRej12TripleAt chunk t) := by
  unfold parseRej12TripleAt parseRej12Triple
  simp only [hd1, hd2, ↓reduceIte, List.singleton_append, List.length_cons, List.length_nil,
    rejWriteCandidates, Nat.add_assoc, and_self]

/-! ## 2. Shared Preamble & Triples `5..7` -/

theorem step_load3_bfi_57 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {s0 s : State} {buf : List (BitVec 8)}
    {nChunks chunkIdx sampled cnt : Nat} (idx t : Nat) {Pbuf Prest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hs0 : RejTripleState isVarA s0 slotBase sampled cnt s) (ht : t < 8)
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hf0 : prog.fetch (pcAt pcBase idx) = some (rejLoadByte isVarA (rS1 isVarA) (3 * t)))
    (hf1 : prog.fetch (pcAt pcBase (idx + 1)) = some (rejLoadByte isVarA (rB1 isVarA) (3 * t + 1)))
    (hf2 : prog.fetch (pcAt pcBase (idx + 2)) = some (rejLoadByte isVarA (rS0 isVarA) (3 * t + 2)))
    (hf3 : prog.fetch (pcAt pcBase (idx + 3)) =
      some (.bitfield .W32 .BFM (rS1 isVarA) (rB1 isVarA) 24 3))
    (hnext : ∀ stM : State,
      RejTripleState isVarA s0 slotBase sampled cnt stM →
      stM.readReg64 (rS1 isVarA) =
        (rej12D1W32 (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t) 0#8)
          (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8)).zeroExtend 64 →
      stM.readReg64 (rB1 isVarA) =
        (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8).zeroExtend 64 →
      stM.readReg64 (rS0 isVarA) =
        (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 2) 0#8).zeroExtend 64 →
      SepWP prog target (stM.setPC (pcAt pcBase (idx + 4))) (Pbuf ∗ Prest) post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) (Pbuf ∗ Prest) post oom := by
  have hmemS1 : rS1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemS0 : rS0 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hne1 : rS1 isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hne2 : rS1 isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hne3 : rB1 isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneOutS1 : rOut isVarA ≠ rS1 isVarA := by cases isVarA <;> decide
  have hneOutB1 : rOut isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneOutS0 : rOut isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneCntS1 : rCnt isVarA ≠ rS1 isVarA := by cases isVarA <;> decide
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntS0 : rCnt isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  refine step_load_chunk_byte idx (3 * t) hs0.1 hbuf0 hf0 hread hchunk (by omega) ?_
  refine step_load_chunk_byte (idx + 1) (3 * t + 1)
    (writeScratch64 hs0.1 hmemS1 _) hbuf0 hf1 hread hchunk (by omega) ?_
  refine step_load_chunk_byte (idx + 2) (3 * t + 2)
    (writeScratch64 (writeScratch64 hs0.1 hmemS1 _) hmemB1 _)
    hbuf0 hf2 hread hchunk (by omega) ?_
  refine step_bfi_d1 (idx + 3)
    (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t) 0#8)
    (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8) hs0.1.1 hf3
    (by rw [readReg64_writeReg64_ne_of _ hne2, readReg64_writeReg64_ne_of _ hne1,
          read_writeScratch_self _ hmemS1])
    (by rw [readReg64_writeReg64_ne_of _ hne3, read_writeScratch_self _ hmemB1]) ?_
  exact hnext _
    ⟨writeScratch64 (writeScratch64 (writeScratch64 (writeScratch64 hs0.1 hmemS1 _) hmemB1 _) hmemS0 _) hmemS1 _,
     by rw [readReg64_writeReg64_ne_of _ hneOutS1, readReg64_writeReg64_ne_of _ hneOutS0,
          readReg64_writeReg64_ne_of _ hneOutB1, readReg64_writeReg64_ne_of _ hneOutS1]
        exact hs0.2.1,
     by rw [readReg64_writeReg64_ne_of _ hneCntS1, readReg64_writeReg64_ne_of _ hneCntS0,
          readReg64_writeReg64_ne_of _ hneCntB1, readReg64_writeReg64_ne_of _ hneCntS1]
        exact hs0.2.2⟩
    (read_writeScratch_self _ hmemS1 _)
    (by rw [readReg64_writeReg64_ne_of _ hne1.symm, readReg64_writeReg64_ne_of _ hne3,
          read_writeScratch_self _ hmemB1])
    (by rw [readReg64_writeReg64_ne_of _ hne2.symm, read_writeScratch_self _ hmemS0])

/-- Triple 7 (`bytes 21..23`, spine entry `99 - spShift` and out-of-line entry `189`)
    steps to `pcAt pcBase 11` (`pcCommit`). -/
theorem step_rej_triple7 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {spShift nChunks chunkIdx sampled cnt : Nat}
    {s0 : State} {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsh : spShift ≤ 7)
    (hfSp : FetchesInstrsAt prog pcBase (99 - spShift) (rejSpine7Instrs isVarA spShift))
    (hfOut : FetchesInstrsAt prog pcBase 189 (rejOutPre57Instrs isVarA spShift 7))
    (hfSt : FetchesInstrsAt prog pcBase 195 (rejStore7Instrs isVarA))
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256) (hcnt : cnt ≤ 14)
    (hcont : ∀ s' cnt' hws',
      RejTripleState isVarA s0 slotBase sampled cnt' s' →
      cnt' = cnt + (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) 7).length →
      hws' = rejWriteCandidates hws (sampled + cnt)
        (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) 7) →
      SepWP prog target (s'.setPC (pcAt pcBase 11))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom) :
    (∀ s, RejTripleState isVarA s0 slotBase sampled cnt s →
      SepWP prog target (s.setPC (pcAt pcBase (99 - spShift)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom) ∧
    (∀ s, RejTripleState isVarA s0 slotBase sampled cnt s →
      SepWP prog target (s.setPC (pcAt pcBase 189))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom) := by
  let b0 := ((buf.drop (24 * chunkIdx)).take 24).getD 21 0#8
  let b1 := ((buf.drop (24 * chunkIdx)).take 24).getD 22 0#8
  let b2 := ((buf.drop (24 * chunkIdx)).take 24).getD 23 0#8
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemCnt : rCnt isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hneOutCnt : rOut isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
  have hneOutB1 : rOut isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hStore2 : ∀ st c hw, RejTripleState isVarA s0 slotBase sampled c st →
      hw.length = 272 → c < 16 → st.readReg64 (rB1 isVarA) = (rej12D2W32 b1 b2).zeroExtend 64 →
      (∀ s' : State, RejTripleState isVarA s0 slotBase sampled (c + 1) s' →
        SepWP prog target (s'.setPC (pcAt pcBase 11))
          (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hw.set (sampled + c) (BitVec.ofNat 16 (rej12D2 b1 b2)))) ∗ F))
          post oom) →
      SepWP prog target (st.setPC (pcAt pcBase 201))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hw) ∗ F)) post oom := by
    intro st c hw hst hwl hc hb1v hk
    refine step_strh_regOff_inc 201 (rej12D2 b1 b2) hst.1.1 (hfSt.get 6) (hfSt.get 7)
      hwl hs hc hst.2.1 hst.2.2 (trunc16_d2_reg hb1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    exact step_b_uncond 203 11 hrun1 (hfSt.get 8)
      (hk s1 ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
              (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩)
  have hD2Spine : ∀ st, RejTripleState isVarA s0 slotBase sampled cnt st →
      st.readReg64 (rB1 isVarA) = b1.zeroExtend 64 →
      st.readReg64 (rS0 isVarA) = b2.zeroExtend 64 →
      ¬(rej12D1 b0 b1 < mlkemQ) →
      SepWP prog target (st.setPC (pcAt pcBase (99 - spShift + 6)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
    intro st hst hb1v hb2v hd1
    refine step_lsr_orr_d2 (99 - spShift + 6) b1 b2 hst.1.1 (hfSp.get 6) (hfSp.get 7) hb1v hb2v
      fun s1 hrun1 hsp1 hv1 hoth1 hb1_1 => ?_
    have hst' : RejTripleState isVarA s0 slotBase sampled cnt s1 :=
      ⟨of_single_scratch hst.1 hmemB1 hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutB1).trans hst.2.1, (hoth1 _ hneCntB1).trans hst.2.2⟩
    refine step_cmp32_bCond (99 - spShift + 8) 11 (rej12D2W32 b1 b2) hst'.1.1
      (hfSp.get 8) (hfSp.get 9) hb1_1 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .HI (subsPState32 (rej12D2W32 b1 b2) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_hi_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine step_b_uncond (99 - spShift + 10) 201 hst'.1.1 (hfSp.get 10) ?_
      refine hStore2 _ cnt hws ⟨hst'.1.setPState _, hst'.2.1, hst'.2.2⟩ hlen (by omega)
        hb1_1 fun s' hs' => ?_
      have hc01 := tripleAt_01 (t := 7) hws sampled cnt hd1 hd2
      exact hcont s' (cnt + 1) _ hs' hc01.1 hc01.2
    · simp only [hd2, not_false_eq_true, decide_true, ↓reduceIte]
      have hc00 := tripleAt_00 (t := 7) hws sampled cnt hd1 hd2
      exact hcont _ cnt hws ⟨hst'.1.setPState _, hst'.2.1, hst'.2.2⟩ hc00.1 hc00.2
  have hStore1 : ∀ st, RejTripleState isVarA s0 slotBase sampled cnt st →
      st.readReg64 (rS1 isVarA) = (rej12D1W32 b0 b1).zeroExtend 64 →
      st.readReg64 (rB1 isVarA) = b1.zeroExtend 64 →
      st.readReg64 (rS0 isVarA) = b2.zeroExtend 64 →
      rej12D1 b0 b1 < mlkemQ →
      SepWP prog target (st.setPC (pcAt pcBase 195))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
    intro st hst hd1v hb1v hb2v hd1
    refine step_strh_regOff_inc 195 (rej12D1 b0 b1) hst.1.1 (hfSt.get 0) (hfSt.get 1)
      hlen hs (by omega) hst.2.1 hst.2.2 (trunc16_d1_reg hd1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    let hws1 := hws.set (sampled + cnt) (BitVec.ofNat 16 (rej12D1 b0 b1))
    have hneB1 : rB1 isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
    have hneS0 : rS0 isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
    have hst1_pre : RejTripleState isVarA s0 slotBase sampled (cnt + 1) s1 :=
      ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
    refine step_lsr_orr_d2 197 b1 b2 hrun1 (hfSt.get 2) (hfSt.get 3)
      ((hoth1 _ hneB1).trans hb1v) ((hoth1 _ hneS0).trans hb2v)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst1 : RejTripleState isVarA s0 slotBase sampled (cnt + 1) s2 :=
      ⟨of_single_scratch hst1_pre.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hst1_pre.2.1, (hoth2 _ hneCntB1).trans hst1_pre.2.2⟩
    refine step_cmp32_bCond 199 11 (rej12D2W32 b1 b2) hst1.1.1 (hfSt.get 4) (hfSt.get 5) hb1_2 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .HI (subsPState32 (rej12D2W32 b1 b2) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_hi_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine hStore2 _ (cnt + 1) hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩
        (by simp [hws1, hlen]) (by omega) hb1_2 fun s' hs' => ?_
      have hc11 := tripleAt_11 (t := 7) hws sampled cnt hd1 hd2
      exact hcont s' (cnt + 2) _ (by simpa [Nat.add_assoc] using hs') hc11.1 hc11.2
    · simp only [hd2, not_false_eq_true, decide_true, ↓reduceIte]
      have hc10 := tripleAt_10 (t := 7) hws sampled cnt hd1 hd2
      exact hcont _ (cnt + 1) hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩ hc10.1 hc10.2
  constructor
  · intro s hs0
    refine step_load3_bfi_57 (99 - spShift) 7 hs0 (by omega) hbuf0 hread hchunk
      (hfSp.get 0) (hfSp.get 1) (hfSp.get 2) (hfSp.get 3) fun stM hstM hd1v hb1v hb2v => ?_
    refine step_cmp32_bCond (99 - spShift + 4) 195 (rej12D1W32 b0 b1) hstM.1.1
      (hfSp.get 4) (hfSp.get 5) hd1v ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .LS (subsPState32 (rej12D1W32 b0 b1) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_ls_d1]
    by_cases hd1 : rej12D1 b0 b1 < mlkemQ
    · simp only [hd1, decide_true, ↓reduceIte]
      exact hStore1 _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hd1v hb1v hb2v hd1
    · simp only [hd1, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hD2Spine _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hb1v hb2v hd1
  · intro s hs0
    refine step_load3_bfi_57 189 7 hs0 (by omega) hbuf0 hread hchunk
      (hfOut.get 0) (hfOut.get 1) (hfOut.get 2) (hfOut.get 3) fun stM hstM hd1v hb1v hb2v => ?_
    refine step_cmp32_bCond 193 (39 - spShift + 10 * (7 - 1) + 6) (rej12D1W32 b0 b1) hstM.1.1
      (hfOut.get 4) (hfOut.get 5) hd1v ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .HI (subsPState32 (rej12D1W32 b0 b1) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_hi_d1]
    by_cases hd1 : rej12D1 b0 b1 < mlkemQ
    · simp only [hd1, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hStore1 _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hd1v hb1v hb2v hd1
    · simp only [hd1, not_false_eq_true, decide_true, ↓reduceIte,
        show 39 - spShift + 10 * (7 - 1) + 6 = 99 - spShift + 6 by omega]
      exact hD2Spine _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hb1v hb2v hd1

/-- Triples `5..6` (`bytes 15..20`, spine entry `39 - spShift + 10*(t-1)` and out-of-line entry
    `105 + 14*(t-1)`) step to the next triple's spine (`39 - spShift + 10*t`) or out-of-line
    (`105 + 14*t`) entry. -/
theorem step_rej_triple_5_6 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {spShift t nChunks chunkIdx sampled cnt : Nat}
    {s0 : State} {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (ht5 : 5 ≤ t) (ht6 : t ≤ 6)
    (hfSp : FetchesInstrsAt prog pcBase (39 - spShift + 10 * (t - 1))
      (rejSpine56Instrs isVarA spShift t))
    (hfOut : FetchesInstrsAt prog pcBase (105 + 14 * (t - 1))
      (rejOutPre57Instrs isVarA spShift t))
    (hfSt : FetchesInstrsAt prog pcBase (167 + 14 * (t - 5))
      (rejStore56Instrs isVarA spShift t))
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256) (hcnt : cnt ≤ 2 * t)
    (hcontSp : ∀ s' cnt' hws', RejTripleState isVarA s0 slotBase sampled cnt' s' →
      cnt' = cnt + (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) t).length →
      hws' = rejWriteCandidates hws (sampled + cnt) (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) t) →
      SepWP prog target (s'.setPC (pcAt pcBase (39 - spShift + 10 * t)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom)
    (hcontOut : ∀ s' cnt' hws', RejTripleState isVarA s0 slotBase sampled cnt' s' →
      cnt' = cnt + (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) t).length →
      hws' = rejWriteCandidates hws (sampled + cnt) (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) t) →
      SepWP prog target (s'.setPC (pcAt pcBase (105 + 14 * t)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom) :
    (∀ s, RejTripleState isVarA s0 slotBase sampled cnt s →
      SepWP prog target (s.setPC (pcAt pcBase (39 - spShift + 10 * (t - 1))))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom) ∧
    (∀ s, RejTripleState isVarA s0 slotBase sampled cnt s →
      SepWP prog target (s.setPC (pcAt pcBase (105 + 14 * (t - 1))))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom) := by
  let b0 := ((buf.drop (24 * chunkIdx)).take 24).getD (3 * t) 0#8
  let b1 := ((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8
  let b2 := ((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 2) 0#8
  let spIdx := 39 - spShift + 10 * (t - 1)
  let outIdx := 105 + 14 * (t - 1)
  let store1Idx := 167 + 14 * (t - 5)
  let nextSpIdx := 39 - spShift + 10 * t
  let nextOutIdx := 105 + 14 * t
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemCnt : rCnt isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hneOutCnt : rOut isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
  have hneOutB1 : rOut isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hStore2 : ∀ st c hw, RejTripleState isVarA s0 slotBase sampled c st →
      hw.length = 272 → c < 16 → st.readReg64 (rB1 isVarA) = (rej12D2W32 b1 b2).zeroExtend 64 →
      (∀ s' : State, RejTripleState isVarA s0 slotBase sampled (c + 1) s' →
        SepWP prog target (s'.setPC (pcAt pcBase nextOutIdx))
          (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hw.set (sampled + c) (BitVec.ofNat 16 (rej12D2 b1 b2)))) ∗ F))
          post oom) →
      SepWP prog target (st.setPC (pcAt pcBase (store1Idx + 6)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hw) ∗ F)) post oom := by
    intro st c hw hst hwl hc hb1v hk
    refine step_strh_regOff_inc (store1Idx + 6) (rej12D2 b1 b2) hst.1.1 (hfSt.get 6) (hfSt.get 7)
      hwl hs hc hst.2.1 hst.2.2 (trunc16_d2_reg hb1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    rw [show store1Idx + 6 + 2 = nextOutIdx by dsimp only [store1Idx, nextOutIdx]; omega]
    exact hk s1 ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
                 (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
  have hD2Spine : ∀ st, RejTripleState isVarA s0 slotBase sampled cnt st →
      st.readReg64 (rB1 isVarA) = b1.zeroExtend 64 →
      st.readReg64 (rS0 isVarA) = b2.zeroExtend 64 →
      ¬(rej12D1 b0 b1 < mlkemQ) →
      SepWP prog target (st.setPC (pcAt pcBase (spIdx + 6)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
    intro st hst hb1v hb2v hd1
    refine step_lsr_orr_d2 (spIdx + 6) b1 b2 hst.1.1 (hfSp.get 6) (hfSp.get 7) hb1v hb2v
      fun s1 hrun1 hsp1 hv1 hoth1 hb1_1 => ?_
    have hst' : RejTripleState isVarA s0 slotBase sampled cnt s1 :=
      ⟨of_single_scratch hst.1 hmemB1 hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutB1).trans hst.2.1, (hoth1 _ hneCntB1).trans hst.2.2⟩
    refine step_cmp32_bCond (spIdx + 8) (store1Idx + 6) (rej12D2W32 b1 b2) hst'.1.1
      (hfSp.get 8) (hfSp.get 9) hb1_1 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .LS (subsPState32 (rej12D2W32 b1 b2) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_ls_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, decide_true, ↓reduceIte]
      refine hStore2 _ cnt hws ⟨hst'.1.setPState _, hst'.2.1, hst'.2.2⟩ hlen (by omega)
        hb1_1 fun s' hs' => ?_
      have hc01 := tripleAt_01 (t := t) hws sampled cnt hd1 hd2
      exact hcontOut s' (cnt + 1) _ hs' hc01.1 hc01.2
    · simp only [hd2, decide_false, Bool.false_eq_true, ↓reduceIte,
        show spIdx + 8 + 2 = nextSpIdx by dsimp only [spIdx, nextSpIdx]; omega]
      have hc00 := tripleAt_00 (t := t) hws sampled cnt hd1 hd2
      exact hcontSp _ cnt hws ⟨hst'.1.setPState _, hst'.2.1, hst'.2.2⟩ hc00.1 hc00.2
  have hStore1 : ∀ st, RejTripleState isVarA s0 slotBase sampled cnt st →
      st.readReg64 (rS1 isVarA) = (rej12D1W32 b0 b1).zeroExtend 64 →
      st.readReg64 (rB1 isVarA) = b1.zeroExtend 64 →
      st.readReg64 (rS0 isVarA) = b2.zeroExtend 64 →
      rej12D1 b0 b1 < mlkemQ →
      SepWP prog target (st.setPC (pcAt pcBase store1Idx))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
    intro st hst hd1v hb1v hb2v hd1
    refine step_strh_regOff_inc store1Idx (rej12D1 b0 b1) hst.1.1 (hfSt.get 0) (hfSt.get 1)
      hlen hs (by omega) hst.2.1 hst.2.2 (trunc16_d1_reg hd1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    let hws1 := hws.set (sampled + cnt) (BitVec.ofNat 16 (rej12D1 b0 b1))
    have hneB1 : rB1 isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
    have hneS0 : rS0 isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
    have hst1_pre : RejTripleState isVarA s0 slotBase sampled (cnt + 1) s1 :=
      ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
    refine step_lsr_orr_d2 (store1Idx + 2) b1 b2 hrun1 (hfSt.get 2) (hfSt.get 3)
      ((hoth1 _ hneB1).trans hb1v) ((hoth1 _ hneS0).trans hb2v)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst1 : RejTripleState isVarA s0 slotBase sampled (cnt + 1) s2 :=
      ⟨of_single_scratch hst1_pre.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hst1_pre.2.1, (hoth2 _ hneCntB1).trans hst1_pre.2.2⟩
    refine step_cmp32_bCond (store1Idx + 4) nextSpIdx (rej12D2W32 b1 b2) hst1.1.1
      (hfSt.get 4) (hfSt.get 5) hb1_2 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .HI (subsPState32 (rej12D2W32 b1 b2) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_hi_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine hStore2 _ (cnt + 1) hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩
        (by simp [hws1, hlen]) (by omega) hb1_2 fun s' hs' => ?_
      have hc11 := tripleAt_11 (t := t) hws sampled cnt hd1 hd2
      exact hcontOut s' (cnt + 2) _ (by simpa [Nat.add_assoc] using hs') hc11.1 hc11.2
    · simp only [hd2, not_false_eq_true, decide_true, ↓reduceIte]
      have hc10 := tripleAt_10 (t := t) hws sampled cnt hd1 hd2
      exact hcontSp _ (cnt + 1) hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩ hc10.1 hc10.2
  constructor
  · intro s hs0
    refine step_load3_bfi_57 spIdx t hs0 (by omega) hbuf0 hread hchunk
      (hfSp.get 0) (hfSp.get 1) (hfSp.get 2) (hfSp.get 3) fun stM hstM hd1v hb1v hb2v => ?_
    refine step_cmp32_bCond (spIdx + 4) store1Idx (rej12D1W32 b0 b1) hstM.1.1
      (hfSp.get 4) (hfSp.get 5) hd1v ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .LS (subsPState32 (rej12D1W32 b0 b1) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_ls_d1]
    by_cases hd1 : rej12D1 b0 b1 < mlkemQ
    · simp only [hd1, decide_true, ↓reduceIte]
      exact hStore1 _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hd1v hb1v hb2v hd1
    · simp only [hd1, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hD2Spine _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hb1v hb2v hd1
  · intro s hs0
    refine step_load3_bfi_57 outIdx t hs0 (by omega) hbuf0 hread hchunk
      (hfOut.get 0) (hfOut.get 1) (hfOut.get 2) (hfOut.get 3) fun stM hstM hd1v hb1v hb2v => ?_
    refine step_cmp32_bCond (outIdx + 4) (spIdx + 6) (rej12D1W32 b0 b1) hstM.1.1
      (hfOut.get 4) (hfOut.get 5) hd1v ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .HI (subsPState32 (rej12D1W32 b0 b1) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_hi_d1]
    by_cases hd1 : rej12D1 b0 b1 < mlkemQ
    · simp only [hd1, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        show outIdx + 4 + 2 = store1Idx by dsimp only [outIdx, store1Idx]; omega]
      exact hStore1 _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hd1v hb1v hb2v hd1
    · simp only [hd1, not_false_eq_true, decide_true, ↓reduceIte]
      exact hD2Spine _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hb1v hb2v hd1

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57
