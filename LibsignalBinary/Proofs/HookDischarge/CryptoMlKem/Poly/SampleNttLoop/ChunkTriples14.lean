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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57 -- proof-setup: allow-public-import

/-!
# Backwards-Trellis `SepWP` Lemmas for Triples `1..4` (`SampleNttLoop.ChunkTriples14`)

Two-track `SepWP` lemmas for triples `1..4` (`bytes 3..14`) of `rej_sample` across `B03`–`B07`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples14
open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkemQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE rej12D1 rej12D1W32 rej12D2 rej12D2W32 rejWriteCandidates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (
  RejBufReadable condHolds_cmp32_3328_hi_d1 condHolds_cmp32_3328_hi_d2
  condHolds_cmp32_3328_ls_d1 condHolds_cmp32_3328_ls_d2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt RejTripleState parseRej12TripleAt pcAt
  rB1 rBuf rCnt rOut rS0 readReg64_writeReg64_ne_of read_writeScratch_self
  rejLoadByte rejOutPre24Instrs rejScratchRegs rejSpine14Instrs rejStore14Instrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples (
  of_single_scratch step_bfi_d1 step_cmp32_bCond step_load_chunk_byte
  step_lsr_orr_d2 step_strh_regOff_inc trunc16_d1_reg trunc16_d2_reg writeScratch64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57 (
  tripleAt_00 tripleAt_01 tripleAt_10 tripleAt_11)

theorem step_load2_bfi_14 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {s0 s : State} {buf : List (BitVec 8)}
    {nChunks chunkIdx sampled cnt : Nat} (idx t : Nat) {Pbuf Prest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hs0 : RejTripleState isVarA s0 slotBase sampled cnt s) (ht : t < 8)
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hf0 : prog.fetch (pcAt pcBase idx) = some (rejLoadByte isVarA (rS0 isVarA) (3 * t)))
    (hf1 : prog.fetch (pcAt pcBase (idx + 1)) = some (rejLoadByte isVarA (rB1 isVarA) (3 * t + 1)))
    (hf2 : prog.fetch (pcAt pcBase (idx + 2)) =
      some (.bitfield .W32 .BFM (rS0 isVarA) (rB1 isVarA) 24 3))
    (hnext : ∀ stM : State,
      RejTripleState isVarA s0 slotBase sampled cnt stM →
      stM.readReg64 (rS0 isVarA) =
        (rej12D1W32 (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t) 0#8)
          (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8)).zeroExtend 64 →
      stM.readReg64 (rB1 isVarA) =
        (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8).zeroExtend 64 →
      SepWP prog target (stM.setPC (pcAt pcBase (idx + 3))) (Pbuf ∗ Prest) post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) (Pbuf ∗ Prest) post oom := by
  have hmemS0 : rS0 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hne : rS0 isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneOutS0 : rOut isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneOutB1 : rOut isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntS0 : rCnt isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  refine step_load_chunk_byte idx (3 * t) hs0.1 hbuf0 hf0 hread hchunk (by omega) ?_
  refine step_load_chunk_byte (idx + 1) (3 * t + 1)
    (writeScratch64 hs0.1 hmemS0 _) hbuf0 hf1 hread hchunk (by omega) ?_
  refine step_bfi_d1 (idx + 2)
    (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t) 0#8)
    (((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8) hs0.1.1 hf2
    (by rw [readReg64_writeReg64_ne_of _ hne, read_writeScratch_self _ hmemS0])
    (read_writeScratch_self _ hmemB1 _) ?_
  exact hnext _
    ⟨writeScratch64 (writeScratch64 (writeScratch64 hs0.1 hmemS0 _) hmemB1 _) hmemS0 _,
     by rw [readReg64_writeReg64_ne_of _ hneOutS0, readReg64_writeReg64_ne_of _ hneOutB1,
          readReg64_writeReg64_ne_of _ hneOutS0]
        exact hs0.2.1,
     by rw [readReg64_writeReg64_ne_of _ hneCntS0, readReg64_writeReg64_ne_of _ hneCntB1,
          readReg64_writeReg64_ne_of _ hneCntS0]
        exact hs0.2.2⟩
    (read_writeScratch_self _ hmemS0 _)
    (by rw [readReg64_writeReg64_ne_of _ hne.symm, read_writeScratch_self _ hmemB1])

/-- Triples `1..4` (`bytes 3..14`): spine entry (`39 - spShift + 10*(t-1)`) for `1 ≤ t ≤ 4`
    and out-of-line entry (`105 + 14*(t-1)`) for `2 ≤ t ≤ 4`. -/
theorem step_rej_triple_1_4 {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {spShift t nChunks chunkIdx sampled cnt : Nat}
    {s0 : State} {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (ht1 : 1 ≤ t) (ht4 : t ≤ 4)
    (hfSp : FetchesInstrsAt prog pcBase (39 - spShift + 10 * (t - 1))
      (rejSpine14Instrs isVarA spShift t))
    (hfSt : FetchesInstrsAt prog pcBase (110 + 14 * (t - 1))
      (rejStore14Instrs isVarA spShift t))
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
    (FetchesInstrsAt prog pcBase (105 + 14 * (t - 1)) (rejOutPre24Instrs isVarA spShift t) →
      2 ≤ t → ∀ s, RejTripleState isVarA s0 slotBase sampled cnt s →
      SepWP prog target (s.setPC (pcAt pcBase (105 + 14 * (t - 1))))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom) := by
  let b0 := ((buf.drop (24 * chunkIdx)).take 24).getD (3 * t) 0#8
  let b1 := ((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 1) 0#8
  let b2 := ((buf.drop (24 * chunkIdx)).take 24).getD (3 * t + 2) 0#8
  let spIdx := 39 - spShift + 10 * (t - 1)
  let outIdx := 105 + 14 * (t - 1)
  let store1Idx := 110 + 14 * (t - 1)
  let nextSpIdx := 39 - spShift + 10 * t
  let nextOutIdx := 105 + 14 * t
  have hmemS0 : rS0 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemCnt : rCnt isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hneB1S0 : rB1 isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneOutS0 : rOut isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneCntS0 : rCnt isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneOutCnt : rOut isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
  have hneOutB1 : rOut isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hStore2 : ∀ st c hw, RejTripleState isVarA s0 slotBase sampled c st →
      hw.length = 272 → c < 16 → st.readReg64 (rB1 isVarA) = (rej12D2W32 b1 b2).zeroExtend 64 →
      (∀ s' : State, RejTripleState isVarA s0 slotBase sampled (c + 1) s' →
        SepWP prog target (s'.setPC (pcAt pcBase nextOutIdx))
          (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hw.set (sampled + c) (BitVec.ofNat 16 (rej12D2 b1 b2)))) ∗ F))
          post oom) →
      SepWP prog target (st.setPC (pcAt pcBase (store1Idx + 7)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hw) ∗ F)) post oom := by
    intro st c hw hst hwl hc hb1v hk
    refine step_strh_regOff_inc (store1Idx + 7) (rej12D2 b1 b2) hst.1.1 (hfSt.get 7) (hfSt.get 8)
      hwl hs hc hst.2.1 hst.2.2 (trunc16_d2_reg hb1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    rw [show store1Idx + 7 + 2 = nextOutIdx by dsimp only [store1Idx, nextOutIdx]; omega]
    exact hk s1 ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
                 (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
  have hD2Spine : ∀ st, RejTripleState isVarA s0 slotBase sampled cnt st →
      st.readReg64 (rB1 isVarA) = b1.zeroExtend 64 →
      ¬(rej12D1 b0 b1 < mlkemQ) →
      SepWP prog target (st.setPC (pcAt pcBase (spIdx + 5)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
    intro st hst hb1v hd1
    refine step_load_chunk_byte (spIdx + 5) (3 * t + 2) hst.1 hbuf0 (hfSp.get 5) hread hchunk
      (by omega) ?_
    refine step_lsr_orr_d2 (spIdx + 6) b1 b2 hst.1.1 (hfSp.get 6) (hfSp.get 7)
      (by rw [readReg64_writeReg64_ne_of _ hneB1S0]; exact hb1v)
      (read_writeScratch_self _ hmemS0 _)
      fun s1 hrun1 hsp1 hv1 hoth1 hb1_1 => ?_
    have hstL : RejTripleState isVarA s0 slotBase sampled cnt
        (st.writeReg64 (rS0 isVarA) (b2.zeroExtend 64)) :=
      ⟨writeScratch64 hst.1 hmemS0 _,
       (readReg64_writeReg64_ne_of _ hneOutS0).trans hst.2.1,
       (readReg64_writeReg64_ne_of _ hneCntS0).trans hst.2.2⟩
    have hst' : RejTripleState isVarA s0 slotBase sampled cnt s1 :=
      ⟨of_single_scratch hstL.1 hmemB1 hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutB1).trans hstL.2.1, (hoth1 _ hneCntB1).trans hstL.2.2⟩
    refine step_cmp32_bCond (spIdx + 8) (store1Idx + 7) (rej12D2W32 b1 b2) hst'.1.1
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
      st.readReg64 (rS0 isVarA) = (rej12D1W32 b0 b1).zeroExtend 64 →
      st.readReg64 (rB1 isVarA) = b1.zeroExtend 64 →
      rej12D1 b0 b1 < mlkemQ →
      SepWP prog target (st.setPC (pcAt pcBase store1Idx))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
    intro st hst hd1v hb1v hd1
    refine step_strh_regOff_inc store1Idx (rej12D1 b0 b1) hst.1.1 (hfSt.get 0) (hfSt.get 1)
      hlen hs (by omega) hst.2.1 hst.2.2 (trunc16_d1_reg hd1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    let hws1 := hws.set (sampled + cnt) (BitVec.ofNat 16 (rej12D1 b0 b1))
    have hneB1 : rB1 isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
    have hst1_pre : RejTripleState isVarA s0 slotBase sampled (cnt + 1) s1 :=
      ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
    refine step_load_chunk_byte (store1Idx + 2) (3 * t + 2) hst1_pre.1 hbuf0 (hfSt.get 2)
      hread hchunk (by omega) ?_
    have hst1_ld : RejTripleState isVarA s0 slotBase sampled (cnt + 1)
        (s1.writeReg64 (rS0 isVarA) (b2.zeroExtend 64)) :=
      ⟨writeScratch64 hst1_pre.1 hmemS0 _,
       (readReg64_writeReg64_ne_of _ hneOutS0).trans hst1_pre.2.1,
       (readReg64_writeReg64_ne_of _ hneCntS0).trans hst1_pre.2.2⟩
    refine step_lsr_orr_d2 (store1Idx + 3) b1 b2 hrun1 (hfSt.get 3) (hfSt.get 4)
      (by rw [readReg64_writeReg64_ne_of _ hneB1S0]; exact (hoth1 _ hneB1).trans hb1v)
      (read_writeScratch_self _ hmemS0 _)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst1 : RejTripleState isVarA s0 slotBase sampled (cnt + 1) s2 :=
      ⟨of_single_scratch hst1_ld.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hst1_ld.2.1, (hoth2 _ hneCntB1).trans hst1_ld.2.2⟩
    refine step_cmp32_bCond (store1Idx + 5) nextSpIdx (rej12D2W32 b1 b2) hst1.1.1
      (hfSt.get 5) (hfSt.get 6) hb1_2 ?_
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
    refine step_load2_bfi_14 spIdx t hs0 (by omega) hbuf0 hread hchunk
      (hfSp.get 0) (hfSp.get 1) (hfSp.get 2) fun stM hstM hd1v hb1v => ?_
    refine step_cmp32_bCond (spIdx + 3) store1Idx (rej12D1W32 b0 b1) hstM.1.1
      (hfSp.get 3) (hfSp.get 4) hd1v ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .LS (subsPState32 (rej12D1W32 b0 b1) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_ls_d1]
    by_cases hd1 : rej12D1 b0 b1 < mlkemQ
    · simp only [hd1, decide_true, ↓reduceIte]
      exact hStore1 _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hd1v hb1v hd1
    · simp only [hd1, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hD2Spine _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hb1v hd1
  · intro hfOut _ s hs0
    refine step_load2_bfi_14 outIdx t hs0 (by omega) hbuf0 hread hchunk
      (hfOut.get 0) (hfOut.get 1) (hfOut.get 2) fun stM hstM hd1v hb1v => ?_
    refine step_cmp32_bCond (outIdx + 3) (spIdx + 5) (rej12D1W32 b0 b1) hstM.1.1
      (hfOut.get 3) (hfOut.get 4) hd1v ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .HI (subsPState32 (rej12D1W32 b0 b1) 3328#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3328_hi_d1]
    by_cases hd1 : rej12D1 b0 b1 < mlkemQ
    · simp only [hd1, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        show outIdx + 3 + 2 = store1Idx by dsimp only [outIdx, store1Idx]; omega]
      exact hStore1 _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hd1v hb1v hd1
    · simp only [hd1, not_false_eq_true, decide_true, ↓reduceIte]
      exact hD2Spine _ ⟨hstM.1.setPState _, hstM.2.1, hstM.2.2⟩ hb1v hd1

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples14
