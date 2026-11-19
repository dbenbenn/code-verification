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
# Entry Triple `0` `SepWP` Lemmas (`SampleNttLoop.ChunkTriple0`)

`SepWP` lemmas for entry triple `0` (`bytes 0..2`, Variants A/B at `[17..38]` and Variant C at
`[17..31]` + `[103..109]`) of `rej_sample` across `B03`–`B07`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriple0
open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkemQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE rej12D1 rej12D1W32 rej12D2 rej12D2W32 rejWriteCandidates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (
  RejBufReadable condHolds_cmp32_3329_cc_d2 condHolds_cmp32_3329_cs_d1 condHolds_cmp32_3329_cs_d2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt RejTripleState ScratchPreserved parseRej12TripleAt pcAt pcAt_succ
  rB1 rBuf rCnt rOut rS0 rSampled rSlotBase readReg64_writeReg64_ne_of read_writeScratch_self
  rejLoadByte rejScratchRegs rejTriple0ABInstrs rejTriple0CFastInstrs rejTriple0CSlowInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples (
  of_single_scratch step_b_uncond step_bfi_d1 step_cmp32_bCond step_load_chunk_byte
  step_lsr_orr_d2 step_mov_xzr_cnt step_strh_regOff_inc step_strh_zero_movz1
  trunc16_d1_reg trunc16_d2_reg writeScratch64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples57 (
  tripleAt_00 tripleAt_01 tripleAt_10 tripleAt_11)

private theorem advancePC_writeReg64_setPC (s : State) (a : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).advancePC = (s.writeReg64 r v).setPC (a + 4#64) := by
  cases s; cases r <;> rfl

theorem step_add_out {prog : Program} {target pcBase slotBase : BitVec 64}
    {isVarA : Bool} {s0 s : State} {sampled : Nat} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp : ScratchPreserved isVarA s0 s)
    (hslot0 : s0.readReg64 (rSlotBase isVarA) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled isVarA) = BitVec.ofNat 64 sampled)
    (hf : prog.fetch (pcAt pcBase 19) =
      some (.addSubShift .W64 .ADD (rOut isVarA) (rSlotBase isVarA) (rSampled isVarA) .LSL 1))
    (hnext : SepWP prog target
      ((s.writeReg64 (rOut isVarA) (slotBase + (BitVec.ofNat 64 sampled <<< 1))).setPC
        (pcAt pcBase 20)) P post oom) :
    SepWP prog target (s.setPC (pcAt pcBase 19)) P post oom := by
  have hslot : s.readReg64 (rSlotBase isVarA) = slotBase := hsp.readSlotBase.trans hslot0
  have hsamp : s.readReg64 (rSampled isVarA) = BitVec.ofNat 64 sampled :=
    hsp.readSampled.trans hsamp0
  refine SepWP.step_pure_setPC
    (s' := (s.writeReg64 (rOut isVarA) (slotBase + (BitVec.ofNat 64 sampled <<< 1))).setPC
      (pcAt pcBase 20)) hsp.1 hf ?_ rfl hnext
  simp [Program.evalInst, execInstWithSvc, execAddSubShift, State.readReg, shiftVal, shift64,
    hslot, hsamp, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ (pcBase := pcBase) (idx := 19)]

theorem step_triple0_preamble {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {s0 s : State} {buf : List (BitVec 8)}
    {nChunks chunkIdx sampled : Nat} {Pbuf Prest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp0 : ScratchPreserved isVarA s0 s)
    (hslot0 : s0.readReg64 (rSlotBase isVarA) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled isVarA) = BitVec.ofNat 64 sampled)
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hf0 : prog.fetch (pcAt pcBase 17) = some (rejLoadByte isVarA (rCnt isVarA) 0))
    (hf1 : prog.fetch (pcAt pcBase 18) = some (rejLoadByte isVarA (rB1 isVarA) 1))
    (hf2 : prog.fetch (pcAt pcBase 19) =
      some (.addSubShift .W64 .ADD (rOut isVarA) (rSlotBase isVarA) (rSampled isVarA) .LSL 1))
    (hf3 : prog.fetch (pcAt pcBase 20) =
      some (.bitfield .W32 .BFM (rCnt isVarA) (rB1 isVarA) 24 3))
    (hnext : ∀ stM : State,
      ScratchPreserved isVarA s0 stM →
      stM.readReg64 (rOut isVarA) = slotBase + (BitVec.ofNat 64 sampled <<< 1) →
      stM.readReg64 (rCnt isVarA) =
        (rej12D1W32 (((buf.drop (24 * chunkIdx)).take 24).getD 0 0#8)
          (((buf.drop (24 * chunkIdx)).take 24).getD 1 0#8)).zeroExtend 64 →
      stM.readReg64 (rB1 isVarA) =
        (((buf.drop (24 * chunkIdx)).take 24).getD 1 0#8).zeroExtend 64 →
      SepWP prog target (stM.setPC (pcAt pcBase 21)) (Pbuf ∗ Prest) post oom) :
    SepWP prog target (s.setPC (pcAt pcBase 17)) (Pbuf ∗ Prest) post oom := by
  have hmemCnt : rCnt isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemOut : rOut isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntOut : rCnt isVarA ≠ rOut isVarA := by cases isVarA <;> decide
  have hneB1Out : rB1 isVarA ≠ rOut isVarA := by cases isVarA <;> decide
  refine step_load_chunk_byte 17 0 hsp0 hbuf0 hf0 hread hchunk (by omega) ?_
  refine step_load_chunk_byte 18 1 (writeScratch64 hsp0 hmemCnt _) hbuf0 hf1 hread hchunk
    (by omega) ?_
  have hspL := writeScratch64 (writeScratch64 hsp0 hmemCnt
    ((((buf.drop (24 * chunkIdx)).take 24).getD 0 0#8).zeroExtend 64)) hmemB1
    ((((buf.drop (24 * chunkIdx)).take 24).getD 1 0#8).zeroExtend 64)
  refine step_add_out hspL hslot0 hsamp0 hf2 ?_
  have hspO := writeScratch64 hspL hmemOut (slotBase + (BitVec.ofNat 64 sampled <<< 1))
  refine step_bfi_d1 20
    (((buf.drop (24 * chunkIdx)).take 24).getD 0 0#8)
    (((buf.drop (24 * chunkIdx)).take 24).getD 1 0#8) hspO.1 hf3
    (by rw [readReg64_writeReg64_ne_of _ hneCntOut,
          readReg64_writeReg64_ne_of _ hneCntB1, read_writeScratch_self _ hmemCnt])
    (by rw [readReg64_writeReg64_ne_of _ hneB1Out, read_writeScratch_self _ hmemB1]) ?_
  exact hnext _ (writeScratch64 hspO hmemCnt _)
    (by rw [readReg64_writeReg64_ne_of _ hneCntOut.symm, read_writeScratch_self _ hmemOut])
    (read_writeScratch_self _ hmemCnt _)
    (by rw [readReg64_writeReg64_ne_of _ hneCntB1.symm,
          readReg64_writeReg64_ne_of _ hneB1Out, read_writeScratch_self _ hmemB1])

/-- Entry Triple `0` for Variants A and B (`[17..38]` → `pcAt pcBase 39`). -/
theorem step_rej_triple0_AB {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {isVarA : Bool} {nChunks chunkIdx sampled : Nat}
    {s0 : State} {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s0.status = .Running)
    (hf : FetchesInstrsAt prog pcBase 17 (rejTriple0ABInstrs isVarA))
    (hslot0 : s0.readReg64 (rSlotBase isVarA) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled isVarA) = BitVec.ofNat 64 sampled)
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256)
    (hcont : ∀ s' cnt' hws', RejTripleState isVarA s0 slotBase sampled cnt' s' →
      cnt' = (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) 0).length →
      hws' = rejWriteCandidates hws sampled (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) 0) →
      SepWP prog target (s'.setPC (pcAt pcBase 39))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom) :
    SepWP prog target (s0.setPC (pcAt pcBase 17))
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  let b0 := ((buf.drop (24 * chunkIdx)).take 24).getD 0 0#8
  let b1 := ((buf.drop (24 * chunkIdx)).take 24).getD 1 0#8
  let b2 := ((buf.drop (24 * chunkIdx)).take 24).getD 2 0#8
  have hmemS0 : rS0 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemB1 : rB1 isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hmemCnt : rCnt isVarA ∈ rejScratchRegs isVarA := by simp [rejScratchRegs]
  have hneB1S0 : rB1 isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneB1Cnt : rB1 isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
  have hneOutS0 : rOut isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneCntS0 : rCnt isVarA ≠ rS0 isVarA := by cases isVarA <;> decide
  have hneOutCnt : rOut isVarA ≠ rCnt isVarA := by cases isVarA <;> decide
  have hneOutB1 : rOut isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hneCntB1 : rCnt isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  have hStoreD2 : ∀ st c hw, RejTripleState isVarA s0 slotBase sampled c st →
      hw.length = 272 → c < 16 → st.readReg64 (rB1 isVarA) = (rej12D2W32 b1 b2).zeroExtend 64 →
      (∀ s' : State, RejTripleState isVarA s0 slotBase sampled (c + 1) s' →
        SepWP prog target (s'.setPC (pcAt pcBase 39))
          (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hw.set (sampled + c) (BitVec.ofNat 16 (rej12D2 b1 b2)))) ∗ F))
          post oom) →
      SepWP prog target (st.setPC (pcAt pcBase 37))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hw) ∗ F)) post oom := by
    intro st c hw hst hwl hc hb1v hk
    refine step_strh_regOff_inc 37 (rej12D2 b1 b2) hst.1.1 (hf.get 20) (hf.get 21)
      hwl hs hc hst.2.1 hst.2.2 (trunc16_d2_reg hb1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    exact hk s1 ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
                 (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
  refine step_triple0_preamble (ScratchPreserved.refl hrun) hslot0 hsamp0 hbuf0 hread hchunk
    (hf.get 0) (hf.get 1) (hf.get 2) (hf.get 3) fun stM hspM houtM hd1v hb1v => ?_
  refine step_cmp32_bCond 21 31 (rej12D1W32 b0 b1) hspM.1 (hf.get 4) (hf.get 5) hd1v ?_
  change SepWP prog target ((_ : State).setPC (if ConditionHolds .CS (subsPState32 (rej12D1W32 b0 b1) 3329#32) then _ else _)) _ post oom
  rw [condHolds_cmp32_3329_cs_d1]
  by_cases hd1 : rej12D1 b0 b1 < mlkemQ
  · simp only [hd1, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine step_strh_zero_movz1 (isVarA := isVarA) 23 (rej12D1 b0 b1) hspM.1
      (hf.get 6) (hf.get 7) hlen hs houtM
      (trunc16_d1_reg hd1v) fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    let hws1 := hws.set sampled (BitVec.ofNat 16 (rej12D1 b0 b1))
    have hst1_pre : RejTripleState isVarA s0 slotBase sampled 1 s1 :=
      ⟨of_single_scratch (hspM.setPState _) hmemCnt hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutCnt).trans houtM, hcnt1⟩
    refine step_load_chunk_byte 25 2 hst1_pre.1 hbuf0 (hf.get 8) hread hchunk (by omega) ?_
    have hst1_ld : RejTripleState isVarA s0 slotBase sampled 1
        (s1.writeReg64 (rS0 isVarA) (b2.zeroExtend 64)) :=
      ⟨writeScratch64 hst1_pre.1 hmemS0 _,
       (readReg64_writeReg64_ne_of _ hneOutS0).trans hst1_pre.2.1,
       (readReg64_writeReg64_ne_of _ hneCntS0).trans hst1_pre.2.2⟩
    refine step_lsr_orr_d2 26 b1 b2 hrun1 (hf.get 9) (hf.get 10)
      (by rw [readReg64_writeReg64_ne_of _ hneB1S0]; exact (hoth1 _ hneB1Cnt).trans hb1v)
      (read_writeScratch_self _ hmemS0 _)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst1 : RejTripleState isVarA s0 slotBase sampled 1 s2 :=
      ⟨of_single_scratch hst1_ld.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hst1_ld.2.1, (hoth2 _ hneCntB1).trans hst1_ld.2.2⟩
    refine step_cmp32_bCond 28 37 (rej12D2W32 b1 b2) hst1.1.1 (hf.get 11) (hf.get 12) hb1_2 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .CC (subsPState32 (rej12D2W32 b1 b2) 3329#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3329_cc_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, decide_true, ↓reduceIte]
      refine hStoreD2 _ 1 hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩
        (by simp [hws1, hlen]) (by omega) hb1_2 fun s' hs' => ?_
      have hc11 := tripleAt_11 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc11
      exact hcont s' 2 _ hs' hc11.1 hc11.2
    · simp only [hd2, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine step_b_uncond 30 39 hst1.1.1 (hf.get 13) ?_
      have hc10 := tripleAt_10 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc10
      exact hcont _ 1 hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩ hc10.1 hc10.2
  · simp only [hd1, not_false_eq_true, decide_true, ↓reduceIte]
    refine step_mov_xzr_cnt (isVarA := isVarA) 31 hspM.1 (hf.get 14) ?_
    let sZ := (stM.setPState (subsPState32 (rej12D1W32 b0 b1) 3329#32)).writeReg64
      (rCnt isVarA) (BitVec.ofNat 64 0)
    have hstZ : RejTripleState isVarA s0 slotBase sampled 0 sZ :=
      ⟨writeScratch64 (hspM.setPState _) hmemCnt _,
       (readReg64_writeReg64_ne_of _ hneOutCnt).trans houtM,
       read_writeScratch_self _ hmemCnt _⟩
    refine step_load_chunk_byte 32 2 hstZ.1 hbuf0 (hf.get 15) hread hchunk (by omega) ?_
    have hstZ_ld : RejTripleState isVarA s0 slotBase sampled 0
        (sZ.writeReg64 (rS0 isVarA) (b2.zeroExtend 64)) :=
      ⟨writeScratch64 hstZ.1 hmemS0 _,
       (readReg64_writeReg64_ne_of _ hneOutS0).trans hstZ.2.1,
       (readReg64_writeReg64_ne_of _ hneCntS0).trans hstZ.2.2⟩
    refine step_lsr_orr_d2 33 b1 b2 hstZ.1.1 (hf.get 16) (hf.get 17)
      (by rw [readReg64_writeReg64_ne_of _ hneB1S0,
            readReg64_writeReg64_ne_of _ hneB1Cnt]; exact hb1v)
      (read_writeScratch_self _ hmemS0 _)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst0 : RejTripleState isVarA s0 slotBase sampled 0 s2 :=
      ⟨of_single_scratch hstZ_ld.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hstZ_ld.2.1, (hoth2 _ hneCntB1).trans hstZ_ld.2.2⟩
    refine step_cmp32_bCond 35 39 (rej12D2W32 b1 b2) hst0.1.1 (hf.get 18) (hf.get 19) hb1_2 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .CS (subsPState32 (rej12D2W32 b1 b2) 3329#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3329_cs_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine hStoreD2 _ 0 hws ⟨hst0.1.setPState _, hst0.2.1, hst0.2.2⟩ hlen (by omega)
        hb1_2 fun s' hs' => ?_
      have hc01 := tripleAt_01 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc01
      exact hcont s' 1 _ hs' hc01.1 hc01.2
    · simp only [hd2, not_false_eq_true, decide_true, ↓reduceIte]
      have hc00 := tripleAt_00 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc00
      exact hcont _ 0 hws ⟨hst0.1.setPState _, hst0.2.1, hst0.2.2⟩ hc00.1 hc00.2

/-- Entry Triple `0` for Variant C (`[17..31]` + `[103..109]` → `pcAt pcBase 32`). -/
theorem step_rej_triple0_C {prog : Program} {target pcBase sqBase slotBase : BitVec 64}
    {nChunks chunkIdx sampled : Nat}
    {s0 : State} {buf : List (BitVec 8)} {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s0.status = .Running)
    (hfFast : FetchesInstrsAt prog pcBase 17 rejTriple0CFastInstrs)
    (hfSlow : FetchesInstrsAt prog pcBase 103 rejTriple0CSlowInstrs)
    (hslot0 : s0.readReg64 (rSlotBase false) = slotBase)
    (hsamp0 : s0.readReg64 (rSampled false) = BitVec.ofNat 64 sampled)
    (hbuf0 : s0.readReg64 (rBuf false) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks)
    (hlen : hws.length = 272) (hs : sampled < 256)
    (hcont : ∀ s' cnt' hws', RejTripleState false s0 slotBase sampled cnt' s' →
      cnt' = (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) 0).length →
      hws' = rejWriteCandidates hws sampled (parseRej12TripleAt ((buf.drop (24 * chunkIdx)).take 24) 0) →
      SepWP prog target (s'.setPC (pcAt pcBase 32))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws') ∗ F)) post oom) :
    SepWP prog target (s0.setPC (pcAt pcBase 17))
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  let b0 := ((buf.drop (24 * chunkIdx)).take 24).getD 0 0#8
  let b1 := ((buf.drop (24 * chunkIdx)).take 24).getD 1 0#8
  let b2 := ((buf.drop (24 * chunkIdx)).take 24).getD 2 0#8
  have hmemS0 : rS0 false ∈ rejScratchRegs false := by simp [rejScratchRegs]
  have hmemB1 : rB1 false ∈ rejScratchRegs false := by simp [rejScratchRegs]
  have hmemCnt : rCnt false ∈ rejScratchRegs false := by simp [rejScratchRegs]
  have hneB1S0 : rB1 false ≠ rS0 false := by decide
  have hneB1Cnt : rB1 false ≠ rCnt false := by decide
  have hneOutS0 : rOut false ≠ rS0 false := by decide
  have hneCntS0 : rCnt false ≠ rS0 false := by decide
  have hneOutCnt : rOut false ≠ rCnt false := by decide
  have hneOutB1 : rOut false ≠ rB1 false := by decide
  have hneCntB1 : rCnt false ≠ rB1 false := by decide
  have hStoreD2 : ∀ st c hw, RejTripleState false s0 slotBase sampled c st →
      hw.length = 272 → c < 16 → st.readReg64 (rB1 false) = (rej12D2W32 b1 b2).zeroExtend 64 →
      (∀ s' : State, RejTripleState false s0 slotBase sampled (c + 1) s' →
        SepWP prog target (s'.setPC (pcAt pcBase 32))
          (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hw.set (sampled + c) (BitVec.ofNat 16 (rej12D2 b1 b2)))) ∗ F))
          post oom) →
      SepWP prog target (st.setPC (pcAt pcBase 30))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hw) ∗ F)) post oom := by
    intro st c hw hst hwl hc hb1v hk
    refine step_strh_regOff_inc 30 (rej12D2 b1 b2) hst.1.1 (hfFast.get 13) (hfFast.get 14)
      hwl hs hc hst.2.1 hst.2.2 (trunc16_d2_reg hb1v)
      fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    exact hk s1 ⟨of_single_scratch hst.1 hmemCnt hrun1 hsp1 hv1 hoth1,
                 (hoth1 _ hneOutCnt).trans hst.2.1, hcnt1⟩
  refine step_triple0_preamble (ScratchPreserved.refl hrun) hslot0 hsamp0 hbuf0 hread hchunk
    (hfFast.get 0) (hfFast.get 1) (hfFast.get 2) (hfFast.get 3) fun stM hspM houtM hd1v hb1v => ?_
  refine step_cmp32_bCond 21 103 (rej12D1W32 b0 b1) hspM.1 (hfFast.get 4) (hfFast.get 5) hd1v ?_
  change SepWP prog target ((_ : State).setPC (if ConditionHolds .CS (subsPState32 (rej12D1W32 b0 b1) 3329#32) then _ else _)) _ post oom
  rw [condHolds_cmp32_3329_cs_d1]
  by_cases hd1 : rej12D1 b0 b1 < mlkemQ
  · simp only [hd1, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine step_strh_zero_movz1 (isVarA := false) 23 (rej12D1 b0 b1) hspM.1
      (hfFast.get 6) (hfFast.get 7) hlen hs houtM
      (trunc16_d1_reg hd1v) fun s1 hrun1 hsp1 hv1 hoth1 hcnt1 => ?_
    let hws1 := hws.set sampled (BitVec.ofNat 16 (rej12D1 b0 b1))
    have hst1_pre : RejTripleState false s0 slotBase sampled 1 s1 :=
      ⟨of_single_scratch (hspM.setPState _) hmemCnt hrun1 hsp1 hv1 hoth1,
       (hoth1 _ hneOutCnt).trans houtM, hcnt1⟩
    refine step_load_chunk_byte 25 2 hst1_pre.1 hbuf0 (hfFast.get 8) hread hchunk (by omega) ?_
    have hst1_ld : RejTripleState false s0 slotBase sampled 1
        (s1.writeReg64 (rS0 false) (b2.zeroExtend 64)) :=
      ⟨writeScratch64 hst1_pre.1 hmemS0 _,
       (readReg64_writeReg64_ne_of _ hneOutS0).trans hst1_pre.2.1,
       (readReg64_writeReg64_ne_of _ hneCntS0).trans hst1_pre.2.2⟩
    refine step_lsr_orr_d2 26 b1 b2 hrun1 (hfFast.get 9) (hfFast.get 10)
      (by rw [readReg64_writeReg64_ne_of _ hneB1S0]; exact (hoth1 _ hneB1Cnt).trans hb1v)
      (read_writeScratch_self _ hmemS0 _)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst1 : RejTripleState false s0 slotBase sampled 1 s2 :=
      ⟨of_single_scratch hst1_ld.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hst1_ld.2.1, (hoth2 _ hneCntB1).trans hst1_ld.2.2⟩
    refine step_cmp32_bCond 28 32 (rej12D2W32 b1 b2) hst1.1.1 (hfFast.get 11) (hfFast.get 12) hb1_2 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .CS (subsPState32 (rej12D2W32 b1 b2) 3329#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3329_cs_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine hStoreD2 _ 1 hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩
        (by simp [hws1, hlen]) (by omega) hb1_2 fun s' hs' => ?_
      have hc11 := tripleAt_11 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc11
      exact hcont s' 2 _ hs' hc11.1 hc11.2
    · simp only [hd2, not_false_eq_true, decide_true, ↓reduceIte]
      have hc10 := tripleAt_10 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc10
      exact hcont _ 1 hws1 ⟨hst1.1.setPState _, hst1.2.1, hst1.2.2⟩ hc10.1 hc10.2
  · simp only [hd1, not_false_eq_true, decide_true, ↓reduceIte]
    refine step_mov_xzr_cnt (isVarA := false) 103 hspM.1 (hfSlow.get 0) ?_
    let sZ := (stM.setPState (subsPState32 (rej12D1W32 b0 b1) 3329#32)).writeReg64
      (rCnt false) (BitVec.ofNat 64 0)
    have hstZ : RejTripleState false s0 slotBase sampled 0 sZ :=
      ⟨writeScratch64 (hspM.setPState _) hmemCnt _,
       (readReg64_writeReg64_ne_of _ hneOutCnt).trans houtM,
       read_writeScratch_self _ hmemCnt _⟩
    refine step_load_chunk_byte 104 2 hstZ.1 hbuf0 (hfSlow.get 1) hread hchunk (by omega) ?_
    have hstZ_ld : RejTripleState false s0 slotBase sampled 0
        (sZ.writeReg64 (rS0 false) (b2.zeroExtend 64)) :=
      ⟨writeScratch64 hstZ.1 hmemS0 _,
       (readReg64_writeReg64_ne_of _ hneOutS0).trans hstZ.2.1,
       (readReg64_writeReg64_ne_of _ hneCntS0).trans hstZ.2.2⟩
    refine step_lsr_orr_d2 105 b1 b2 hstZ.1.1 (hfSlow.get 2) (hfSlow.get 3)
      (by rw [readReg64_writeReg64_ne_of _ hneB1S0,
            readReg64_writeReg64_ne_of _ hneB1Cnt]; exact hb1v)
      (read_writeScratch_self _ hmemS0 _)
      fun s2 hrun2 hsp2 hv2 hoth2 hb1_2 => ?_
    have hst0 : RejTripleState false s0 slotBase sampled 0 s2 :=
      ⟨of_single_scratch hstZ_ld.1 hmemB1 hrun2 hsp2 hv2 hoth2,
       (hoth2 _ hneOutB1).trans hstZ_ld.2.1, (hoth2 _ hneCntB1).trans hstZ_ld.2.2⟩
    refine step_cmp32_bCond 107 30 (rej12D2W32 b1 b2) hst0.1.1 (hfSlow.get 4) (hfSlow.get 5) hb1_2 ?_
    change SepWP prog target ((_ : State).setPC (if ConditionHolds .CC (subsPState32 (rej12D2W32 b1 b2) 3329#32) then _ else _)) _ post oom
    rw [condHolds_cmp32_3329_cc_d2]
    by_cases hd2 : rej12D2 b1 b2 < mlkemQ
    · simp only [hd2, decide_true, ↓reduceIte]
      refine hStoreD2 _ 0 hws ⟨hst0.1.setPState _, hst0.2.1, hst0.2.2⟩ hlen (by omega)
        hb1_2 fun s' hs' => ?_
      have hc01 := tripleAt_01 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc01
      exact hcont s' 1 _ hs' hc01.1 hc01.2
    · simp only [hd2, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine step_b_uncond 109 32 hst0.1.1 (hfSlow.get 6) ?_
      have hc00 := tripleAt_00 (t := 0) hws sampled 0 hd1 hd2
      simp only [Nat.add_zero, Nat.zero_add] at hc00
      exact hcont _ 0 hws ⟨hst0.1.setPState _, hst0.2.1, hst0.2.2⟩ hc00.1 hc00.2

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriple0
