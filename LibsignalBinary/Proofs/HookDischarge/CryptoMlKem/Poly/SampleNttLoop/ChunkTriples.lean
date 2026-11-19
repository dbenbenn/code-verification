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

/-!
# Micro-Step `SepWP` Lemmas for `rej_sample` (`SampleNttLoop.ChunkTriples`)

Instruction-sequence `SepWP` lemmas on `s.setPC (pcAt pcBase idx)` (byte loads, 12-bit
`bfi`/`lsr`+`orr` extraction, 32-bit `cmp`+`b.cond`, indexed/zero-offset halfword `strh`,
and `mov` immediate/zero) for `rej_sample` across `B03`–`B07`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE
  rej12D1
  rej12D1W32
  rej12D1W32_truncate16
  rej12D2
  rej12D2W32
  rej12D2W32_truncate16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (
  RejBufReadable
  addr_rejSlot_regOff
  addr_rejSlot_zero
  evalBitfield_bfi_d1
  evalBitfield_lsr4_orr_d2
  sepLoad8_rejChunk_byte
  sepStore16_rejSlot
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  ScratchPreserved
  brDisp
  pcAt
  pcAt_brDisp
  pcAt_succ
  rB1
  rBuf
  rCnt
  rOut
  rS0
  readReg64_writeReg64_ne_of
  rejByteAddr
  rejLoadByte
  rejScratchRegs
  rejStoreRegOff
)

/-! ## 1. State Normalization Helpers -/

private theorem setPC_setPC (s : State) (a b : BitVec 64) :
    (s.setPC a).setPC b = s.setPC b := by cases s; rfl

private theorem setPC_writeReg64_setPC (s : State) (a b : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).setPC b = (s.writeReg64 r v).setPC b := by
  cases s; cases r <;> rfl

private theorem advancePC_writeReg64_setPC (s : State) (a : BitVec 64) (r : Reg) (v : BitVec 64) :
    ((s.setPC a).writeReg64 r v).advancePC = (s.writeReg64 r v).setPC (a + 4#64) := by
  cases s; cases r <;> rfl

private theorem advancePC_setPState_setPC (s : State) (a : BitVec 64) (ps : PState) :
    ((s.setPC a).setPState ps).advancePC = (s.setPState ps).setPC (a + 4#64) := by
  cases s; rfl

theorem writeScratch64 {isVarA : Bool} {s0 s : State}
    (h : ScratchPreserved isVarA s0 s) {rt : Reg}
    (hrt : rt ∈ rejScratchRegs isVarA) (val : BitVec 64) :
    ScratchPreserved isVarA s0 (s.writeReg64 rt val) :=
  h.writeScratch (w := .W64) hrt val

theorem of_single_scratch {isVarA : Bool} {s0 s s1 : State} {rt : Reg}
    (h : ScratchPreserved isVarA s0 s) (hrt : rt ∈ rejScratchRegs isVarA)
    (hrun : s1.status = .Running) (hsp : s1.sp = s.sp) (hv : s1.vregs = s.vregs)
    (hother : ∀ r : Reg, r ≠ rt → s1.readReg64 r = s.readReg64 r) :
    ScratchPreserved isVarA s0 s1 :=
  ⟨hrun, hsp.trans h.2.1, hv.trans h.2.2.1,
   fun r hr => (hother r fun heq => hr (heq ▸ hrt)).trans (h.2.2.2 r hr)⟩

theorem trunc16_d1_reg {s : State} {rt : Reg} {b0 b1 : BitVec 8}
    (h : s.readReg64 rt = (rej12D1W32 b0 b1).zeroExtend 64) :
    (s.readReg32 rt).truncate 16 = BitVec.ofNat 16 (rej12D1 b0 b1) := by
  rw [State.readReg32.eq_1, h,
    show ((rej12D1W32 b0 b1).zeroExtend 64).truncate 32 = rej12D1W32 b0 b1 by bv_bits]
  exact rej12D1W32_truncate16 b0 b1

theorem trunc16_d2_reg {s : State} {rt : Reg} {b1 b2 : BitVec 8}
    (h : s.readReg64 rt = (rej12D2W32 b1 b2).zeroExtend 64) :
    (s.readReg32 rt).truncate 16 = BitVec.ofNat 16 (rej12D2 b1 b2) := by
  rw [State.readReg32.eq_1, h,
    show ((rej12D2W32 b1 b2).zeroExtend 64).truncate 32 = rej12D2W32 b1 b2 by bv_bits]
  exact rej12D2W32_truncate16 b1 b2

/-! ## 2. Core Instruction-Sequence `SepWP` Lemmas -/

theorem step_load_chunk_byte {prog : Program} {target pcBase sqBase : BitVec 64}
    {isVarA : Bool} {s0 s : State} {buf : List (BitVec 8)} {nChunks chunkIdx : Nat}
    (idx j : Nat) {rt : Reg} {Pbuf Prest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp : ScratchPreserved isVarA s0 s)
    (hbuf0 : s0.readReg64 (rBuf isVarA) = sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11))
    (hfetch : prog.fetch (pcAt pcBase idx) = some (rejLoadByte isVarA rt j))
    (hread : RejBufReadable sqBase buf nChunks Pbuf) (hchunk : chunkIdx < nChunks) (hj : j < 24)
    (hnext : SepWP prog target
      ((s.writeReg64 rt ((((buf.drop (24 * chunkIdx)).take 24).getD j 0#8).zeroExtend 64)).setPC
        (pcAt pcBase (idx + 1))) (Pbuf ∗ Prest) post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) (Pbuf ∗ Prest) post oom := by
  have hrb : (s.setPC (pcAt pcBase idx)).readReg64 (rBuf isVarA) =
      sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11) := hsp.readBuf.trans hbuf0
  let disp : BitVec 64 :=
    if j < 11 then BitVec.ofNat 64 j - 11#64 else BitVec.ofNat 64 (j - 11)
  have hspA : checkAddrSPAligned (s.setPC (pcAt pcBase idx)) (rejByteAddr (rBuf isVarA) j) = true := by
    unfold rejByteAddr; split <;> cases isVarA <;> rfl
  have haddr : evalAddrMode (s.setPC (pcAt pcBase idx)) (rejByteAddr (rBuf isVarA) j) =
      ((sqBase + BitVec.ofNat 64 (24 * chunkIdx + 11)) + disp, none) := by
    unfold rejByteAddr disp; by_cases h11 : j < 11 <;> simp [h11, evalAddrMode, hrb]
  have hdisp : 11#64 + disp = BitVec.ofNat 64 j := by
    unfold disp; by_cases h11 : j < 11
    · simp only [h11, ↓reduceIte]; bv_omega
    · simp only [h11, ↓reduceIte]; bv_omega
  refine SepWP.step_ldr8
    (s' := (s.writeReg64 rt ((((buf.drop (24 * chunkIdx)).take 24).getD j 0#8).zeroExtend 64)).setPC
      (pcAt pcBase (idx + 1)))
    rfl hsp.1 hfetch hspA haddr
    (sepLoad8_rejChunk_byte hread hchunk hj hdisp rfl) ?_ hnext
  simp [applyWriteback, State.writeReg, setPC_writeReg64_setPC, pcAt_succ]

theorem step_bfi_d1 {prog : Program} {target pcBase : BitVec 64}
    {s : State} (idx : Nat) (b0 b1 : BitVec 8) {rd rn : Reg}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hfetch : prog.fetch (pcAt pcBase idx) = some (.bitfield .W32 .BFM rd rn 24 3))
    (hd : s.readReg64 rd = b0.zeroExtend 64) (hn : s.readReg64 rn = b1.zeroExtend 64)
    (hnext : SepWP prog target
      ((s.writeReg64 rd ((rej12D1W32 b0 b1).zeroExtend 64)).setPC (pcAt pcBase (idx + 1)))
      P post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) P post oom := by
  refine SepWP.step_pure_setPC
    (s' := (s.writeReg64 rd ((rej12D1W32 b0 b1).zeroExtend 64)).setPC (pcAt pcBase (idx + 1)))
    hrun hfetch ?_ rfl hnext
  simp [Program.evalInst, execInstWithSvc, execBitfield, State.readReg, State.readReg32.eq_1,
    hd, hn, evalBitfield_bfi_d1, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ]

theorem step_lsr_orr_d2 {prog : Program} {target pcBase : BitVec 64}
    {isVarA : Bool} {s : State} (idx : Nat) (b1 b2 : BitVec 8)
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hf0 : prog.fetch (pcAt pcBase idx) =
      some (.bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31))
    (hf1 : prog.fetch (pcAt pcBase (idx + 1)) =
      some (.logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4))
    (hb1 : s.readReg64 (rB1 isVarA) = b1.zeroExtend 64)
    (hb2 : s.readReg64 (rS0 isVarA) = b2.zeroExtend 64)
    (hnext : ∀ s1 : State,
      s1.status = .Running →
      s1.sp = s.sp →
      s1.vregs = s.vregs →
      (∀ r : Reg, r ≠ rB1 isVarA → s1.readReg64 r = s.readReg64 r) →
      s1.readReg64 (rB1 isVarA) = (rej12D2W32 b1 b2).zeroExtend 64 →
      SepWP prog target (s1.setPC (pcAt pcBase (idx + 2))) P post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) P post oom := by
  let lsrVal := evalBitfield .W32 .UBFM (b1.zeroExtend 64) (b1.zeroExtend 64) 4 31
  have hlsr_tr : (lsrVal.truncate 32).zeroExtend 64 = lsrVal := by
    have : lsrVal = ((((b1.zeroExtend 64).truncate 32).zeroExtend 64 >>> 4).truncate 32).zeroExtend 64 := rfl
    rw [this]; bv_bits
  have hlsr_sw : BitVec.setWidth 64 (BitVec.setWidth 32 lsrVal) = lsrVal := hlsr_tr
  have hne : rS0 isVarA ≠ rB1 isVarA := by cases isVarA <;> decide
  let sA := s.writeReg64 (rB1 isVarA) lsrVal
  have hb1_rd : sA.readReg64 (rB1 isVarA) = lsrVal := by cases isVarA <;> simp [sA, rB1]
  refine SepWP.step_pure_setPC (s' := sA.setPC (pcAt pcBase (idx + 1))) hrun hf0 ?_ rfl ?_
  · simp [Program.evalInst, execInstWithSvc, execBitfield, State.readReg, State.readReg32.eq_1,
      hb1, lsrVal, hlsr_sw, sA, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ]
  · let sB := sA.writeReg64 (rB1 isVarA) ((rej12D2W32 b1 b2).zeroExtend 64)
    refine SepWP.step_pure_setPC (s' := sB.setPC (pcAt pcBase (idx + 2)))
      (by simp [sA, hrun]) hf1 ?_ rfl (hnext sB ?_ ?_ ?_ ?_ ?_)
    · have horr := evalBitfield_lsr4_orr_d2 b1 b2 s.pstate
      have hps : (evalLogical .W32 .ORR lsrVal (shiftVal .W32 (b2.zeroExtend 64) .LSL 4) s.pstate).2 =
          none := rfl
      have hpair : evalLogical .W32 .ORR lsrVal (shiftVal .W32 (b2.zeroExtend 64) .LSL 4) s.pstate =
          ((rej12D2W32 b1 b2).zeroExtend 64, none) := Prod.ext horr hps
      have hpst : sA.pstate = s.pstate := by cases s; cases isVarA <;> rfl
      have hs0_rd : sA.readReg64 (rS0 isVarA) = b2.zeroExtend 64 :=
        (readReg64_writeReg64_ne_of s hne).trans hb2
      simp [Program.evalInst, execInstWithSvc, execLogicalShift, State.readReg, State.readReg32.eq_1,
        hb1_rd, hs0_rd, hlsr_sw, hpst, hpair, sB, State.writeReg,
        advancePC_writeReg64_setPC, pcAt_succ (pcBase := pcBase) (idx := idx + 1)]
    · simp [sB, sA, hrun]
    · cases s; cases isVarA <;> rfl
    · cases s; cases isVarA <;> rfl
    · intro r hr; simp [sB, sA, readReg64_writeReg64_ne_of _ hr]
    · cases isVarA <;> simp [sB, rB1]

theorem step_cmp32_bCond {prog : Program} {target pcBase : BitVec 64}
    {s : State} (idx dstIdx : Nat) (v32 : BitVec 32) {rn : Reg} {imm12 : BitVec 12}
    {cond : CondCode} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hf0 : prog.fetch (pcAt pcBase idx) = some (.addSubImm .W32 .SUBS .xzr rn imm12 false))
    (hf1 : prog.fetch (pcAt pcBase (idx + 1)) = some (.bCond cond (brDisp (idx + 1) dstIdx)))
    (hrn : s.readReg64 rn = v32.zeroExtend 64)
    (hnext : SepWP prog target
      ((s.setPState (subsPState32 v32 (imm12.zeroExtend 32))).setPC
        (if ConditionHolds cond (subsPState32 v32 (imm12.zeroExtend 32)) then
          pcAt pcBase dstIdx
        else pcAt pcBase (idx + 2))) P post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) P post oom := by
  let ps' := subsPState32 v32 (imm12.zeroExtend 32)
  refine SepWP.step_pure_setPC (s' := (s.setPState ps').setPC (pcAt pcBase (idx + 1)))
    hrun hf0 ?_ rfl ?_
  · simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.readReg32.eq_1,
      hrn, ps', State.writeReg, advancePC_setPState_setPC, pcAt_succ]
  · refine SepWP.step_pure_setPC
      (s' := (s.setPState ps').setPC
        (if ConditionHolds cond ps' then pcAt pcBase dstIdx else pcAt pcBase (idx + 2)))
      hrun hf1 ?_ rfl hnext
    by_cases hc : ConditionHolds cond ps' <;>
      simp [Program.evalInst, execInstWithSvc, hc, ps', pcAt_brDisp, State.advancePC_setPC,
        setPC_setPC, pcAt_succ (pcBase := pcBase) (idx := idx + 1)]

theorem step_strh_regOff_inc {prog : Program} {target pcBase slotBase : BitVec 64}
    {isVarA : Bool} {s : State} (idx cand : Nat) {sampled cnt : Nat} {rt : Reg}
    {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hf0 : prog.fetch (pcAt pcBase idx) = some (rejStoreRegOff isVarA rt))
    (hf1 : prog.fetch (pcAt pcBase (idx + 1)) =
      some (.addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false))
    (hlen : hws.length = 272) (hs : sampled < 256) (hc : cnt < 16)
    (hout : s.readReg64 (rOut isVarA) = slotBase + (BitVec.ofNat 64 sampled <<< 1))
    (hcnt : s.readReg64 (rCnt isVarA) = BitVec.ofNat 64 cnt)
    (hval : (s.readReg32 rt).truncate 16 = BitVec.ofNat 16 cand)
    (hnext : ∀ s1 : State,
      s1.status = .Running →
      s1.sp = s.sp →
      s1.vregs = s.vregs →
      (∀ r : Reg, r ≠ rCnt isVarA → s1.readReg64 r = s.readReg64 r) →
      s1.readReg64 (rCnt isVarA) = BitVec.ofNat 64 (cnt + 1) →
      SepWP prog target (s1.setPC (pcAt pcBase (idx + 2)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hws.set (sampled + cnt) (BitVec.ofNat 16 cand))) ∗ F))
        post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx))
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  have hspA : checkAddrSPAligned (s.setPC (pcAt pcBase idx))
      (.RegOffset (rOut isVarA) (rCnt isVarA) .UXTX 1) = true := by cases isVarA <;> rfl
  have haddr : evalAddrMode (s.setPC (pcAt pcBase idx))
      (.RegOffset (rOut isVarA) (rCnt isVarA) .UXTX 1) =
      ((slotBase + (BitVec.ofNat 64 sampled <<< 1)) + (BitVec.ofNat 64 cnt <<< 1), none) := by
    simp [evalAddrMode, extendVal, hout, hcnt]
  have hst : SepStore16 ((slotBase + (BitVec.ofNat 64 sampled <<< 1)) + (BitVec.ofNat 64 cnt <<< 1))
      (BitVec.ofNat 16 cand)
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F))
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hws.set (sampled + cnt) (BitVec.ofNat 16 cand))) ∗ F)) :=
    SepStore16.right (sepStore16_rejSlot hlen hs hc (addr_rejSlot_regOff slotBase sampled cnt))
  refine SepWP.step_str16 (s' := s.setPC (pcAt pcBase (idx + 1)))
    rfl hrun hf0 hspA haddr hval hst
    (by simp [applyWriteback, setPC_setPC, pcAt_succ]) fun m' => ?_
  let s1 := (s.setMem m').writeReg64 (rCnt isVarA) (BitVec.ofNat 64 (cnt + 1))
  refine SepWP.step_pure_setMem_setPC (s' := s1.setPC (pcAt pcBase (idx + 2))) hrun hf1 ?_ rfl
    (hnext s1 ?_ ?_ ?_ ?_ ?_)
  · have hadd : BitVec.ofNat 64 cnt + 1#64 = BitVec.ofNat 64 (cnt + 1) := by bv_omega
    have heq : ((s.setPC (pcAt pcBase (idx + 1))).writeReg64
        (rCnt isVarA) (BitVec.ofNat 64 (cnt + 1))).advancePC.setMem m' =
        s1.setPC (pcAt pcBase (idx + 2)) := by
      rw [advancePC_writeReg64_setPC, pcAt_succ]
      cases s; cases isVarA <;> rfl
    simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, hcnt, hadd,
      State.writeReg, heq]
  · simp [s1, hrun]
  · cases s; cases isVarA <;> rfl
  · cases s; cases isVarA <;> rfl
  · intro r hr; simp [s1, readReg64_writeReg64_ne_of _ hr]
  · cases isVarA <;> simp [s1, rCnt]

theorem step_strh_zero_movz1 {prog : Program} {target pcBase slotBase : BitVec 64}
    {isVarA : Bool} {s : State} (idx cand : Nat) {sampled : Nat}
    {hws : List (BitVec 16)} {Pbuf F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hf0 : prog.fetch (pcAt pcBase idx) =
      some (.str .H16 (rCnt isVarA) (.Offset (rOut isVarA) 0#64)))
    (hf1 : prog.fetch (pcAt pcBase (idx + 1)) =
      some (.moveWide .W32 .MOVZ (rCnt isVarA) 1#16 0))
    (hlen : hws.length = 272) (hs : sampled < 256)
    (hout : s.readReg64 (rOut isVarA) = slotBase + (BitVec.ofNat 64 sampled <<< 1))
    (hval : (s.readReg32 (rCnt isVarA)).truncate 16 = BitVec.ofNat 16 cand)
    (hnext : ∀ s1 : State,
      s1.status = .Running →
      s1.sp = s.sp →
      s1.vregs = s.vregs →
      (∀ r : Reg, r ≠ rCnt isVarA → s1.readReg64 r = s.readReg64 r) →
      s1.readReg64 (rCnt isVarA) = BitVec.ofNat 64 1 →
      SepWP prog target (s1.setPC (pcAt pcBase (idx + 2)))
        (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hws.set sampled (BitVec.ofNat 16 cand))) ∗ F))
        post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx))
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F)) post oom := by
  have hspA : checkAddrSPAligned (s.setPC (pcAt pcBase idx))
      (.Offset (rOut isVarA) 0#64) = true := by cases isVarA <;> rfl
  have haddr : evalAddrMode (s.setPC (pcAt pcBase idx)) (.Offset (rOut isVarA) 0#64) =
      ((slotBase + (BitVec.ofNat 64 sampled <<< 1)) + 0#64, none) := by
    simp [evalAddrMode, hout]
  have hst : SepStore16 ((slotBase + (BitVec.ofNat 64 sampled <<< 1)) + 0#64)
      (BitVec.ofNat 16 cand)
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE hws) ∗ F))
      (Pbuf ∗ ((slotBase ↦ₛ packHalfwordsLE (hws.set sampled (BitVec.ofNat 16 cand))) ∗ F)) := by
    simpa using SepStore16.right (sepStore16_rejSlot hlen hs (count := 0) (by omega)
      (addr_rejSlot_zero slotBase sampled))
  refine SepWP.step_str16 (s' := s.setPC (pcAt pcBase (idx + 1)))
    rfl hrun hf0 hspA haddr hval hst
    (by simp [applyWriteback, setPC_setPC, pcAt_succ]) fun m' => ?_
  let s1 := (s.setMem m').writeReg64 (rCnt isVarA) (BitVec.ofNat 64 1)
  refine SepWP.step_pure_setMem_setPC (s' := s1.setPC (pcAt pcBase (idx + 2))) hrun hf1 ?_ rfl
    (hnext s1 ?_ ?_ ?_ ?_ ?_)
  · have heq : ((s.setPC (pcAt pcBase (idx + 1))).writeReg64
        (rCnt isVarA) 1#64).advancePC.setMem m' =
        s1.setPC (pcAt pcBase (idx + 2)) := by
      rw [advancePC_writeReg64_setPC, pcAt_succ]
      cases s; cases isVarA <;> rfl
    simp [Program.evalInst, execInstWithSvc, execMoveWide, State.writeReg, heq]
  · simp [s1, hrun]
  · cases s; cases isVarA <;> rfl
  · cases s; cases isVarA <;> rfl
  · intro r hr; simp [s1, readReg64_writeReg64_ne_of _ hr]
  · cases isVarA <;> simp [s1, rCnt]

theorem step_mov_xzr_cnt {prog : Program} {target pcBase : BitVec 64}
    {isVarA : Bool} {s : State} (idx : Nat) {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hf : prog.fetch (pcAt pcBase idx) =
      some (.logicalShift .W64 .ORR (rCnt isVarA) .xzr .xzr .LSL 0))
    (hnext : SepWP prog target
      ((s.writeReg64 (rCnt isVarA) (BitVec.ofNat 64 0)).setPC (pcAt pcBase (idx + 1)))
      P post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) P post oom :=
  SepWP.step_pure_setPC
    (s' := (s.writeReg64 (rCnt isVarA) (BitVec.ofNat 64 0)).setPC (pcAt pcBase (idx + 1)))
    hrun hf
    (by simp [Program.evalInst, execInstWithSvc, execLogicalShift, State.readReg,
          shiftVal, shift64, evalLogical, State.writeReg, advancePC_writeReg64_setPC, pcAt_succ])
    rfl hnext

theorem step_b_uncond {prog : Program} {target pcBase : BitVec 64}
    {s : State} (idx dstIdx : Nat) {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running)
    (hf : prog.fetch (pcAt pcBase idx) = some (.b (brDisp idx dstIdx)))
    (hnext : SepWP prog target (s.setPC (pcAt pcBase dstIdx)) P post oom) :
    SepWP prog target (s.setPC (pcAt pcBase idx)) P post oom :=
  SepWP.step_pure_setPC (s' := s.setPC (pcAt pcBase dstIdx)) hrun hf
    (by simp [Program.evalInst, execInstWithSvc, pcAt_brDisp, setPC_setPC]) rfl hnext

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkTriples
