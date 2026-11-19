/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg
import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Sentinel-`lr` `SampleNTT` Non-Visitation for `lsEdNegSym` & `lsSharedSecretDropSym` (`ElfSampleNttStuckDivergeExtraTightSentinel`)

Discharges `StepsStrictAvoid` against `mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl)`
for the two sentinel-`lr` rows:
1. `lsEdNegSym` (`edNegSentinelGhost c2EdNegAddr`);
2. `lsSharedSecretDropSym` (`c2SharedSecretDropSentinelGhost`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightSentinel

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.SepLogic SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsEdNegSym lsSharedSecretDropSym)
open LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg
  (edwardsPointNegInstrs edwardsPointNegWords pureWordsProg_hasInstrs_edNeg)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
  (zeroize32Instrs zeroize32Words)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_lsmpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CryptoHooksDehook
  (edNegByteLen_eq f3EmptyEdNegGhostHook f3EmptyEdNegGhostHook_eq keepEdNeg keepEdNeg_iff
   narrowEdNegGhostHook narrowEdNegGhostHook_master_ok narrowEdNegGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook
  (c2EdNegAddr c2SharedSecretDropSentinelGhost c2ZeroizeSentinelGhost edNegSentinelGhost
   keepEdNeg_c2_noPanic keepZeroize32_c2_noPanic resolve_edNeg_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode (masterEdNegSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
  (linkedCallHook_activeRealPre_of_noException)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
  (masterZeroizeSpec processZeroizeSpec pureWordsProg_zeroize32_hasWords
   subroutine_ok_processZeroize_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
  (f3EmptyZeroizeGhostHook f3EmptyZeroizeGhostHook_eq f3EmptyZeroizeGhostHook_master_ok_of_process
   f3EmptyZeroizeGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (keepStaticSecretDrop keepStaticSecretDrop_iff staticSecretDrop_codeLoaded_stripExecOutside)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (isLinkedPanicAddr keepLib2Text keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
  (c2S5Addrs externAt?_s5TrapExt_eq_of_keep_all_false externAt?_s5TrapExt_eq_of_not_mem
   not_mem_s5_of_not_mem_c2S5Addrs s5TrapExt stepsStrictAvoid_of_s5Trap)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2SharedSecretDropAddr c2Zeroize32Addr)

/-! ## 1. Pure Subslice Witnesses & Non-Branch / `.lr`-Commutation Infrastructure -/

private def c2SharedDropWord : BitVec 32 :=
  Obj.branchWord 0x14000000#32 c2SharedSecretDropAddr c2Zeroize32Addr

private noncomputable def checkPureSubsliceSent (rxBytes : List (BitVec 8)) (rxLen : Nat)
    (subProg : Program) : Bool :=
  let off := (subProg.base - f3RxSegBase).toNat
  let subLen := ProofLib.Placed.Split.rLen subProg.code
  Nat.beq (subProg.base.toNat % 4) 0 &&
  Nat.ble (subProg.base.toNat + subLen) (2 ^ 64) &&
  decide (f3RxSegBase + BitVec.ofNat 64 off = subProg.base) &&
  Nat.ble (off + subLen) rxLen &&
  (subProg.code == ProofLib.Placed.Split.rTake subLen (ProofLib.Placed.Split.rDrop off rxBytes))

private theorem codeLoaded_of_pureSubsliceSent {subProg : Program} {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m)
    (h : checkPureSubsliceSent f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) subProg = true) :
    subProg.CodeLoaded m := by
  apply codeLoaded_of_checkProgCodeSubslice hRx
  unfold checkPureSubsliceSent at h
  simp only [ProofLib.Placed.Split.rLen_eq, ProofLib.Placed.Split.rTake_eq,
    ProofLib.Placed.Split.rDrop_eq] at h
  unfold checkProgCodeSubslice
  rwa [f3TrialRxProg_base, f3TrialRxWordTree_eq]

set_option maxRecDepth 2000000 in
private theorem c2SentinelSlices_ok :
    (let rxBytes := f3TrialRxWordTree.toBytes
     let rxLen := ProofLib.Placed.Split.rLen rxBytes
     checkPureSubsliceSent rxBytes rxLen (pureWordsProg c2EdNegAddr edwardsPointNegWords) &&
     checkPureSubsliceSent rxBytes rxLen (pureWordsProg c2SharedSecretDropAddr [c2SharedDropWord]) &&
     checkPureSubsliceSent rxBytes rxLen (pureWordsProg c2Zeroize32Addr zeroize32Words)) = true := by
  rfl_kernel

private theorem c2EdNegSlice_ok :
    checkPureSubsliceSent f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2EdNegAddr edwardsPointNegWords) = true := by
  have h := c2SentinelSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.1

private theorem c2SharedDropSlice_ok :
    checkPureSubsliceSent f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2SharedSecretDropAddr [c2SharedDropWord]) = true := by
  have h := c2SentinelSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.2

private theorem c2Zeroize32Slice_ok :
    checkPureSubsliceSent f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2Zeroize32Addr zeroize32Words) = true := by
  have h := c2SentinelSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.2

private def NonBranchNoLr (inst : Instr) : Bool :=
  match inst with
  | .ldp _ _ rt1 rt2 (.Offset rn _) => (rt1 != .lr) && (rt2 != .lr) && (rn != .lr)
  | .stp _ rt1 rt2 (.Offset rn _) => (rt1 != .lr) && (rt2 != .lr) && (rn != .lr)
  | .ldr _ _ _ rt (.Offset rn _) => (rt != .lr) && (rn != .lr)
  | .str _ rt (.Offset rn _) => (rt != .lr) && (rn != .lr)
  | .str _ rt (.PreIndex rn _) => (rt != .lr) && (rn != .lr)
  | .ldrSimd _ _ (.UnscaledOffset rn _) => (rn != .lr)
  | .strSimd _ _ (.UnscaledOffset rn _) => (rn != .lr)
  | .ldpSimd _ _ _ (.Offset rn _) => (rn != .lr)
  | .stpSimd _ _ _ (.Offset rn _) => (rn != .lr)
  | .moveWide _ _ rd _ _ => (rd != .lr)
  | .logicalImm _ _ rd rn _ => (rd != .lr) && (rn != .lr)
  | .logicalShift _ _ rd rn rm _ _ => (rd != .lr) && (rn != .lr) && (rm != .lr)
  | .addSubShift _ _ rd rn rm _ _ => (rd != .lr) && (rn != .lr) && (rm != .lr)
  | .bitfield _ _ rd rn _ _ => (rd != .lr) && (rn != .lr)
  | .dataProc3 _ _ rd rn rm ra => (rd != .lr) && (rn != .lr) && (rm != .lr) && (ra != .lr)
  | _ => false

private theorem reg_bne_iff_ne {r1 r2 : Reg} : (r1 != r2) = true ↔ r1 ≠ r2 := by
  cases r1 <;> cases r2 <;> simp [bne, BEq.beq, instBEqReg.beq]

private theorem edNegBody56_noLr :
    ((edwardsPointNegInstrs.take 56).all NonBranchNoLr) = true := by decide

private theorem zeroizeBody62_noLr :
    ((zeroize32Instrs.take 62).all NonBranchNoLr) = true := by decide

private theorem writeReg_comm_lr (a : State) (w : Width) {rd : Reg} (hrd : rd ≠ .lr)
    (v L : BitVec 64) :
    (a.writeReg64 .lr L).writeReg w rd v = (a.writeReg w rd v).writeReg64 .lr L := by
  cases w <;>
    simp only [State.writeReg_w32, State.writeReg_w64,
      State.writeReg64_comm_or_same a .lr rd, Ne.symm hrd, ↓reduceIte]

private theorem readReg64_lr_writeReg (a : State) (w : Width) {rd : Reg} (hrd : rd ≠ .lr)
    (v : BitVec 64) :
    (a.writeReg w rd v).readReg64 .lr = a.readReg64 .lr := by
  cases w <;>
    simp only [State.writeReg_w32, State.writeReg_w64] <;>
    exact State.readReg64_writeReg64_ne a rd .lr _ (Ne.symm hrd)

private theorem readReg32_writeReg64_lr (a : State) {r : Reg} (hr : r ≠ .lr) (L : BitVec 64) :
    (a.writeReg64 .lr L).readReg32 r = a.readReg32 r := by
  unfold State.readReg32
  rw [State.readReg64_writeReg64_ne a .lr r L hr]

private theorem readReg_writeReg64_lr (a : State) (w : Width) {r : Reg} (hr : r ≠ .lr) (L : BitVec 64) :
    (a.writeReg64 .lr L).readReg w r = a.readReg w r := by
  cases w
  · exact congrArg (BitVec.zeroExtend 64) (readReg32_writeReg64_lr a hr L)
  · exact State.readReg64_writeReg64_ne a .lr r L hr

private theorem fault_branch_lr (a : State) (L : BitVec 64) (msg : String) :
    (a.writeReg64 .lr L).setStatus (.Exception msg) =
      (a.setStatus (.Exception msg)).writeReg64 .lr L ∧
    (a.setStatus (.Exception msg)).readReg64 .lr = a.readReg64 .lr ∧
    ((a.setStatus (.Exception msg)).status = .Running →
      (a.setStatus (.Exception msg)).pc = a.pc + 4#64) :=
  ⟨by cases a; rfl, by cases a; rfl, fun h => by cases a; cases h⟩

private theorem ite_fault_lr (c : Bool) (a : State) (L : BitVec 64) (msg : String)
    {s1 s2 : State}
    (hs : s1 = s2.writeReg64 .lr L ∧ s2.readReg64 .lr = a.readReg64 .lr ∧
      (s2.status = .Running → s2.pc = a.pc + 4#64)) :
    (if c then (a.writeReg64 .lr L).setStatus (.Exception msg) else s1) =
      (if c then a.setStatus (.Exception msg) else s2).writeReg64 .lr L ∧
    (if c then a.setStatus (.Exception msg) else s2).readReg64 .lr = a.readReg64 .lr ∧
    ((if c then a.setStatus (.Exception msg) else s2).status = .Running →
      (if c then a.setStatus (.Exception msg) else s2).pc = a.pc + 4#64) := by
  cases c
  · simpa using hs
  · simpa using fault_branch_lr a L msg

private theorem checkAddrSPAligned_lr (a : State) (addr : AddrMode) (L : BitVec 64) :
    checkAddrSPAligned (a.writeReg64 .lr L) addr = checkAddrSPAligned a addr := by
  cases addr <;> cases a <;> rfl

private theorem advancePC_writeReg64_lr (s : State) (L : BitVec 64) :
    (s.writeReg64 .lr L).advancePC = s.advancePC.writeReg64 .lr L := by
  cases s; rfl

private theorem setMem_writeReg64_lr (s : State) (m : Memory) (L : BitVec 64) :
    (s.writeReg64 .lr L).setMem m = (s.setMem m).writeReg64 .lr L := by
  cases s; rfl

private theorem setPState_writeReg64_lr (s : State) (ps : PState) (L : BitVec 64) :
    (s.writeReg64 .lr L).setPState ps = (s.setPState ps).writeReg64 .lr L := by
  cases s; rfl

private theorem writeVReg128_writeReg64_lr (s : State) (vt : BitVec 5) (v : BitVec 128) (L : BitVec 64) :
    (s.writeReg64 .lr L).writeVReg128 vt v = (s.writeVReg128 vt v).writeReg64 .lr L := by
  cases s; rfl

private theorem advancePC_pc_writeReg (a : State) (w : Width) (rd : Reg) (v : BitVec 64) :
    ((a.writeReg w rd v).advancePC).pc = a.pc + 4#64 := by
  cases a; cases w <;> cases rd <;> simp [State.writeReg, State.writeReg64, State.advancePC]

private theorem advancePC_pc_writeReg_setPState (a : State) (w : Width) (rd : Reg) (v : BitVec 64) (ps : PState) :
    (((a.writeReg w rd v).setPState ps).advancePC).pc = a.pc + 4#64 := by
  cases a; cases w <;> cases rd <;>
    simp [State.writeReg, State.writeReg64, State.setPState, State.advancePC]

private theorem advancePC_pc_writeReg2 (a : State) (w : Width) (r1 r2 : Reg) (v1 v2 : BitVec 64) :
    (((a.writeReg w r1 v1).writeReg w r2 v2).advancePC).pc = a.pc + 4#64 := by
  have h1 : (a.writeReg w r1 v1).pc = a.pc := by
    cases a; cases w <;> cases r1 <;> simp [State.writeReg, State.writeReg64]
  exact (advancePC_pc_writeReg (a.writeReg w r1 v1) w r2 v2).trans (congrArg (· + 4#64) h1)

private theorem evalInst_nonBranchNoLr_writeReg64_lr (P : Program) {inst : Instr}
    (hnb : NonBranchNoLr inst = true) (a : State) (L : BitVec 64) :
    P.evalInst inst (a.writeReg64 .lr L) = (P.evalInst inst a).writeReg64 .lr L ∧
      (P.evalInst inst a).readReg64 .lr = a.readReg64 .lr ∧
      ((P.evalInst inst a).status = .Running → (P.evalInst inst a).pc = a.pc + 4#64) := by
  have hmem : (a.writeReg64 .lr L).mem = a.mem := by cases a; rfl
  have hps : (a.writeReg64 .lr L).pstate = a.pstate := by cases a; rfl
  have hvr : ∀ vt, (a.writeReg64 .lr L).readVReg128 vt = a.readVReg128 vt := fun _ => by cases a; rfl
  have hadv_lr : ∀ s : State, s.advancePC.readReg64 .lr = s.readReg64 .lr := fun s => by cases s; rfl
  have hsm_lr : ∀ (s : State) m, (s.setMem m).readReg64 .lr = s.readReg64 .lr := fun s _ => by cases s; rfl
  have hsp_lr : ∀ (s : State) ps, (s.setPState ps).readReg64 .lr = s.readReg64 .lr := fun s _ => by cases s; rfl
  have hvw_lr : ∀ (s : State) vt v, (s.writeVReg128 vt v).readReg64 .lr = s.readReg64 .lr := fun s _ _ => by cases s; rfl
  cases inst with
  | ldp w sg rt1 rt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨⟨hrt1, hrt2⟩, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execLdp, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hrn]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeReg_comm_lr _ _ hrt1, writeReg_comm_lr _ _ hrt2, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((readReg64_lr_writeReg _ _ hrt2 _).trans (readReg64_lr_writeReg _ _ hrt1 _)),
        fun _ => advancePC_pc_writeReg2 a _ rt1 rt2 _ _⟩
    | _ => simp [NonBranchNoLr] at hnb
  | stp w rt1 rt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨⟨hrt1, hrt2⟩, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execStp, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem,
          State.readReg64_writeReg64_ne a .lr rn L hrn,
          State.readReg64_writeReg64_ne a .lr rt1 L hrt1,
          State.readReg64_writeReg64_ne a .lr rt2 L hrt2]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | ldr w sz sg rt addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨hrt, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execLdr, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hrn]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeReg_comm_lr _ _ hrt, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrt _),
        fun _ => advancePC_pc_writeReg a w rt _⟩
    | _ => simp [NonBranchNoLr] at hnb
  | str sz rt addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨hrt, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execStr, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem,
          State.readReg64_writeReg64_ne a .lr rn L hrn,
          State.readReg64_writeReg64_ne a .lr rt L hrt]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | PreIndex rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨hrt, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execStr, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem,
          State.readReg64_writeReg64_ne a .lr rn L hrn,
          State.readReg64_writeReg64_ne a .lr rt L hrt]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      have hcomm_rn :
          ((a.setMem (a.mem.writeSized sz (a.readReg64 rn + off) (a.readReg64 rt))).writeReg64 .lr L).writeReg64
              rn (a.readReg64 rn + off) =
            ((a.setMem (a.mem.writeSized sz (a.readReg64 rn + off) (a.readReg64 rt))).writeReg64
              rn (a.readReg64 rn + off)).writeReg64 .lr L := by
        simp only [State.writeReg64_comm_or_same _ .lr rn, Ne.symm hrn, ↓reduceIte]
      rw [setMem_writeReg64_lr, hcomm_rn, advancePC_writeReg64_lr]
      exact ⟨rfl,
        (hadv_lr _).trans ((State.readReg64_writeReg64_ne _ rn .lr _ (Ne.symm hrn)).trans (hsm_lr _ _)),
        fun _ => by
          have hsm_pc : (a.setMem (a.mem.writeSized sz (a.readReg64 rn + off) (a.readReg64 rt))).pc = a.pc := by
            cases a; rfl
          exact (advancePC_pc_writeReg _ .W64 rn _).trans (congrArg (· + 4#64) hsm_pc)⟩
    | _ => simp [NonBranchNoLr] at hnb
  | ldrSimd sz vt addr =>
    cases addr with
    | UnscaledOffset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeVReg128_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hvw_lr _ _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | strSimd sz vt addr =>
    cases addr with
    | UnscaledOffset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb, hvr vt]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | ldpSimd sz vt1 vt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeVReg128_writeReg64_lr, writeVReg128_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hvw_lr _ _ _).trans (hvw_lr _ _ _)), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | stpSimd sz vt1 vt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb, hvr vt1, hvr vt2]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | moveWide w op rd imm hw =>
    simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
    dsimp only [Program.evalInst, execInstWithSvc, execMoveWide]
    cases op
    · dsimp only
      rw [writeReg_comm_lr _ _ hnb, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hnb _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    · dsimp only
      rw [writeReg_comm_lr _ _ hnb, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hnb _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    · dsimp only
      rw [readReg_writeReg64_lr a w hnb L, writeReg_comm_lr _ _ hnb, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hnb _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
  | logicalImm w op rd rn imm =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨hrd, hrn⟩
    dsimp only [Program.evalInst, execInstWithSvc, execLogicalImm]
    rw [readReg_writeReg64_lr a w hrn L, hps]
    cases (evalLogical w op (a.readReg w rn) imm a.pstate).2 with
    | none =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    | some ps =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, setPState_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hsp_lr _ _).trans (readReg64_lr_writeReg _ _ hrd _)),
        fun _ => advancePC_pc_writeReg_setPState a w rd _ ps⟩
  | addSubShift w op rd rn rm sh amt =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨⟨hrd, hrn⟩, hrm⟩
    dsimp only [Program.evalInst, execInstWithSvc, execAddSubShift]
    rw [readReg_writeReg64_lr a w hrn L, readReg_writeReg64_lr a w hrm L]
    cases (evalAddSub w op (a.readReg w rn) (shiftVal w (a.readReg w rm) sh amt) none).2 with
    | none =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    | some ps =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, setPState_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hsp_lr _ _).trans (readReg64_lr_writeReg _ _ hrd _)),
        fun _ => advancePC_pc_writeReg_setPState a w rd _ ps⟩
  | bitfield w op rd rn immr imms =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨hrd, hrn⟩
    dsimp only [Program.evalInst, execInstWithSvc, execBitfield]
    rw [readReg_writeReg64_lr a w hrd L, readReg_writeReg64_lr a w hrn L,
        writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
    exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
      fun _ => advancePC_pc_writeReg a w rd _⟩
  | logicalShift w op rd rn rm sh amt =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨⟨hrd, hrn⟩, hrm⟩
    dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift]
    rw [readReg_writeReg64_lr a w hrn L, readReg_writeReg64_lr a w hrm L, hps]
    cases (evalLogical w op (a.readReg w rn) (shiftVal w (a.readReg w rm) sh amt) a.pstate).2 with
    | none =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    | some ps =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, setPState_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hsp_lr _ _).trans (readReg64_lr_writeReg _ _ hrd _)),
        fun _ => advancePC_pc_writeReg_setPState a w rd _ ps⟩
  | dataProc3 w op rd rn rm ra =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨⟨⟨hrd, hrn⟩, hrm⟩, hra⟩
    dsimp only [Program.evalInst, execInstWithSvc, execDataProc3]
    cases op <;> cases w <;> dsimp only <;>
      repeat first
        | rw [State.readReg64_writeReg64_ne a .lr rn L hrn]
        | rw [State.readReg64_writeReg64_ne a .lr rm L hrm]
        | rw [State.readReg64_writeReg64_ne a .lr ra L hra]
        | rw [readReg32_writeReg64_lr a hrn L]
        | rw [readReg32_writeReg64_lr a hrm L]
        | rw [readReg32_writeReg64_lr a hra L]
    all_goals
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a _ rd _⟩
  | _ => simp [NonBranchNoLr] at hnb

private theorem steps_not_running_eq {P : Program} {s sf : State}
    (hs : s.status ≠ .Running) (h : Steps P s sf) : sf = s := by
  cases h with
  | refl _ => rfl
  | step h1 _ => exact absurd h1.status_running hs

/-! ## 2. `lsEdNegSym` (`edNegSentinelGhost c2EdNegAddr`) -/

private abbrev edNegSentinelOff : BitVec 64 :=
  BitVec.ofNat 64 (4 * edwardsPointNegInstrs.length)

private theorem steps_edNegSentinel_of_visitedIn
    {P_real : Program} {entry lr0 : BitVec 64}
    (hsvc : P_real.svc = emptyStdProg.svc)
    (hreal_no : ∀ pc, keepEdNeg entry pc = true → P_real.externAt? pc = none)
    {s_sent sf_sent : State}
    (hvis : h2fsgen_StepsVisitedIn (keepEdNeg entry) emptyStdProg s_sent sf_sent)
    (hrun_sf : sf_sent.status = .Running)
    (hk_sf : keepEdNeg entry sf_sent.pc = false) :
    ∀ a : State,
      s_sent = a.writeReg64 .lr (entry + edNegSentinelOff) →
      a.readReg64 .lr = lr0 →
      keepEdNeg entry a.pc = true →
      (pureWordsProg entry edwardsPointNegWords).CodeLoaded a.mem →
      Steps P_real a ((sf_sent.writeReg64 .lr lr0).setPC lr0) := by
  induction hvis with
  | refl s =>
    intro a hs _ hka _
    have hpc : s.pc = a.pc := by subst hs; cases a; rfl
    rw [hpc, hka] at hk_sf
    cases hk_sf
  | @step s1 s2 sf hd h1 h2 ih =>
    intro a hs1 hlr_a hka hCode
    let L := entry + edNegSentinelOff
    let P_ed := pureWordsProg entry edwardsPointNegWords
    have hpc1 : s1.pc = a.pc := by subst hs1; cases a; rfl
    have hmem1 : s1.mem = a.mem := by subst hs1; cases a; rfl
    have hrun_a : a.status = .Running := by
      have hr := h1.status_running; subst hs1; cases a; exact hr
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := steps_not_running_eq (fun h => ExecStatus.noConfusion h) h2.toSteps
      rw [heq] at hrun_sf; cases hrun_sf
    | extern _ hext _ _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | extern_fault _ hext _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | @exec inst hrun1 hfm1 =>
      rw [hpc1, hmem1] at hfm1
      have hmod4 : a.pc.toNat % 4 = 0 := by
        unfold Program.fetchMem at hfm1
        have hne : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [hne] at hfm1
        by_contra hnz
        simp [hnz] at hfm1
      have halign_e : entry.toNat % 4 = 0 := hCode.aligned
      have hlt228 : (a.pc - entry).toNat < 228 := by
        rw [keepEdNeg_iff, edNegByteLen_eq] at hka; exact hka
      have hnwrap : entry.toNat + 228 ≤ 2 ^ 64 := hCode.no_wrap
      have hd_mod4 : (a.pc - entry).toNat % 4 = 0 := by
        have hsub_nat : (a.pc - entry).toNat = a.pc.toNat - entry.toNat := by bv_omega
        have hle_e : entry.toNat ≤ a.pc.toNat := by bv_omega
        rw [hsub_nat]; omega
      let k := (a.pc - entry).toNat / 4
      have hk57 : k < 57 := by change (a.pc - entry).toNat / 4 < 57; omega
      have hk4 : 4 * k = (a.pc - entry).toNat := by change 4 * ((a.pc - entry).toNat / 4) = _; omega
      have hpc_off : a.pc = entry + BitVec.ofNat 64 (4 * k) := by
        rw [hk4]; bv_omega
      have hins : hasInstrs P_ed entry edwardsPointNegInstrs := pureWordsProg_hasInstrs_edNeg entry
      have hlen_ins : edwardsPointNegInstrs.length = 57 := rfl
      have hf_ed : P_ed.fetch (entry + BitVec.ofNat 64 (4 * k)) =
          some (edwardsPointNegInstrs[k]'(hlen_ins ▸ hk57)) :=
        hins.fetch_off k (BitVec.ofNat 64 (4 * k)) (hlen_ins ▸ hk57) rfl
      have hfm_ed : P_ed.fetchMem a.mem a.pc = some (edwardsPointNegInstrs[k]'(hlen_ins ▸ hk57)) := by
        rw [hpc_off]; exact Program.fetchMem_of_fetch hCode hf_ed
      have hfm_eq_empty : P_ed.fetchMem a.mem a.pc = emptyStdProg.fetchMem a.mem a.pc := by
        unfold Program.fetchMem
        have h1 : (P_ed.externAt? a.pc).isSome = false := by
          rw [pureWordsProg_externAt_none]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1, h2']
      have hinst_eq : inst = edwardsPointNegInstrs[k]'(hlen_ins ▸ hk57) :=
        Option.some.inj ((hfm1.symm.trans hfm_eq_empty.symm).trans hfm_ed)
      have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
        unfold Program.fetchMem
        have h1 : (P_real.externAt? a.pc).isSome = false := by
          rw [hreal_no a.pc hka]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1]
        simpa [Program.fetchMem, h2'] using hfm1
      have heval_svc : emptyStdProg.evalInst inst = P_real.evalInst inst := by
        funext st; unfold Program.evalInst; rw [hsvc]
      by_cases hk56 : k < 56
      · have hmem_take : inst ∈ edwardsPointNegInstrs.take 56 := by
          rw [hinst_eq, List.mem_iff_getElem]
          refine ⟨k, by simp [hlen_ins]; exact hk56, List.getElem_take⟩
        have hnb : NonBranchNoLr inst = true := List.all_eq_true.mp edNegBody56_noLr inst hmem_take
        obtain ⟨hcomm, hlr_next, hpc_next⟩ := evalInst_nonBranchNoLr_writeReg64_lr P_real hnb a L
        let a' := P_real.evalInst inst a
        have hs2_eq : emptyStdProg.evalInst inst s1 = a'.writeReg64 .lr L := by
          rw [heval_svc, hs1]; exact hcomm
        have hrun_s2 : (emptyStdProg.evalInst inst s1).status = .Running := by
          by_contra hnr
          have heq := steps_not_running_eq hnr h2.toSteps
          exact hnr (heq ▸ hrun_sf)
        have hrun_a' : a'.status = .Running := by
          rw [hs2_eq] at hrun_s2
          have hw_st : (a'.writeReg64 .lr L).status = a'.status := by
            generalize a' = st; cases st; rfl
          exact hw_st ▸ hrun_s2
        have hka' : keepEdNeg entry a'.pc = true := by
          rw [hpc_next hrun_a', hpc_off, keepEdNeg_iff, edNegByteLen_eq]
          have hsub : (entry + BitVec.ofNat 64 (4 * k) + 4#64) - entry =
              BitVec.ofNat 64 (4 * k + 4) := by bv_omega
          rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hstep_real : Step P_real a a' := Step.exec hrun_a hfm_real
        have hCode' : P_ed.CodeLoaded a'.mem := hCode.of_keepsFrozen hstep_real.keepsFrozen
        exact Steps.step hstep_real
          (ih hrun_sf hk_sf a' hs2_eq (hlr_next.trans hlr_a) hka' hCode')
      · have hk_eq56 : k = 56 := by omega
        have hinst_ret : inst = .ret .lr := by
          have h56 : edwardsPointNegInstrs[56]'(by decide) = .ret .lr := by decide
          exact Eq.trans (by simpa only [hk_eq56] using hinst_eq) h56
        subst hinst_ret
        have hs2_pc : (emptyStdProg.evalInst (.ret .lr) s1).pc = L := by
          subst hs1
          dsimp only [Program.evalInst, execInstWithSvc]
          have hlr_L : (a.writeReg64 .lr L).readReg64 .lr = L := by cases a; rfl
          rw [hlr_L]; cases a; rfl
        have hk_L : keepEdNeg entry L = false := by
          rw [Bool.eq_false_iff, Ne, keepEdNeg_iff, edNegByteLen_eq]
          have hsub : L - entry = edNegSentinelOff := by dsimp [L]; bv_omega
          have hoff : edNegSentinelOff = 0xe4#64 := rfl
          rw [hsub, hoff]; decide
        cases h2 with
        | step hd2 _ _ =>
          rw [hs2_pc, hk_L] at hd2; cases hd2
        | refl _ =>
          have hstep_ret : Step P_real a (P_real.evalInst (.ret .lr) a) := Step.exec hrun_a hfm_real
          have htarget_eq :
              (((emptyStdProg.evalInst (.ret .lr) s1).writeReg64 .lr lr0).setPC lr0) =
                P_real.evalInst (.ret .lr) a := by
            subst hs1
            dsimp only [Program.evalInst, execInstWithSvc]
            rw [hlr_a]
            rcases a with ⟨⟨rf⟩, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
            dsimp [State.readReg64, RegFile.read, State.writeReg64, State.setPC, RegFile.write] at hlr_a ⊢
            congr 2; funext i; by_cases hi : i = 30#5 <;> simp [hi, hlr_a]
          rw [htarget_eq]
          exact Steps.step hstep_ret (Steps.refl _)

private theorem keepEdNeg_c2_sub_keepLib2Text {pc : BitVec 64}
    (hk : keepEdNeg c2EdNegAddr pc = true) :
    keepLib2Text pc = true :=
  c2_keepLib2Text_of_sub_lt (by rwa [keepEdNeg_iff] at hk) (by decide) (by decide)

private theorem keepEdNeg_s5_all_false :
    (c2S5Addrs.all fun p => !(keepEdNeg c2EdNegAddr p)) = true := by
  decide

theorem edNeg_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsEdNegSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (edNegSentinelGhost c2EdNegAddr u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (edNegSentinelGhost c2EdNegAddr u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_edNeg_eq hLs
  have hpc' : u.pc = c2EdNegAddr := hpc.trans hRes
  have hk0 : keepEdNeg c2EdNegAddr c2EdNegAddr = true := by
    rw [keepEdNeg_iff, BitVec.sub_self]; decide
  let lr0 := u.readReg64 .lr
  let L := c2EdNegAddr + 0xe4#64
  let u_sent := u.writeReg64 .lr L
  have hnoex_sent : ∀ msg, (narrowEdNegGhostHook c2EdNegAddr u_sent).status ≠ .Exception msg := by
    intro msg hex
    apply hnoex msg
    dsimp only [edNegSentinelGhost, L, u_sent]
    have hbe : (ExecStatus.Exception msg == .Running) = false := rfl
    rw [hex, hbe]; exact hex
  have hrun_sent : u_sent.status = .Running := by cases u; exact hrun
  have hmem_sent : u_sent.mem = u.mem := by cases u; rfl
  have hCode : (pureWordsProg c2EdNegAddr edwardsPointNegWords).CodeLoaded u.mem :=
    codeLoaded_of_pureSubsliceSent hinv.rxCode c2EdNegSlice_ok
  have hk_L : keepEdNeg c2EdNegAddr (u_sent.readReg64 .lr) = false := by
    have hlr_L : u_sent.readReg64 .lr = L := by cases u; rfl
    rw [hlr_L]; decide
  obtain ⟨hvis, _, _⟩ := narrowEdNegGhostHook_visitedIn
    (hmem_sent ▸ hCode)
    (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel))
    hrun_sent hnoex_sent (hmem_sent ▸ hfr) hk_L
  have hnoex_eq : ∀ msg, (f3EmptyEdNegGhostHook (keepEdNeg c2EdNegAddr)
      (pureWordsProg c2EdNegAddr edwardsPointNegWords) c2EdNegAddr u_sent).status ≠ .Exception msg :=
    hnoex_sent
  rw [f3EmptyEdNegGhostHook_eq] at hnoex_eq
  obtain ⟨_, hsp_sent, x, R, hpre⟩ := linkedCallHook_activeRealPre_of_noException hnoex_eq
  obtain ⟨_, _, hout⟩ := narrowEdNegGhostHook_master_ok c2EdNegAddr x R u_sent hrun_sent hpre hsp_sent
  have hret_sf : (narrowEdNegGhostHook c2EdNegAddr u_sent).status = .Running ∧
      (narrowEdNegGhostHook c2EdNegAddr u_sent).pc = L := by
    rcases hout with ⟨hr, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · exact ⟨hr.2.2, hr.1.trans (by cases u; rfl)⟩
    · dsimp only [masterEdNegSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
    · dsimp only [masterEdNegSpec] at he; rw [satisfies_pure_sepConj] at he; exact False.elim he.1
    · dsimp only [masterEdNegSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1
  have hbe : (ExecStatus.Running == .Running) = true := rfl
  have hghost_eq : edNegSentinelGhost c2EdNegAddr u =
      ((narrowEdNegGhostHook c2EdNegAddr u_sent).writeReg64 .lr lr0).setPC lr0 := by
    dsimp only [edNegSentinelGhost, lr0, L, u_sent]
    rw [hret_sf.1, hbe]; rfl
  have hu_sent_pc : u_sent.setPC c2EdNegAddr = u.writeReg64 .lr L := by
    dsimp [u_sent]; cases u; dsimp only [State.writeReg64, State.setPC] at hpc' ⊢; subst hpc'; rfl
  have hk_sf : keepEdNeg c2EdNegAddr (narrowEdNegGhostHook c2EdNegAddr u_sent).pc = false := by
    rw [hret_sf.2]; decide
  have htrap_no : ∀ pc, keepEdNeg c2EdNegAddr pc = true →
      (cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W).externAt? pc = none := by
    intro pc hkp
    rw [externAt?_s5TrapExt_eq_of_keep_all_false hLs W keepEdNeg_s5_all_false hkp]
    exact hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg (keepEdNeg_c2_sub_keepLib2Text hkp))
      (keepEdNeg_c2_noPanic hkp)
  have hst := steps_edNegSentinel_of_visitedIn
    (P_real := cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W)
    rfl htrap_no hvis hret_sf.1 hk_sf u hu_sent_pc rfl (hpc' ▸ hk0) hCode
  rw [← hghost_eq] at hst
  exact stepsStrictAvoid_of_s5Trap hExt W hst hnoex

/-! ## 3. `lsSharedSecretDropSym` (`c2SharedSecretDropSentinelGhost`) -/

private theorem resolve_sharedSecretDrop_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

private theorem zeroize32_sub_proc (entry : BitVec 64) :
    subroutine_ok (pureWordsProg entry zeroize32Words) entry processZeroizeSpec :=
  subroutine_ok_processZeroize_of_hasWords
    (pureWordsProg_externAt_none entry zeroize32Words)
    (pureWordsProg_zeroize32_hasWords entry)

private abbrev zeroize32SentinelOff : BitVec 64 :=
  BitVec.ofNat 64 (4 * zeroize32Instrs.length)

private theorem steps_zeroizeSentinel_of_visitedIn
    {P_real : Program} {entry lr0 : BitVec 64}
    (hsvc : P_real.svc = emptyStdProg.svc)
    (hreal_no : ∀ pc, keepStaticSecretDrop entry pc = true → P_real.externAt? pc = none)
    {s_sent sf_sent : State}
    (hvis : h2fsgen_StepsVisitedIn (keepStaticSecretDrop entry) emptyStdProg s_sent sf_sent)
    (hrun_sf : sf_sent.status = .Running)
    (hk_sf : keepStaticSecretDrop entry sf_sent.pc = false) :
    ∀ a : State,
      s_sent = a.writeReg64 .lr (entry + zeroize32SentinelOff) →
      a.readReg64 .lr = lr0 →
      keepStaticSecretDrop entry a.pc = true →
      (pureWordsProg entry zeroize32Words).CodeLoaded a.mem →
      Steps P_real a ((sf_sent.writeReg64 .lr lr0).setPC lr0) := by
  induction hvis with
  | refl s =>
    intro a hs _ hka _
    have hpc : s.pc = a.pc := by subst hs; cases a; rfl
    rw [hpc, hka] at hk_sf
    cases hk_sf
  | @step s1 s2 sf hd h1 h2 ih =>
    intro a hs1 hlr_a hka hCode
    let L := entry + zeroize32SentinelOff
    let P_z := pureWordsProg entry zeroize32Words
    have hpc1 : s1.pc = a.pc := by subst hs1; cases a; rfl
    have hmem1 : s1.mem = a.mem := by subst hs1; cases a; rfl
    have hrun_a : a.status = .Running := by
      have hr := h1.status_running; subst hs1; cases a; exact hr
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := steps_not_running_eq (fun h => ExecStatus.noConfusion h) h2.toSteps
      rw [heq] at hrun_sf; cases hrun_sf
    | extern _ hext _ _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | extern_fault _ hext _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | @exec inst hrun1 hfm1 =>
      rw [hpc1, hmem1] at hfm1
      have hmod4 : a.pc.toNat % 4 = 0 := by
        unfold Program.fetchMem at hfm1
        have hne : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [hne] at hfm1
        by_contra hnz
        simp [hnz] at hfm1
      have halign_e : entry.toNat % 4 = 0 := hCode.aligned
      have hlt252 : (a.pc - entry).toNat < 252 := by
        rw [keepStaticSecretDrop_iff] at hka
        exact hka
      have hnwrap : entry.toNat + 252 ≤ 2 ^ 64 := by
        have hnw := hCode.no_wrap
        have hbase : P_z.base = entry := rfl
        have hcode : P_z.code = (pureWordsProg 0#64 zeroize32Words).code := rfl
        have hlen0 : (pureWordsProg 0#64 zeroize32Words).code.length = 252 := by decide +kernel
        rwa [hbase, hcode, hlen0] at hnw
      have hd_mod4 : (a.pc - entry).toNat % 4 = 0 := by
        have hsub_nat : (a.pc - entry).toNat = a.pc.toNat - entry.toNat := by bv_omega
        have hle_e : entry.toNat ≤ a.pc.toNat := by bv_omega
        rw [hsub_nat]; omega
      let k := (a.pc - entry).toNat / 4
      have hk63 : k < 63 := by change (a.pc - entry).toNat / 4 < 63; omega
      have hk4 : 4 * k = (a.pc - entry).toNat := by change 4 * ((a.pc - entry).toNat / 4) = _; omega
      have hpc_off : a.pc = entry + BitVec.ofNat 64 (4 * k) := by
        rw [hk4]; bv_omega
      have hins : hasInstrs P_z entry zeroize32Instrs :=
        LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop.hasInstrs_of_hasWords
          (pureWordsProg_zeroize32_hasWords entry)
      have hlen_ins : zeroize32Instrs.length = 63 := rfl
      have hf_z : P_z.fetch (entry + BitVec.ofNat 64 (4 * k)) =
          some (zeroize32Instrs[k]'(hlen_ins ▸ hk63)) :=
        hins.fetch_off k (BitVec.ofNat 64 (4 * k)) (hlen_ins ▸ hk63) rfl
      have hfm_z : P_z.fetchMem a.mem a.pc = some (zeroize32Instrs[k]'(hlen_ins ▸ hk63)) := by
        rw [hpc_off]; exact Program.fetchMem_of_fetch hCode hf_z
      have hfm_eq_empty : P_z.fetchMem a.mem a.pc = emptyStdProg.fetchMem a.mem a.pc := by
        unfold Program.fetchMem
        have h1 : (P_z.externAt? a.pc).isSome = false := by
          rw [pureWordsProg_externAt_none]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1, h2']
      have hinst_eq : inst = zeroize32Instrs[k]'(hlen_ins ▸ hk63) :=
        Option.some.inj ((hfm1.symm.trans hfm_eq_empty.symm).trans hfm_z)
      have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
        unfold Program.fetchMem
        have h1 : (P_real.externAt? a.pc).isSome = false := by
          rw [hreal_no a.pc hka]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1]
        simpa [Program.fetchMem, h2'] using hfm1
      have heval_svc : emptyStdProg.evalInst inst = P_real.evalInst inst := by
        funext st; unfold Program.evalInst; rw [hsvc]
      by_cases hk62 : k < 62
      · have hmem_take : inst ∈ zeroize32Instrs.take 62 := by
          rw [hinst_eq, List.mem_iff_getElem]
          refine ⟨k, by simp [hlen_ins]; exact hk62, List.getElem_take⟩
        have hnb : NonBranchNoLr inst = true := List.all_eq_true.mp zeroizeBody62_noLr inst hmem_take
        obtain ⟨hcomm, hlr_next, hpc_next⟩ := evalInst_nonBranchNoLr_writeReg64_lr P_real hnb a L
        let a' := P_real.evalInst inst a
        have hs2_eq : emptyStdProg.evalInst inst s1 = a'.writeReg64 .lr L := by
          rw [heval_svc, hs1]; exact hcomm
        have hrun_s2 : (emptyStdProg.evalInst inst s1).status = .Running := by
          by_contra hnr
          have heq := steps_not_running_eq hnr h2.toSteps
          exact hnr (heq ▸ hrun_sf)
        have hrun_a' : a'.status = .Running := by
          rw [hs2_eq] at hrun_s2
          have hw_st : (a'.writeReg64 .lr L).status = a'.status := by
            generalize a' = st; cases st; rfl
          exact hw_st ▸ hrun_s2
        have hka' : keepStaticSecretDrop entry a'.pc = true := by
          rw [hpc_next hrun_a', hpc_off, keepStaticSecretDrop_iff]
          have hsub : (entry + BitVec.ofNat 64 (4 * k) + 4#64) - entry =
              BitVec.ofNat 64 (4 * k + 4) := by bv_omega
          rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          show 4 * k + 4 < 252
          omega
        have hstep_real : Step P_real a a' := Step.exec hrun_a hfm_real
        have hCode' : P_z.CodeLoaded a'.mem := hCode.of_keepsFrozen hstep_real.keepsFrozen
        exact Steps.step hstep_real
          (ih hrun_sf hk_sf a' hs2_eq (hlr_next.trans hlr_a) hka' hCode')
      · have hk_eq62 : k = 62 := by omega
        have hinst_ret : inst = .ret .lr := by
          have h62 : zeroize32Instrs[62]'(by decide) = .ret .lr := by decide
          exact Eq.trans (by simpa only [hk_eq62] using hinst_eq) h62
        subst hinst_ret
        have hs2_pc : (emptyStdProg.evalInst (.ret .lr) s1).pc = L := by
          subst hs1
          dsimp only [Program.evalInst, execInstWithSvc]
          have hlr_L : (a.writeReg64 .lr L).readReg64 .lr = L := by cases a; rfl
          rw [hlr_L]; cases a; rfl
        have hk_L : keepStaticSecretDrop entry L = false := by
          rw [Bool.eq_false_iff, Ne, keepStaticSecretDrop_iff]
          have hsub : L - entry = zeroize32SentinelOff := by dsimp [L]; bv_omega
          have hoff : zeroize32SentinelOff = 0xfc#64 := rfl
          rw [hsub, hoff]; show ¬ (0xfc#64 : BitVec 64).toNat < 252; decide
        cases h2 with
        | step hd2 _ _ =>
          rw [hs2_pc, hk_L] at hd2; cases hd2
        | refl _ =>
          have hstep_ret : Step P_real a (P_real.evalInst (.ret .lr) a) := Step.exec hrun_a hfm_real
          have htarget_eq :
              (((emptyStdProg.evalInst (.ret .lr) s1).writeReg64 .lr lr0).setPC lr0) =
                P_real.evalInst (.ret .lr) a := by
            subst hs1
            dsimp only [Program.evalInst, execInstWithSvc]
            rw [hlr_a]
            rcases a with ⟨⟨rf⟩, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
            dsimp [State.readReg64, RegFile.read, State.writeReg64, State.setPC, RegFile.write] at hlr_a ⊢
            congr 2; funext i; by_cases hi : i = 30#5 <;> simp [hi, hlr_a]
          rw [htarget_eq]
          exact Steps.step hstep_ret (Steps.refl _)

private theorem keepZeroize32_c2_sub_keepLib2Text {pc : BitVec 64}
    (hk : keepStaticSecretDrop c2Zeroize32Addr pc = true) :
    keepLib2Text pc = true :=
  c2_keepLib2Text_of_sub_lt (by rwa [keepStaticSecretDrop_iff] at hk) (by decide) (by decide)

private theorem keepZeroize32_s5_all_false :
    (c2S5Addrs.all fun p => !(keepStaticSecretDrop c2Zeroize32Addr p)) = true := by
  decide

theorem sharedSecretDrop_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsSharedSecretDropSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (c2SharedSecretDropSentinelGhost u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (c2SharedSecretDropSentinelGhost u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_sharedSecretDrop_eq hLs
  have hpc' : u.pc = c2SharedSecretDropAddr := hpc.trans hRes
  have hk_drop : keepLib2Text c2SharedSecretDropAddr = true := by decide
  have hn_drop : c2SharedSecretDropAddr ∉ c2S5Addrs := by decide
  have hk0 : keepStaticSecretDrop c2Zeroize32Addr c2Zeroize32Addr = true := by
    rw [keepStaticSecretDrop_iff, BitVec.sub_self]; decide
  let P_trap := cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W
  let P_drop := pureWordsProg c2SharedSecretDropAddr [c2SharedDropWord]
  have hCode_drop : P_drop.CodeLoaded u.mem :=
    codeLoaded_of_pureSubsliceSent hinv.rxCode c2SharedDropSlice_ok
  have hCode_z : (pureWordsProg c2Zeroize32Addr zeroize32Words).CodeLoaded u.mem :=
    codeLoaded_of_pureSubsliceSent hinv.rxCode c2Zeroize32Slice_ok
  have hf_drop : P_drop.fetch (c2SharedSecretDropAddr + 0#64) =
      some (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) :=
    Program.fetch_of_hasWords_decodeAt 0
      (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel)) rfl (by decide)
  have hfm_drop : P_drop.fetchMem u.mem u.pc =
      some (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) := by
    rw [hpc']
    simpa [BitVec.add_zero] using Program.fetchMem_of_fetch hCode_drop hf_drop
  have htrap_drop : P_trap.externAt? c2SharedSecretDropAddr = none := by
    dsimp [P_trap]
    rw [externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_not_mem_c2S5Addrs hLs hn_drop)]
    exact hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk_drop) (by decide)
  have hfm_trap0 : P_trap.fetchMem u.mem u.pc =
      some (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) := by
    unfold Program.fetchMem at hfm_drop ⊢
    have h1 : (P_trap.externAt? u.pc).isSome = false := by
      rw [hpc', htrap_drop]; rfl
    have h2 : (P_drop.externAt? u.pc).isSome = false := by
      rw [pureWordsProg_externAt_none]; rfl
    rw [h1]; simpa [h2] using hfm_drop
  have heval_b : P_trap.evalInst (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) u =
      u.setPC c2Zeroize32Addr := by
    dsimp only [P_trap, Program.evalInst, execInstWithSvc]
    rw [hpc']
    have hadd : c2SharedSecretDropAddr + (c2Zeroize32Addr - c2SharedSecretDropAddr) =
        c2Zeroize32Addr := by decide
    rw [hadd]
  have hstep_b : Step P_trap u (u.setPC c2Zeroize32Addr) :=
    heval_b ▸ Step.exec hrun hfm_trap0
  let lr0 := u.readReg64 .lr
  let L := c2Zeroize32Addr + 0xfc#64
  let u_sent := u.writeReg64 .lr L
  have hnoex_sent : ∀ msg, (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
      (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).status ≠ .Exception msg := by
    intro msg hex
    apply hnoex msg
    dsimp only [c2SharedSecretDropSentinelGhost, c2ZeroizeSentinelGhost, L, u_sent]
    have hbe : (ExecStatus.Exception msg == .Running) = false := rfl
    rw [hex, hbe]; exact hex
  have hrun_sent : u_sent.status = .Running := by cases u; exact hrun
  have hmem_sent : u_sent.mem = u.mem := by cases u; rfl
  have hk_L : keepStaticSecretDrop c2Zeroize32Addr (u_sent.readReg64 .lr) = false := by
    have hlr_L : u_sent.readReg64 .lr = L := by cases u; rfl
    rw [hlr_L]; decide
  have hCodeSub : (pureWordsProg c2Zeroize32Addr zeroize32Words).CodeLoaded
      (ProofLib.stripExecOutside (keepStaticSecretDrop c2Zeroize32Addr) u_sent.mem) := by
    rw [hmem_sent]
    refine staticSecretDrop_codeLoaded_stripExecOutside (fun off hoff => ?_) hCode_z
    rw [keepStaticSecretDrop_iff]
    have hbase : (pureWordsProg c2Zeroize32Addr zeroize32Words).base = c2Zeroize32Addr := rfl
    have hcode : (pureWordsProg c2Zeroize32Addr zeroize32Words).code =
        (pureWordsProg 0#64 zeroize32Words).code := rfl
    have hlen0 : (pureWordsProg 0#64 zeroize32Words).code.length = 252 := by decide +kernel
    rw [hbase]
    rw [hcode, hlen0] at hoff
    have hsub : (c2Zeroize32Addr + BitVec.ofNat 64 off) - c2Zeroize32Addr =
        BitVec.ofNat 64 off := by bv_omega
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hoff
  obtain ⟨hvis, _, _⟩ := f3EmptyZeroizeGhostHook_visitedIn rfl
    (pureWordsProg_externAt_none c2Zeroize32Addr zeroize32Words)
    (pureWordsProg_zeroize32_hasWords c2Zeroize32Addr)
    hrun_sent hnoex_sent (hmem_sent ▸ hfr) hk_L hCodeSub
  have hnoex_eq := hnoex_sent
  rw [f3EmptyZeroizeGhostHook_eq] at hnoex_eq
  obtain ⟨_, hsp_sent, x, R, hpre⟩ := linkedCallHook_activeRealPre_of_noException hnoex_eq
  obtain ⟨_, _, hout⟩ := f3EmptyZeroizeGhostHook_master_ok_of_process rfl
    (pureWordsProg_externAt_none c2Zeroize32Addr zeroize32Words)
    (zeroize32_sub_proc c2Zeroize32Addr)
    (keep := keepStaticSecretDrop c2Zeroize32Addr) x R u_sent hrun_sent hpre hsp_sent
  have hret_sf : (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).status = .Running ∧
      (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).pc = L := by
    rcases hout with ⟨hr, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · exact ⟨hr.2.2, hr.1.trans (by cases u; rfl)⟩
    · dsimp only [masterZeroizeSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
    · dsimp only [masterZeroizeSpec] at he; rw [satisfies_pure_sepConj] at he; exact False.elim he.1
    · dsimp only [masterZeroizeSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1
  have hbe : (ExecStatus.Running == .Running) = true := rfl
  have hghost_eq : c2SharedSecretDropSentinelGhost u =
      ((f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).writeReg64 .lr lr0).setPC lr0 := by
    dsimp only [c2SharedSecretDropSentinelGhost, c2ZeroizeSentinelGhost, lr0, L, u_sent]
    rw [hret_sf.1, hbe]; rfl
  have hu_sent_pc : u_sent.setPC c2Zeroize32Addr = (u.setPC c2Zeroize32Addr).writeReg64 .lr L := by
    dsimp [u_sent]; cases u; rfl
  have hlr_z : (u.setPC c2Zeroize32Addr).readReg64 .lr = lr0 := by
    dsimp [lr0]; cases u; rfl
  have hk_sf : keepStaticSecretDrop c2Zeroize32Addr
      (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).pc = false := by
    rw [hret_sf.2]; decide
  have htrap_no : ∀ pc, keepStaticSecretDrop c2Zeroize32Addr pc = true →
      P_trap.externAt? pc = none := by
    intro pc hkp
    dsimp [P_trap]
    rw [externAt?_s5TrapExt_eq_of_keep_all_false hLs W keepZeroize32_s5_all_false hkp]
    exact hExt.realRxNoExtern mmpl W
      (keepLib2Text_sub_rxProg (keepZeroize32_c2_sub_keepLib2Text hkp))
      (keepZeroize32_c2_noPanic hkp)
  have hst_z := steps_zeroizeSentinel_of_visitedIn
    (P_real := P_trap) (lr0 := lr0) rfl htrap_no
    hvis hret_sf.1 hk_sf (u.setPC c2Zeroize32Addr) hu_sent_pc hlr_z hk0
    (by cases u; exact hCode_z)
  have hst := Steps.step hstep_b hst_z
  rw [← hghost_eq] at hst
  exact stepsStrictAvoid_of_s5Trap hExt W hst hnoex

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightSentinel
