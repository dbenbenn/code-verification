/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Shared `keygen` Parser Context & Failure-Convergence Seam (Block `617`)

Budget-threaded parser context (`KeygenCtxPlaced`, `KeygenGoalPlaced`, `keygenBase`) and shared
failure-convergence steps (`step_keygen_530_fail_placed`, `step_keygen_52c_placed`) so
`KeygenPlacedBudget` does not `public import` `KeygenConvPlacedBudget`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenCtxPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced CallV CallW InMainPlaced LsCodeInv addrParse addrWords argsBuf
   callCellsPlaced callHeap locals mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize
   mainSaved parseArgs parseUnsigned sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (KeygenRegs locals_merge_memRegion m2LocalsRest)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (MainCalleesROBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
  (step_drop_addr_ae8_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim st s' = A.pool lim st s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

@[expose] def keygenBase {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (stk : Nat)
    (buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (me : AddrV) (Statics : SepProp) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  addrWords A.repAlloc me cap ptr (BitVec.ofNat 64 me.name.length) devw ∗
    argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
    argsBuf A.repAlloc 3#64 buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
    ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
    ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ cStrAtRO p1 bs1 ∗
    ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
    ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗
    ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗
    mainSaved s0 ∗
    ((fsp + 0x48#64) ↦₆₄ devw) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
    memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
    stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics

theorem keygenBase_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) {s' : State} (stk : Nat)
    (buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (me : AddrV) (Statics : SepProp)
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    keygenBase A lim st s0 s' stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics =
      keygenBase A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics := by
  dsimp only [keygenBase]
  rw [pool_congr_vm A lim st s hbs hbrk htp hphys hperm hfs]

structure KeygenCtxPlaced [LibsignalPlacement] {M : AllocCostModel} (CodeOk : Memory → Prop)
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (uuidParse : UuidParser) (i : Inputs) (s0 : State)
    (stk hookStack resStack : Nat) (buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (me : AddrV)
    (Statics : SepProp) (Q Qp : State → SepProp → Prop) (oom : State → SepProp) : Prop where
  hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack
  hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk
  hstk64 : stk ≤ 2 ^ 63
  hok : CliInputsOk i
  hne : i.argv ≠ []
  hlen : i.argv.length = 3
  hps : [(p1, bs1), (p2, bs2), (p3, bs3)].map (·.2) = i.argv.map bytesOfString
  hcmd : bs1 = utf8 "keygen"
  haddr : addrParse uuidParse bs2 = some me
  hvcap : vcap ≠ 0#64
  hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
    (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
      s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp
  hnext : ∀ (s' : State) (w : CallW) (c : CallV),
    parseArgs uuidParse (i.argv.map bytesOfString) = some c →
    AtCallPlaced CodeOk s0 s' w i.argv.length buf →
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
      (callHeap A.repAlloc w c ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8) st) s' ∗ Statics)
      Q Qp oom

abbrev KeygenGoalPlaced [LibsignalPlacement] {M : AllocCostModel} {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (_K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (s : State) (w3 : BitVec 64) (PreP3 : SepProp) : Prop :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
    (PreP3 ∗ ((fsp + 0x40#64) ↦₆₄ w3) ∗
      keygenBase A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics)
    Q Qp oom

theorem KeygenCtxPlaced.parse_none [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hu : parseUnsigned (2 ^ 32 - 1) bs3 = none) :
    parseArgs uuidParse (i.argv.map bytesOfString) = none := by
  rw [← K.hps]
  simp only [List.map_cons, List.map_nil, parseArgs, K.hcmd, ↓reduceIte, K.haddr, hu]

theorem KeygenCtxPlaced.parse_gt100 [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {v : Nat}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hu : parseUnsigned (2 ^ 32 - 1) bs3 = some v) (hgt : ¬ v ≤ 100) :
    parseArgs uuidParse (i.argv.map bytesOfString) = none := by
  rw [← K.hps]
  simp only [List.map_cons, List.map_nil, parseArgs, K.hcmd, ↓reduceIte, K.haddr, hu, hgt]

theorem KeygenCtxPlaced.parse_ok [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {v : Nat}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hu : parseUnsigned (2 ^ 32 - 1) bs3 = some v) (hle : v ≤ 100) :
    parseArgs uuidParse (i.argv.map bytesOfString) = some (.keygen me v) := by
  rw [← K.hps]
  simp only [List.map_cons, List.map_nil, parseArgs, K.hcmd, ↓reduceIte, K.haddr, hu, hle]

theorem step_keygen_530_fail_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x538) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hw11 : (s.readReg64 (.gpr 11#5)).setWidth 32 = 0#32)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb44#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0xb44 :=
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_drop_addr_ae8_pool_placed (hookStack := hookStack) (resStack := resStack) (st := st)
      (buf := buf) (vcap := vcap) (vptr := vptr)
      (cap := cap) (ptr := ptr) (len := BitVec.ofNat 64 me.name.length) (devw := devw) (me := me)
      (ps := [(p1, bs1), (p2, bs2), (p3, bs3)])
      (Rest := cStrAtRO p3 bs3 ∗
        ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
        ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ cStrAtRO p1 bs1 ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics)
      K.hc.allocFs K.hstk K.hstk64 K.hok K.hne hparse hin1
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, kr.x19])
      (by simp only [arm64_norm, kr.x20])
      (by simp only [show Reg.x1 = Reg.gpr 1#5 from rfl, arm64_norm, hx1])
      (by simp only [arm64_norm, kr.x23])
      (by simp only [arm64_norm, kr.x24, K.hlen])
      K.hvcap (by simp only [arm64_norm, kr.trace]) (by simp only [arm64_norm, kr.fs]) K.hexit)
  conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]), K.hlen]
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  dsimp only [keygenBase]
  have hperm : ∀ (P3 W3 AW V B X0 C0 X1 C1 X2 C2 X3 X4 MS W4 W1 M1 M2 ST PL STX : SepProp),
      P3 ∗ W3 ∗ (AW ∗ V ∗ B ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ X2 ∗ C2 ∗ X3 ∗ X4 ∗
        MS ∗ W4 ∗ W1 ∗ M1 ∗ M2 ∗ ST ∗ PL ∗ STX) ⊢
        (W3 ∗ W4 ∗ W1 ∗ M1 ∗ M2) ∗
          (AW ∗ V ∗ B ∗ MS ∗ ST ∗ PL ∗
            (P3 ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ X2 ∗ C2 ∗ X3 ∗ X4 ∗ STX)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Entails.of_eq (by sep_ac_rfl)
  have hp2 : ∀ (M0 AW V B MS ST PL R : SepProp),
      M0 ∗ (AW ∗ V ∗ B ∗ MS ∗ ST ∗ PL ∗ R) ⊢ AW ∗ V ∗ B ∗ MS ∗ M0 ∗ ST ∗ PL ∗ R :=
    fun _ _ _ _ _ _ _ _ => Entails.of_eq (by sep_ac_rfl)
  exact Entails.trans (hperm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 devw w1))
      (hp2 _ _ _ _ _ _ _ _))

theorem step_keygen_52c_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x534) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_keygen_530_fail_placed (w3 := w3) K
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
      (by simp only [arm64_norm]) hparse)
  conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
    bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  exact Entails.refl _

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenCtxPlacedBudget
