/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenCtxPlacedBudget -- proof-setup: allow-public-import
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
# Budget-Threaded Relocatable `keygen` Convergence Blocks (Block `617`)

Re-exports `KeygenCtxPlacedBudget` and verifies `keygen`'s decimal-parsing convergence blocks
(`M+0x524 .. M+0x550`, `0xf40`, `0xfc4 .. 0xfe0`) under `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallW InMainPlaced LsCodeInv callHeap isDigit mPcPlaced_eq mProgPlaced mProgPlaced_eq
   mainFrameSize parseArgs parseUnsigned sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (KeygenRegs cond_513_257_bit0 fsp_align_of_spAligned parseUnsigned_some_of_digits
   pure_intro_entails shl32_bit0 shl32_of_lo32 shr32_shl32 stripPlus)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenCtxPlacedBudget
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
  (step_ok_tail_548_gen_placed)

-- AUTO-BRIDGE BEGIN
export LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenCtxPlacedBudget
  (pool_congr_vm keygenBase keygenBase_congr_vm KeygenCtxPlaced KeygenGoalPlaced
   step_keygen_530_fail_placed step_keygen_52c_placed)
-- AUTO-BRIDGE END

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem step_keygen_530_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {n : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x538) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hw11 : (s.readReg64 (.gpr 11#5)).setWidth 32 = 1#32)
    (hw21 : (s.readReg64 (.gpr 21#5)).setWidth 32 = BitVec.ofNat 32 n)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some (.keygen me n)) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced, keygenBase]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hfsp_align0 := fsp_align_of_spAligned hsp0
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x550#64) hinv
  wp_steps_sync_pool ((blkPl_617).base + 0x550#64)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0x550 := {
    pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
    run := by simp only [arm64_norm, *]
    sp := by simp only [arm64_norm, *]
    fp := by simp only [arm64_norm, *]
    inv := hinv1
    vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
    spAligned := hsp0 }
  let w5v := ((s.readReg64 (.gpr 21#5)).setWidth 32).setWidth 64
  let w : CallW := ⟨0x8000000000000000#64, cap, ptr, BitVec.ofNat 64 me.name.length, devw, w5v,
    s.readReg64 (.gpr 26#5)⟩
  have hw5_lo : w5v.setWidth 32 = BitVec.ofNat 32 n := by
    dsimp only [w5v]; rw [← hw21]; bv_bits
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_ok_tail_548_gen_placed (hookStack := hookStack) (resStack := resStack) (st := st)
      (buf := buf) (vcap := vcap) (vptr := vptr)
      (w := w) (c := .keygen me n) (ps := [(p1, bs1), (p2, bs2), (p3, bs3)])
      (ArgvFrame := argvAtROP (s0.readReg64 .x1)
        ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]))
      (Statics := Statics)
      K.hc.allocFs K.hstk K.hstk64 hparse hin1
      (by simp only [arm64_norm, kr.x19]) (by simp only [arm64_norm, kr.x20])
      (by simp only [arm64_norm, kr.x23])
      (by simp only [arm64_norm, kr.x24, K.hlen])
      (by simp only [arm64_norm, w]) (by simp only [arm64_norm, hx22, w])
      (by simp only [arm64_norm, w])
      (by simp only [arm64_norm, BitVec.zero_or, w, w5v])
      K.hvcap (by simp only [arm64_norm, kr.trace]) (by simp only [arm64_norm, kr.fs]) K.hnext)
  rw [hfsp, K.hlen]
  simp only [arm64_norm]
  dsimp only [callHeap, argvAtROP, w]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, show Reg.x1 = Reg.gpr 1#5 from rfl, hx1, hx15]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (pure_intro_entails ⟨trivial, hw5_lo⟩ (Entails.refl _))))
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_keygen_f04_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0xf40) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx13 : s.readReg64 (.gpr 13#5) = ptr) (hx14 : s.readReg64 (.gpr 14#5) = cap)
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
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) hparse)
  conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
    bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  exact Entails.refl _

theorem step_keygen_fac_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {v : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0xfe0) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hv_lt : v < 2 ^ 32) (hx8 : s.readReg64 (.gpr 8#5) = (BitVec.ofNat 64 v) <<< 32)
    (hne_ds : stripPlus bs3 ≠ []) (hdig : ∀ b ∈ stripPlus bs3, isDigit b = true)
    (hval : (stripPlus bs3).foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = v) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  have hu : parseUnsigned (2 ^ 32 - 1) bs3 = some v :=
    parseUnsigned_some_of_digits hne_ds hdig hval (by omega)
  have hlsr : ((BitVec.ofNat 64 v) <<< 32) >>> 32 = BitVec.ofNat 64 v := shr32_shl32 hv_lt
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0x538 :=
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
  rw [← mProgPlaced_eq]
  by_cases hle : v ≤ 100
  · have hcmp : (101#64).ule (BitVec.ofNat 64 v) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
        decide_eq_false_iff_not]
      omega
    refine SepWPp.weaken_pre ?_
      (step_keygen_530_ok_placed (w3 := w3) K hin1
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
        (by simp only [arm64_norm, hx1])
        (by simp only [arm64_norm, hcmp, Bool.false_eq_true, ↓reduceIte])
        (by apply BitVec.eq_of_toNat_eq; simp only [arm64_norm, BitVec.toNat_setWidth,
          BitVec.toNat_ofNat]; omega)
        (K.parse_ok hu hle))
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
      bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _
  · have hcmp : (101#64).ule (BitVec.ofNat 64 v) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
        decide_eq_true_eq]
      omega
    refine SepWPp.weaken_pre ?_
      (step_keygen_530_fail_placed (w3 := w3) K hin1
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
        (by simp only [arm64_norm, hcmp, ↓reduceIte])
        (K.parse_gt100 hu hle))
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
      bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _

theorem step_keygen_524_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {v : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x52c) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hv_lt : v < 2 ^ 32) (hx9 : (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 v)
    (hne_ds : stripPlus bs3 ≠ []) (hdig : ∀ b ∈ stripPlus bs3, isDigit b = true)
    (hval : (stripPlus bs3).foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = v) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  have hshl := shl32_of_lo32 hv_lt hx9
  have hb0 := shl32_bit0 (s.readReg64 (.gpr 9#5))
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xfe0#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_keygen_fac_placed (w3 := w3) K
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
      (by simp only [arm64_norm, hx1]) hv_lt
      (by simp only [arm64_norm, *]) hne_ds hdig hval)
  conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
    bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  exact Entails.refl _

theorem step_keygen_f90_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 remPtr : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {b : BitVec 8} {rest : List (BitVec 8)}
    {me : AddrV} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0xfc4) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx8 : s.readReg64 (.gpr 8#5) = remPtr)
    (hrest : (remPtr ↦ᵣ (b :: rest)) ∗ RestP3 = cStrAtRO p3 bs3)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3
      ((remPtr ↦ᵣ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  rw [ProofLib.pointsToBytesRO_cons, sepConj_assoc, sepConj_assoc]
  have hb0_cond := cond_513_257_bit0 ((BitVec.zeroExtend 32 b - 48#32).ult 10#32)
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x534#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_keygen_52c_placed (w3 := w3) K
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1]) hparse)
  conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
    bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlacedBudget
