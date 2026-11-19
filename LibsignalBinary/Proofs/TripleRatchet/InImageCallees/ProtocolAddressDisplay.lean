/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ProtocolAddressDisplay

theorem stackAt_addrDisplay (sp : BitVec 64) :
    stackAt sp addrDisplayStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp extHookStack 6 (by decide)

theorem fmtWrite_tripleRatchetExterns_trap (C : Crypto)
    (A : RustAlloc) (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    HookSat (Rust.withPanics (trTrapExterns C abs)) fmtWriteName (fmtWriteSpec A) := by
  have habs := tripleRatchetExterns_abs C 0#64 abs
  have h4 : Rust.withPanics (trTrapExterns C abs) fmtWriteName =
      abs fmtWriteName := by
    rw [withPanics_trTrap_eq_kit C 0#64 abs (n := fmtWriteName) (by decide)]
    exact Option.some.inj (congrArg (·[3]?) habs)
  simpa [HookSat, h4] using hW

theorem fmtWrite_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) fmtWriteName (fmtWriteSpec A) := by
  have habs := tripleRatchetExterns_abs C ctl abs
  have h4 : Rust.withPanics (tripleRatchetExterns C ctl abs) fmtWriteName =
      abs fmtWriteName := Option.some.inj (congrArg (·[3]?) habs)
  simpa [HookSat, h4] using hW

theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

open ProofLib.ProgramReflection

end ProtocolAddressDisplay

open ProtocolAddressDisplay

attribute [local irreducible] Program.fnAddr Program.fnOff
/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) parameterized by `hwrite`. -/
theorem addrDisplay_placed_ok_of_contract [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hwrite : subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (lsρ lsFmtWriteSym) (fmtWriteSpec A)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (addrDisplaySpec A) := by
  simp only [addrDisplaySpec, stackAt_addrDisplay]
  cells_unfold
  wpp_init x s0
  obtain ⟨f, v, vt, bs⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := lsρ lsFmtWriteSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (v, bs))
    (ret_pc := (blkPl_215).base + bv% (60)) hwrite
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (rfl : v = v)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  simp only [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
  apply SepWP.exists_elim; intro bs'
  apply SepWP.pure_elim; rintro ⟨hw0, htr⟩
  wp_steps
  wp_done

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) meets `addrDisplaySpec A`. -/
theorem addrDisplay_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hW : HookSat H lsFmtWriteSym (fmtWriteSpec A)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (addrDisplaySpec A) :=
  addrDisplay_placed_ok_of_contract A H (ls_hook_ok_of_mem hW)

end CryptoVerification.LibsignalTripleRatchet
