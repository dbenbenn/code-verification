/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesX
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.StartGroupX
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem skipField_at_depth_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hSlowCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 293)
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)))
    (hSliceCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 76)
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A depth (fun _ => True))) := by
  induction depth with
  | zero => exact skipField_depth_zero_placed_ok_x hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipFieldX_or_lscl (skipField_varint_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth)
        (subroutine_ok_skipFieldX_or_lscl (skipField_sixtyFourBit_placed_ok_x hFromCall d hdepth)
          (subroutine_ok_skipFieldX_or_lscl (skipField_lengthDelimited_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth)
            (subroutine_ok_skipFieldX_or_lscl (skipField_startGroup_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth hrec)
              (subroutine_ok_skipFieldX_or_lscl (skipField_endGroup_placed_ok_x hFromCall d hdepth)
                (skipField_thirtyTwoBit_placed_ok_x hFromCall d hdepth)))))
    refine subroutine_ok_skipFieldX_imp_lscl (fun x _ => ?_) hAll
    cases x.wt <;> simp

namespace SkipFieldCalls

theorem skipFieldSpecAtX_reaches_outcome_eq_lscl [LibsignalPlacement] (prog : Program) (A : RustAlloc)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)) x R s0 s0 =
      reaches_outcome prog (withLsCodeLoaded lsmpl (skipFieldSpecX A)) x R s0 s0 := by
  have hpost : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).post x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).post x := by
    funext s0' sf'
    dsimp only [withLsCodeLoaded, skipFieldSpecAtX, skipFieldSpecX]
    cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs <;> rfl
  have hpan : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).onPanic x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).onPanic x := rfl
  have hexit : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).onExit x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).onExit x := rfl
  have hoom : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).onOom x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).onOom x := rfl
  have hout : ∀ sf,
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)) x R s0 sf =
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipFieldSpecX A)) x R s0 sf := by
    intro sf; dsimp only [SubroutineOutcome]; rw [hpost, hpan, hexit, hoom]
  exact propext ⟨fun h => h.mono_outcome (fun sf hs => hout sf ▸ hs),
    fun h => h.mono_outcome (fun sf hs => (hout sf).symm ▸ hs)⟩

theorem subroutine_ok_skipFieldSpecX_of_at_depth_lscl [LibsignalPlacement] {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : ∀ depth, depth < 2 ^ 32 → subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipFieldSpecAtX A depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipFieldSpecX A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipFieldSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  rw [← skipFieldSpecAtX_reaches_outcome_eq_lscl prog A (fun _ => True) x R s0]
  refine (h x.depth hdepth).to_outcome x R s0 hpc hrun ?_ hsp
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

end SkipFieldCalls

theorem skipField_placed_ok_of_contracts_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A decodeErrorHookStackX))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A))) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecX A)) :=
  SkipFieldCalls.subroutine_ok_skipFieldSpecX_of_at_depth_lscl
    (skipField_at_depth_placed_ok_x
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H)
        (subroutine_ok_withLsCodeLoaded_of_plain hFrom))
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H) hSlow)
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H) hSlice))

theorem skipField_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecX A)) :=
  skipField_placed_ok_of_contracts_x
    (decode_error_from_placed_ok_x hshim halloc hpanic)
    (decode_varint_slow_placed_ok_x hshim halloc hpanic)
    (decode_varint_slice_placed_ok_x hshim halloc hpanic)

end CryptoVerification.LibsignalTripleRatchet.Prost

