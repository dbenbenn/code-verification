/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `try_decrypt_from_record::{closure#0}` (`0x381ac`)

Proves fixed-image (`log_closure_ok`) and relocatable `[LibsignalFullPlacement]`
(`log_closure_placed_ok`, `log_closure_coins_placed_ok`) contracts for the log-off fast path of
`try_decrypt_from_record::{closure#0}` (blocks `159` and `462`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_closure (sp : BitVec 64) :
    stackAt sp closureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2)) ∗
      stackAt (sp - 64#64) 296 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) := by
  have h1 := stackAt_split_cells sp 320 8 (by decide)
  have h2 := stackAt_split_bottom (sp - 64#64) 296 24 (by decide)
  have hsub : (sp - 64#64) - BitVec.ofNat 64 (296 + 24) = sp - 384#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (24 : Nat) = 8 * 3 by rfl, memRegion_cells (sp - 384#64) 3 (by decide)] at h2
  change stackAt sp closureStack = stackAt (sp - 64#64) 320 ∗ cells (sp - 64#64) 8 at h1
  have hc3 : cells (sp - 384#64) 3 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2)) := by
    cells_unfold
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) := by
    cells_unfold
  rw [h1, h2, hc3, hc8, sepConj_assoc]

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_logFilterSym (pl : Arm64.Obj.MultiPlacement) :
    libsignalSessionLib.resolve pl lsLogFilterSym = pl.ρ lsLogFilterSym :=
  ls_resolve_data (by decide +kernel)

/-- Relocatable `MAX_LOG_LEVEL_FILTER == 0` assertion (`lsLogFilterAddr ↦₆₄ 0#64`). -/
@[expose] def lsLogOff [LibsignalPlacement] : SepProp :=
  lsLogFilterAddr ↦₆₄ 0#64

/-- Relocatable specification of `try_decrypt_from_record::{closure#0}` on the log-off fast path. -/
@[expose] def logClosurePlacedSpec [LibsignalPlacement] : Spec Unit where
  pre := fun _ s => lsLogOff ∗ stackAt s.sp closureStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ lsLogOff ∗ stackAt s0.sp closureStack

/-- Block `159`: `try_decrypt_from_record::<HookRng>::{closure#0}` meets
`logClosurePlacedSpec` under `[LibsignalFullPlacement]`. -/
theorem log_closure_placed_ok [LibsignalFullPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_159).rebase (blkPl_159).base H) (blkPl_159).base
      logClosurePlacedSpec := by
  unfold logClosurePlacedSpec lsLogOff lsLogFilterAddr
  simp only [stackAt_closure, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  wp_steps
  wp_done

/-- Block `462`: `try_decrypt_from_record::<Coins>::{closure#0}` meets
`logClosurePlacedSpec` under `[LibsignalFullPlacement]`. -/
theorem log_closure_coins_placed_ok [LibsignalFullPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_462).rebase (blkPl_462).base H) (blkPl_462).base
      logClosurePlacedSpec := by
  unfold logClosurePlacedSpec lsLogOff lsLogFilterAddr
  simp only [stackAt_closure, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  wp_steps
  wp_done

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
