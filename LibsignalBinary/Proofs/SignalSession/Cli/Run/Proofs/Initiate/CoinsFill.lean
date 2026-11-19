/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.Apply
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `signal_session_coins_fill` Separation-Logic Contract

Proves `coinsFillSpec` for `signal_session_coins_fill(dst, len)` against `coinsCursorAt` on both
`initProg img W` (`signal_session_coins_fill_ok`) and `initProgExt img ext`
(`signal_session_coins_fill_ext_ok`), combining the copied prefix and zero-padded suffix into
`((padCoins coins).toList.drop pos).take len`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev cliCoinsFillName : String := "signal_session_coins_fill"

/-- Stack budget for `signal_session_coins_fill` (`0x20` frame + `extHookStack`). -/
abbrev cliCoinsFillStack : Nat := 0x20 + extHookStack

/-! ## Specification and proof -/

/-- Ghost state for a `signal_session_coins_fill(dst, len)` call over `padCoins coins`. -/
structure CoinsFillGhost where
  dst : BitVec 64
  len : Nat
  p₀ : BitVec 64
  coins : List (BitVec 8)
  pos : Nat

set_option maxRecDepth 200000

section Helpers

open ProofLib.ProgramReflection CryptoVerification.CodeLayout

private theorem coinsFill_stack_split (sp : BitVec 64) {stk : Nat}
    (hstk : cliCoinsFillStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      stackAt (sp - 80#64) 0 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
  have hge : 80 ≤ stk := by
    unfold cliCoinsFillStack extHookStack at hstk
    omega
  have hsplit : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗ stackAt sp 80 := by
    have hs0 := stackAt_split_bottom sp 80 (stk - 80) (by omega)
    rwa [Nat.add_sub_of_le hge] at hs0
  have h1 := ProofLib.stackAt_split_cells sp 0 10 (by omega)
  change stackAt sp 80 = stackAt (sp - 80#64) 0 ∗ cells (sp - 80#64) 10 at h1
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [hsplit, h1, hc10]

private theorem coinsFill_bv_sub {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [BitVec.le_def, BitVec.toNat_ofNat]
    omega

private theorem coinsFill_coins_split (p₀ : BitVec 64) (coins : List (BitVec 8))
    (m k : Nat) (hmk : m + k ≤ coins.length) :
    (p₀ ↦ₛ coins) =
      (p₀ ↦ₛ coins.take m) ∗
      ((p₀ + BitVec.ofNat 64 m) ↦ₛ (coins.drop m).take k) ∗
      ((p₀ + BitVec.ofNat 64 (m + k)) ↦ₛ coins.drop (m + k)) := by
  have heq : coins = coins.take m ++ ((coins.drop m).take k ++ coins.drop (m + k)) := by
    have hdrop : (coins.drop m).drop k = coins.drop (m + k) := List.drop_drop
    rw [← hdrop, List.take_append_drop, List.take_append_drop]
  have hlm : (coins.take m).length = m := by simp; omega
  have hlk : ((coins.drop m).take k).length = k := by simp; omega
  conv => lhs; rw [heq]
  rw [pointsToBytes_append, hlm, pointsToBytes_append, hlk, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem coinsFill_slice_eq (coins : List (BitVec 8)) (pos len : Nat)
    (hpad : pos + len ≤ initiateTapeLen) :
    (coins.drop (min pos coins.length)).take (min (coins.length - min pos coins.length) len) ++
      List.replicate (len - min (coins.length - min pos coins.length) len) 0#8 =
      ((padCoins coins).toList.drop pos).take len := by
  have hpad_list : (padCoins coins).toList =
      coins.take initiateTapeLen ++ List.replicate (initiateTapeLen - coins.length) 0#8 := by
    simp [padCoins]
  apply List.ext_getElem
  · rw [hpad_list]
    simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate,
      initiateTapeLen] at hpad ⊢
    omega
  · intro i h1 h2
    have hi_lt : i < len := by
      rw [hpad_list] at h2
      simp only [List.length_take, List.length_drop, List.length_append,
        List.length_replicate, initiateTapeLen] at h2 hpad
      omega
    simp only [hpad_list, List.getElem_take, List.getElem_drop]
    by_cases hik : i < min (coins.length - min pos coins.length) len
    · have hlt_t : pos + i < (coins.take initiateTapeLen).length := by
        simp only [List.length_take]; omega
      rw [List.getElem_append_left (by simp only [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop,
        List.getElem_append_left hlt_t, List.getElem_take]
      congr 1
      omega
    · have hge_c : (coins.take initiateTapeLen).length ≤ pos + i := by
        simp only [List.length_take]; omega
      rw [List.getElem_append_right (by simp only [List.length_take, List.length_drop]; omega),
        List.getElem_replicate, List.getElem_append_right hge_c, List.getElem_replicate]

private theorem coinsFill_csel_eq (cLen pos len : Nat)
    (hc : cLen < 2 ^ 64) (hl : len < 2 ^ 64) :
    (if (BitVec.ofNat 64 (cLen - min pos cLen)).ult (BitVec.ofNat 64 len) = true then
      BitVec.ofNat 64 (cLen - min pos cLen)
    else BitVec.ofNat 64 len) =
      BitVec.ofNat 64 (min (cLen - min pos cLen) len) := by
  have hleft : cLen - min pos cLen < 2 ^ 64 := by omega
  have hult : (BitVec.ofNat 64 (cLen - min pos cLen)).ult (BitVec.ofNat 64 len) =
      decide (cLen - min pos cLen < len) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hl]
  rw [hult]
  by_cases hlt : cLen - min pos cLen < len
  · simp [hlt, Nat.min_eq_left (Nat.le_of_lt hlt)]
  · simp [hlt, Nat.min_eq_right (Nat.le_of_not_lt hlt)]

private theorem coinsFill_dst_join (dst : BitVec 64) (coins : List (BitVec 8))
    (pos len : Nat) (hpad : pos + len ≤ initiateTapeLen) (R' : SepProp) :
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
    ((dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ R') := by
  have hmid : ((coins.drop (min pos coins.length)).take
      (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hmerge :
      ((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len)) =
      (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) := by
    rw [sepConj_comm]
    conv => lhs; arg 2; arg 1; arg 2; rw [← hmid]
    rw [← pointsToBytes_append, coinsFill_slice_eq coins pos len hpad]
  rw [← sepConj_assoc, hmerge]

private def coinsFillMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗
      (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (dst ↦ₛ bs) ∗
      (src ↦ₛ bs)

private def coinsFillMemzeroSpec : Spec (BitVec 64 × Nat) where
  pre := fun (p, n) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      BitVec.truncate 8 (s0.readReg32 .x1) = 0#8 ∧
      (s0.readReg64 .x2).toNat = n ∧
      n ≤ 2 ^ 64⌝ ∗
      memRegion p n
  post := fun (p, n) s0 sf =>
    ⌜sf.readReg64 .x0 = p ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (p ↦ₛ List.replicate n 0#8)

end Helpers

section FixedTable

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

end FixedTable

/-! ## Extern-parameterized contract (`CliExternsOk`) -/

theorem coinsFill_memHookStack_fits :
    80 + CliExt.memHookStack ≤ cliCoinsFillStack := by
  dsimp only [CliExt.memHookStack, cliCoinsFillStack, extHookStack]; decide

section ExtHelpers

open ProofLib.ProgramReflection CryptoVerification.CodeLayout

private theorem coinsFill_stack_split_ext (sp : BitVec 64) {stk : Nat}
    (hstk : cliCoinsFillStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - (80 + CliExt.memHookStack)) ∗
      stackAt (sp - 80#64) CliExt.memHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
  have hfit := coinsFill_memHookStack_fits
  have hge : 80 + CliExt.memHookStack ≤ stk := Nat.le_trans hfit hstk
  have hsplit : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - (80 + CliExt.memHookStack)) ∗
        stackAt sp (80 + CliExt.memHookStack) := by
    have hs0 := stackAt_split_bottom sp (80 + CliExt.memHookStack)
      (stk - (80 + CliExt.memHookStack)) (by dsimp only [CliExt.memHookStack] at *; omega)
    rwa [Nat.add_sub_of_le hge] at hs0
  have h1 := ProofLib.stackAt_split_cells sp CliExt.memHookStack 10
    (by dsimp only [CliExt.memHookStack]; omega)
  change stackAt sp (80 + CliExt.memHookStack) =
      stackAt (sp - 80#64) CliExt.memHookStack ∗ cells (sp - 80#64) 10 at h1
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [hsplit, h1, hc10]

private theorem coinsFill_dst_join_ext (dst : BitVec 64) (coins : List (BitVec 8))
    (pos len : Nat) (hpad : pos + len ≤ initiateTapeLen) (S R' : SepProp) :
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      S ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
    ((dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ S ∗ R') := by
  have hmid : ((coins.drop (min pos coins.length)).take
      (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hmerge :
      ((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len)) =
      (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) := by
    rw [sepConj_comm]
    conv => lhs; arg 2; arg 1; arg 2; rw [← hmid]
    rw [← pointsToBytes_append, coinsFill_slice_eq coins pos len hpad]
  calc
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      S ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
      (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len))) ∗ S ∗ R' := by ac_rfl
    _ = (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ S ∗ R' := by rw [hmerge]

private def coinsFillMemcpyExtSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗
      (src ↦ₛ bs) ∗
      stackAt s0.sp CliExt.memHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (dst ↦ₛ bs) ∗
      (src ↦ₛ bs) ∗
      stackAt s0.sp CliExt.memHookStack

private def coinsFillMemzeroExtSpec : Spec (BitVec 64 × Nat) where
  pre := fun (p, n) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      BitVec.truncate 8 (s0.readReg32 .x1) = 0#8 ∧
      (s0.readReg64 .x2).toNat = n⌝ ∗
      memRegion p n ∗
      stackAt s0.sp CliExt.memHookStack
  post := fun (p, n) s0 sf =>
    ⌜sf.readReg64 .x0 = p ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (p ↦ₛ List.replicate n 0#8) ∗
      stackAt s0.sp CliExt.memHookStack

end ExtHelpers

section ExtBody

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

end ExtBody

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
