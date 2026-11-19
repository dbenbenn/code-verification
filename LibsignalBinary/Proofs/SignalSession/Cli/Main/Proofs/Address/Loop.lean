/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Alloc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Multi-Digit Accumulator Loop for `signal_session::address`
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

@[simp, arm64_norm] theorem reg_x0_norm : Reg.x0 = Reg.gpr 0#5 := rfl
@[simp, arm64_norm] theorem reg_x1_norm : Reg.x1 = Reg.gpr 1#5 := rfl
@[simp, arm64_norm] theorem reg_x2_norm : Reg.x2 = Reg.gpr 2#5 := rfl
@[simp, arm64_norm] theorem reg_x8_norm : Reg.x8 = Reg.gpr 8#5 := rfl
@[simp, arm64_norm] theorem reg_x9_norm : Reg.x9 = Reg.gpr 9#5 := rfl
@[simp, arm64_norm] theorem reg_x10_norm : Reg.x10 = Reg.gpr 10#5 := rfl
@[simp, arm64_norm] theorem reg_x19_norm : Reg.x19 = Reg.gpr 19#5 := rfl
@[simp, arm64_norm] theorem reg_x20_norm : Reg.x20 = Reg.gpr 20#5 := rfl
@[simp, arm64_norm] theorem reg_x21_norm : Reg.x21 = Reg.gpr 21#5 := rfl
@[simp, arm64_norm] theorem reg_x22_norm : Reg.x22 = Reg.gpr 22#5 := rfl
@[simp, arm64_norm] theorem reg_x24_norm : Reg.x24 = Reg.gpr 24#5 := rfl

theorem zext64_ofNat32 (n : Nat) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).zeroExtend 64 = BitVec.ofNat 64 n := by
  clear * - hn; bv_omega

@[expose] def stripPlus (dev : List (BitVec 8)) : List (BitVec 8) :=
  match dev with
  | c :: r => if c = 43#8 then r else dev
  | [] => []

@[simp, arm64_norm]
theorem trunc32_zext64_and (u : BitVec 32) (m : BitVec 64) :
    BitVec.truncate 32 (u.zeroExtend 64 &&& m) = u &&& BitVec.truncate 32 m := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem trunc32_zext64_shl1 (u : BitVec 32) :
    BitVec.truncate 32 (u.zeroExtend 64 <<< 1) = u <<< 1 := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem trunc32_zext8_shl2 (b : BitVec 8) :
    BitVec.truncate 32 (b.zeroExtend 64 <<< 2) = b.zeroExtend 32 <<< 2 := by
  revert b; decide

@[simp, arm64_norm]
theorem trunc32_zext64_shr8 (u : BitVec 32) :
    BitVec.truncate 32 (u.zeroExtend 64 >>> 8) = u >>> 8 := by
  ext i hi
  by_cases h8 : 8 + i < 32
  · simp [h8, show 8 + i < 64 by omega]
  · simp [show 8 + i < 64 by omega, BitVec.getLsbD_eq_getElem]

@[simp, arm64_norm]
theorem trunc8_zext32_mask (u : BitVec 32) :
    (u.truncate 8).zeroExtend 32 = u &&& 0xff#32 := by
  ext i hi
  by_cases h8 : i < 8
  · have hmask : (0xff#32)[i] = true := by revert i; decide
    simp [hi, h8, hmask]
  · have hmask : (0xff#32)[i] = false := by
      have hlt : i < 32 := hi
      revert h8 hlt; revert i; decide
    simp [hi, h8, hmask]

@[simp, arm64_norm]
theorem extractLsb0_zext64 (u : BitVec 32) :
    BitVec.extractLsb' 0 1 (u.zeroExtend 64) = BitVec.truncate 1 u := by
  ext i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp

theorem loop_mul10_eq0 (acc : Nat) (hacc : acc ≤ 255) :
    (((((BitVec.ofNat 32 acc &&& 0xff#32) +
        ((BitVec.ofNat 32 acc &&& 0xff#32) <<< 2)) <<< 1) &&& 0xf00#32) == 0#32) =
      decide (acc ≤ 25) := by
  have hfin : ∃ k : Fin 256, k.val = acc := ⟨⟨acc, by omega⟩, rfl⟩
  rcases hfin with ⟨k, rfl⟩
  revert k; decide

theorem carry_bit1_of_acc' (acc' : Nat) (hacc' : acc' ≤ 259) :
    BitVec.truncate 1 (BitVec.ofNat 32 acc' >>> 8) =
      if acc' ≤ 255 then 0#1 else 1#1 := by
  have hfin : ∃ k : Fin 260, k.val = acc' := ⟨⟨acc', by omega⟩, rfl⟩
  rcases hfin with ⟨k, rfl⟩
  revert k; decide

theorem parseUnsigned_acc26_none {dev ds done : List (BitVec 8)} {b : BitVec 8}
    {rest : List (BitVec 8)}
    (hds : ds = stripPlus dev)
    (hsplit : ds = done ++ (b :: rest))
    (hacc : 26 ≤ done.foldl (fun a c => 10 * a + (c.toNat - 48)) 0) :
    parseUnsigned 255 dev = none := by
  have h256 : 256 ≤ (done ++ [b]).foldl (fun a c => 10 * a + (c.toNat - 48)) 0 := by
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]; omega
  exact parseUnsigned_overflow_prefix hds (rem := rest) (by simp [hsplit]) h256

theorem parseUnsigned_some_of_all_digits {dev ds : List (BitVec 8)}
    (hds : ds = stripPlus dev)
    (hne : ds ≠ [])
    (hdig : ∀ c ∈ ds, isDigit c = true)
    (hle : ds.foldl (fun a c => 10 * a + (c.toNat - 48)) 0 ≤ 255) :
    parseUnsigned 255 dev =
      some (ds.foldl (fun a c => 10 * a + (c.toNat - 48)) 0) := by
  rw [parseUnsigned_of_ds 255 dev ds hds]
  have hany : ds.any (fun c => !isDigit c) = false :=
    List.any_eq_false.mpr fun c hc => by simp [hdig c hc]
  simp [hne, hany, hle]

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
