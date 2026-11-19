/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# V1 Path Step Lemmas for `spqr::initial_state`

Basic-block and callee-bridge lemmas for the `.v1` execution path (`0x542d0..0x5447c`) of
`spqr::initial_state`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.CodeLayout
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Callee-saved register save area at `[s0.sp - 96 .. s0.sp)` (`96` bytes = 12 words). -/
@[expose] def h61s_initialStateSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem h61s_initialStateSavedCells_entails_memRegion (s0 : State) :
    h61s_initialStateSavedCells s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold h61s_initialStateSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))))))))
  exact Entails.of_eq (by simp only [arm64_norm])

theorem stackAt_initialStateExt_split_base (sp : BitVec 64) :
    stackAt sp initialStateStackExt =
      stackAt sp initialStateStack ∗ memRegion (sp - 19408#64) 1232 := by
  change memRegion (sp - 19408#64) 19408 =
    memRegion (sp - 18176#64) 18176 ∗ memRegion (sp - 19408#64) 1232
  rw [ProofLib.memRegion_split' (b := sp - 19408#64) (n := 1232) (k := 18176)
        (b' := sp - 18176#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem h61s_stackAt_split_gen (sp : BitVec 64) (calleeStack : Nat)
    (hmax : calleeStack + 496 ≤ 2 ^ 64 := by decide) :
    stackAt sp (calleeStack + 496) =
      stackAt (sp - 496#64) calleeStack ∗ memRegion (sp - 496#64) 40 ∗
      memRegion (sp - 456#64) 352 ∗ memRegion (sp - 104#64) 8 ∗ cells (sp - 96#64) 12 := by
  have h1 := ProofLib.stackAt_split_cells sp (calleeStack + 400) 12
    (by change (calleeStack + 400) + 96 ≤ 2 ^ 64; omega)
  have h1b : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  rw [show calleeStack + 496 = (calleeStack + 400) + 8 * 12 by omega, h1, h1b]
  have h2 : stackAt (sp - 96#64) (calleeStack + 400) =
      memRegion ((sp - 496#64) - BitVec.ofNat 64 calleeStack) calleeStack ∗
      memRegion (sp - 496#64) 40 ∗ memRegion (sp - 456#64) 352 ∗ memRegion (sp - 104#64) 8 := by
    unfold stackAt
    have hsub1 : (sp - 96#64) - BitVec.ofNat 64 (calleeStack + 400) =
        (sp - 496#64) - BitVec.ofNat 64 calleeStack := by
      rw [BitVec.ofNat_add, show BitVec.ofNat 64 400 = 400#64 from rfl]; bv_omega
    rw [hsub1,
        ProofLib.memRegion_split' (b := (sp - 496#64) - BitVec.ofNat 64 calleeStack)
          (n := calleeStack) (k := 400) (b' := sp - 496#64) (by omega)
          (by bv_omega) (by omega),
        ProofLib.memRegion_split' (b := sp - 496#64) (n := 40) (k := 360)
          (b' := sp - 456#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 456#64) (n := 352) (k := 8)
          (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  rw [h2]; unfold stackAt; ac_rfl

theorem h61s_stack_restore_gen (s0 : State) (calleeStack : Nat)
    (hmax : calleeStack + 496 ≤ 2 ^ 64 := by decide) :
    stackAt (s0.sp - 496#64) calleeStack ∗ memRegion (s0.sp - 496#64) 40 ∗
    memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
    h61s_initialStateSavedCells s0 ⊢ stackAt s0.sp (calleeStack + 496) := by
  rw [h61s_stackAt_split_gen s0.sp calleeStack hmax,
      ← ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (h61s_initialStateSavedCells_entails_memRegion s0))))

theorem stackAt_callee_split (sp : BitVec 64) (calleeStack subStack : Nat)
    (hle : subStack ≤ calleeStack := by decide)
    (hmax : calleeStack ≤ 2 ^ 64 := by decide) :
    stackAt sp calleeStack =
      stackAt sp subStack ∗
        memRegion (sp - BitVec.ofNat 64 calleeStack) (calleeStack - subStack) := by
  have h := ProofLib.stackAt_split_bottom sp subStack (calleeStack - subStack) (by omega)
  rw [Nat.add_sub_of_le hle] at h
  rw [h, sepConj_comm]

theorem memRegion_ret_32_split (ret : BitVec 64) :
    memRegion ret 32 = (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗ memRegion (ret + 8#64) 24 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 24)
        (b' := ret + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight ret]

theorem memRegion_pqState_split (a : BitVec 64) :
    memRegion a 352 =
      cells a 3 ∗
      (∃∗ v0 : BitVec 32, (a + 0x18#64) ↦₃₂ v0) ∗ (∃∗ v1 : BitVec 32, (a + 0x1c#64) ↦₃₂ v1) ∗
      (∃∗ v2 : BitVec 32, (a + 0x20#64) ↦₃₂ v2) ∗ (∃∗ v3 : BitVec 32, (a + 0x24#64) ↦₃₂ v3) ∗
      (∃∗ v4 : BitVec 32, (a + 0x28#64) ↦₃₂ v4) ∗ memRegion (a + 0x2c#64) 4 ∗
      (∃∗ w6 : BitVec 64, (a + 0x30#64) ↦₆₄ w6) ∗ memRegion (a + 0x38#64) 72 ∗
      memRegion (a + 0x80#64) optProtoInnerStateSize := by
  change memRegion a 352 =
    cells a 3 ∗
    (∃∗ v0 : BitVec 32, (a + 0x18#64) ↦₃₂ v0) ∗ (∃∗ v1 : BitVec 32, (a + 0x1c#64) ↦₃₂ v1) ∗
    (∃∗ v2 : BitVec 32, (a + 0x20#64) ↦₃₂ v2) ∗ (∃∗ v3 : BitVec 32, (a + 0x24#64) ↦₃₂ v3) ∗
    (∃∗ v4 : BitVec 32, (a + 0x28#64) ↦₃₂ v4) ∗ memRegion (a + 0x2c#64) 4 ∗
    (∃∗ w6 : BitVec 64, (a + 0x30#64) ↦₆₄ w6) ∗ memRegion (a + 0x38#64) 72 ∗
    memRegion (a + 0x80#64) 224
  rw [ProofLib.memRegion_split' (b := a) (n := 24) (k := 328) (b' := a + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x18#64) (n := 4) (k := 324) (b' := a + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x1c#64) (n := 4) (k := 320) (b' := a + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x20#64) (n := 4) (k := 316) (b' := a + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x24#64) (n := 4) (k := 312) (b' := a + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x28#64) (n := 4) (k := 308) (b' := a + 0x2c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x2c#64) (n := 4) (k := 304) (b' := a + 0x30#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x30#64) (n := 8) (k := 296) (b' := a + 0x38#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x38#64) (n := 72) (k := 224) (b' := a + 0x80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells a 3 (by decide),
      ProofLib.memRegion_four (a + 0x18#64), ProofLib.memRegion_four (a + 0x1c#64),
      ProofLib.memRegion_four (a + 0x20#64), ProofLib.memRegion_four (a + 0x24#64),
      ProofLib.memRegion_four (a + 0x28#64), ProofLib.memRegion_eight (a + 0x30#64)]

theorem testBit63_ofNat_of_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hbv : BitVec.ofNat 64 n < 0x100000000#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h
  revert hbv; generalize BitVec.ofNat 64 n = v; bv_bits

/-! ## 2. Prologue (`+0 -> +232`) and Epilogue (`+396 -> +424 -> ret`) -/

theorem vecU8Buf_nil (A : RustAlloc) : (emp : SepProp) ⊢ RustHeap.vecU8Buf A 0#64 1#64 [] := by
  unfold RustHeap.vecU8Buf
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

theorem vecU8Buf_nonempty (A : RustAlloc) (ptr : BitVec 64) (bs : Bytes)
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs) ⊢
      RustHeap.vecU8Buf A (BitVec.ofNat 64 bs.length) ptr bs := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h
    rw [htoNat] at this; change bs.length = 0 at this; omega
  unfold RustHeap.vecU8Buf
  refine Entails.pure_right ⟨by omega, by omega, hptr⟩ ?_
  rw [ite_eq_right_iff.mpr (fun h => absurd h hcap_ne),
    htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  exact Entails.refl _

@[expose] def initInnerSpecGen (calleeStack : Nat) (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec InitInnerGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp calleeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp calleeStack
  onPanic := fun _ s0 sf => initInnerOnPanic s0 sf

theorem csel_maxJump_eq (cp : ChainParams) :
    BitVec.truncate 32
      (if (cp.maxJump == 25000#32) = true then 0#64 else BitVec.truncate 64 cp.maxJump) =
      cp.intoPb.maxJump := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxJump = 25000#32 <;> simp [h]

theorem csel_maxOoo_eq (cp : ChainParams) :
    BitVec.truncate 32
      (if (cp.maxOooKeys == 2000#32) = true then 0#64 else BitVec.truncate 64 cp.maxOooKeys) =
      cp.intoPb.maxOooKeys := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxOooKeys = 2000#32 <;> simp [h]

attribute [local wp_norm] csel_maxJump_eq csel_maxOoo_eq

theorem readReg32_of_eq {s1 s2 : State} {r : Reg} (h : s2.readReg64 r = s1.readReg64 r) :
    s2.readReg32 r = s1.readReg32 r :=
  congrArg (BitVec.truncate 32) h

end CryptoVerification.SpqrV1.Top.InitialState
