/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import ProofLib.SepLogic.WP.Apply
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection.Variant.TrapTransfer
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Proofs for `<ProtocolAddress as Display>::fmt`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`addrDisplayEnvSpec` and
`addrDisplaySpec`) for `<ProtocolAddress as Display>::fmt` against `fmtWriteProtoAddrLsEnvSpec`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement blkPC_215 blkPl_215 lsFmtWriteSym ls_hook_ok_of_mem lsmpl lsρ
)
open CryptoVerification.LibsignalTripleRatchet.ProtocolAddressDisplay (stackAt_addrDisplay)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extHookStack subroutine_ok_withLsCodeRoLoaded_rodata' withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSessionRepr (vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (
  CliFmtWriteProtoAddrCall LsRetAddrFmtWrite cliFmtWriteProtoAddrSpec cliStringDisplayShimBlocks
  dotTplBytes fmtWriteProtoAddrLsEnvSpec lsDeviceIdDisplayBlock
  lsRetAddrFmtWrite_blockPlacement_base_add withLsRetFmtWrite
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  AddrDisplayGhost addrDisplayEnvSpec
)
open VerifiedLibraries.RustStd (
  fmtArgEntriesAt fmtArgumentsAt fmtRef8 fmtRefString fmtSrcBytes
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sp_sub_48_lsb0_false {s0 : State} (hal : s0.spAligned = true) :
    (s0.sp - 48#64).getLsbD 0 = false := by
  dsimp only [State.spAligned] at hal
  rw [beq_iff_eq] at hal
  have h1 : (s0.sp - 48#64) &&& 1#64 = (s0.sp &&& 15#64) &&& 1#64 := by bv_kernel
  have h2 : (s0.sp - 48#64) &&& 1#64 = 0#64 := by rw [h1, hal]; rfl
  have h3 := congrArg (fun v : BitVec 64 => v.getLsbD 0) h2
  simpa [BitVec.getLsbD_and] using h3

private def protoAddrFrame (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  (if g.name.cap = 0 then emp
   else A.live g.name.ptr g.name.cap.toNat 1 ∗
     memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
       (g.name.cap.toNat - g.name.bytes.length)) ∗
  memRegion (a + 25#64) 7

private abbrev addrDisplayCall [LibsignalPlacement] (g : AddrDisplayGhost) (sp : BitVec 64) :
    CliFmtWriteProtoAddrCall where
  v := g.v
  cap0 := g.cap0
  ptr0 := g.ptr0
  x2 := lsρ "libsignal_core:.rodata.str1.1+0x10e"
  x3 := sp - 48#64
  namePtr := g.addrPtr
  nameCap := g.rem.name.cap
  nameDataPtr := g.rem.name.ptr
  shimBlock := 216
  devPtr := g.addrPtr + 24#64
  bs := g.bs
  nameBs := g.rem.name.bytes
  argsRo := false
  strRefRo := false
  strSrcRo := false
  devRo := false
  dev := g.rem.device
  vtKind := g.vtKind

private theorem protocolAddressAt_entails_clientSep [LibsignalPlacement] (A : RustAlloc)
    (g : AddrDisplayGhost) (sp : BitVec 64) :
    protocolAddressAt A g.rem g.addrPtr ⊢
      (addrDisplayCall g sp).clientSep ∗ protoAddrFrame A g.rem g.addrPtr := by
  unfold protocolAddressAt vecGhostAt vecU8At vecHeader protoAddrFrame addrDisplayCall
    CliFmtWriteProtoAddrCall.clientSep fmtRefString fmtSrcBytes fmtRef8 Arm64.Rust.vecHeader
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hcap : g.rem.name.cap = 0
  · by_cases hnil : g.rem.name.bytes = []
    · simp only [hcap, ↓reduceIte, hnil, pointsToBytes_nil]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [hcap, ↓reduceIte]
      refine Entails.trans (Entails.of_eq
        (Q := ⌜g.rem.name.bytes.length ≤ BitVec.toNat 0 ∧
          BitVec.toNat 0 < 2 ^ 63 ∧ g.rem.name.ptr ≠ 0⌝ ∗
          (g.addrPtr ↦₆₄ 0 ∗ (g.addrPtr + 8#64) ↦₆₄ g.rem.name.ptr ∗
            (g.addrPtr + 16#64) ↦₆₄ BitVec.ofNat 64 g.rem.name.bytes.length ∗
            emp ∗ (g.addrPtr + 24#64) ↦₈ g.rem.device ∗
            memRegion (g.addrPtr + 25#64) 7))
        (by sep_ac_rfl)) ?_
      refine Entails.pure_left fun ⟨hle, _, _⟩ => False.elim (hnil ?_)
      apply List.eq_nil_of_length_eq_zero
      change g.rem.name.bytes.length ≤ 0 at hle
      omega
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem protocolAddressAt_of_clientSep [LibsignalPlacement] (A : RustAlloc)
    (g : AddrDisplayGhost) (sp : BitVec 64) :
    (addrDisplayCall g sp).clientSep ∗ protoAddrFrame A g.rem g.addrPtr ⊢
      protocolAddressAt A g.rem g.addrPtr := by
  unfold protocolAddressAt vecGhostAt vecU8At vecHeader protoAddrFrame addrDisplayCall
    CliFmtWriteProtoAddrCall.clientSep fmtRefString fmtSrcBytes fmtRef8 Arm64.Rust.vecHeader
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hcap : g.rem.name.cap = 0
  · by_cases hnil : g.rem.name.bytes = []
    · simp only [hcap, ↓reduceIte, hnil, pointsToBytes_nil]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [hcap, ↓reduceIte]
      refine Entails.trans (Entails.of_eq
        (Q := ⌜g.rem.name.bytes.length ≤ BitVec.toNat 0 ∧
          BitVec.toNat 0 < 2 ^ 63 ∧ g.rem.name.ptr ≠ 0⌝ ∗
          (g.addrPtr ↦₆₄ 0 ∗ (g.addrPtr + 8#64) ↦₆₄ g.rem.name.ptr ∗
            (g.addrPtr + 16#64) ↦₆₄ BitVec.ofNat 64 g.rem.name.bytes.length ∗
            g.rem.name.ptr ↦ₛ g.rem.name.bytes ∗
            (g.addrPtr + 24#64) ↦₈ g.rem.device ∗
            emp ∗ memRegion (g.addrPtr + 25#64) 7))
        (by sep_ac_rfl)) ?_
      refine Entails.pure_left fun ⟨hle, _, _⟩ => False.elim (hnil ?_)
      apply List.eq_nil_of_length_eq_zero
      change g.rem.name.bytes.length ≤ 0 at hle
      omega
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem fmtArgumentsAt_addrDisplayCall_eq [LibsignalPlacement]
    (g : AddrDisplayGhost) {sp : BitVec 64} (hlsb : (sp - 48#64).getLsbD 0 = false) :
    fmtArgumentsAt (addrDisplayCall g sp).argsRo (addrDisplayCall g sp).x2
      (addrDisplayCall g sp).x3 dotTplBytes (addrDisplayCall g sp).args =
      (lsρ "libsignal_core:.rodata.str1.1+0x10e" ↦ᵣ dotTplBytes) ∗
      ((sp - 48#64) ↦₆₄ g.addrPtr) ∗
      ((sp - 40#64) ↦₆₄ lsmpl.base 216) ∗
      ((sp - 32#64) ↦₆₄ (g.addrPtr + 24#64)) ∗
      ((sp - 24#64) ↦₆₄ lsmpl.base 214) := by
  dsimp only [addrDisplayCall, CliFmtWriteProtoAddrCall.args, lsDeviceIdDisplayBlock,
    fmtArgumentsAt, fmtArgEntriesAt]
  have h48_16 : sp - 48#64 + 16#64 = sp - 32#64 := by bv_kernel
  have h48_8 : sp - 48#64 + 8#64 = sp - 40#64 := by bv_kernel
  have h32_8 : sp - 32#64 + 8#64 = sp - 24#64 := by bv_kernel
  simp only [hlsb, Bool.false_eq_true, ↓reduceIte, h48_16, h48_8, h32_8, sepConj_emp, sepConj_assoc]

private def fmtWriteProtoAddrLsExternSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop) :
    Spec (CliFmtWriteProtoAddrCall × M.σ) where
  pre := fun (c, st0) s =>
    ⌜LsRetAddrFmtWrite (s.readReg64 .lr) ∧
      s.readReg64 .x0 = c.v ∧ s.readReg64 .x1 = c.vtKind.vtableAddr ∧
      s.readReg64 .x2 = c.x2 ∧ s.readReg64 .x3 = c.x3 ∧
      c.shimBlock ∈ cliStringDisplayShimBlocks ∧
      c.x3.getLsbD 0 = false ∧ c.nameBs.length < 2 ^ 60 ∧
      FitsEnv M lim st0 Env ∧ Env c.exactEvs⌝ ∗
      vecU8At A.repAlloc c.v c.cap0 c.ptr0 c.bs ∗
      fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
      c.clientSep ∗
      A.pool lim st0 s ∗ stackAt s.sp extHookStack
  post := (cliFmtWriteProtoAddrSpec M A lim (fun _ => Env)).post

private theorem fmtWriteProtoAddrLsEnvSpec_eq_extern [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop) :
    fmtWriteProtoAddrLsEnvSpec M A lim Env = fmtWriteProtoAddrLsExternSpec M A lim Env := by
  dsimp only [fmtWriteProtoAddrLsEnvSpec, withLsRetFmtWrite, cliFmtWriteProtoAddrSpec,
    fmtWriteProtoAddrLsExternSpec]
  congr 1; funext ⟨c, st0⟩ s
  rw [pure_sepConj_pure_assoc]

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) parameterized by `hwrite`
against `addrDisplayEnvSpec M A lim Env`. -/
theorem addrDisplay_placed_ok_of_contract [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)}
    (hwrite : subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (lsρ lsFmtWriteSym) (fmtWriteProtoAddrLsEnvSpec M A lim Env)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (withLsCodeRoLoaded lsmpl (addrDisplayEnvSpec M A lim Env)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata'
    (roSym := "libsignal_core:.rodata.str1.1+0x10e") (roBytes := dotTplBytes) (by decide) ?_
  simp only [addrDisplayEnvSpec, stackAt_addrDisplay]
  rw [fmtWriteProtoAddrLsEnvSpec_eq_extern] at hwrite
  dsimp only [fmtWriteProtoAddrLsExternSpec, cliFmtWriteProtoAddrSpec] at hwrite
  cells_unfold
  wp_init x s0
  rcases x with ⟨g, st⟩
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = g.addrPtr := by assumption
  have hx1 : s0.readReg64 .x1 = g.f := by assumption
  rw [hx0, hx1] at *
  have hx3_lsb : (s0.sp - 48#64).getLsbD 0 = false :=
    sp_sub_48_lsb0_false ‹s0.spAligned = true›
  have hlr_ok : LsRetAddrFmtWrite ((blkPl_215).base + 60#64) :=
    lsRetAddrFmtWrite_blockPlacement_base_add 215 60#64 (by decide) (by decide) (by decide)
  have hshim216 : (216 : Nat) ∈ cliStringDisplayShimBlocks := by decide
  refine SepWP.focus_weaken (protocolAddressAt_entails_clientSep A.repAlloc g s0.sp)
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ lsFmtWriteSym)
  simp only [State.setMem_setMem]
  have hargs_fold :
      (lsρ "libsignal_core:.rodata.str1.1+0x10e" ↦ᵣ dotTplBytes) ∗
      ((s0.sp - 48#64) ↦₆₄ g.addrPtr) ∗
      ((s0.sp - 40#64) ↦₆₄ lsmpl.base 216) ∗
      ((s0.sp - 32#64) ↦₆₄ (g.addrPtr + 24#64)) ∗
      ((s0.sp - 24#64) ↦₆₄ lsmpl.base 214) ⊢
      fmtArgumentsAt (addrDisplayCall g s0.sp).argsRo (addrDisplayCall g s0.sp).x2
        (addrDisplayCall g s0.sp).x3 dotTplBytes (addrDisplayCall g s0.sp).args :=
    Entails.of_eq (fmtArgumentsAt_addrDisplayCall_eq g hx3_lsb).symm
  refine SepWP.focus_weaken hargs_fold (by sep_focus) ?_
  wp_call hwrite (addrDisplayCall g s0.sp, st)
  rw [fmtArgumentsAt_addrDisplayCall_eq g hx3_lsb]
  refine SepWP.focus_weaken (protocolAddressAt_of_clientSep A.repAlloc g s0.sp)
    (by sep_focus) ?_
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) meets
`withLsCodeRoLoaded lsmpl (addrDisplayEnvSpec M A lim Env)`. -/
theorem addrDisplay_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)}
    (hW : HookSat H lsFmtWriteSym (fmtWriteProtoAddrLsEnvSpec M A lim Env)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (withLsCodeRoLoaded lsmpl (addrDisplayEnvSpec M A lim Env)) :=
  addrDisplay_placed_ok_of_contract (ls_hook_ok_of_mem hW)

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget
