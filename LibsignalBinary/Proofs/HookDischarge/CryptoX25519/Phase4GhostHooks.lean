/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.SpecBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
import ProofLib.Hoare.LibcHooks
import ProofLib.Hoare.Model
import ProofLib.Process.FsLemmas
import ProofLib.Process.OracleEq
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.DiffieHellmanProof
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretProof

/-!
# `linkedCallHookG` ghost hooks, consumer `HookOk`, and `GhostRowReplayOn`

Ghost-hook wrappers, state-preservation lemmas, consumer `HookOk` contracts, and
`GhostRowReplayOn` replay theorems for `lsPubFromSecretSym` (block `18`) and
`lsDiffieHellmanSym` (block `17`) of `x25519CliMultiLib`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj (CodeBlock MultiPlacedLib MultiPlacement)
open ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto PubKeyFn)
open CryptoGames.Ratchet (X25519Fn)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (pubFromSecretHook diffieHellmanHook
  pubFromSecretSpec diffieHellmanSpec pubFromSecretHook_ok diffieHellmanHook_ok
  DerivePublicKeyBytesCall derivePublicKeyBytesStackSpec extHookStack)
open CryptoVerification.SignalSession (CliHooks libsignalSessionLib cliExternsPlaced
  lsPubFromSecretSym lsDiffieHellmanSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (withStack pureByteFunctionSpec inputAfter dhSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FdsHiFrame PoolPreserved
  RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesStackBudgetSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (PreservesNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ActiveRealPre ActiveRealRun
  ExecFrozen SpecStripSInvariant SpecPreservesFsTrace keepFsTrace linkedCallHook
  satisfies_stripExecOutside stepsUntil_of_stripS_standard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (linkedCallHookG
  linkedCallHookG_eq_of_guard linkedCallHookG_eq_of_not_guard linkedCallHookG_eq_conj
  withStateGuard hookOk_linkedCallHookG linkedCallHookG_fs linkedCallHookG_fsT
  linkedCallHookG_activeRealPre_of_noException ghostExternReplaysOn_of_linkedCallHookG_liftVis)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
  (lsRetAddr624_of_noException_via_activeRealPre keepLr_false_of_noException_via_activeRealPre
   specStripSInvariant_withLsRet specPreservesFsTrace_withLsRet hookOk_withLsRet_of_simulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet hookOk_withLsRet
  subroutine_ok_withLsRet withLsRet_frameLeft withLsRet_pre_setPC withLsRet_outcome_setPC
  withLsRet_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_svc emptyStdProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowReplayOn)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (X25519BlockOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (x25519Ref x25519PubFromSecretRef)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs
  (publicKeyFromSecretSpec PublicKeyFromStaticSecretOk
   staticSecretDiffieHellmanSpec StaticSecretDiffieHellmanOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
  (X25519BlocksHookFree x25519MultiKeep strip_codeLoaded_x25519
   x25519CliMultiLib_externAt_none x25519BlocksHookFree_externAt_none_of_keep
   x25519_blockProgram_withTraceEq_keepsFs_withVmPreserved
   withRoOk X25519CliRoOk x25519CliRoOk_of_keepsFrozen x25519CliRoOk_stripExecOutside
   specSimulates_withVmPreserved specSimulates_keepsFs
   pubFromSecret_simulates_hooks_roOk diffieHellman_simulates_hooks_roOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.DiffieHellmanProof
  (static_secret_diffie_hellman_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretProof
  (public_key_from_static_secret_ok)

/-! ## 1. Pure Fallbacks (`pubFromSecretHook`, `diffieHellmanHook`) & Stacked Master Specs -/

/-- State preservation bundle satisfied by pure byte-writing `retHook` fallbacks. -/
@[expose] def PureFallbackPreserved (fb : State → State) : Prop :=
  ∀ s0 : State,
    VmPreserved s0 (fb s0) ∧
    (fb s0).fs = s0.fs ∧
    (fb s0).trace = s0.trace ∧
    (fb s0).tpidrEl0 = s0.tpidrEl0 ∧
    (fb s0).oracle = s0.oracle

private theorem retHook_writeBytes_preserved (addr : State → BitVec 64)
    (bs : State → List (BitVec 8)) :
    PureFallbackPreserved (retHook fun s => s.setMem (s.mem.writeBytes (addr s) (bs s))) := by
  intro s0
  refine ⟨⟨⟨rfl, rfl, rfl⟩, rfl, fun a => ?_, FdsHiFrame.of_fs_eq rfl⟩, rfl, rfl, rfl, rfl⟩
  simp only [retHook, State.setPC, State.setMem, Memory.perm_writeBytes]

theorem pubFromSecretHook_preserved (pubKey : PubKeyFn) :
    PureFallbackPreserved (pubFromSecretHook pubKey) :=
  retHook_writeBytes_preserved _ _

theorem diffieHellmanHook_preserved (X : X25519Fn) :
    PureFallbackPreserved (diffieHellmanHook X) :=
  retHook_writeBytes_preserved _ _

theorem pubFromSecretFallback_preserved :
    PureFallbackPreserved (pubFromSecretHook x25519PubFromSecretRef) :=
  pubFromSecretHook_preserved x25519PubFromSecretRef

theorem diffieHellmanFallback_preserved :
    PureFallbackPreserved (diffieHellmanHook x25519Ref) :=
  diffieHellmanHook_preserved x25519Ref

private theorem keepFsTrace_eq_of_preserved {fb : State → State}
    (hfb : PureFallbackPreserved fb) :
    keepFsTrace fb = fb := by
  funext s0
  have h := hfb s0
  unfold keepFsTrace
  cases hfb0 : fb s0
  have hfs := h.2.1
  have htr := h.2.2.1
  rw [hfb0] at hfs htr
  dsimp only at hfs htr
  subst hfs; subst htr
  rfl

private theorem hookOk_withStack_of_hookOk {α : Type} {fb : State → State} {spec : Spec α}
    (hok : HookOk fb spec) (stk : Nat)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    HookOk fb (withStack spec stk) :=
  fun x R s0 hrun hpre hsp => by
    dsimp only [withStack] at hpre
    rw [sepConj_assoc] at hpre
    obtain ⟨hkf, hsym, hout⟩ := hok x (stackAt s0.sp stk ∗ R) s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withStack]
      rwa [sepConj_assoc]
    · rw [hpan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · rw [hex] at he; exact (not_satisfies_false_sepConj he).elim
    · rw [hoom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem hookOk_keepsFs_of_hookOk {α : Type} {fb : State → State} {spec : Spec α}
    (hok : HookOk fb spec) (hfs : ∀ s0 : State, (fb s0).fs = s0.fs)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    HookOk fb (keepsFs spec) :=
  fun x R s0 hrun hpre hsp => by
    obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [keepsFs]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hfs s0, hpost⟩
    · rw [hpan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · rw [hex] at he; exact (not_satisfies_false_sepConj he).elim
    · rw [hoom] at ho; exact (not_satisfies_false_sepConj ho).elim

theorem pubFromSecretHook_keepsFs_withStack_ok (pubKey : PubKeyFn) (stk : Nat := extHookStack) :
    HookOk (pubFromSecretHook pubKey) (keepsFs (withStack (pubFromSecretSpec pubKey) stk)) :=
  hookOk_keepsFs_of_hookOk (hookOk_withStack_of_hookOk (pubFromSecretHook_ok pubKey) stk)
    (fun _ => rfl)

theorem diffieHellmanHook_keepsFs_withStack_ok (X : X25519Fn) (stk : Nat := extHookStack) :
    HookOk (diffieHellmanHook X) (keepsFs (withStack (diffieHellmanSpec X) stk)) :=
  hookOk_keepsFs_of_hookOk (hookOk_withStack_of_hookOk (diffieHellmanHook_ok X) stk)
    (fun _ => rfl)

theorem pubFromSecretFallback_ok (stk : Nat := 1904) :
    HookOk (pubFromSecretHook x25519PubFromSecretRef)
      (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)) :=
  pubFromSecretHook_keepsFs_withStack_ok x25519PubFromSecretRef stk

theorem diffieHellmanFallback_ok (stk : Nat := 1808) :
    HookOk (pubFromSecretHook x25519PubFromSecretRef)
      (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) 1904)) ∧
    HookOk (diffieHellmanHook x25519Ref)
      (keepsFs (withStack (diffieHellmanSpec x25519Ref) stk)) :=
  ⟨pubFromSecretFallback_ok 1904, diffieHellmanHook_keepsFs_withStack_ok x25519Ref stk⟩

/-! ## 2. Active State Guard (`x25519ActiveInvMem`, `x25519ActiveGuard`) -/

/-- Alias for `X25519CliRoOk` (`fe51_one`, `fe51_mont_a24`, and `ed25519_basepoint_table`). -/
abbrev X25519GhostRoOk (mpl : MultiPlacement) (m : Memory) : Prop :=
  X25519CliRoOk mpl m

/-- Memory invariant for `x25519CliMultiLib`: valid placement, all 19 blocks `CodeLoaded`, and
    all 3 `.rodata` sections `X25519CliRoOk`. -/
@[expose] def x25519ActiveInvMem (x25519Mpl : MultiPlacement) (m : Memory) : Prop :=
  x25519CliMultiLib.Placeable x25519Mpl ∧
  x25519CliMultiLib.CodeLoaded x25519Mpl m ∧
  X25519CliRoOk x25519Mpl m

/-- State guard for `linkedCallHookG` on `x25519CliMultiLib`. -/
@[expose] def x25519ActiveGuard (x25519Mpl : MultiPlacement) (s : State) : Prop :=
  x25519ActiveInvMem x25519Mpl s.mem

theorem x25519ActiveInvMem_stripExecOutside {x25519Mpl : MultiPlacement} {m : Memory}
    (hInv : x25519ActiveInvMem x25519Mpl m) :
    x25519ActiveInvMem x25519Mpl (stripExecOutside (x25519MultiKeep x25519Mpl) m) :=
  ⟨hInv.1, strip_codeLoaded_x25519 hInv.2.1,
   x25519CliRoOk_stripExecOutside (x25519MultiKeep x25519Mpl) hInv.2.2⟩

theorem x25519ActiveGuard_stripS (x25519Mpl : MultiPlacement) (s0 : State)
    (hG : x25519ActiveGuard x25519Mpl s0) :
    x25519ActiveGuard x25519Mpl (stripS (x25519MultiKeep x25519Mpl) s0) := by
  cases s0; exact x25519ActiveInvMem_stripExecOutside hG

theorem x25519ActiveGuard_stripS_setPC (x25519Mpl : MultiPlacement) (entry : BitVec 64)
    (s0 : State) (_hFr : ExecFrozen s0.mem) (hG : x25519ActiveGuard x25519Mpl s0) :
    x25519ActiveGuard x25519Mpl (stripS (x25519MultiKeep x25519Mpl) (s0.setPC entry)) := by
  cases s0; exact x25519ActiveInvMem_stripExecOutside hG

theorem x25519ActiveInvMem_of_keepsFrozen {x25519Mpl : MultiPlacement} {m m' : Memory}
    (hInv : x25519ActiveInvMem x25519Mpl m) (hkf : m.KeepsFrozen m') :
    x25519ActiveInvMem x25519Mpl m' :=
  ⟨hInv.1, hInv.2.1.of_keepsFrozen hkf, x25519CliRoOk_of_keepsFrozen hInv.2.2 hkf⟩

private theorem x25519CliMultiLib_blocks_code_pos :
    (x25519CliMultiLib.blocks.all fun b => decide (0 < b.code.length)) = true := by
  decide +kernel

private theorem x25519MultiKeep_base_of_placeable {mpl : MultiPlacement} {k : Nat}
    (hk : k < x25519CliMultiLib.blocks.length) (hpl : x25519CliMultiLib.Placeable mpl) :
    x25519MultiKeep mpl (mpl.base k) = true := by
  have hb := of_decide_eq_true (List.all_eq_true.mp x25519CliMultiLib_blocks_code_pos
    (x25519CliMultiLib.blocks[k]) (List.getElem_mem hk))
  have hbt := (hpl.blocks_ok k hk).len_aligned
  have hlen : (x25519CliMultiLib.blockProgram mpl k).code.length =
      (x25519CliMultiLib.blocks[k]).code.length := by
    change ((x25519CliMultiLib.blockLib k).text.patched
      (x25519CliMultiLib.blockPlacement mpl k)).length = _
    rw [CodeBlock.length_patched_of_aligned _
      (by rw [x25519CliMultiLib.blockLib_text hk]; exact hbt),
      x25519CliMultiLib.blockLib_text hk]
  have hpos : 0 < (x25519CliMultiLib.blockProgram mpl k).code.length := by omega
  let Pk := x25519CliMultiLib.blockProgram mpl k
  have hbase : Pk.base = mpl.base k := rfl
  have hsub : mpl.base k - Pk.base = 0#64 := by rw [hbase]; bv_omega
  have hin : (mpl.base k - Pk.base).toNat < Pk.code.length := by
    rw [hsub]; exact hpos
  unfold x25519MultiKeep
  rw [List.any_eq_true]
  exact ⟨k, List.mem_range.mpr hk, decide_eq_true hin⟩

/-! ## 3. Generic `X25519BlockBridge` & `x25519BlockGhost` Infrastructure -/

/-- Generic `linkedCallHookG` wrapper for block `j` of `x25519CliMultiLib` under `x25519ActiveGuard`. -/
@[expose] noncomputable def x25519BlockGhost [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) (fallback : State → State) : State → State :=
  linkedCallHookG
    (x25519ActiveGuard x25519Mpl)
    (x25519MultiKeep x25519Mpl)
    emptyStdProg
    (x25519CliMultiLib.blockProgram x25519Mpl j)
    (x25519Mpl.base j)
    (withLsRet master)
    fallback

theorem x25519BlockGhost_fs [LibsignalPlacement] (x25519Mpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) (fallback : State → State) (s0 : State) :
    (x25519BlockGhost x25519Mpl j master fallback s0).fs = s0.fs :=
  linkedCallHookG_fs _ _ _ _ _ _ _ s0

theorem x25519BlockGhost_fsT [LibsignalPlacement] (x25519Mpl : MultiPlacement) (j : Nat) {α : Type}
    (master : Spec α) (fallback : State → State) :
    HookFsTraced IsFsC (x25519BlockGhost x25519Mpl j master fallback) :=
  linkedCallHookG_fsT _ _ _ _ _ _ _

theorem x25519BlockGhost_preserves_execFrozen [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (j : Nat) {α : Type} (master : Spec α) {fallback : State → State}
    (hfb : PureFallbackPreserved fallback) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (x25519BlockGhost x25519Mpl j master fallback u).mem := by
  unfold x25519BlockGhost
  rw [linkedCallHookG_eq_conj]
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
    · rw [keepFsTrace_eq_of_preserved hfb]
      exact ExecFrozen.of_perm_eq hfr (hfb u).1.2.2.1
  · exact hfr

theorem x25519BlockGhost_lsRetAddr624_of_noException [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α : Type}
    {master : Spec α} {fallback : State → State} {u : State}
    (hnoex : ∀ msg, (x25519BlockGhost x25519Mpl j master fallback u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  lsRetAddr624_of_noException_via_activeRealPre linkedCallHookG_activeRealPre_of_noException hnoex

theorem x25519BlockGhost_keepLr_false_of_noException [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α : Type}
    {master : Spec α} {fallback : State → State} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hnoex : ∀ msg, (x25519BlockGhost x25519Mpl j master fallback u).status ≠ .Exception msg) :
    x25519MultiKeep x25519Mpl (u.readReg64 .lr) = false :=
  keepLr_false_of_noException_via_activeRealPre hKeep
    linkedCallHookG_activeRealPre_of_noException hnoex

private theorem perm_eq_of_stripExecOutside_keepsFrozen {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64, (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [ProofLib.strip_perm, ProofLib.strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a <;> cases hpf : mf.perm a
    · rfl
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rename_i p0 pf
      rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
      rcases p0 with ⟨r0, w0, x0, _, _⟩; rcases pf with ⟨rf, wf, xf, _, _⟩
      unfold ProofLib.stripPerm at hst
      cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
        cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

/-- Bridge bundle connecting a proved `X25519BlockOk j blockSpec` internal contract to an external
    stacked `master` spec and pure `fallback`. -/
structure X25519BlockBridge (j : Nat) {α β : Type}
    (blockSpec : MultiPlacement → Spec β) (master : Spec α) (fallback : State → State) : Prop where
  hj : j < x25519CliMultiLib.blocks.length := by decide
  blk_ok : X25519BlockOk j blockSpec
  blk_pan : ∀ mpl, (blockSpec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl
  blk_ex : ∀ mpl, (blockSpec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl
  blk_oom : ∀ mpl, (blockSpec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl
  blk_pre_mem : ∀ mpl y (s : State) (m : Memory),
    (blockSpec mpl).pre y (s.setMem m) = (blockSpec mpl).pre y s := by
      intro _ _ s _; cases s; rfl
  blk_post_mem : ∀ mpl y (s0 sf : State) (m0 mf : Memory),
    (blockSpec mpl).post y (s0.setMem m0) (sf.setMem mf) = (blockSpec mpl).post y s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl
  sim : ∀ mpl : MultiPlacement,
    SpecSimulates
      (keepsFs (Spec.withTraceEq (blockSpec mpl)))
      (withRoOk (X25519CliRoOk mpl) master)
  m_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl
  m_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl
  m_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl
  strip_inv : ∀ keep, SpecStripSInvariant keep master := by
    intro _
    exact ⟨fun _ s => by cases s; rfl, fun _ s0 sf => by cases s0; cases sf; rfl,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  post_fsT : ∀ x (R : SepProp) (s0 sf : State),
    (sf.mem ⊨ master.post x s0 sf ∗ R) → sf.fs = s0.fs ∧ sf.trace = s0.trace
  pre_pc : ∀ x (s : State) (pc : BitVec 64), master.pre x (s.setPC pc) = master.pre x s := by
    intro _ s _; cases s; rfl
  out_pc : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
    SubroutineOutcome master x R (s0.setPC pc) sf → SubroutineOutcome master x R s0 sf := by
      intro _ _ s0 sf _ h; cases s0; cases sf; exact h
  fb_pres : PureFallbackPreserved fallback
  fb_ok : HookOk fallback master

private theorem x25519Bridge_preservesFsTrace {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) :
    SpecPreservesFsTrace master :=
  fun x R s0 sf hout => by
    rcases hout with ⟨_, _, hp⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · obtain ⟨hfs, htr⟩ := B.post_fsT x R s0 sf hp
      exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
    · rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
    · rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem specSimulates_perm_vm_keepsFs_traceEq {β : Type} (spec : Spec β)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates
      (Spec.withTraceEq (keepsFs (withVmPreserved spec)))
      (withVmPreserved (keepsFs (Spec.withTraceEq spec))) := by
  refine SpecSimulates.of_map (hpan := hpan) (hex := hex) (hoom := hoom) fun y R s0 hpre =>
    ⟨y, R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [Spec.withTraceEq, keepsFs, withVmPreserved] at hpost ⊢
  exact Satisfies.mono (by sep_entail) hpost

private theorem x25519SubroutineOk_guarded_withVmPreserved {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) (x25519Mpl : MultiPlacement) :
    subroutine_ok (x25519CliMultiLib.blockProgram x25519Mpl j) (x25519Mpl.base j)
      (withStateGuard (x25519ActiveGuard x25519Mpl) (withVmPreserved master)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre0 hsp _hcode0
  dsimp only [withStateGuard, withVmPreserved] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hpl, hcl, hro⟩, hpre_m⟩
  have hblk0 : subroutine_ok (x25519CliMultiLib.blockProgram x25519Mpl j) (x25519Mpl.base j)
      (x25519CliMultiLib.withCodeLoaded x25519Mpl (blockSpec x25519Mpl)) :=
    @B.blk_ok ⟨x25519Mpl, hpl⟩
  have hblk_lift := x25519_blockProgram_withTraceEq_keepsFs_withVmPreserved
    (externs := fun _ => none) B.hj hpl hblk0
    (B.blk_pan x25519Mpl) (B.blk_ex x25519Mpl) (B.blk_oom x25519Mpl)
    (B.blk_pre_mem x25519Mpl) (B.blk_post_mem x25519Mpl)
  have hsim_vm : SpecSimulates
      (Spec.withTraceEq (keepsFs (withVmPreserved (blockSpec x25519Mpl))))
      (withRoOk (X25519CliRoOk x25519Mpl) (withVmPreserved master)) :=
    (specSimulates_perm_vm_keepsFs_traceEq (blockSpec x25519Mpl)
      (B.blk_pan x25519Mpl) (B.blk_ex x25519Mpl) (B.blk_oom x25519Mpl)).trans
      (specSimulates_withVmPreserved (B.sim x25519Mpl))
  have hpre_ro : s0.mem ⊨
      (withRoOk (X25519CliRoOk x25519Mpl) (withVmPreserved master)).pre x s0 ∗ R := by
    dsimp only [withRoOk, withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro, hpre_m⟩
  obtain ⟨y, R₁, hpre_blk, htrans⟩ := hsim_vm x R s0 hpre_ro
  have hpre_cl : s0.mem ⊨
      (x25519CliMultiLib.withCodeLoaded x25519Mpl
        (Spec.withTraceEq (keepsFs (withVmPreserved (blockSpec x25519Mpl))))).pre y s0 ∗ R₁ := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl]
    exact hpre_blk
  refine hblk_lift.mono_outcome y R₁ s0 hpc hrun hpre_cl hsp fun sf hout => ?_
  have hout_m := htrans sf hout
  rcases hout_m with ⟨hret, hcc, hpost⟩ | hrest
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

private theorem x25519SubroutineOk_guarded_withLsRet [LibsignalPlacement] {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) (x25519Mpl : MultiPlacement) :
    subroutine_ok (x25519CliMultiLib.blockProgram x25519Mpl j) (x25519Mpl.base j)
      (withStateGuard (x25519ActiveGuard x25519Mpl) (withLsRet master)) := by
  have hDrop : SpecSimulates
      (withStateGuard (x25519ActiveGuard x25519Mpl) (withVmPreserved master))
      (withStateGuard (x25519ActiveGuard x25519Mpl) master) :=
    fun x R s0 hpre => ⟨x, R, hpre, fun sf hout => by
      rcases hout with ⟨hret, hcc, hpost⟩ | h
      · dsimp only [withStateGuard, withVmPreserved] at hpost ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
        exact Or.inl ⟨hret, hcc, hpost.2⟩
      · exact Or.inr h⟩
  have hLs := subroutine_ok_withLsRet
    (SpecSimulates.subroutine_ok hDrop (x25519SubroutineOk_guarded_withVmPreserved B x25519Mpl))
  have hComm :
      withLsRet (withStateGuard (x25519ActiveGuard x25519Mpl) master) =
        withStateGuard (x25519ActiveGuard x25519Mpl) (withLsRet master) :=
    withLsRet_frameLeft master (fun _ s => ⌜x25519ActiveGuard x25519Mpl s⌝) master.post
  rwa [hComm] at hLs

theorem x25519BlockGhost_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement} {j : Nat}
    {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback) (withLsRet master) := by
  have hkfb := keepFsTrace_eq_of_preserved B.fb_pres
  exact hookOk_linkedCallHookG
    emptyStdProg_svc
    rfl
    (fun pc _ => emptyStdProg_externAt_none pc)
    (x25519CliMultiLib_externAt_none x25519Mpl j B.hj (fun _ => none))
    (fun s0 hFr hG => x25519ActiveGuard_stripS_setPC x25519Mpl (x25519Mpl.base j) s0 hFr hG)
    (x25519SubroutineOk_guarded_withLsRet B x25519Mpl)
    (specStripSInvariant_withLsRet (B.strip_inv (x25519MultiKeep x25519Mpl)))
    (specPreservesFsTrace_withLsRet (x25519Bridge_preservesFsTrace B))
    (withLsRet_pre_setPC B.pre_pc)
    (withLsRet_outcome_setPC B.out_pc)
    (by rw [hkfb]; exact hookOk_withLsRet B.fb_ok)

theorem x25519BlockGhost_vmPreserved_and_nonSyscall [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) (s0 : State) :
    let sf := x25519BlockGhost x25519Mpl j master fallback s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle := by
  classical
  dsimp only
  unfold x25519BlockGhost
  have hkfb := keepFsTrace_eq_of_preserved B.fb_pres
  by_cases hG : x25519ActiveGuard x25519Mpl s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpreLs⟩
        dsimp only [withLsRet] at hpreLs
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpreLs
        rcases hpreLs with ⟨_hlr, hpre_m⟩
        let keep := x25519MultiKeep x25519Mpl
        let s1 := s0.setPC (x25519Mpl.base j)
        let s1' := stripS keep s1
        have hs1_pre : s1.mem ⊨ master.pre x s1 ∗ R := by
          dsimp only [s1]; rw [B.pre_pc]; cases s0; exact hpre_m
        have hs1'_pre : s1'.mem ⊨ master.pre x s1' ∗ R := by
          have hsat := satisfies_stripExecOutside keep hs1_pre
          rwa [← (B.strip_inv keep).pre_eq x s1] at hsat
        have hs1'_preG : s1'.mem ⊨
            (withStateGuard (x25519ActiveGuard x25519Mpl) (withVmPreserved master)).pre x s1' ∗ R := by
          dsimp only [withStateGuard, withVmPreserved]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          exact ⟨x25519ActiveGuard_stripS_setPC x25519Mpl (x25519Mpl.base j) s0 hReal.1 hG, hs1'_pre⟩
        obtain ⟨sf', hsteps', hout'⟩ := reaches_outcome_iff.1
          (subroutine_ok_iff.1 (x25519SubroutineOk_guarded_withVmPreserved B x25519Mpl)
            x R s1' (by cases s0; rfl) (by cases s0; exact hrun) hs1'_preG (by cases s0; exact hsp))
          hReal.2.2.1
        have hsub_no := x25519CliMultiLib_externAt_none x25519Mpl j B.hj (fun _ => none)
        rcases hout' with ⟨hret', _, hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
        · have hr0 : Returned s0 sf' :=
            ⟨by cases s0; exact hret'.1, by cases s0; exact hret'.2.1, hret'.2.2⟩
          obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
            stepsUntil_of_stripS_standard (s0 := s0)
              emptyStdProg_svc rfl
              (fun pc _ => emptyStdProg_externAt_none pc)
              (fun pc f he => nomatch hsub_no pc ▸ he)
              hReal.2.1 hsteps' (Or.inl hr0) (by rw [hr0.2.2]; decide) s1 rfl hReal.1
          have hchoose := Classical.choose_spec hReal.2.2.2
          rw [StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf]
          have horc' := Steps.oracle_eq_of_standard rfl hsub_no hsteps'
          rw [hsf_eq] at horc'
          dsimp only [withStateGuard, withVmPreserved] at hpost'
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
          obtain ⟨hvm', hpostM'⟩ := hpost'
          obtain ⟨hfs', htr'⟩ := B.post_fsT x R s1' sf' hpostM'
          rw [hsf_eq] at hvm' hfs' htr'
          have hfs : sf.fs = s0.fs := by dsimp only [s1', s1] at hfs'; cases s0; cases sf; exact hfs'
          have htr : sf.trace = s0.trace := by dsimp only [s1', s1] at htr'; cases s0; cases sf; exact htr'
          have horc : sf.oracle = s0.oracle := by dsimp only [s1', s1] at horc'; cases s0; cases sf; exact horc'
          have hperm_strip : ∀ a : BitVec 64,
              (stripExecOutside keep sf.mem).perm a = (stripExecOutside keep s0.mem).perm a := by
            intro a; have hp := hvm'.2.2.1 a; dsimp only [s1', s1] at hp; cases s0; cases sf; exact hp
          have hperm := perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf
            huntil.toSteps.keepsFrozen hperm_strip
          have hpool : PoolPreserved s0 sf := by
            rcases hvm'.1 with ⟨h1, h2, h3⟩
            dsimp only [s1', s1] at h1 h2 h3
            exact ⟨by cases s0; cases sf; exact h1,
              by cases s0; cases sf; exact h2,
              by cases s0; cases sf; exact h3⟩
          have hphys : sf.physMemAvail = s0.physMemAvail := by
            have hp := hvm'.2.1; dsimp only [s1', s1] at hp; cases s0; cases sf; exact hp
          exact ⟨⟨hpool, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩, hfs, htr, hpool.2.2, horc⟩
        · dsimp only [withStateGuard, withVmPreserved] at hp
          rw [B.m_pan] at hp; exact (not_satisfies_false_sepConj hp).elim
        · dsimp only [withStateGuard, withVmPreserved] at he
          rw [B.m_ex] at he; exact (not_satisfies_false_sepConj he).elim
        · dsimp only [withStateGuard, withVmPreserved] at ho
          rw [B.m_oom] at ho; exact (not_satisfies_false_sepConj ho).elim
      · rw [hkfb]; exact B.fb_pres s0
    · exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, FdsHiFrame.of_fs_eq rfl⟩, rfl, rfl, rfl, rfl⟩
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [hkfb]; exact B.fb_pres s0
    · exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, FdsHiFrame.of_fs_eq rfl⟩, rfl, rfl, rfl, rfl⟩

theorem x25519BlockGhost_vmPreserved [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) (s0 : State) :
    VmPreserved s0 (x25519BlockGhost x25519Mpl j master fallback s0) :=
  (x25519BlockGhost_vmPreserved_and_nonSyscall B s0).1

theorem x25519BlockGhost_rustVmPreserved [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) (s0 : State) :
    Arm64.Rust.VmPreserved s0 (x25519BlockGhost x25519Mpl j master fallback s0) := by
  have hvm := x25519BlockGhost_vmPreserved (x25519Mpl := x25519Mpl) B s0
  exact ⟨hvm.1.1, hvm.1.2.1, hvm.1.2.2, funext hvm.2.2.1⟩

theorem x25519BlockGhost_trace [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) (s0 : State) :
    (x25519BlockGhost x25519Mpl j master fallback s0).trace = s0.trace :=
  (x25519BlockGhost_vmPreserved_and_nonSyscall B s0).2.2.1

theorem preservesNoAllocFailed_x25519BlockGhost [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) :
    PreservesNoAllocFailed (x25519BlockGhost x25519Mpl j master fallback) := by
  intro s hno
  rwa [x25519BlockGhost_trace B s]

theorem x25519BlockGhost_withVmPreserved_ok [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback) (withLsRet (withVmPreserved master)) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withVmPreserved (x25519BlockGhost_ok B) (x25519BlockGhost_vmPreserved B)

theorem withLsRet_withAlloc [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc A lim spec) = withAlloc A lim (withLsRet spec) := by
  cases spec
  dsimp only [withLsRet, withAlloc]
  congr 1
  funext ⟨x, st⟩ s
  simp only [sepConj_assoc]

private theorem x25519Ghost_lift_ls_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement} {j : Nat}
    {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) {target : Spec γ}
    (hsim : SpecSimulates master target) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback) (withLsRet target) :=
  hookOk_withLsRet_of_simulates hsim (x25519BlockGhost_ok B)

private theorem x25519Ghost_lift_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement} {j : Nat}
    {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback) {target : Spec γ}
    (hsim : SpecSimulates master target) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback) (withLsRet (withVmPreserved target)) :=
  hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved hsim)
    (x25519BlockGhost_withVmPreserved_ok B)

private theorem x25519Ghost_lift_keepsFs_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement}
    {j : Nat} {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α}
    {fallback : State → State} (B : X25519BlockBridge j blockSpec master fallback)
    {target : Spec γ} (hsim : SpecSimulates master (keepsFs target)) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback)
      (withLsRet (withVmPreserved (keepsFs target))) :=
  hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved hsim)
    (x25519BlockGhost_withVmPreserved_ok B)

private theorem x25519Ghost_lift_withAlloc_ls_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement}
    {j : Nat} {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α}
    {fallback : State → State} (B : X25519BlockBridge j blockSpec master fallback)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {target : Spec γ} (hsim : SpecSimulates master target) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback) (withAlloc A lim (withLsRet target)) := by
  have h1 : HookOk (x25519BlockGhost x25519Mpl j master fallback)
      (withVmPreserved (withLsRet target)) := by
    rw [← withLsRet_withVmPreserved]
    exact x25519Ghost_lift_ok B hsim
  exact hookOk_withAlloc_of_withVmPreserved A lim h1

private theorem x25519Ghost_lift_withAlloc_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement}
    {j : Nat} {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α}
    {fallback : State → State} (B : X25519BlockBridge j blockSpec master fallback)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {target : Spec γ} (hsim : SpecSimulates master target) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback) (withLsRet (withAlloc A lim target)) := by
  rw [withLsRet_withAlloc]
  exact x25519Ghost_lift_withAlloc_ls_ok B A lim hsim

private theorem x25519Ghost_lift_withAlloc_vm_ok [LibsignalPlacement] {x25519Mpl : MultiPlacement}
    {j : Nat} {α β γ : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α}
    {fallback : State → State} (B : X25519BlockBridge j blockSpec master fallback)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {target : Spec γ} (hsim : SpecSimulates master target) :
    HookOk (x25519BlockGhost x25519Mpl j master fallback)
      (withAlloc A lim (withVmPreserved (withLsRet target))) := by
  have h1 : HookOk (x25519BlockGhost x25519Mpl j master fallback)
      (withVmPreserved (withLsRet target)) := by
    rw [← withLsRet_withVmPreserved]
    exact x25519Ghost_lift_ok B hsim
  exact hookOk_withAlloc_withVmPreserved A lim h1

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u; dsimp only [State.setPC] at hpc ⊢; subst hpc; rfl

theorem x25519BlockGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (sym : String) {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn (x25519ActiveInvMem x25519Mpl)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl sym) (x25519Mpl.base j)) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True)
      (x25519BlockGhost x25519Mpl j master fallback) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨x25519BlockGhost_preserves_execFrozen x25519Mpl j master B.fb_pres hfr,
     x25519BlockGhost_fs x25519Mpl j master fallback u⟩
  replay_at_stub := by
    intro W _ _ stubPc _ P_real _ _ _ _
    refine Or.inr ⟨hRealStubNone W, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvS
    have hlr_out : x25519MultiKeep x25519Mpl (u.readReg64 .lr) = false :=
      x25519BlockGhost_keepLr_false_of_noException hKeep hnoex
    have hInvMem : x25519ActiveInvMem x25519Mpl u.mem := hInvX25519 u hInvS
    have hrep := (ghostExternReplaysOn_of_linkedCallHookG_liftVis
      (InvMem := x25519ActiveInvMem x25519Mpl)
      (Guard := x25519ActiveGuard x25519Mpl)
      (keep := x25519MultiKeep x25519Mpl)
      (P_run := emptyStdProg)
      (P_real := P_real)
      (P_sub := x25519CliMultiLib.blockProgram x25519Mpl j)
      (stubPc := stubPc)
      (entryTarget := x25519Mpl.base j)
      (spec := withLsRet master)
      (fallback := fallback)
      emptyStdProg_svc
      rfl
      (fun pc _ => emptyStdProg_externAt_none pc)
      (x25519CliMultiLib_externAt_none x25519Mpl j B.hj (fun _ => none))
      (hRealStubNone W)
      (hStub W)
      (fun _ _ _ _ _ hvis =>
        h2fsgen_steps_lift_of_visitedIn_noExtern emptyStdProg_svc
          (fun pc _ => emptyStdProg_externAt_none pc)
          (fun _ hkp => hRealX25519NoExt W hkp) hvis)
      (fun _ _ hInv => (strip_codeLoaded_x25519 hInv.2.1) j B.hj)
      (fun _ _ hInv hkf' => x25519ActiveInvMem_of_keepsFrozen hInv hkf')
      (fun _ _ hInv => hInv)
      (fun s0 hFr hG => x25519ActiveGuard_stripS_setPC x25519Mpl (x25519Mpl.base j) s0 hFr hG)
      (x25519SubroutineOk_guarded_withLsRet B x25519Mpl)
      (specStripSInvariant_withLsRet (B.strip_inv (x25519MultiKeep x25519Mpl)))
      (specPreservesFsTrace_withLsRet (x25519Bridge_preservesFsTrace B))
      (withLsRet_pre_setPC B.pre_pc)
      (withLsRet_outcome_setPC B.out_pc)).2
      u hpc hrun hnoex hfr hlr_out hInvMem
    exact ⟨hrep.1, hrep.2.1,
      hInvKeep u _ hInvS hkf (x25519BlockGhost_fs x25519Mpl j master fallback u)⟩

theorem x25519BlockGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (sym : String) {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback)
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl sym = x25519Mpl.base j)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True)
      (x25519BlockGhost x25519Mpl j master fallback) :=
  x25519BlockGhost_rowReplayOn_of_stub mpl mmpl x25519Mpl InvS EG sym B
    hInvX25519 hInvKeep hKeep hRealX25519NoExt
    (fun W => by
      rw [hTargetEq]
      exact hRealX25519NoExt W (x25519MultiKeep_base_of_placeable B.hj hpl))
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

/-! ## 4. Concrete Ghost Hooks (`x25519PubFromSecretGhost`, `x25519DiffieHellmanGhost`) & Bridges -/

/-- `linkedCallHookG` ghost hook for `lsPubFromSecretSym` (`x25519CliMultiLib` block `18`,
    stack `1904` B, fallback `pubFromSecretHook x25519PubFromSecretRef`). -/
@[expose] noncomputable def x25519PubFromSecretGhost [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) : State → State :=
  x25519BlockGhost x25519Mpl 18
    (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) 1904))
    (pubFromSecretHook x25519PubFromSecretRef)

/-- `linkedCallHookG` ghost hook for `lsDiffieHellmanSym` (`x25519CliMultiLib` block `17`,
    stack `1808` B, fallback `diffieHellmanHook x25519Ref`). -/
@[expose] noncomputable def x25519DiffieHellmanGhost [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) : State → State :=
  x25519BlockGhost x25519Mpl 17
    (keepsFs (withStack (diffieHellmanSpec x25519Ref) 1808))
    (diffieHellmanHook x25519Ref)

private theorem pubFromSecret_post_fsT (stk : Nat)
    (x : BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) (R : SepProp) (s0 sf : State)
    (h : sf.mem ⊨ (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)).post x s0 sf ∗ R) :
    sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rcases x with ⟨secA, sec, ret⟩
  dsimp only [keepsFs, withStack, pubFromSecretSpec] at h
  have h1 : sf.mem ⊨ ⌜sf.fs = s0.fs⌝ ∗ (⌜sf.trace = s0.trace⌝ ∗
      ((secA ↦ₛ sec.toList) ∗ (ret ↦ₛ (x25519PubFromSecretRef sec).toList) ∗ stackAt s0.sp stk ∗ R)) :=
    Satisfies.mono (by sep_entail) h
  obtain ⟨hfs, h2⟩ := (satisfies_pure_sepConj _ _ _).mp h1
  exact ⟨hfs, ((satisfies_pure_sepConj _ _ _).mp h2).1⟩

private theorem diffieHellman_post_fsT (stk : Nat)
    (x : BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64)
    (R : SepProp) (s0 sf : State)
    (h : sf.mem ⊨ (keepsFs (withStack (diffieHellmanSpec x25519Ref) stk)).post x s0 sf ∗ R) :
    sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rcases x with ⟨secA, sec, pubA, pub, ret⟩
  dsimp only [keepsFs, withStack, diffieHellmanSpec] at h
  have h1 : sf.mem ⊨ ⌜sf.fs = s0.fs⌝ ∗ (⌜sf.trace = s0.trace⌝ ∗
      ((secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗
        (ret ↦ₛ (x25519Ref sec pub).toList) ∗ stackAt s0.sp stk ∗ R)) :=
    Satisfies.mono (by sep_entail) h
  obtain ⟨hfs, h2⟩ := (satisfies_pure_sepConj _ _ _).mp h1
  exact ⟨hfs, ((satisfies_pure_sepConj _ _ _).mp h2).1⟩

theorem pubFromSecretBridge_of (hPub : PublicKeyFromStaticSecretOk) :
    X25519BlockBridge 18 publicKeyFromSecretSpec
      (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) 1904))
      (pubFromSecretHook x25519PubFromSecretRef) where
  blk_ok := hPub
  blk_pre_mem := fun _ ⟨_, _, _, _⟩ s _ => by cases s; rfl
  blk_post_mem := fun _ ⟨_, _, _, _⟩ s0 sf _ _ => by cases s0; cases sf; rfl
  sim := fun mpl => specSimulates_keepsFs (pubFromSecret_simulates_hooks_roOk mpl (Nat.le_refl 1904))
  strip_inv := fun _ =>
    ⟨fun ⟨_, _, _⟩ s => by cases s; rfl,
     fun ⟨_, _, _⟩ s0 sf => by cases s0; cases sf; rfl,
     fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  post_fsT := pubFromSecret_post_fsT 1904
  pre_pc := fun ⟨_, _, _⟩ s _ => by cases s; rfl
  out_pc := fun ⟨_, _, _⟩ _ s0 sf _ h => by cases s0; cases sf; exact h
  fb_pres := pubFromSecretFallback_preserved
  fb_ok := pubFromSecretFallback_ok 1904

theorem pubFromSecretBridge :
    X25519BlockBridge 18 publicKeyFromSecretSpec
      (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) 1904))
      (pubFromSecretHook x25519PubFromSecretRef) :=
  pubFromSecretBridge_of public_key_from_static_secret_ok

theorem diffieHellmanBridge_of (hDH : StaticSecretDiffieHellmanOk) :
    X25519BlockBridge 17 staticSecretDiffieHellmanSpec
      (keepsFs (withStack (diffieHellmanSpec x25519Ref) 1808))
      (diffieHellmanHook x25519Ref) where
  blk_ok := hDH
  blk_pre_mem := fun _ ⟨_, _, _, _, _, _⟩ s _ => by cases s; rfl
  blk_post_mem := fun _ ⟨_, _, _, _, _, _⟩ s0 sf _ _ => by cases s0; cases sf; rfl
  sim := fun mpl => specSimulates_keepsFs (diffieHellman_simulates_hooks_roOk mpl (Nat.le_refl 1808))
  strip_inv := fun _ =>
    ⟨fun ⟨_, _, _, _, _⟩ s => by cases s; rfl,
     fun ⟨_, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl,
     fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  post_fsT := diffieHellman_post_fsT 1808
  pre_pc := fun ⟨_, _, _, _, _⟩ s _ => by cases s; rfl
  out_pc := fun ⟨_, _, _, _, _⟩ _ s0 sf _ h => by cases s0; cases sf; exact h
  fb_pres := diffieHellmanFallback_preserved
  fb_ok := (diffieHellmanFallback_ok 1808).2

theorem diffieHellmanBridge :
    X25519BlockBridge 17 staticSecretDiffieHellmanSpec
      (keepsFs (withStack (diffieHellmanSpec x25519Ref) 1808))
      (diffieHellmanHook x25519Ref) :=
  diffieHellmanBridge_of static_secret_diffie_hellman_ok

/-! ### 4.1 State-Preservation Theorems for Both Ghost Hooks -/

theorem x25519PubFromSecretGhost_vmPreserved_and_nonSyscall_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    let sf := x25519PubFromSecretGhost x25519Mpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  x25519BlockGhost_vmPreserved_and_nonSyscall (pubFromSecretBridge_of hPub) s0

theorem x25519PubFromSecretGhost_vmPreserved_and_nonSyscall [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    let sf := x25519PubFromSecretGhost x25519Mpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  x25519BlockGhost_vmPreserved_and_nonSyscall pubFromSecretBridge s0

theorem x25519PubFromSecretGhost_vmPreserved_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    VmPreserved s0 (x25519PubFromSecretGhost x25519Mpl s0) :=
  x25519BlockGhost_vmPreserved (pubFromSecretBridge_of hPub) s0

theorem x25519PubFromSecretGhost_vmPreserved [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    VmPreserved s0 (x25519PubFromSecretGhost x25519Mpl s0) :=
  x25519BlockGhost_vmPreserved pubFromSecretBridge s0

theorem x25519PubFromSecretGhost_rustVmPreserved_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    Arm64.Rust.VmPreserved s0 (x25519PubFromSecretGhost x25519Mpl s0) :=
  x25519BlockGhost_rustVmPreserved (pubFromSecretBridge_of hPub) s0

theorem x25519PubFromSecretGhost_rustVmPreserved [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    Arm64.Rust.VmPreserved s0 (x25519PubFromSecretGhost x25519Mpl s0) :=
  x25519BlockGhost_rustVmPreserved pubFromSecretBridge s0

theorem x25519PubFromSecretGhost_fs [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    (x25519PubFromSecretGhost x25519Mpl s0).fs = s0.fs :=
  x25519BlockGhost_fs x25519Mpl 18 _ _ s0

theorem x25519PubFromSecretGhost_trace_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    (x25519PubFromSecretGhost x25519Mpl s0).trace = s0.trace :=
  x25519BlockGhost_trace (pubFromSecretBridge_of hPub) s0

theorem x25519PubFromSecretGhost_trace [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    (x25519PubFromSecretGhost x25519Mpl s0).trace = s0.trace :=
  x25519BlockGhost_trace pubFromSecretBridge s0

theorem x25519PubFromSecretGhost_fsT [LibsignalPlacement] (x25519Mpl : MultiPlacement) :
    HookFsTraced IsFsC (x25519PubFromSecretGhost x25519Mpl) :=
  x25519BlockGhost_fsT x25519Mpl 18 _ _

theorem preservesNoAllocFailed_x25519PubFromSecretGhost_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement) :
    PreservesNoAllocFailed (x25519PubFromSecretGhost x25519Mpl) :=
  preservesNoAllocFailed_x25519BlockGhost (pubFromSecretBridge_of hPub)

theorem preservesNoAllocFailed_x25519PubFromSecretGhost [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) :
    PreservesNoAllocFailed (x25519PubFromSecretGhost x25519Mpl) :=
  preservesNoAllocFailed_x25519BlockGhost pubFromSecretBridge

theorem x25519PubFromSecretGhost_preserves_execFrozen [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (x25519PubFromSecretGhost x25519Mpl u).mem :=
  x25519BlockGhost_preserves_execFrozen x25519Mpl 18 _ pubFromSecretFallback_preserved hfr

theorem x25519PubFromSecretGhost_lsRetAddr624_of_noException [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {u : State}
    (hnoex : ∀ msg, (x25519PubFromSecretGhost x25519Mpl u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  x25519BlockGhost_lsRetAddr624_of_noException hnoex

theorem x25519PubFromSecretGhost_keepLr_false_of_noException [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hnoex : ∀ msg, (x25519PubFromSecretGhost x25519Mpl u).status ≠ .Exception msg) :
    x25519MultiKeep x25519Mpl (u.readReg64 .lr) = false :=
  x25519BlockGhost_keepLr_false_of_noException hKeep hnoex

theorem x25519DiffieHellmanGhost_vmPreserved_and_nonSyscall_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    let sf := x25519DiffieHellmanGhost x25519Mpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  x25519BlockGhost_vmPreserved_and_nonSyscall (diffieHellmanBridge_of hDH) s0

theorem x25519DiffieHellmanGhost_vmPreserved_and_nonSyscall [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    let sf := x25519DiffieHellmanGhost x25519Mpl s0
    VmPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.oracle = s0.oracle :=
  x25519BlockGhost_vmPreserved_and_nonSyscall diffieHellmanBridge s0

theorem x25519DiffieHellmanGhost_vmPreserved_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    VmPreserved s0 (x25519DiffieHellmanGhost x25519Mpl s0) :=
  x25519BlockGhost_vmPreserved (diffieHellmanBridge_of hDH) s0

theorem x25519DiffieHellmanGhost_vmPreserved [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    VmPreserved s0 (x25519DiffieHellmanGhost x25519Mpl s0) :=
  x25519BlockGhost_vmPreserved diffieHellmanBridge s0

theorem x25519DiffieHellmanGhost_rustVmPreserved_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    Arm64.Rust.VmPreserved s0 (x25519DiffieHellmanGhost x25519Mpl s0) :=
  x25519BlockGhost_rustVmPreserved (diffieHellmanBridge_of hDH) s0

theorem x25519DiffieHellmanGhost_rustVmPreserved [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    Arm64.Rust.VmPreserved s0 (x25519DiffieHellmanGhost x25519Mpl s0) :=
  x25519BlockGhost_rustVmPreserved diffieHellmanBridge s0

theorem x25519DiffieHellmanGhost_fs [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    (x25519DiffieHellmanGhost x25519Mpl s0).fs = s0.fs :=
  x25519BlockGhost_fs x25519Mpl 17 _ _ s0

theorem x25519DiffieHellmanGhost_trace_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement) (s0 : State) :
    (x25519DiffieHellmanGhost x25519Mpl s0).trace = s0.trace :=
  x25519BlockGhost_trace (diffieHellmanBridge_of hDH) s0

theorem x25519DiffieHellmanGhost_trace [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (s0 : State) :
    (x25519DiffieHellmanGhost x25519Mpl s0).trace = s0.trace :=
  x25519BlockGhost_trace diffieHellmanBridge s0

theorem x25519DiffieHellmanGhost_fsT [LibsignalPlacement] (x25519Mpl : MultiPlacement) :
    HookFsTraced IsFsC (x25519DiffieHellmanGhost x25519Mpl) :=
  x25519BlockGhost_fsT x25519Mpl 17 _ _

theorem preservesNoAllocFailed_x25519DiffieHellmanGhost_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement) :
    PreservesNoAllocFailed (x25519DiffieHellmanGhost x25519Mpl) :=
  preservesNoAllocFailed_x25519BlockGhost (diffieHellmanBridge_of hDH)

theorem preservesNoAllocFailed_x25519DiffieHellmanGhost [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) :
    PreservesNoAllocFailed (x25519DiffieHellmanGhost x25519Mpl) :=
  preservesNoAllocFailed_x25519BlockGhost diffieHellmanBridge

theorem x25519DiffieHellmanGhost_preserves_execFrozen [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (x25519DiffieHellmanGhost x25519Mpl u).mem :=
  x25519BlockGhost_preserves_execFrozen x25519Mpl 17 _ diffieHellmanFallback_preserved hfr

theorem x25519DiffieHellmanGhost_lsRetAddr624_of_noException [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {u : State}
    (hnoex : ∀ msg, (x25519DiffieHellmanGhost x25519Mpl u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  x25519BlockGhost_lsRetAddr624_of_noException hnoex

theorem x25519DiffieHellmanGhost_keepLr_false_of_noException [LibsignalPlacement]
    {x25519Mpl : MultiPlacement} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hnoex : ∀ msg, (x25519DiffieHellmanGhost x25519Mpl u).status ≠ .Exception msg) :
    x25519MultiKeep x25519Mpl (u.readReg64 .lr) = false :=
  x25519BlockGhost_keepLr_false_of_noException hKeep hnoex

/-! ## 5. Consumer `SpecSimulates`, `HookOk` Matrix, & `GhostRowReplayOn` -/

private theorem specSimulates_withStack_mono {α : Type} (core : Spec α) {stk₀ stk : Nat}
    (hlo : stk₀ ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (hpan : core.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : core.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : core.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withStack core stk₀) (withStack core stk) := by
  refine SpecSimulates.of_map (hpan := hpan) (hex := hex) (hoom := hoom) fun x R s0 hpre => ?_
  dsimp only [withStack] at hpre
  rw [stackAt_shrink s0.sp stk stk₀ hlo hhi] at hpre
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk₀) ∗ R,
    Satisfies.mono (by dsimp only [withStack]; sep_entail) hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [withStack] at hpost ⊢
  rw [stackAt_shrink s0.sp stk stk₀ hlo hhi]
  exact Satisfies.mono (by sep_entail) hpost

private theorem pubFromSecret_sim_cliExt {C : Crypto}
    (hC : C.pubKey = x25519PubFromSecretRef) :
    SpecSimulates
      (withStack (pubFromSecretSpec x25519PubFromSecretRef) extHookStack)
      (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C) := by
  have heq : CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C =
      withStack (pubFromSecretSpec x25519PubFromSecretRef) extHookStack := by
    rw [← hC]; rfl
  rw [heq]
  exact fun x R _ hpre => ⟨x, R, hpre, fun _ hout => hout⟩

private theorem pubFromSecret_sim_pureByteFunction (byVal : Bool) :
    SpecSimulates
      (withStack (pubFromSecretSpec x25519PubFromSecretRef) extHookStack)
      (pureByteFunctionSpec x25519PubFromSecretRef byVal) := by
  cases byVal
  · exact fun x R _ hpre => ⟨x, R, hpre, fun _ hout => hout⟩
  · refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre =>
      ⟨(inA, v, ret), R, hpre, fun sf _ _ hpost => ?_⟩
    dsimp only [withStack, pubFromSecretSpec, pureByteFunctionSpec, inputAfter, reduceIte] at hpost ⊢
    have hent : (inA ↦ₛ v.toList) ⊢ memRegion inA 32 := by
      simpa using pointsToBytes_entails_memRegion inA v.toList
    exact Satisfies.mono (by
      refine sepConj_mono (sepConj_mono ?_ (Entails.refl _)) (Entails.refl _)
      refine sepConj_mono (Entails.refl _) (sepConj_mono hent (Entails.refl _))) hpost

private theorem pubFromSecret_sim_derivePublicKeyBytesStack (stk : Nat) :
    SpecSimulates
      (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)
      (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk) := by
  refine SpecSimulates.of_map fun x R s0 hpre => ?_
  refine ⟨(x.secret, x.sec, x.out), R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [withStack, pubFromSecretSpec, derivePublicKeyBytesStackSpec] at hpre ⊢
    exact Satisfies.mono (by sep_entail) hpre
  · dsimp only [withStack, pubFromSecretSpec, derivePublicKeyBytesStackSpec] at hpost ⊢
    exact Satisfies.mono (by sep_entail) hpost

private theorem derivePublicKeyBytesStack_sim_budget (stk : Nat) :
    SpecSimulates
      (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))
      (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk) := by
  refine SpecSimulates.of_map fun x R s0 hpre =>
    ⟨x, R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [withVmPreserved, derivePublicKeyBytesStackSpec,
    derivePublicKeyBytesStackBudgetSpec] at hpost ⊢
  have h1 : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗ (⌜sf.trace = s0.trace⌝ ∗
      ((x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (x25519PubFromSecretRef x.sec).toList) ∗
        stackAt s0.sp stk ∗ R)) :=
    Satisfies.mono (by sep_entail) hpost
  obtain ⟨hvm, h2⟩ := (satisfies_pure_sepConj _ _ _).mp h1
  obtain ⟨htr, h3⟩ := (satisfies_pure_sepConj _ _ _).mp h2
  have h4 : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      ((x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (x25519PubFromSecretRef x.sec).toList) ∗
        stackAt s0.sp stk ∗ R) :=
    (satisfies_pure_sepConj _ _ _).mpr ⟨⟨htr, hvm⟩, h3⟩
  exact Satisfies.mono (by sep_entail) h4

private theorem diffieHellman_sim_cliExt {C : Crypto} (hC : C.X = x25519Ref) :
    SpecSimulates
      (withStack (diffieHellmanSpec x25519Ref) extHookStack)
      (dhSpec C) := by
  have heq : dhSpec C = withStack (diffieHellmanSpec x25519Ref) extHookStack := by
    rw [← hC]; rfl
  rw [heq]
  exact fun x R _ hpre => ⟨x, R, hpre, fun _ hout => hout⟩

/-! ### 5.1 `x25519PubFromSecretGhost` (`lsPubFromSecretSym`, Block `18`) `HookOk` & Replay -/

theorem x25519PubFromSecretGhost_master_ok_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) 1904))) :=
  x25519BlockGhost_ok (pubFromSecretBridge_of hPub)

theorem x25519PubFromSecretGhost_master_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) 1904))) :=
  x25519BlockGhost_ok pubFromSecretBridge

theorem x25519PubFromSecretGhost_ls_ok_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)) :=
  x25519Ghost_lift_ls_ok (pubFromSecretBridge_of hPub)
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519PubFromSecretGhost_ls_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)) :=
  x25519PubFromSecretGhost_ls_ok_of public_key_from_static_secret_ok x25519Mpl stk hlo hhi

theorem x25519PubFromSecretGhost_at_ok_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  x25519Ghost_lift_ok (pubFromSecretBridge_of hPub)
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519PubFromSecretGhost_at_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  x25519PubFromSecretGhost_at_ok_of public_key_from_static_secret_ok x25519Mpl stk hlo hhi

theorem x25519PubFromSecretGhost_keepsFs_ok_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)))) :=
  x25519Ghost_lift_keepsFs_ok (pubFromSecretBridge_of hPub)
    (specSimulates_keepsFs (specSimulates_withStack_mono _ hlo hhi))

theorem x25519PubFromSecretGhost_keepsFs_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)))) :=
  x25519PubFromSecretGhost_keepsFs_ok_of public_key_from_static_secret_ok x25519Mpl stk hlo hhi

theorem x25519PubFromSecretGhost_withAlloc_ls_ok_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withAlloc A lim (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  x25519Ghost_lift_withAlloc_ls_ok (pubFromSecretBridge_of hPub) A lim
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519PubFromSecretGhost_withAlloc_ls_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withAlloc A lim (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  x25519PubFromSecretGhost_withAlloc_ls_ok_of public_key_from_static_secret_ok x25519Mpl A lim stk hlo hhi

theorem x25519PubFromSecretGhost_withAlloc_ok_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withAlloc A lim (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  x25519Ghost_lift_withAlloc_ok (pubFromSecretBridge_of hPub) A lim
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519PubFromSecretGhost_withAlloc_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withAlloc A lim (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  x25519PubFromSecretGhost_withAlloc_ok_of public_key_from_static_secret_ok x25519Mpl A lim stk hlo hhi

theorem x25519PubFromSecretGhost_cliExt_ls_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)) :=
  x25519Ghost_lift_ls_ok pubFromSecretBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_cliExt hC)))

theorem x25519PubFromSecretGhost_cliExt_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  x25519Ghost_lift_ok pubFromSecretBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_cliExt hC)))

theorem x25519PubFromSecretGhost_cliExt_keepsFs_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))) :=
  x25519Ghost_lift_keepsFs_ok pubFromSecretBridge
    (specSimulates_keepsFs
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_cliExt hC)))

theorem x25519PubFromSecretGhost_cliExt_withAlloc_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  x25519Ghost_lift_withAlloc_ls_ok pubFromSecretBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_cliExt hC)))

theorem x25519PubFromSecretGhost_cliExt_withAlloc_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  x25519Ghost_lift_withAlloc_ok pubFromSecretBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_cliExt hC)))

theorem x25519PubFromSecretGhost_pureByteFunction_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (byVal : Bool := false) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal)) :=
  x25519Ghost_lift_ls_ok pubFromSecretBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_pureByteFunction byVal)))

theorem x25519PubFromSecretGhost_pureByteFunction_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (byVal : Bool := false) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  x25519Ghost_lift_ok pubFromSecretBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_pureByteFunction byVal)))

theorem x25519PubFromSecretGhost_pureByteFunction_keepsFs_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (byVal : Bool := false) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (pureByteFunctionSpec x25519PubFromSecretRef byVal)))) :=
  x25519Ghost_lift_keepsFs_ok pubFromSecretBridge
    (specSimulates_keepsFs
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_pureByteFunction byVal)))

theorem x25519PubFromSecretGhost_pureByteFunction_withAlloc_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (byVal : Bool := false) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withAlloc A lim (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  x25519Ghost_lift_withAlloc_ls_ok pubFromSecretBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_pureByteFunction byVal)))

theorem x25519PubFromSecretGhost_pureByteFunction_withAlloc_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (byVal : Bool := false) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withAlloc A lim (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  x25519Ghost_lift_withAlloc_ok pubFromSecretBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1904 ≤ extHookStack) (by decide)).trans
        (pubFromSecret_sim_pureByteFunction byVal)))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStack_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) :=
  x25519Ghost_lift_ls_ok pubFromSecretBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ hlo hhi).trans
        (pubFromSecret_sim_derivePublicKeyBytesStack stk)))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStack_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  x25519Ghost_lift_ok pubFromSecretBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ hlo hhi).trans
        (pubFromSecret_sim_derivePublicKeyBytesStack stk)))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStack_keepsFs_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))) :=
  x25519Ghost_lift_keepsFs_ok pubFromSecretBridge
    (specSimulates_keepsFs
      ((specSimulates_withStack_mono _ hlo hhi).trans
        (pubFromSecret_sim_derivePublicKeyBytesStack stk)))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStack_withAlloc_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  x25519Ghost_lift_withAlloc_ls_ok pubFromSecretBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ hlo hhi).trans
        (pubFromSecret_sim_derivePublicKeyBytesStack stk)))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStack_withAlloc_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  x25519Ghost_lift_withAlloc_ok pubFromSecretBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ hlo hhi).trans
        (pubFromSecret_sim_derivePublicKeyBytesStack stk)))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)) :=
  hookOk_withLsRet_of_simulates (derivePublicKeyBytesStack_sim_budget stk)
    (x25519PubFromSecretGhost_derivePublicKeyBytesStack_ok x25519Mpl stk hlo hhi)

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) := by
  rw [withLsRet_withVmPreserved]
  exact hookOk_withVmPreserved
    (x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ls_ok x25519Mpl stk hlo hhi)
    (x25519PubFromSecretGhost_vmPreserved x25519Mpl)

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_keepsFs_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs
        (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)))) := by
  have h1 : HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (keepsFs (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))) := by
    have hcomm : SpecSimulates
        (withVmPreserved (keepsFs (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))
        (keepsFs (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) := by
      refine SpecSimulates.of_map fun x R _ hpre => ⟨x, R, hpre, fun _ _ _ hpost => ?_⟩
      dsimp only [withVmPreserved, keepsFs] at hpost ⊢
      exact Satisfies.mono (by sep_entail) hpost
    exact hookOk_withLsRet_of_simulates hcomm
      (x25519PubFromSecretGhost_derivePublicKeyBytesStack_keepsFs_ok x25519Mpl stk hlo hhi)
  have h2 : HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (keepsFs (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
    hookOk_withLsRet_of_simulates (specSimulates_keepsFs (derivePublicKeyBytesStack_sim_budget stk)) h1
  rw [withLsRet_withVmPreserved]
  exact hookOk_withVmPreserved h2 (x25519PubFromSecretGhost_vmPreserved x25519Mpl)

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (hookOk_withVmPreserved
      (x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ls_ok x25519Mpl stk hlo hhi)
      (x25519PubFromSecretGhost_vmPreserved x25519Mpl))

theorem x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519PubFromSecretGhost x25519Mpl)
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) := by
  rw [withLsRet_withAlloc]
  exact x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ls_ok
    x25519Mpl A lim stk hlo hhi

theorem x25519PubFromSecretGhost_rowReplayOn_of_stub_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsPubFromSecretSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn (x25519ActiveInvMem x25519Mpl)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsPubFromSecretSym) (x25519Mpl.base 18)) :
    GhostRowReplayOn mpl mmpl InvS EG lsPubFromSecretSym (fun _ => True)
      (x25519PubFromSecretGhost x25519Mpl) :=
  x25519BlockGhost_rowReplayOn_of_stub mpl mmpl x25519Mpl InvS EG lsPubFromSecretSym
    (pubFromSecretBridge_of hPub) hInvX25519 hInvKeep hKeep hRealX25519NoExt hRealStubNone hStub

theorem x25519PubFromSecretGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsPubFromSecretSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn (x25519ActiveInvMem x25519Mpl)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsPubFromSecretSym) (x25519Mpl.base 18)) :
    GhostRowReplayOn mpl mmpl InvS EG lsPubFromSecretSym (fun _ => True)
      (x25519PubFromSecretGhost x25519Mpl) :=
  x25519PubFromSecretGhost_rowReplayOn_of_stub_of public_key_from_static_secret_ok
    mpl mmpl x25519Mpl InvS EG hInvX25519 hInvKeep hKeep hRealX25519NoExt hRealStubNone hStub

theorem x25519PubFromSecretGhost_rowReplayOn_of [LibsignalPlacement]
    (hPub : PublicKeyFromStaticSecretOk) (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsPubFromSecretSym = x25519Mpl.base 18)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsPubFromSecretSym (fun _ => True)
      (x25519PubFromSecretGhost x25519Mpl) :=
  x25519BlockGhost_rowReplayOn mpl mmpl x25519Mpl InvS EG lsPubFromSecretSym
    (pubFromSecretBridge_of hPub) hpl hTargetEq hInvX25519 hInvKeep hKeep hRealX25519NoExt

theorem x25519PubFromSecretGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsPubFromSecretSym = x25519Mpl.base 18)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsPubFromSecretSym (fun _ => True)
      (x25519PubFromSecretGhost x25519Mpl) :=
  x25519PubFromSecretGhost_rowReplayOn_of public_key_from_static_secret_ok
    mpl mmpl x25519Mpl InvS EG hpl hTargetEq hInvX25519 hInvKeep hKeep hRealX25519NoExt

theorem x25519PubFromSecretGhost_rowReplayOn_of_hookFree [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsPubFromSecretSym = x25519Mpl.base 18)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hFree : ∀ W : CliHooks,
      X25519BlocksHookFree (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) x25519Mpl) :
    GhostRowReplayOn mpl mmpl InvS EG lsPubFromSecretSym (fun _ => True)
      (x25519PubFromSecretGhost x25519Mpl) :=
  x25519PubFromSecretGhost_rowReplayOn mpl mmpl x25519Mpl InvS EG hpl hTargetEq
    hInvX25519 hInvKeep hKeep fun W _ hkp =>
      x25519BlocksHookFree_externAt_none_of_keep hpl (hFree W) hkp

/-! ### 5.2 `x25519DiffieHellmanGhost` (`lsDiffieHellmanSym`, Block `17`) `HookOk` & Replay -/

theorem x25519DiffieHellmanGhost_master_ok_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (keepsFs (withStack (diffieHellmanSpec x25519Ref) 1808))) :=
  x25519BlockGhost_ok (diffieHellmanBridge_of hDH)

theorem x25519DiffieHellmanGhost_master_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (keepsFs (withStack (diffieHellmanSpec x25519Ref) 1808))) :=
  x25519BlockGhost_ok diffieHellmanBridge

theorem x25519DiffieHellmanGhost_ls_ok_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk)) :=
  x25519Ghost_lift_ls_ok (diffieHellmanBridge_of hDH)
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519DiffieHellmanGhost_ls_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk)) :=
  x25519DiffieHellmanGhost_ls_ok_of static_secret_diffie_hellman_ok x25519Mpl stk hlo hhi

theorem x25519DiffieHellmanGhost_at_ok_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withVmPreserved (withStack (diffieHellmanSpec x25519Ref) stk))) :=
  x25519Ghost_lift_ok (diffieHellmanBridge_of hDH)
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519DiffieHellmanGhost_at_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withVmPreserved (withStack (diffieHellmanSpec x25519Ref) stk))) :=
  x25519DiffieHellmanGhost_at_ok_of static_secret_diffie_hellman_ok x25519Mpl stk hlo hhi

theorem x25519DiffieHellmanGhost_keepsFs_ok_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (withStack (diffieHellmanSpec x25519Ref) stk)))) :=
  x25519Ghost_lift_keepsFs_ok (diffieHellmanBridge_of hDH)
    (specSimulates_keepsFs (specSimulates_withStack_mono _ hlo hhi))

theorem x25519DiffieHellmanGhost_keepsFs_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (withStack (diffieHellmanSpec x25519Ref) stk)))) :=
  x25519DiffieHellmanGhost_keepsFs_ok_of static_secret_diffie_hellman_ok x25519Mpl stk hlo hhi

theorem x25519DiffieHellmanGhost_withAlloc_ls_ok_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withAlloc A lim (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk))) :=
  x25519Ghost_lift_withAlloc_ls_ok (diffieHellmanBridge_of hDH) A lim
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519DiffieHellmanGhost_withAlloc_ls_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withAlloc A lim (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk))) :=
  x25519DiffieHellmanGhost_withAlloc_ls_ok_of static_secret_diffie_hellman_ok x25519Mpl A lim stk hlo hhi

theorem x25519DiffieHellmanGhost_withAlloc_ok_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withAlloc A lim (withStack (diffieHellmanSpec x25519Ref) stk))) :=
  x25519Ghost_lift_withAlloc_ok (diffieHellmanBridge_of hDH) A lim
    (SpecSimulates.drop_keepsFs.trans (specSimulates_withStack_mono _ hlo hhi))

theorem x25519DiffieHellmanGhost_withAlloc_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withAlloc A lim (withStack (diffieHellmanSpec x25519Ref) stk))) :=
  x25519DiffieHellmanGhost_withAlloc_ok_of static_secret_diffie_hellman_ok x25519Mpl A lim stk hlo hhi

theorem x25519DiffieHellmanGhost_cliExt_ls_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl) (withLsRet (dhSpec C)) :=
  x25519Ghost_lift_ls_ok diffieHellmanBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1808 ≤ extHookStack) (by decide)).trans
        (diffieHellman_sim_cliExt hC)))

theorem x25519DiffieHellmanGhost_cliExt_ok [LibsignalPlacement] (x25519Mpl : MultiPlacement)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl) (withLsRet (withVmPreserved (dhSpec C))) :=
  x25519Ghost_lift_ok diffieHellmanBridge
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1808 ≤ extHookStack) (by decide)).trans
        (diffieHellman_sim_cliExt hC)))

theorem x25519DiffieHellmanGhost_cliExt_keepsFs_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withVmPreserved (keepsFs (dhSpec C)))) :=
  x25519Ghost_lift_keepsFs_ok diffieHellmanBridge
    (specSimulates_keepsFs
      ((specSimulates_withStack_mono _ (by decide : 1808 ≤ extHookStack) (by decide)).trans
        (diffieHellman_sim_cliExt hC)))

theorem x25519DiffieHellmanGhost_cliExt_withAlloc_ls_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withAlloc A lim (withLsRet (dhSpec C))) :=
  x25519Ghost_lift_withAlloc_ls_ok diffieHellmanBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1808 ≤ extHookStack) (by decide)).trans
        (diffieHellman_sim_cliExt hC)))

theorem x25519DiffieHellmanGhost_cliExt_withAlloc_ok [LibsignalPlacement]
    (x25519Mpl : MultiPlacement) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk (x25519DiffieHellmanGhost x25519Mpl)
      (withLsRet (withAlloc A lim (dhSpec C))) :=
  x25519Ghost_lift_withAlloc_ok diffieHellmanBridge A lim
    (SpecSimulates.drop_keepsFs.trans
      ((specSimulates_withStack_mono _ (by decide : 1808 ≤ extHookStack) (by decide)).trans
        (diffieHellman_sim_cliExt hC)))

theorem x25519DiffieHellmanGhost_rowReplayOn_of_stub_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsDiffieHellmanSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn (x25519ActiveInvMem x25519Mpl)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsDiffieHellmanSym) (x25519Mpl.base 17)) :
    GhostRowReplayOn mpl mmpl InvS EG lsDiffieHellmanSym (fun _ => True)
      (x25519DiffieHellmanGhost x25519Mpl) :=
  x25519BlockGhost_rowReplayOn_of_stub mpl mmpl x25519Mpl InvS EG lsDiffieHellmanSym
    (diffieHellmanBridge_of hDH) hInvX25519 hInvKeep hKeep hRealX25519NoExt hRealStubNone hStub

theorem x25519DiffieHellmanGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsDiffieHellmanSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn (x25519ActiveInvMem x25519Mpl)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsDiffieHellmanSym) (x25519Mpl.base 17)) :
    GhostRowReplayOn mpl mmpl InvS EG lsDiffieHellmanSym (fun _ => True)
      (x25519DiffieHellmanGhost x25519Mpl) :=
  x25519DiffieHellmanGhost_rowReplayOn_of_stub_of static_secret_diffie_hellman_ok
    mpl mmpl x25519Mpl InvS EG hInvX25519 hInvKeep hKeep hRealX25519NoExt hRealStubNone hStub

theorem x25519DiffieHellmanGhost_rowReplayOn_of [LibsignalPlacement]
    (hDH : StaticSecretDiffieHellmanOk) (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsDiffieHellmanSym = x25519Mpl.base 17)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsDiffieHellmanSym (fun _ => True)
      (x25519DiffieHellmanGhost x25519Mpl) :=
  x25519BlockGhost_rowReplayOn mpl mmpl x25519Mpl InvS EG lsDiffieHellmanSym
    (diffieHellmanBridge_of hDH) hpl hTargetEq hInvX25519 hInvKeep hKeep hRealX25519NoExt

theorem x25519DiffieHellmanGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsDiffieHellmanSym = x25519Mpl.base 17)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hRealX25519NoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      x25519MultiKeep x25519Mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsDiffieHellmanSym (fun _ => True)
      (x25519DiffieHellmanGhost x25519Mpl) :=
  x25519DiffieHellmanGhost_rowReplayOn_of static_secret_diffie_hellman_ok
    mpl mmpl x25519Mpl InvS EG hpl hTargetEq hInvX25519 hInvKeep hKeep hRealX25519NoExt

theorem x25519DiffieHellmanGhost_rowReplayOn_of_hookFree [LibsignalPlacement]
    (mpl mmpl x25519Mpl : MultiPlacement)
    (InvS : State → Prop) (EG : CliHooks → String → Option (State → State))
    (hpl : x25519CliMultiLib.Placeable x25519Mpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsDiffieHellmanSym = x25519Mpl.base 17)
    (hInvX25519 : ∀ u : State, InvS u → x25519ActiveInvMem x25519Mpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → x25519MultiKeep x25519Mpl lr = false)
    (hFree : ∀ W : CliHooks,
      X25519BlocksHookFree (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) x25519Mpl) :
    GhostRowReplayOn mpl mmpl InvS EG lsDiffieHellmanSym (fun _ => True)
      (x25519DiffieHellmanGhost x25519Mpl) :=
  x25519DiffieHellmanGhost_rowReplayOn mpl mmpl x25519Mpl InvS EG hpl hTargetEq
    hInvX25519 hInvKeep hKeep fun W _ hkp =>
      x25519BlocksHookFree_externAt_none_of_keep hpl (hFree W) hkp

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks
