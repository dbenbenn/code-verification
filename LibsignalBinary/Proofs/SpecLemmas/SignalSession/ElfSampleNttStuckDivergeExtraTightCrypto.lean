/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256Row -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512Row -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519Row -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore -- proof-setup: allow-public-import
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs

/-!
# Tight-Keep `SampleNTT` Non-Visitation for the 4 Crypto Rows (`ElfSampleNttStuckDivergeExtraTightCrypto`)

Discharges `StepsStrictAvoid` against `mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl)`
for the 4 crypto tight-keep rows:
`lsCompress256Sym`, `lsCompress512Sym`, `lsPubFromSecretSym`, and `lsDiffieHellmanSym`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCrypto

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj (MultiPlacedLib MultiPlacement Placement)
open ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E (Sha512State)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsCompress256Sym lsDiffieHellmanSym lsPubFromSecretSym)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256
  (compress256MasterRO_simulates_stackedMasterRO_roSep compress256StackedMasterROSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Lib sha2K32Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop (compress256_fnAddr)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
  (sha256KBytes sha256K_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
  (sha256CompressState_eq_spqrSha256Compress)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
  (compress256MasterROSpec compress256_master_ro_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512
  (compress512StackedMasterSpec compress512_master_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (compress512Lib sha2K64Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Loop (compress512_fnAddr)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells (sha512KBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
  (X25519CliRoOk specSimulates_withVmPreserved withRoOk x25519CliMultiLib_externAt_none
   x25519MultiKeep x25519_blockProgram_withTraceEq_keepsFs_withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks
  (X25519BlockBridge diffieHellmanBridge pubFromSecretBridge x25519ActiveGuard
   x25519ActiveGuard_stripS_setPC x25519ActiveInvMem x25519ActiveInvMem_stripExecOutside
   x25519BlockGhost x25519BlockGhost_keepLr_false_of_noException x25519DiffieHellmanGhost
   x25519PubFromSecretGhost)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates withRoData)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen SpecPreservesFsTrace SpecStripSInvariant)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
  (c2Compress256Pl c2Compress256Pl_base c2_compress256Lib_placeable c2_compress256_hKeep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256Row
  (c2_compress256_hCL c2_compress256_hRealHullNoExt c2_compress256_hRo)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512
  (c2Compress512Addr c2Compress512K64Addr lsCompress512Sym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512Row
  (c2Compress512LayoutFacts_of_linkedAt c2_compress512_hCL c2_compress512_hKeep
   c2_compress512_hRealHullNoExt c2_compress512_hRo)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_lsmpl c2Lib2RxSliceFacts_lsmpl c2ResolveFacts_lsmpl c2RoSliceFacts)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519 (c2X25519Mpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519Row
  (c2X25519LayoutFacts_of_linkedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256Ghost compress256SubProg compress256SubProg_codeLoaded_stripExecOutside
   compress256SubProg_externAt_none compress256SubProg_svc keepR_compress256
   masterCompress256ROSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays
  (compress512Ghost compress512Placement compress512Placement_base compress512SubProg
   compress512SubProg_codeLoaded_stripExecOutside compress512SubProg_externAt_none
   compress512SubProg_svc keepR_compress512 masterCompress512Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (linkedCallHookG_activeRealPre_of_noException linkedCallHookG_visitedIn roTableGuard
   roTableGuard_stripS withStateGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
  (keepLr_false_of_noException_via_activeRealPre specPreservesFsTrace_withLsRet
   specStripSInvariant_withLsRet subroutine_ok_withRoData_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg_externAt_none emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (subroutine_ok_withLsRet withLsRet withLsRet_frameLeft withLsRet_outcome_setPC
   withLsRet_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519GhostReplays
  (c2_x25519_activeInvMem_of_f3CodeInv c2_x25519_keep_lr_false c2_x25519_realNoExt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
  (c2S5Addrs setPC_eq_self_of_pc_eq stepsStrictAvoid_s5_of_visitedIn_all_false)

/-! ## 1. Row 1: `lsCompress256Sym` (`compress256_avoidS5`) -/

set_option maxRecDepth 400000 in
private theorem c2Compress256Keep_s5_all_false :
    (c2S5Addrs.all fun p => !(keepR_compress256 c2Compress256Pl p)) = true := by
  decide +kernel

private theorem sha256KBytes_length_le : sha256KBytes.length ≤ 2 ^ 64 := by
  have h : sha256KBytes.length = 256 := by
    simp [sha256KBytes, List.length_flatMap, unpack32_length, sha256K_length]
  omega

private theorem specStripSInvariant_masterCompress256RO (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterCompress256ROSpec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem specStripSInvariant_masterCompress256ROLs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (withLsRet masterCompress256ROSpec) :=
  specStripSInvariant_withLsRet (specStripSInvariant_masterCompress256RO keep)

private theorem specPreservesFsTrace_masterCompress256RO :
    SpecPreservesFsTrace masterCompress256ROSpec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterCompress256ROSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.1
    have htr : sf.trace = s0.trace := hpost.1.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem specPreservesFsTrace_masterCompress256ROLs [LibsignalPlacement] :
    SpecPreservesFsTrace (withLsRet masterCompress256ROSpec) :=
  specPreservesFsTrace_withLsRet specPreservesFsTrace_masterCompress256RO

private theorem masterCompress256RO_pre_setPC
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    masterCompress256ROSpec.pre x (s.setPC pc) = masterCompress256ROSpec.pre x s := by
  cases s; rfl

private theorem masterCompress256RO_outcome_setPC
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterCompress256ROSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterCompress256ROSpec x R s0 sf := by
  rcases h with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨by cases s0; exact hret, by cases s0; exact hcc, ?_⟩
    have heq : masterCompress256ROSpec.post x (s0.setPC pc) sf =
        masterCompress256ROSpec.post x s0 sf := by
      cases s0; rfl
    rwa [heq] at hpost
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem masterCompress256ROLs_pre_setPC [LibsignalPlacement]
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    (withLsRet masterCompress256ROSpec).pre x (s.setPC pc) =
      (withLsRet masterCompress256ROSpec).pre x s :=
  withLsRet_pre_setPC masterCompress256RO_pre_setPC x s pc

private theorem masterCompress256ROLs_outcome_setPC [LibsignalPlacement]
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (withLsRet masterCompress256ROSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLsRet masterCompress256ROSpec) x R s0 sf :=
  withLsRet_outcome_setPC masterCompress256RO_outcome_setPC x R s0 sf pc h

set_option maxRecDepth 400000 in
private theorem compress256StackedMasterRO_subroutine_ok {pl : Placement}
    (hpl : compress256Lib.Placeable pl) {hookStack : Nat} (hstack : 176 ≤ hookStack) :
    subroutine_ok (compress256SubProg pl) pl.base
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes (compress256StackedMasterROSpec hookStack)) := by
  have hm := compress256_master_ro_ok hpl (P := compress256SubProg pl)
    (fun _ _ => compress256SubProg_externAt_none pl _)
  rw [compress256_fnAddr pl] at hm
  have hsim : SpecSimulates (compress256MasterROSpec (pl.ρ sha2K32Sym))
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes (compress256StackedMasterROSpec hookStack)) :=
    (compress256MasterRO_simulates_stackedMasterRO_roSep (pl.ρ sha2K32Sym) hstack).trans
      (SpecSimulates.withRoData_of_sep sha256KBytes_length_le)
  have hm_sim :=
    (LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift.SpecSimulates.withPlacedCodeLoaded
      hsim compress256Lib pl).subroutine_ok hm
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hL0 : (compress256Lib.program pl).CodeLoaded s0.mem := by
    have hb : (compress256SubProg pl).base = (compress256Lib.program pl).base := rfl
    have hc : (compress256SubProg pl).code = (compress256Lib.program pl).code := rfl
    refine Program.CodeLoaded.intro (hb ▸ hLP.aligned) (hb ▸ hc ▸ hLP.no_wrap) fun i hi => ?_
    have hi' : i < (compress256SubProg pl).code.length := hc.symm ▸ hi
    have hget? : (compress256SubProg pl).code[i]? = (compress256Lib.program pl).code[i]? :=
      congrArg (fun l => l[i]?) hc
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hget?
    rw [← hb, ← Option.some.inj hget?]
    exact ⟨hLP.byte_eq i hi', hLP.perm_eq i hi', hLP.isLazyFree_eq i hi'⟩
  have hpre_cl : s0.mem ⊨
      (LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift.withPlacedCodeLoaded
        compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (compress256StackedMasterROSpec hookStack))).pre x s0 ∗ R := by
    dsimp only [LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift.withPlacedCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, satisfies_pure_sepConj]
    exact ⟨hL0, hpre⟩
  exact hm_sim.mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ h => h)

private theorem subroutine_ok_masterCompress256RO {pl : Placement}
    (hpl : compress256Lib.Placeable pl) :
    subroutine_ok (compress256SubProg pl) pl.base
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes masterCompress256ROSpec) := by
  have hst := compress256StackedMasterRO_subroutine_ok hpl (by decide : 176 ≤ 176)
  apply subroutine_ok.of_codeLoaded
  intro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp _
  refine hst.mono_outcome (ro, stA, st, blkA, bs, n) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, compress256StackedMasterROSpec] at hpost
    dsimp only [withRoData, masterCompress256ROSpec]
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨⟨hpf, _⟩, hmem⟩ := hpost
    rw [sha256CompressState_eq_spqrSha256Compress] at hmem
    exact ⟨⟨hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2.1, hpf.2.2.2.2.1,
            hpf.2.2.2.2.2.1, hpf.2.2.2.2.2.2.1⟩, hmem⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem subroutine_ok_masterCompress256ROLs [LibsignalPlacement] {pl : Placement}
    (hpl : compress256Lib.Placeable pl) :
    subroutine_ok (compress256SubProg pl) pl.base
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes (withLsRet masterCompress256ROSpec)) :=
  subroutine_ok_withRoData_withLsRet (subroutine_ok_masterCompress256RO hpl)

theorem compress256_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsCompress256Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (compress256Ghost c2Compress256Pl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (compress256Ghost c2Compress256Pl u) := by
  have _ := hrun
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hTargetEq : libsignalSessionLib.resolve lsmpl lsCompress256Sym = c2Compress256Pl.base :=
    hRes.compress256_eq.trans c2Compress256Pl_base.symm
  have hGu : roTableGuard (c2Compress256Pl.ρ sha2K32Sym) sha256KBytes u :=
    c2_compress256_hRo c2RoSliceFacts.compress256K32Slice hLs
      (InvS := fun z => F3CodeInv lsmpl mmpl z.mem) (fun _ h => h) u hinv
  have hActPre := linkedCallHookG_activeRealPre_of_noException hnoex
  have hlr_out : keepR_compress256 c2Compress256Pl (u.readReg64 .lr) = false :=
    keepLr_false_of_noException_via_activeRealPre
      (fun _ hlr => c2_compress256_hKeep hLs hlr)
      linkedCallHookG_activeRealPre_of_noException hnoex
  have hCL : (compress256SubProg c2Compress256Pl).CodeLoaded u.mem :=
    c2_compress256_hCL hRx.compress256
      (InvS := fun z => F3CodeInv lsmpl mmpl z.mem) (fun _ h => h) u hinv
  have hCodeSub :
      (compress256SubProg c2Compress256Pl).CodeLoaded
        (stripExecOutside (keepR_compress256 c2Compress256Pl) u.mem) :=
    compress256SubProg_codeLoaded_stripExecOutside c2_compress256Lib_placeable hCL
  obtain ⟨hvis, _⟩ := linkedCallHookG_visitedIn
    emptyStdProg_svc
    (compress256SubProg_svc c2Compress256Pl)
    (fun pc _ => emptyStdProg_externAt_none pc)
    (compress256SubProg_externAt_none c2Compress256Pl)
    (roTableGuard_stripS (keepR_compress256 c2Compress256Pl) c2Compress256Pl.base
      (c2Compress256Pl.ρ sha2K32Sym) sha256KBytes)
    (subroutine_ok_masterCompress256ROLs c2_compress256Lib_placeable)
    (specStripSInvariant_masterCompress256ROLs (keepR_compress256 c2Compress256Pl))
    specPreservesFsTrace_masterCompress256ROLs
    masterCompress256ROLs_pre_setPC
    masterCompress256ROLs_outcome_setPC
    hGu hActPre hfr hlr_out hCodeSub
  rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)] at hvis
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    (fun _ hk => c2_compress256_hRealHullNoExt hExt W hk)
    c2Compress256Keep_s5_all_false
    hvis

/-! ## 2. Row 2: `lsCompress512Sym` (`compress512_avoidS5`) -/

set_option maxRecDepth 400000 in
private theorem c2Compress512Keep_s5_all_false :
    (c2S5Addrs.all fun p =>
      !(keepR_compress512 (compress512Placement c2Compress512Addr c2Compress512K64Addr) p)) =
      true := by
  decide +kernel

private theorem specStripSInvariant_masterCompress512 (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterCompress512Spec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem specStripSInvariant_masterCompress512Ls [LibsignalPlacement]
    (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (withLsRet masterCompress512Spec) :=
  specStripSInvariant_withLsRet (specStripSInvariant_masterCompress512 keep)

private theorem specPreservesFsTrace_masterCompress512 :
    SpecPreservesFsTrace masterCompress512Spec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterCompress512Spec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.1
    have htr : sf.trace = s0.trace := hpost.1.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem specPreservesFsTrace_masterCompress512Ls [LibsignalPlacement] :
    SpecPreservesFsTrace (withLsRet masterCompress512Spec) :=
  specPreservesFsTrace_withLsRet specPreservesFsTrace_masterCompress512

private theorem masterCompress512_pre_setPC
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    masterCompress512Spec.pre x (s.setPC pc) = masterCompress512Spec.pre x s := by
  cases s; rfl

private theorem masterCompress512_outcome_setPC
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterCompress512Spec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterCompress512Spec x R s0 sf := by
  rcases h with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨by cases s0; exact hret, by cases s0; exact hcc, ?_⟩
    have heq : masterCompress512Spec.post x (s0.setPC pc) sf =
        masterCompress512Spec.post x s0 sf := by
      cases s0; rfl
    rwa [heq] at hpost
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem masterCompress512Ls_pre_setPC [LibsignalPlacement]
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    (withLsRet masterCompress512Spec).pre x (s.setPC pc) =
      (withLsRet masterCompress512Spec).pre x s :=
  withLsRet_pre_setPC masterCompress512_pre_setPC x s pc

private theorem masterCompress512Ls_outcome_setPC [LibsignalPlacement]
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (withLsRet masterCompress512Spec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLsRet masterCompress512Spec) x R s0 sf :=
  withLsRet_outcome_setPC masterCompress512_outcome_setPC x R s0 sf pc h

set_option maxRecDepth 400000 in
private theorem compress512StackedMaster_subroutine_ok {pl : Placement}
    (hpl : compress512Lib.Placeable pl) {hookStack : Nat} (hstack : 256 ≤ hookStack) :
    subroutine_ok (compress512SubProg pl) pl.base
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes (compress512StackedMasterSpec hookStack)) := by
  have hm := compress512_master_ok hpl (P := compress512SubProg pl)
    (fun _ _ => compress512SubProg_externAt_none pl _) hstack
  rw [compress512_fnAddr pl] at hm
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hL0 : (compress512Lib.program pl).CodeLoaded s0.mem := by
    have hb : (compress512SubProg pl).base = (compress512Lib.program pl).base := rfl
    have hc : (compress512SubProg pl).code = (compress512Lib.program pl).code := rfl
    refine Program.CodeLoaded.intro (hb ▸ hLP.aligned) (hb ▸ hc ▸ hLP.no_wrap) fun i hi => ?_
    have hi' : i < (compress512SubProg pl).code.length := hc.symm ▸ hi
    have hget? : (compress512SubProg pl).code[i]? = (compress512Lib.program pl).code[i]? :=
      congrArg (fun l => l[i]?) hc
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hget?
    rw [← hb, ← Option.some.inj hget?]
    exact ⟨hLP.byte_eq i hi', hLP.perm_eq i hi', hLP.isLazyFree_eq i hi'⟩
  have hpre_cl : s0.mem ⊨
      (LibsignalBinary.Proofs.HookDischarge.CryptoSha512.StepsLift.withPlacedCodeLoaded
        compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (compress512StackedMasterSpec hookStack))).pre x s0 ∗ R := by
    dsimp only [LibsignalBinary.Proofs.HookDischarge.CryptoSha512.StepsLift.withPlacedCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, satisfies_pure_sepConj]
    exact ⟨hL0, hpre⟩
  exact hm.mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ h => h)

private theorem subroutine_ok_masterCompress512 {pl : Placement}
    (hpl : compress512Lib.Placeable pl) :
    subroutine_ok (compress512SubProg pl) pl.base
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes masterCompress512Spec) := by
  have hst := compress512StackedMaster_subroutine_ok hpl (by decide : 256 ≤ 256)
  apply subroutine_ok.of_codeLoaded
  intro ⟨stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp _
  refine hst.mono_outcome (stA, st, blkA, bs, n) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, compress512StackedMasterSpec] at hpost
    dsimp only [withRoData, masterCompress512Spec]
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨⟨hpf, _⟩, hmem⟩ := hpost
    exact ⟨⟨hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2.1, hpf.2.2.2.2.1,
            hpf.2.2.2.2.2.1, hpf.2.2.2.2.2.2.1⟩, hmem⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem subroutine_ok_masterCompress512Ls [LibsignalPlacement] {pl : Placement}
    (hpl : compress512Lib.Placeable pl) :
    subroutine_ok (compress512SubProg pl) pl.base
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes (withLsRet masterCompress512Spec)) :=
  subroutine_ok_withRoData_withLsRet (subroutine_ok_masterCompress512 hpl)

theorem compress512_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsCompress512Sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (compress512Ghost (compress512Placement c2Compress512Addr c2Compress512K64Addr) u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (compress512Ghost (compress512Placement c2Compress512Addr c2Compress512K64Addr) u) := by
  have _ := hrun
  let pl := compress512Placement c2Compress512Addr c2Compress512K64Addr
  have hLay := c2Compress512LayoutFacts_of_linkedAt hLs
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hTargetEq : libsignalSessionLib.resolve lsmpl lsCompress512Sym = pl.base :=
    hLay.resolve_eq.trans (compress512Placement_base c2Compress512Addr c2Compress512K64Addr).symm
  have hGu : roTableGuard (pl.ρ sha2K64Sym) sha512KBytes u :=
    c2_compress512_hRo hLay hLs
      (InvS := fun z => F3CodeInv lsmpl mmpl z.mem) (fun _ h => h) u hinv
  have hActPre := linkedCallHookG_activeRealPre_of_noException hnoex
  have hlr_out : keepR_compress512 pl (u.readReg64 .lr) = false :=
    keepLr_false_of_noException_via_activeRealPre
      (fun _ hlr => c2_compress512_hKeep hLay hLs hlr)
      linkedCallHookG_activeRealPre_of_noException hnoex
  have hCL : (compress512SubProg pl).CodeLoaded u.mem :=
    c2_compress512_hCL hLay
      (InvS := fun z => F3CodeInv lsmpl mmpl z.mem) (fun _ h => h) u hinv
  have hCodeSub :
      (compress512SubProg pl).CodeLoaded (stripExecOutside (keepR_compress512 pl) u.mem) :=
    compress512SubProg_codeLoaded_stripExecOutside hLay.placeable hCL
  obtain ⟨hvis, _⟩ := linkedCallHookG_visitedIn
    emptyStdProg_svc
    (compress512SubProg_svc pl)
    (fun pc _ => emptyStdProg_externAt_none pc)
    (compress512SubProg_externAt_none pl)
    (roTableGuard_stripS (keepR_compress512 pl) pl.base (pl.ρ sha2K64Sym) sha512KBytes)
    (subroutine_ok_masterCompress512Ls hLay.placeable)
    (specStripSInvariant_masterCompress512Ls (keepR_compress512 pl))
    specPreservesFsTrace_masterCompress512Ls
    masterCompress512Ls_pre_setPC
    masterCompress512Ls_outcome_setPC
    hGu hActPre hfr hlr_out hCodeSub
  rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)] at hvis
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    (fun _ hk => c2_compress512_hRealHullNoExt hLay hExt W hk)
    c2Compress512Keep_s5_all_false
    hvis

/-! ## 3. Rows 3 & 4: `lsPubFromSecretSym` & `lsDiffieHellmanSym` (`x25519BlockGhost_avoidS5`) -/

set_option maxRecDepth 400000 in
private theorem c2X25519MultiKeep_s5_all_false :
    (c2S5Addrs.all fun p => !(x25519MultiKeep c2X25519Mpl p)) = true := by
  decide +kernel

private theorem x25519BlockProgram_svc (x25519Mpl : MultiPlacement) (j : Nat) :
    (x25519CliMultiLib.blockProgram x25519Mpl j).svc = Syscall.standard := rfl

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
    ⟨y, R, hpre, fun _ _ _ hpost => ?_⟩
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
    fun x R s0 hpre => ⟨x, R, hpre, fun _ hout => by
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

private theorem x25519BlockGhost_avoidS5 [LibsignalPlacement]
    {mmpl : MultiPlacement} {sym : String} {j : Nat} {α β : Type}
    {blockSpec : MultiPlacement → Spec β} {master : Spec α} {fallback : State → State}
    (B : X25519BlockBridge j blockSpec master fallback)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hTargetEq : libsignalSessionLib.resolve lsmpl sym = c2X25519Mpl.base j)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hnoex : ∀ msg, (x25519BlockGhost c2X25519Mpl j master fallback u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (x25519BlockGhost c2X25519Mpl j master fallback u) := by
  have hLay := c2X25519LayoutFacts_of_linkedAt hLs
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hInvM : x25519ActiveInvMem c2X25519Mpl u.mem :=
    c2_x25519_activeInvMem_of_f3CodeInv hLay hLs hinv
  have hGu : x25519ActiveGuard c2X25519Mpl u := hInvM
  have hActPre := linkedCallHookG_activeRealPre_of_noException hnoex
  have hlr_out : x25519MultiKeep c2X25519Mpl (u.readReg64 .lr) = false :=
    x25519BlockGhost_keepLr_false_of_noException (c2_x25519_keep_lr_false hLay hLs) hnoex
  have hCodeSub :
      (x25519CliMultiLib.blockProgram c2X25519Mpl j).CodeLoaded
        (stripExecOutside (x25519MultiKeep c2X25519Mpl) u.mem) :=
    (x25519ActiveInvMem_stripExecOutside hInvM).2.1 j B.hj
  obtain ⟨hvis, _⟩ := linkedCallHookG_visitedIn
    emptyStdProg_svc
    (x25519BlockProgram_svc c2X25519Mpl j)
    (fun pc _ => emptyStdProg_externAt_none pc)
    (x25519CliMultiLib_externAt_none c2X25519Mpl j B.hj (fun _ => none))
    (fun s0 hFr hG => x25519ActiveGuard_stripS_setPC c2X25519Mpl (c2X25519Mpl.base j) s0 hFr hG)
    (x25519SubroutineOk_guarded_withLsRet B c2X25519Mpl)
    (specStripSInvariant_withLsRet (B.strip_inv (x25519MultiKeep c2X25519Mpl)))
    (specPreservesFsTrace_withLsRet (x25519Bridge_preservesFsTrace B))
    (withLsRet_pre_setPC B.pre_pc)
    (withLsRet_outcome_setPC B.out_pc)
    hGu hActPre hfr hlr_out hCodeSub
  rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)] at hvis
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    (fun _ hk => c2_x25519_realNoExt hLay hExt W hk)
    c2X25519MultiKeep_s5_all_false
    hvis

theorem x25519PubFromSecret_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsPubFromSecretSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (x25519PubFromSecretGhost c2X25519Mpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (x25519PubFromSecretGhost c2X25519Mpl u) := by
  have _ := hrun
  exact x25519BlockGhost_avoidS5 pubFromSecretBridge hLs
    (c2X25519LayoutFacts_of_linkedAt hLs).resolve_pubFromSecret W hpc hnoex hfr hinv

theorem x25519DiffieHellman_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsDiffieHellmanSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (x25519DiffieHellmanGhost c2X25519Mpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (x25519DiffieHellmanGhost c2X25519Mpl u) := by
  have _ := hrun
  exact x25519BlockGhost_avoidS5 diffieHellmanBridge hLs
    (c2X25519LayoutFacts_of_linkedAt hLs).resolve_diffieHellman W hpc hnoex hfr hinv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCrypto
