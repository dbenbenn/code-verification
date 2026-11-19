/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Pure
import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwned
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPoll
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Shims
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Poll Stage P2 V1 Base Callees and Stack Bounds

Proves stack bounds (`stageP2V1CallStack_le_subStack`, `stageP2CallStack4K_le_subStack`), `FsAt`
lifts (`cliPollStageP2_fsAt`), error payload entailments, and pure internal callee bundles
(`cliInitBobErrOwned_ok`, `cliStageP2PureCallees_ok`) for Stage P2 V1.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Stack Arithmetic & Error Payload Helpers -/

/-- Non-null guarantee for stack pointer `sp - 576#64` when `dpClosSubStack B ≤ sp.toNat`. -/
theorem sp_sub_576_ne_zero (B : RunBudgets) {sp : BitVec 64}
    (hle : dpClosSubStack B ≤ sp.toNat) :
    sp - 576#64 ≠ 0#64 := by
  have h524 : 524288 ≤ dpClosSubStack B := by
    dsimp only [dpClosSubStack]; omega
  intro heq
  have h1 : (sp - 576#64).toNat = 0 := congrArg BitVec.toNat heq
  have hlt : (576#64 : BitVec 64).toNat ≤ sp.toNat := by
    change 576 ≤ sp.toNat; omega
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hlt)] at h1
  change sp.toNat - 576 = 0 at h1
  omega

/-- Lift `P ⊢ decResAt A outPtr r` to `P ⊢ decResAt A outPtr r ∗ anyHeap`. -/
theorem entails_decResAt_anyHeap_of_err_ext {A : RustAlloc}
    {P : SepProp} (outPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (h : P ⊢ decResAt A outPtr (.error err)) :
    P ⊢ decResAt A outPtr (.error err) ∗ anyHeap :=
  Entails.trans h (entails_sepConj_anyHeap _)

/-- Lift `P ⊢ decResAt A0 outPtr r` to `P ⊢ decResAt A0 outPtr r ∗ anyHeap`. -/
theorem entails_decResAt_anyHeap_of_err
    {P : SepProp} (outPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (h : P ⊢ decResAt E2E.HooksE.A0 outPtr (.error err)) :
    P ⊢ decResAt E2E.HooksE.A0 outPtr (.error err) ∗ anyHeap :=
  entails_decResAt_anyHeap_of_err_ext outPtr err h

/-! ## 2. Stack Budget, Pure Callees Bridge, & `FsAt` -/

/-- `stageP2V1CallStack` fits within `dpClosSubStack B` for the CLI Poll store kits. -/
theorem stageP2V1CallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, _, _, _, _, _, _, hkpS, hkpP, hregS, hregP,
    hpkS, hpkP, _, _, hspkS, hspkP, hkpkS, hkpkP, _, _⟩
  have hPure := stageP2PureAndErrStack_le_subStack B
  have hb700 : stageP2bStack + 0x700 ≤ dpClosSubStack B := by
    have h0 : stageP2bStack + 0x700 ≤ 1048576 - 3280 := by decide
    exact Nat.le_trans h0 (Nat.le_add_right _ _)
  let spkK := cliPollSpkKit A b F0 spkId (cliKitStk B)
  let kpkK := cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B)
  let pkK := cliPollPkKit A b F0 opkIdWord (cliKitStk B)
  let selfK := cliPollSelfKit A b F0 peer (cliKitStk B)
  change stageP2V1CallStack spkK kpkK pkK selfK ≤ dpClosSubStack B
  have hs1 : spkK.getShimStack = (cliKitStk B).spkGetShim := rfl
  have hs2 : spkK.getPollStack = (cliKitStk B).spkGetPoll := rfl
  have hk1 : kpkK.getShimStack = (cliKitStk B).kpkGetShim := rfl
  have hk2 : kpkK.getPollStack = (cliKitStk B).kpkGetPoll := rfl
  have hp1 : pkK.getShimStack = (cliKitStk B).pkGetShim := rfl
  have hp2 : pkK.getPollStack = (cliKitStk B).pkGetPoll := rfl
  have hi1 : selfK.kpShimStack = (cliKitStk B).kpShim := rfl
  have hi2 : selfK.kpPollStack = (cliKitStk B).kpPoll := rfl
  have hi3 : selfK.regIdShimStack = (cliKitStk B).regIdShim := rfl
  have hi4 : selfK.regIdPollStack = (cliKitStk B).regIdPoll := rfl
  have hpure_eq : Kits.stageP2PureAndErrStack = Poll.stageP2PureAndErrStack := rfl
  dsimp only [stageP2V1CallStack, Kits.stageP2CallStack, stageP2Sub1To4Stack, stageP2Sub56Stack,
    spkGetCallStack, kpkGetCallStack, pkGetCallStack, selfKpCallStack, selfRegIdCallStack]
  rw [hs1, hs2, hk1, hk2, hp1, hp2, hi1, hi2, hi3, hi4, hpure_eq]
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr
    ⟨Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hspkS, Nat.max_le.mpr ⟨hspkP, hPure⟩⟩,
       Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hkpkS, Nat.max_le.mpr ⟨hkpkP, hPure⟩⟩,
         Nat.max_le.mpr ⟨hpkS, Nat.max_le.mpr ⟨hpkP, hPure⟩⟩⟩⟩,
     Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hkpS, Nat.max_le.mpr ⟨hkpP, hPure⟩⟩,
       Nat.max_le.mpr ⟨hregS, Nat.max_le.mpr ⟨hregP, hPure⟩⟩⟩⟩, hb700⟩

/-- `Kits.stageP2PureAndErrStack4K` (`33536` B) fits within `dpClosSubStack B`. -/
theorem stageP2PureAndErrStack4K_le_subStack (B : RunBudgets) :
    Kits.stageP2PureAndErrStack4K ≤ dpClosSubStack B :=
  Nat.le_trans (by decide : Kits.stageP2PureAndErrStack4K ≤ 1048576 - 3280) (Nat.le_add_right _ _)

/-- `Kits.stageP2CallStack4K` (and `stageP2bStack + 0x700`) fits within `dpClosSubStack B` for the
CLI Poll store kits. -/
theorem stageP2CallStack4K_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    max
      (Kits.stageP2CallStack4K
        (cliPollSpkKit A b F0 spkId (cliKitStk B))
        (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
        (cliPollSelfKit A b F0 peer (cliKitStk B)))
      (stageP2bStack + 0x700) ≤ dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, _, _, _, _, _, _, hkpS, hkpP, hregS, hregP,
    hpkS, hpkP, _, _, hspkS, hspkP, hkpkS, hkpkP, _, _⟩
  have hPure4K := stageP2PureAndErrStack4K_le_subStack B
  have hb700 : stageP2bStack + 0x700 ≤ dpClosSubStack B :=
    Nat.le_trans (by decide : stageP2bStack + 0x700 ≤ 1048576 - 3280) (Nat.le_add_right _ _)
  let spkK := cliPollSpkKit A b F0 spkId (cliKitStk B)
  let kpkK := cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B)
  let pkK := cliPollPkKit A b F0 opkIdWord (cliKitStk B)
  let selfK := cliPollSelfKit A b F0 peer (cliKitStk B)
  change max (Kits.stageP2CallStack4K spkK kpkK pkK selfK) (stageP2bStack + 0x700) ≤ dpClosSubStack B
  have hs1 : spkK.getShimStack = (cliKitStk B).spkGetShim := rfl
  have hs2 : spkK.getPollStack = (cliKitStk B).spkGetPoll := rfl
  have hk1 : kpkK.getShimStack = (cliKitStk B).kpkGetShim := rfl
  have hk2 : kpkK.getPollStack = (cliKitStk B).kpkGetPoll := rfl
  have hp1 : pkK.getShimStack = (cliKitStk B).pkGetShim := rfl
  have hp2 : pkK.getPollStack = (cliKitStk B).pkGetPoll := rfl
  have hi1 : selfK.kpShimStack = (cliKitStk B).kpShim := rfl
  have hi2 : selfK.kpPollStack = (cliKitStk B).kpPoll := rfl
  have hi3 : selfK.regIdShimStack = (cliKitStk B).regIdShim := rfl
  have hi4 : selfK.regIdPollStack = (cliKitStk B).regIdPoll := rfl
  dsimp only [Kits.stageP2CallStack4K, Kits.stageP2Sub1To4Stack4K, Kits.stageP2Sub56Stack4K,
    Kits.spkGetCallStack4K, Kits.kpkGetCallStack4K, Kits.pkGetCallStack4K,
    Kits.selfKpCallStack4K, Kits.selfRegIdCallStack4K]
  rw [hs1, hs2, hk1, hk2, hp1, hp2, hi1, hi2, hi3, hi4]
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr
    ⟨Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hspkS, Nat.max_le.mpr ⟨hspkP, hPure4K⟩⟩,
       Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hkpkS, Nat.max_le.mpr ⟨hkpkP, hPure4K⟩⟩,
         Nat.max_le.mpr ⟨hpkS, Nat.max_le.mpr ⟨hpkP, hPure4K⟩⟩⟩⟩,
     Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hkpS, Nat.max_le.mpr ⟨hkpP, hPure4K⟩⟩,
       Nat.max_le.mpr ⟨hregS, Nat.max_le.mpr ⟨hregP, hPure4K⟩⟩⟩⟩, hb700⟩

/-- `StructuralPrims` for `modelPrims X P`. -/
theorem cliModelPrims_structural_ext (X : UnreachedPqxdhPrimitives) (P : PEParams) :
    StructuralPrims (modelPrims X P) :=
  Pqxdh.Initiator.structuralPrims_initiatorModelPrims X P

/-- `StructuralPrims` for `modelPrims X ⟨W.C, W.Q⟩`. -/
theorem cliModelPrims_structural (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    StructuralPrims (modelPrims X ⟨W.C, W.Q⟩) :=
  cliModelPrims_structural_ext X ⟨W.C, W.Q⟩

/-- `PrimitivesMatchCrypto` for `modelPrims X P`. -/
theorem cliModelPrims_matchCrypto_ext (X : UnreachedPqxdhPrimitives) (P : PEParams) :
    PrimitivesMatchCrypto (modelPrims X P) P.C :=
  Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X P

/-- `PrimitivesMatchCrypto` for `modelPrims X ⟨W.C, W.Q⟩`. -/
theorem cliModelPrims_matchCrypto (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    PrimitivesMatchCrypto (modelPrims X ⟨W.C, W.Q⟩) W.C :=
  cliModelPrims_matchCrypto_ext X ⟨W.C, W.Q⟩

private theorem ofU8_toU8_base : ∀ bs : List (BitVec 8), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg₂ List.cons rfl (ofU8_toU8_base rest)

private theorem shared_bytesToBv8_eq_ofU8_base :
    ∀ bs : List UInt8, Shared.bytesToBv8 bs = ofU8 bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      ((BitVec.ofNat_toNat 8 b.toBitVec).trans b.toBitVec.setWidth_eq)
      (shared_bytesToBv8_eq_ofU8_base rest)

private theorem u8Vec_toList_eq_bytesToBv8_base {n : Nat} {bs : List UInt8} (h : bs.length = n) :
    (u8Vec n bs).toList = Shared.bytesToBv8 bs := by
  have hof : (ofU8 bs).length = n := by simp [ofU8, h]
  change ((ofU8 bs ++ List.replicate n 0#8).take n) = Shared.bytesToBv8 bs
  rw [shared_bytesToBv8_eq_ofU8_base, List.take_append_of_le_length (Nat.le_of_eq hof.symm),
    List.take_of_length_le (Nat.le_of_eq hof)]

private theorem fitBv8_vecU8_eq_base {n : Nat} (v : List.Vector (BitVec 8) n) :
    Initiator.fitBv8 n (E2E.vecU8 v) = v.toList := by
  have hlen : (E2E.vecU8 v).length = n := by simp [E2E.vecU8, toU8, v.toList_length]
  change Shared.fitBv8 n (E2E.vecU8 v) = v.toList
  rw [Shared.fitBv8_eq_bytesToBv8 hlen, shared_bytesToBv8_eq_ofU8_base, E2E.vecU8, ofU8_toU8_base]

private theorem optEdAt_entails_dalekMontToEdOutAt_base
    (X : UnreachedPqxdhPrimitives) (P : PEParams) (outPtr : BitVec 64)
    (inBytes : List UInt8) (signBit : UInt8) :
    CliExt.optionEdwardsPointAt outPtr
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.legacyMontToEd
        (u8Vec 32 inBytes) (BitVec.ofNat 8 signBit.toNat &&& 1#8)) ⊢
      ResponderCore.dalekMontToEdOutAt
        (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P))
        outPtr inBytes (signBit &&& 1) := by
  have hsign : BitVec.ofNat 8 signBit.toNat &&& 1#8 = (signBit &&& 1).toBitVec := by
    rcases signBit with ⟨v⟩
    simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, UInt8.toBitVec_and]
    rfl
  have hmte :
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P)).montToEd inBytes (signBit &&& 1) =
        (LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.legacyMontToEd
          (u8Vec 32 inBytes) (signBit &&& 1).toBitVec).map E2E.vecU8 := by
    dsimp only [ResponderCore.ofSignalPqxdhPrimitives, SignalPqxdh.Primitives.montToEdBytes,
      modelPrims, blockLevelPrims,
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.legacyMontToEd]
    cases SignalPqxdh.montLiftEd (u8Vec 32 inBytes).toList (signBit &&& 1).toBitVec <;> rfl
  unfold ResponderCore.dalekMontToEdOutAt
  rw [hsign, hmte]
  cases hres :
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.legacyMontToEd
      (u8Vec 32 inBytes) (signBit &&& 1).toBitVec with
  | none =>
    exact Entails.of_eq rfl
  | some ed =>
    dsimp only [CliExt.optionEdwardsPointAt, Option.map]
    have hu64 : Initiator.u64le 1#64 = unpack64 1#64 := by decide
    rw [fitBv8_vecU8_eq_base ed, hu64, pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes]
    exact Entails.of_eq rfl

/-- `pqxdhAccept = none` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem pqxdhAcceptErr_entails_decResAt_anyHeap_ext (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64) (err : ApiError AddrVal Unit) :
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
    Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ⊢
      decResAt A outPtr (.error err) ∗ anyHeap := by
  unfold Kits.pqxdhAcceptErrPayloadAt
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun isStr => ?_
  cases isStr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sepConj_comm]
    refine Entails.pure_left fun htag => ?_
    subst htag
    exact entails_decResAt_anyHeap_of_err_ext outPtr err
      (plainSpeWords_entails_decResAt_err A outPtr 10 (by decide) w2 w3 w4 w5 w6 err)
  · simp only [↓reduceIte]
    rw [← sepConj_assoc, sepConj_comm (speWordsAt outPtr errTag w2 w3 w4 w5 w6), sepConj_assoc]
    refine Entails.pure_left fun htag => ?_
    subst htag
    have hstr := strSpeWords_entails_decResAt_anyHeap A outPtr 24 (by decide)
      w2 w3 w4 w5 w6 emp err
    rw [sepConj_emp] at hstr
    exact hstr

/-- `pqxdhAccept = none` error payload entails `decResAt A0 outPtr (.error err) ∗ anyHeap`. -/
theorem pqxdhAcceptErr_entails_decResAt_anyHeap
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64) (err : ApiError AddrVal Unit) :
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
    Kits.pqxdhAcceptErrPayloadAt E2E.HooksE.A0 errTag w2 w3 w4 ⊢
      decResAt E2E.HooksE.A0 outPtr (.error err) ∗ anyHeap :=
  pqxdhAcceptErr_entails_decResAt_anyHeap_ext E2E.HooksE.A0 outPtr errTag w2 w3 w4 w5 w6 err

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
