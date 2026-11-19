/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize

/-!
# Stage P2 Shared Definitions and Callee Bundles

Defines Stage P2 stack budgets, prefix-generalized `SepWPp` / `AllocContracts` combinators,
4 KiB-stacked `StageP2ClosureHooks`, generic-capacity `vecU8` and 48-byte `SignalProtocolError`
layout lemmas, SPQR V1 Bob session byte layouts, and `StageP2PureCallees{,4K}`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateStack initialStateValue)

set_option maxRecDepth 200000

/-! ## 1. Stack Budgets & Splitting Lemmas (`stageP2_*`) -/

/-- Pure/unwind callee stack floor across Substages P2.1–P2.6 and error exits:
covers `stageP2aStack` (`4400`), `stageP2bStack + 0x700` (V1 `initialize_bob_session`),
`allocHookStack`, and `dropSessionStructureLocal2Stack` (`futDropSpec` uses `0` stack). -/
@[expose] def stageP2PureAndErrStack : Nat :=
  max (stageP2bStack + 0x700)
    (max stageP2aStack
      (max allocHookStack dropSessionStructureLocal2Stack))

/-- Callee stack budget for Substage P2.2 (`get_signed_pre_key` shim, poll, drop, keypair serde). -/
@[expose] def spkGetCallStack {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b) : Nat :=
  max spkKit.getShimStack (max spkKit.getPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.3 (`get_kyber_pre_key` shim, poll, drop, kem serde). -/
@[expose] def kpkGetCallStack {A : RustAlloc} {b : BitVec 64} (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max kpkKit.getShimStack (max kpkKit.getPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.4 (`get_pre_key` shim, poll, drop, prekey serde). -/
@[expose] def pkGetCallStack {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) : Nat :=
  max pkKit.getShimStack (max pkKit.getPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.5 (`get_identity_key_pair` shim/poll/drop + V1 Bob init). -/
@[expose] def selfKpCallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.kpShimStack (max skit.kpPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.6 (`get_local_registration_id` shim/poll/drop + promote). -/
@[expose] def selfRegIdCallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.regIdShimStack (max skit.regIdPollStack stageP2PureAndErrStack)

/-- Combined stack budget for Substages P2.1–P2.4 (`spkKit`, `kpkKit`, `pkKit`, and unwinds). -/
@[expose] def stageP2Sub1To4Stack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) : Nat :=
  max (spkGetCallStack spkKit) (max (kpkGetCallStack kpkKit) (pkGetCallStack pkKit))

/-- Combined stack budget for Substages P2.5–P2.6 (`skit` self-identity methods, V1 Bob init,
promote, and unwinds). -/
@[expose] def stageP2Sub56Stack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (selfKpCallStack skit) (selfRegIdCallStack skit)

/-- Unified stack budget for full Stage P2 (`+0x868 -> +0x1778` and all 6 error exits). -/
@[expose] def stageP2CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2Sub1To4Stack spkKit kpkKit pkKit) (stageP2Sub56Stack skit)

theorem p2_stackAt_split_of_le (sp : BitVec 64) (big small : Nat)
    (hle : small ≤ big) (hbig : big ≤ 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

theorem p2_stageP2bV1_le_pure : stageP2bStack + 0x700 ≤ stageP2PureAndErrStack :=
  Nat.le_max_left _ _

theorem p2_stageP2b_le_pure : stageP2bStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_add_right _ _) p2_stageP2bV1_le_pure

theorem p2_stageP2a_le_pure : stageP2aStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_alloc_le_pure : allocHookStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem p2_dropSS3_le_pure : dropSessionStructureLocal2Stack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem p2_pure_le_sub1To4 {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) :
    stageP2PureAndErrStack ≤ stageP2Sub1To4Stack spkKit kpkKit pkKit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)

theorem p2_pure_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)

theorem p2_sub1To4_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub1To4Stack spkKit kpkKit pkKit ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_left _ _

theorem p2_sub56_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub56Stack skit ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_right _ _

theorem p2_pure_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_pure_le_sub1To4 spkKit kpkKit pkKit)
    (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit)

/-! ### 1b. 4K / `Ext` Stack Budgets (`stageP2PureAndErrStack4K = 33536`) -/

@[expose] def stageP2PureAndErrStack4K : Nat := max (768 + Initiator.pqxdhEntryStackExt) stageP2PureAndErrStack
@[expose] def spkGetCallStack4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b) : Nat :=
  max spkKit.getShimStack (max spkKit.getPollStack stageP2PureAndErrStack4K)
@[expose] def kpkGetCallStack4K {A : RustAlloc} {b : BitVec 64} (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max kpkKit.getShimStack (max kpkKit.getPollStack stageP2PureAndErrStack4K)
@[expose] def pkGetCallStack4K {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) : Nat :=
  max pkKit.getShimStack (max pkKit.getPollStack stageP2PureAndErrStack4K)
@[expose] def selfKpCallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.kpShimStack (max skit.kpPollStack stageP2PureAndErrStack4K)
@[expose] def selfRegIdCallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.regIdShimStack (max skit.regIdPollStack stageP2PureAndErrStack4K)
@[expose] def stageP2Sub1To4Stack4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b) (pkKit : PreKeyStoreSpec A b) : Nat :=
  max (spkGetCallStack4K spkKit) (max (kpkGetCallStack4K kpkKit) (pkGetCallStack4K pkKit))
@[expose] def stageP2Sub56Stack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (selfKpCallStack4K skit) (selfRegIdCallStack4K skit)
@[expose] def stageP2CallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2Sub1To4Stack4K spkKit kpkKit pkKit) (stageP2Sub56Stack4K skit)

theorem p2_pure_le_pure4K : stageP2PureAndErrStack ≤ stageP2PureAndErrStack4K := Nat.le_max_right _ _
theorem p2_bobExt_le_pure4K : 768 + Initiator.pqxdhEntryStackExt ≤ stageP2PureAndErrStack4K := Nat.le_max_left _ _
theorem p2_pure4K_le_sub1To4_4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b) (pkKit : PreKeyStoreSpec A b) :
    stageP2PureAndErrStack4K ≤ stageP2Sub1To4Stack4K spkKit kpkKit pkKit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
theorem p2_pure4K_le_sub56_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : stageP2PureAndErrStack4K ≤ stageP2Sub56Stack4K skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
theorem p2_sub1To4_4K_le_stageP2_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub1To4Stack4K spkKit kpkKit pkKit ≤ stageP2CallStack4K spkKit kpkKit pkKit skit := Nat.le_max_left _ _
theorem p2_sub56_4K_le_stageP2_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub56Stack4K skit ≤ stageP2CallStack4K spkKit kpkKit pkKit skit := Nat.le_max_right _ _
theorem p2_pure4K_le_stageP2_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack4K ≤ stageP2CallStack4K spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_pure4K_le_sub1To4_4K spkKit kpkKit pkKit) (p2_sub1To4_4K_le_stageP2_4K spkKit kpkKit pkKit skit)
private theorem p2_max3_mono_right {a b c c' : Nat} (h : c ≤ c') :
    max a (max b c) ≤ max a (max b c') :=
  Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
      Nat.le_trans h (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩⟩

theorem p2_sub1To4_le_4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b) (pkKit : PreKeyStoreSpec A b) :
    stageP2Sub1To4Stack spkKit kpkKit pkKit ≤ stageP2Sub1To4Stack4K spkKit kpkKit pkKit :=
  Nat.max_le.mpr ⟨Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K) (Nat.le_max_left _ _),
    Nat.max_le.mpr ⟨Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
      Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩⟩
theorem p2_sub56_le_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : stageP2Sub56Stack skit ≤ stageP2Sub56Stack4K skit :=
  Nat.max_le.mpr ⟨Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K) (Nat.le_max_left _ _),
    Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K) (Nat.le_max_right _ _)⟩
theorem p2_callStack_le_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2CallStack spkKit kpkKit pkKit skit ≤ stageP2CallStack4K spkKit kpkKit pkKit skit :=
  Nat.max_le.mpr ⟨Nat.le_trans (p2_sub1To4_le_4K spkKit kpkKit pkKit)
      (p2_sub1To4_4K_le_stageP2_4K spkKit kpkKit pkKit skit),
    Nat.le_trans (p2_sub56_le_4K skit) (p2_sub56_4K_le_stageP2_4K spkKit kpkKit pkKit skit)⟩

/-! ## 2. Prefix-Generalized `SepWPp` & `AllocContracts` Combinators (`p2_*`) -/

theorem p2_allocFailedIn_of_trace_prefix {s0 s sf : State}
    (htr : s0.trace <+: s.trace) (ha : allocFailedIn s sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢
  obtain ⟨d, hd⟩ := htr
  rw [← hd, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

theorem p2_allowPanic_oom_of_trace_prefix {s0 s sf : State} {F : SepProp}
    (htr : s0.trace <+: s.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    exact ⟨p2_allocFailedIn_of_trace_prefix htr ha, htr.trans hp⟩
  exact allowPanic_frame himp hm

@[simp, arm64_norm ↓, wp_norm ↓]
theorem p2_calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) : calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl
@[simp, arm64_norm ↓, wp_norm ↓]
theorem p2_calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) : calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg64_0 (s : State) (v : BitVec 64) : calleeSavedVRegs (s.writeVReg64 0#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg64_1 (s : State) (v : BitVec 64) : calleeSavedVRegs (s.writeVReg64 1#5 v) = calleeSavedVRegs s := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem p2_bobPanic_to_panicOom_prefix {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (htr : s0.trace <+: s.trace)
    (h : SepWPp prog ret s P Q (BobPanicOom s)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hq⟩ | ⟨hoom, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P_f, hmf, hq⟩⟩
  · refine ⟨sf, hst, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun R' hm' => ?_⟩)⟩
    have h' := hq R' hm'
    have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
        allocFailedIn s0 sf ∧ s0.trace <+: sf.trace :=
      fun ⟨ha, hp⟩ => ⟨p2_allocFailedIn_of_trace_prefix htr ha, htr.trans hp⟩
    exact Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono himp))) h'
  · exact ⟨sf, hst, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem p2_bind_sepWPp_exists_frame {α : Type} {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : α → SepProp}
    {Q_regs : α → State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => ∃ a : α, Q_regs a sm ∧ (P_m ⊢ P_stage_post a))
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ (a : α) (sm : State), Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs a sm →
      SepWPp prog ret sm (P_stage_post a ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, a, hregs, hent⟩ | ⟨hpan, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post a ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext a sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- 4 KiB-stacked `memcpy` contract (`rfl`-compatible with `CliExt.memcpySpec`). -/
@[expose] def p2Memcpy4KSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (libcMemcpySpec allocHookStack).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

theorem p2_framelessMemcpy_to_4K {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry framelessMemcpySpec) :
    subroutine_ok prog entry p2Memcpy4KSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [p2Memcpy4KSpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(dst, src, bs), stackAt s0.sp allocHookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [framelessMemcpySpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [framelessMemcpySpec, p2Memcpy4KSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

theorem p2_cond_ne_adds64_of_ne_neg3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 w 3#64) = true := by
  have hne : w + 3#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem p2_cond_ne_adds64_of_ne_neg2 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffe#64) :
    ConditionHolds CondCode.NE (addsPState64 w 2#64) = true := by
  have hne : w + 2#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem p2_cond_eq_adds64_of_ne_neg1 {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  have hne : w + 1#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

theorem p2_zext64_trunc32_id (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 32 = w := by
  bv_omega

/-- Unaligned 48-byte poll/sret cell layout `(w0, o1, o2, o3, o4, o5, o6)` matching the closure's
quadword reads from `sp + 0xa98` / `sp + 0x3e8` and writes to `outPtr`. -/
@[expose] def p2PollCellsAt (p w0 : BitVec 64) (o1 : BitVec 32)
    (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) : SepProp :=
  (p ↦₆₄ w0) ∗
  ((p + 0x8#64) ↦₃₂ o1) ∗
  ((p + 0xc#64) ↦₆₄ o2) ∗
  ((p + 0x14#64) ↦₆₄ o3) ∗
  ((p + 0x1c#64) ↦₆₄ o4) ∗
  ((p + 0x24#64) ↦₆₄ o5) ∗
  ((p + 0x2c#64) ↦₃₂ o6)

/-- Exact 40-byte realignment at arbitrary base `a + 8`. -/
theorem p2_words5_repack (a w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 0x08#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) ∗ ((a + 0x18#64) ↦₆₄ w3) ∗
        ((a + 0x20#64) ↦₆₄ w4) ∗ ((a + 0x28#64) ↦₆₄ w5) =
      ((a + 0x08#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((a + 0x0c#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((a + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((a + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((a + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((a + 0x2c#64) ↦₃₂ w5.extractLsb' 32 32) := by
  rw [← pointsTo32_pair (a + 0x0c#64), ← pointsTo32_pair (a + 0x14#64),
      ← pointsTo32_pair (a + 0x1c#64), ← pointsTo32_pair (a + 0x24#64)]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Exact 48-byte cell bijection between `speWordsAt p w0 w1 w2 w3 w4 w5` and `p2PollCellsAt`. -/
theorem p2_speWordsAt_eq_pollCellsAt (p w0 w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt p w0 w1 w2 w3 w4 w5 =
      p2PollCellsAt p w0
        (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) := by
  unfold speWordsAt p2PollCellsAt
  have hrep :
      ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
          ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) =
        ((p + 0x08#64) ↦₃₂ w1.extractLsb' 0 32) ∗
          ((p + 0x0c#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
          ((p + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
          ((p + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
          ((p + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
          ((p + 0x2c#64) ↦₃₂ w5.extractLsb' 32 32) :=
    p2_words5_repack p w1 w2 w3 w4 w5
  exact congrArg ((p ↦₆₄ w0) ∗ ·) hrep

/-- Done-state coroutine layout at error/return (`0x7d8` bytes with discriminant `1#8` at `+0x2c0`),
`rfl`-equal to `dpFutDoneAt coroPtr`. -/
@[expose] def p2CoroDoneAt (coroPtr : BitVec 64) : SepProp :=
  memRegion coroPtr 0x2c0 ∗
    ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    memRegion (coroPtr + 0x2c1#64) (0x7d8 - 0x2c1)

/-- Rejoin a non-empty `vecU8` buffer `(ptr ↦ₛ xs) ∗ memRegion (ptr + len) (cap - len)` into
`A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat` for `__rust_dealloc`. -/
theorem p2_vecBuf_dealloc_nonzero (A : RustAlloc) (cap ptr : BitVec 64) (xs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) (hxs_le : xs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ xs) ∗
       memRegion (ptr + BitVec.ofNat 64 xs.length) (cap.toNat - xs.length)) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hcap_ne' : cap ≠ 0 := hcap_ne
  simp only [hcap_ne', ↓reduceIte]
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr xs.length ∗
        memRegion (ptr + BitVec.ofNat 64 xs.length) (cap.toNat - xs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := xs.length) (k := cap.toNat - xs.length)
      (b' := ptr + BitVec.ofNat 64 xs.length) (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptr xs))

/-! ## 4. SPQR V1 Bob Session Byte Layouts (`rfl`-compatible with `BobTailV1`) -/

/-- `Params` Bob passes to `spqr::initial_state` (`rfl`-equal to `BobTailV1.bobSpqrParams`). -/
@[expose] def p2BobSpqrParams (pqrKey : SignalPqxdh.Bytes) : CryptoVerification.LibsignalSpqrV1.Params :=
  { direction := .b2a, version := .v1, minVersion := .v1, authKey := bytesToBv8 pqrKey }

/-- Heap part of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs`
(`rfl`-equal to `BobTailV1.bobSpqrVecBuf`). -/
@[expose] def p2BobSpqrVecBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- First 144 bytes of Bob's V1 `SessionState` (`rfl`-equal to `BobTailV1.bobHead144Bv8V1`). -/
@[expose] def p2BobHead144Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen

/-- Full 344-byte `SessionState` built by `initialize_bob_session` at V1
(`rfl`-equal to `BobTailV1.bobSession344Bv8V1`). -/
@[expose] def p2BobSession344Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  p2BobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32 pad_f4 ++
  bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2

/-- First 56 bytes of Bob's `SessionState` (`+0x00..+0x38`). -/
@[expose] def p2BobSessHead56Bv8 (localIkBoxPtr remoteIkBoxPtr : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64

/-- Middle 280 bytes (`+0x38..+0x150`) of Bob's V1 `SessionState`. -/
@[expose] def p2BobSessMid280V1 (rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++
  unpack32 pad_f4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 c0 ++ unpack64 c1 ++ unpack64 c2 ++ unpack64 c3 ++ unpack64 c4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 d0 ++ unpack64 d1 ++ unpack64 d2 ++
  unpack64 4#64

/-- Bob's 344-byte V1 `SessionState` with `remoteRegId` and `localRegId` written at `+0x150..0x158`. -/
@[expose] def p2BobSessRegIdsV1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) : List (BitVec 8) :=
  p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
    (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
      (unpack32 remoteRegId ++ unpack32 localRegId))

theorem p2BobSessHead56Bv8_length (p1 p2 : BitVec 64) :
    (p2BobSessHead56Bv8 p1 p2).length = 56 := by
  simp [p2BobSessHead56Bv8]

theorem p2BobSessMid280V1_length (p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length = 280 := by
  unfold p2BobSessMid280V1 senderChainBytes100
  simp only [List.length_append, unpack64_length, unpack32_length]

attribute [local irreducible] unpack64 unpack32 senderChainBytes100 in
theorem p2BobSession344Bv8V1_eq_head56_mid280V1 (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    p2BobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      p2BobSessHead56Bv8 p1 p2 ++
        (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
          unpack64 0#64) := by
  unfold p2BobSession344Bv8V1 p2BobHead144Bv8V1 p2BobSessHead56Bv8 p2BobSessMid280V1 bobTail96Bv8
  simp only [List.append_assoc]

/-! ## 5. Ext-Generic Pure Callee Bundle (`StageP2PureCallees`) -/

/-- 4 KiB-stacked `SessionRecord::promote_state` (empty-record fast path). -/
@[expose] def promoteStateEmpty4KSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, srcPtr, bs) s =>
    ⌜s.readReg64 .x0 = recPtr ∧ s.readReg64 .x1 = srcPtr ∧ bs.length = 344⌝ ∗
    ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun (recPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

theorem promoteStateEmptySpec_to_4K {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry promoteStateEmptySpec) :
    subroutine_ok prog entry promoteStateEmpty4KSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨recPtr, srcPtr, bs⟩ R s0 hpre
  dsimp only [promoteStateEmpty4KSpec] at hpre
  rw [stackAt_promote_state_eq s0.sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(recPtr, srcPtr, bs), stackAt (s0.sp - 96#64) (allocHookStack - 96) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [promoteStateEmptySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [promoteStateEmptySpec, promoteStateEmpty4KSpec] at hpost ⊢
    rw [stackAt_promote_state_eq s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

/-- Stack-parameterized `<IdentityKey>::is_same_account` contract under `DistinctSid`. -/
@[expose] def isSameAccountDistinctAtSpec (A : RustAlloc) (parse : UuidParser) (stk : Nat) :
    Spec (BitVec 64 × IdentityKey × BitVec 64 × AddrGhost ×
      BitVec 64 × IdentityKey × BitVec 64 × AddrGhost) where
  pre := fun (lIkA, lIk, locA, loc, rIkA, rIk, remA, rem) s =>
    ⌜s.readReg64 .x0 = lIkA ∧ s.readReg64 .x1 = locA ∧ s.readReg64 .x2 = rIkA ∧
      s.readReg64 .x3 = remA ∧ (lIk ≠ rIk ∨ DistinctSid parse loc.name.bytes rem.name.bytes)⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ protocolAddressAt A loc locA ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ protocolAddressAt A rem remA ∗ stackAt s.sp stk
  post := fun (lIkA, lIk, locA, loc, rIkA, rIk, remA, rem) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ protocolAddressAt A loc locA ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ protocolAddressAt A rem remA ∗ stackAt s0.sp stk

theorem isSameAccountDistinctSpec_to_ext {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry (isSameAccountDistinctSpec A parse)) :
    subroutine_ok prog entry
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A parse) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
    isSameAccountDistinctStack (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
            IsSameAccountDistinctGhost),
    memRegion (s0.sp - BitVec.ofNat 64
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt -
        isSameAccountDistinctStack) ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [isSameAccountDistinctSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [isSameAccountDistinctSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
      isSameAccountDistinctStack (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
