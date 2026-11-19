/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OneKeyVtables
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P2.1–P2.3 Composition and `KeyPair` Layout Helpers for `message_decrypt_prekey::{closure#0}`

Provides `keyPair64UnalignedAt` simplification helpers, clean substage wrappers, and the combined
Substages P2.1–P2.3 composition (`+0x0868#64 -> +0x0d5c#64`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  bobSession344WithRegIdsBv8 bobSession280MidBv8 bobSession344Bv8 initBobErrAt protocolAddressAt

/-! ## 1. Layout & `keyPair64UnalignedAt` Simplification Helpers -/

theorem SepWPp.post_entails {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {P_post P_post' : State → SepProp} {Q_regs : State →
      Prop} (hstage : SepWPp prog ret s P
      (fun sf P_m => (P_m ⊢ P_post sf) ∧ Q_regs sf) (PanicOomProp s0))
    (hent : ∀ sf, P_post sf ⊢ P_post' sf) :
    SepWPp prog ret s P
      (fun sf P_m => (P_m ⊢ P_post' sf) ∧ Q_regs sf) (PanicOomProp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_m, hmf, hPm, hregs⟩ | hpan⟩ := hstage R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_m, hmf, Entails.trans hPm (hent sf), hregs⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem SepWPp.ret_sepWPp_frame' {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop} {Q : State →
      SepProp → Prop} (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => (P_m ⊢ P_stage_post sf) ∧ Q_regs sf) (PanicOomProp s0))
    (hP : P = P_stage ∗ F) (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running → Q_regs sf →
      Q sf (P_stage_post sf ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  SepWPp.bind_sepWPp_frame' hstage hP fun sf hpc hrun hregs => SepWPp.done hpc hrun (hret sf hpc
    hrun hregs)

/-! ## 2. Clean Substage Wrappers (`stageP2_sub2_clean_ok`, `stageP2_sub4_none_clean_ok`,
  `stageP2_sub4_some_clean_ok`) -/

/-! ## 3. Combined Substage P2.1–P2.3 (`stageP2_sub1_to_3_ok`, `+0x0868#64 -> +0x0d5c#64`) -/

@[expose] def opkIdIsSomeWord (opkBSk? : Option Bytes) : BitVec 32 :=
  match opkBSk? with
  | none => 0#32
  | some _ => 1#32

theorem memRegion_288_split_65_223 (a : BitVec 64) :
    memRegion a 288 = memRegion a 65 ∗ memRegion (a + 65#64) 223 := by
  rw [show (288 : Nat) = 65 + 223 from rfl, memRegion_split a 65 223 (by decide)]

theorem processPrekeyActive10At_eq (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr preKeyVt kyberStorePtr kyberVt : BitVec 64) :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr preKeyVt kyberStorePtr kyberVt =
    ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ idVt) ∗
    ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
    ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberVt) ∗
    ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ preKeyVt) ∗
    ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) := by
  unfold processPrekeyActive10At; ac_rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible]
  futVtableAtP spkRecordSrcAt sessionRecordEmptyHeaderAt
  opkOptFieldAt opkUnusedFieldAt bobParamsFieldsAt inMemId16BoxAt decryptPrekeySavedRegsAt

end CryptoVerification.E2E.Pqxdh.ResponderClosure
