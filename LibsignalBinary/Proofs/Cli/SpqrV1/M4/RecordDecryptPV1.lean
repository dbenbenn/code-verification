/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordClonePV1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordCloneExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDropChainExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDropExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDropVecExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordExitTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSegDecryptExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSegmentsTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSetStateExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.LogClosure
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel

/-!
# CLI `try_decrypt_from_record` Region under `DistinctSid` and Tight `onPanic`

Proves the CLI `try_decrypt_from_record` region (`recordRegionEntry` → `recordRegionExit`)
against `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight` (weak `remote ≠ local ∨ DistinctSid`
precondition and tight `recordDecryptOnPanicTight` panic condition):
- `CryptoVerification.Cli.LibsignalSpqrV1.M4.recordDecrypt_region_okTPTight`
- `CryptoVerification.Cli.LibsignalSpqrV1.M4.recordDecrypt_region_vregs_okTPTight`
- `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight`
- `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight`
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts

open CryptoVerification.SignalSession (CliExternsOk)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Tight `onPanic` Record Spec & Weakening Helpers -/

/-- Tight panic condition for `try_decrypt_from_record`: the model panics or an allocation failed,
and the trace only grew (dropping the `(version check ∧ S.recvPanics …)` disjunct). -/
@[expose] def _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight
    (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : RecordDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜((x.model C S uuidParse).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
    anyHeap

private theorem rdp_tryDecrypt_onPanic_entails_tight {C : Crypto} {S : SpqrModel}
    {x : RecordDecryptGhost} {G₁ : SessionGhost}
    {s0 s sf : State} {F : SepProp} {sp : BitVec 64}
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (htr : s.trace = s0.trace) :
    CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidTryParse
        (mkTryDecryptGhost sp x G₁) s sf ∗ F ⊢
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidTryParse x s0 sf := by
  dsimp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight,
    CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hpan, hpref⟩ => ?_
  unfold allocFailedIn at hpan ⊢
  rw [htr] at hpan hpref
  refine Entails.pure_right ⟨?_, hpref⟩ (entails_anyHeap _)
  rcases hpan with hmod | halloc
  · exact Or.inl (model_panic_of_tryDecrypt_panic C S sp x G₁ heq hmod)
  · exact Or.inr halloc

private theorem rdp_grow_onPanic_entails_tight {P1 : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P1 ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨Or.inr halloc, hpref⟩ (entails_anyHeap _)

private def rdpNoPanic (S : SpqrModel) : SpqrModel :=
  { S with recvPanics := fun _ _ => false }

private theorem rdp_tryModel_noPanic_or_panic (C : Crypto) (S : SpqrModel)
    (y : TryDecryptGhost) :
    y.model C (rdpNoPanic S) uuidTryParse = y.model C S uuidTryParse ∨
      (y.model C S uuidTryParse).1 = .error .panic := by
  rcases htr : Mut.exec TripleRatchet.fromSessionState y.st with ⟨e | tr, st1⟩
  · left
    rw [(Decrypt.Model.model_of_fromSessionState_error (S := rdpNoPanic S) htr).1,
      (Decrypt.Model.model_of_fromSessionState_error (S := S) htr).1]
  · rcases herc :
        Mut.exec (RatchetState.ensureReceiverChain C y.msg.senderRatchetKey (coinsOf y.rest))
          tr.ratchet with ⟨e | ck, r1⟩
    · left
      rw [Decrypt.Model.model_of_ensureReceiverChain_error (S := rdpNoPanic S) htr herc,
        Decrypt.Model.model_of_ensureReceiverChain_error (S := S) htr herc]
    · rcases hcmk :
          Mut.exec
            (RatchetState.consumeMessageKey C.F y.msg.senderRatchetKey ck y.msg.counter y.msgType)
            r1 with ⟨e | mkg, r2⟩
      · left
        rw [Decrypt.Model.model_of_cmk_error (S := rdpNoPanic S) htr herc hcmk,
          Decrypt.Model.model_of_cmk_error (S := S) htr herc hcmk]
      · have hpq : tr.pqrState = y.st.pqRatchetState :=
          (Decrypt.Model.fromSessionState_ok_inv htr).2.2.1
        cases hp : S.recvPanics y.st.pqRatchetState y.msg.pqRatchet
        · left
          have hnp : S.recvPanics tr.pqrState y.msg.pqRatchet = false := hpq ▸ hp
          have hnp' : (rdpNoPanic S).recvPanics tr.pqrState y.msg.pqRatchet = false := rfl
          rcases hspqr : S.recv tr.pqrState y.msg.pqRatchet with sd | ⟨newPqrState, pqrKey⟩
          · rw [Decrypt.Model.model_of_spqr_error (S := rdpNoPanic S) htr herc hcmk hspqr hnp',
              Decrypt.Model.model_of_spqr_error (S := S) htr herc hcmk hspqr hnp]
          · cases hmac :
                y.msg.verifyMacWithAddresses C.F
                  (serializeAddresses (serviceIdParse uuidTryParse) y.rem y.loc)
                  tr.remoteIdentityKey tr.localIdentityKey
                  (mkg.generateKeys C.F pqrKey).macKey
            · rw [Decrypt.Model.model_of_verifyMac_false (S := rdpNoPanic S)
                  htr herc hcmk hspqr hmac hnp',
                Decrypt.Model.model_of_verifyMac_false (S := S) htr herc hcmk hspqr hmac hnp]
            · cases haes :
                  aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv y.msg.ciphertext
              · rw [Decrypt.Model.model_of_aesDec_none (S := rdpNoPanic S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_none (S := S) htr herc hcmk hspqr hmac haes hnp]
              · rw [Decrypt.Model.model_of_aesDec_some (S := rdpNoPanic S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_some (S := S) htr herc hcmk hspqr hmac haes hnp]
        · right
          exact Decrypt.Model.model_of_recvPanics htr herc hcmk hp

private theorem rdp_model_noPanic_or_panic (C : Crypto) (S : SpqrModel)
    (x : RecordDecryptGhost) :
    x.model C (rdpNoPanic S) uuidTryParse = x.model C S uuidTryParse ∨
      (x.model C S uuidTryParse).1 = .error .panic := by
  by_cases heq : x.st.version.toNat = x.msg.messageVersion.toNat
  · rw [model_eq_of_version_eq C (rdpNoPanic S) 0#64 x x.G heq]
    rcases rdp_tryModel_noPanic_or_panic C S (mkTryDecryptGhost 0#64 x x.G) with h | hpan
    · left
      rw [h, ← model_eq_of_version_eq C S 0#64 x x.G heq]
    · right
      exact model_panic_of_tryDecrypt_panic C S 0#64 x x.G heq hpan
  · left
    dsimp [RecordDecryptGhost.model, SessionState.tryDecryptFromRecord, Mut.exec, StateT.run,
      ExceptT.run, ExceptT.mk, pure, Except.pure, Bind.bind, Monad.toBind, ExceptT.bind,
      ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, StateT.lift, throw, throwThe, MonadExceptOf.throw]
    simp [heq]

private theorem rdp_spec_S_exists (C : Crypto) (S : SpqrModel) (x : RecordDecryptGhost) :
    ∃ S' : SpqrModel,
      x.model C S' uuidTryParse = x.model C S uuidTryParse ∧
      (∀ (s0 sf : State),
        (x.model C S' uuidTryParse).1 = .error .panic ∨
          (x.st.version.toNat = x.msg.messageVersion.toNat ∧
            S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
          allocFailedIn s0 sf →
        (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf) := by
  rcases rdp_model_noPanic_or_panic C S x with hmod_eq | hmod_pan
  · refine ⟨rdpNoPanic S, hmod_eq, fun s0 sf h => ?_⟩
    rcases h with hp | ⟨_, hpan⟩ | halloc
    · exact Or.inl (hmod_eq ▸ hp)
    · exact nomatch hpan
    · exact Or.inr halloc
  · exact ⟨S, rfl, fun _ _ _ => Or.inl hmod_pan⟩

end CryptoVerification.Cli.LibsignalSpqrV1.M4
