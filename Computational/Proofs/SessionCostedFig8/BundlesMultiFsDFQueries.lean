/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFQueries

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (CostedReduction)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.PRFPRNG (prngSMCodecDF)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.SM.Construction (Header fsaeadMultiHeaderAdIface)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open _root_.CryptoVerification.LibsignalSession (LCt)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (compileFsMultiDFAtomic)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot (
  compileFsMultiDFAtomic_isQueryBoundP_base compileFsMultiDFAtomic_makesAtMostQueries_base)

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

/-- Every `IsQueryBoundP` on session `j` of `R.eval (fun _ => A) ()` transfers directly to
`(compileFsMultiDFAtomic ... stage la j qep qR B0 R).eval (fun _ => A) ()` (unconditionally in `(ℓ, j, qep, qR)`). -/
theorem compileFsMultiDFAtomic_isQueryBoundP (stage la : Bool) (j qep qR B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (P : (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain → Bool)
    (k : ℕ)
    (hP : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, q⟩ => decide (s = j) && P q) = true) k) :
    ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr q => P q) = true) k := by
  exact compileFsMultiDFAtomic_isQueryBoundP_base ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R A P k hP

/-- Per-session `FSAEAD.MakesAtMostQueries ... qSess` (e.g. `qSess = 2 * q`) for
`compileFsMultiDFAtomic` from a session-`j` query bound on `R.eval`. -/
theorem compileFsMultiDFAtomic_makesAtMostQueries (stage la : Bool) (j qep qR B0 qSess : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hQ : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, _⟩ => decide (s = j)) = true) qSess) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) qSess := by
  exact compileFsMultiDFAtomic_makesAtMostQueries_base ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 qSess R A hQ

end

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFQueries
