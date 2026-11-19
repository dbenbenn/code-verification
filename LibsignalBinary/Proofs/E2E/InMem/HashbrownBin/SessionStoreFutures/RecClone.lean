/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Callees
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionClone
import LibsignalBinary.Proofs.E2E.Record.Serialization.VecVecClone
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `SessionRecord` Clone and Drop Bridges for `InMemSessionStore`
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem sessionAt_eq_head_tail (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s =
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  apply ProofLib.sepProp_eq_of_entails
  · exact sessionAt_unpack_head_tail A ss G s
  · apply Entails.sepExists_elim; intro bs336
    apply Entails.pure_left; rintro ⟨_, _, hinl⟩
    exact sessionAt_pack_head_tail A ss G s hinl

theorem vecAt_empty_prev_eq_vecHeader (A : RustAlloc) (r : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r 0#64 8#64 [] =
      vecHeader r 0#64 8#64 0#64 := by
  have hbuf : vecBuf A 24 8 (fun (_ : Unit) _ => emp) 0#64 8#64 [] = emp := by
    unfold vecBuf
    simp
  unfold vecAt
  rw [hbuf, sepConj_emp]
  rfl

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
