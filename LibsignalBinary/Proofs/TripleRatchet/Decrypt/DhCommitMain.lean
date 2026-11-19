/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment: Shared Arithmetic & `ReachesOrPanic` Helpers

Shared bitvector/arithmetic lemmas and `ReachesOrPanic.seq_meta` for `DhCommit`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open DhCommitFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DhCommitFacts

theorem le_of_eq_succ_lt {m n : Nat} (heq : m = n + 1) (hlt : n < 2 ^ 32) : m ≤ 2 ^ 32 := by
  omega

end DhCommitFacts

theorem setWidth8_zeroExtend64_shared_lb (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 8 = w.setWidth 8 := by
  bv_kernel

theorem ReachesOrPanic.seq_meta [LibsignalPlacement] {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Unit}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab → P s1 →
      ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hP | hPan⟩ := h1
  · obtain ⟨s2, hsteps2, hQ⟩ := h2 s1 hsteps1.keepsFrozen hsteps1.symtab_eq hP
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr hPan⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
