/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# Triple-Ratchet Extern-Hook Idempotence Helpers

Proves `tripleRatchetExterns_idem` and `selExt_idem`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr

/-- `tripleRatchetExterns` is idempotent. -/
theorem tripleRatchetExterns_idem (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    tripleRatchetExterns C ctl (tripleRatchetExterns C ctl abs) =
      tripleRatchetExterns C ctl abs := by
  funext sym
  dsimp only [tripleRatchetExterns]
  cases h : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) sym with
  | some h0 => rfl
  | none =>
    dsimp only
    split_ifs <;> rfl

/-- Spec-hook environment `tripleRatchetExterns C ctl ext`. -/
abbrev selExt (_b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : String → Option (State → State) :=
  tripleRatchetExterns C ctl ext

theorem selExt_idem (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    selExt b C ctl (tripleRatchetExterns C ctl abs) = tripleRatchetExterns C ctl abs :=
  tripleRatchetExterns_idem C ctl abs

end CryptoVerification.LibsignalTripleRatchet
