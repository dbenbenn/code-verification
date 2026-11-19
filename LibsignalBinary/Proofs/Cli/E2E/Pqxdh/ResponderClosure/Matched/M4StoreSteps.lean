/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P4 Nonzero-`prevCap` `Ok` Epilogue (`p4_seg4e_dealloc_ext_wp`)

Proves `p4_seg4e_dealloc_ext_wp` (`+0x048c → retAddr` when `prevCap ≠ 0#64`), deallocating the spare
`previous_sessions` buffer `prevPtr` (`prevCap.toNat * 24` bytes, align `8`) via `__rust_dealloc`
before writing `Ok(pt)` to `retPtr` and restoring callee-saved registers.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem mul24_eq_m4 {prevCap : BitVec 64} (_h : prevCap.toNat * 24 < 2 ^ 63) :
    ((prevCap + (prevCap <<< 1)) <<< 3) = BitVec.ofNat 64 (prevCap.toNat * 24) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
