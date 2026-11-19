/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Aux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs

/-!
# Stage P2 Substage P2.5 at SPQR V1

Proves kit-parameterized Substage P2.5 (`+0x36ac → +0x125c` on `Ok`, `+0x07bc` Arm 4 on
`get_identity_key_pair` error, or `+0x125c` Arm 5 on `acceptKeys = none`) on
`tripleRatchetProgAtExt img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

/-! ## 1. Memory Splitting Helpers for 72-Byte `kitKpPollSpec` Output -/

/-- Split the 344-byte `sp + 0x3e0` scratch slot into the 72-byte `kitKpPollSpec` output buffer
(`sp + 0x3e0..0x428`) and the remaining 272 bytes (`sp + 0x428..0x538`). -/
theorem sp3e0_344_split_72_272 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 72 ∗ memRegion (sp + 0x428#64) 272 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 72) (k := 272)
    (b' := sp + 0x428#64) rfl (by bv_omega) (by decide)

/-- Merge the 7-byte trailing padding of `kpPollOutAt (.ok kp)` at `sp + 0x421` with the remaining
272 bytes at `sp + 0x428` back into the 279-byte tail `memRegion (sp + 0x421#64) 279`. -/
theorem sp421_7_272_eq_279 (sp : BitVec 64) :
    memRegion (sp + 0x421#64) 7 ∗ memRegion (sp + 0x428#64) 272 =
      memRegion (sp + 0x421#64) 279 :=
  (ProofLib.memRegion_split' (b := sp + 0x421#64) (n := 7) (k := 272)
    (b' := sp + 0x428#64) rfl (by bv_omega) (by decide)).symm

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_kpPoll_le_selfKpCallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    skit.kpPollStack ≤ selfKpCallStack skit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_kpPoll_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    skit.kpPollStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (p2_kpPoll_le_selfKpCallStack skit) (Nat.le_max_left _ _)

theorem p2_isSameAcct_le_pure : isSameAccountDistinctStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : isSameAccountDistinctStack ≤ stageP2bStack) p2_stageP2b_le_pure

theorem p2_ro_intro_sub5 {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → s.mem ⊨ Ro ∗ R)
    (h : SepWPp prog ret s (Ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (Ro ∗ P) ∗ R := by rw [sepConj_assoc]; exact hro hm
  exact h R hm' hL

theorem p2_drop_left_sub5 {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_drop_frame_sub5 {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest) (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ p2_drop_left_sub5 h

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem p2_allocHook_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    allocHookStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans p2_alloc_le_pure (p2_pure_le_sub56 skit)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
