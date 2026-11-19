/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFront -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLen
import Aesop.BuiltinRules
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Simps
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsBack
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenStepsFrontExt
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

public section

set_option autoImplicit false

/-!
# `<SessionStructure as prost::Message>::encoded_len` (`0x25fd0`)

Verifies protobuf tags 9–15 and the epilogue, and assembles the full subroutine contract of
`<SessionStructure as prost::Message>::encoded_len` (`0x25fd0`, Block `86`) against `sessionLenSpec`
on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sessHwVarintLen_eq_encodeVarint_length
  sessHwVarintLen_bvShift_eq_encodeVarint_length
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length
  sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  Prost.noneCap_add_one_beq_zero
  Prost.noneCap_add_one_bne_zero
  Prost.optU32Tag_beq_one
  Prost.optU32Tag_bne_one
  Prost.zext64_optU32Tag_truncate32
  sess_ule_zero_64
  sess_ult_zero_64
  add_neg440_eq_624
  add_neg416_eq_652
  add_neg164_eq_912
  add_neg140_eq_940
  truncate32_signExtend64
  bv_encPendingMem_sum
  bv_encPendingKyber_sum

/-! ## Tag 9 (`pending_pre_key` at `ss + 248`, `444..700` and `1056..1072`) -/

end CryptoVerification.E2E.Record.Serialization.SessionLenAux

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization.SessionLenAux
open Proofs.libsignal.Hooks2

private def pendingTailLen (opt : Option TailVecGhost) : Prop :=
  match opt with | none => True | some g => g.tail.length = 24

private def kyberTailLen (opt : Option TailVecGhost) : Prop :=
  match opt with | none => True | some g => g.tail.length = 8

private def tailLensPure (G : SessionGhost) : SepProp :=
  ⌜pendingTailLen G.pending⌝ ∗ ⌜kyberTailLen G.kyber⌝

private theorem optTailVecAt_pending_eq' (A : RustAlloc) (a : BitVec 64)
    (opt : Option TailVecGhost) (m : Option PendingPreKey) :
    PendingRel opt m →
    optTailVecAt A 48 a opt = ⌜pendingTailLen opt⌝ ∗ pendingUnpacked A a opt m := by
  intro hrel
  rw [optTailVecAt_pending_eq A a opt m hrel]
  cases opt <;> rfl

private theorem optTailVecAt_kyber_eq' (A : RustAlloc) (a : BitVec 64)
    (opt : Option TailVecGhost) (m : Option PendingKyberPreKey) :
    KyberRel opt m →
    optTailVecAt A 32 a opt = ⌜kyberTailLen opt⌝ ∗ kyberUnpacked A a opt m := by
  intro hrel
  rw [optTailVecAt_kyber_eq A a opt m hrel]
  cases opt <;> rfl

/-- Fully unpacked heap body of `sessionStateAt` with `pendingUnpacked` and `kyberUnpacked`. -/
private def sessionFullUnpacked (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  tags1to5Cells ss G s ∗
  optSenderChainAt A (ss + 144#64) G.sender s.state.senderChain ∗
  (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
   ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip s.state.receiverChains).length) ∗
   vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains)) ∗
  pendingUnpacked A (ss + 248#64) G.pending s.pendingPreKey ∗
  tags10to15Cells ss s ∗
  kyberUnpacked A (ss + 296#64) G.kyber s.pendingKyberPreKey ∗
  sessionUnused A ss G s ∗
  tailLensPure G

private theorem sessionBodyUnpacked_eq (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8)))
    (hpending : PendingRel G.pending s.pendingPreKey)
    (hkyber : KyberRel G.kyber s.pendingKyberPreKey) :
    sessionBodyUnpacked A ss G s = sessionFullUnpacked A ss G s := by
  unfold sessionBodyUnpacked sessionFullUnpacked tailLensPure
  rw [optTailVecAt_pending_eq' A (ss + 248#64) G.pending s.pendingPreKey hpending,
      optTailVecAt_kyber_eq' A (ss + 296#64) G.kyber s.pendingKyberPreKey hkyber]
  ac_rfl

private theorem sp_sub64_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    ((sp - 64#64) &&& 15#64 == 0#64) = true := by
  have hmod : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
  have h0 : sp.toNat % 16 = 0 := by
    have := congrArg BitVec.toNat h
    simpa [hmod] using this
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [hmod, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  omega

section Placed

open CryptoVerification.E2E.Record.Placed

/-- Block `86` (`<SessionStructure as prost::Message>::encoded_len`) under `[LibsignalPlacement]`. -/
theorem sessionLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)) :=
  sessionLen_placed_ok A H

theorem sessionLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 86)
      (withLsCl lsmpl (sessionLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (sessionLen_placed_ok A H)

end Placed

end CryptoVerification.E2E.Record.Serialization
