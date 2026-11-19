/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0
  extractLsb_0_64_append extractLsb_64_64_append setWidth_64_append
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

theorem sepWPp_of_sepWP_final {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog ret s P Q) : SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_ret h

theorem sepWPp_name_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (k : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  k s rfl

theorem getResultAt_ok_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 0x1e0#64) (.ok bs) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 0x1e0#64) ↦₆₄ okTagVec) ∗
        ((sp - 0x1d8#64) ↦₆₄ cap) ∗
        ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
        ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs ∗
        memRegion (sp - 0x1c0#64) 16) := by
  dsimp only [getResultAt, vecResultAt]
  have e1 : sp - 0x1e0#64 + 8#64 = sp - 0x1d8#64 := by bv_omega
  have e2 : sp - 0x1e0#64 + 0x20#64 = sp - 0x1c0#64 := by bv_omega
  rw [e1, e2, vecU8_eq_bytes_tail A (sp - 0x1d8#64) bs (sp - 0x1d0#64) (sp - 0x1c8#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepProp_ext <;>
    (refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))

theorem finish_common_reassemble (A : RustAlloc) (s0 : State) (x : SessLoadPollGhost)
    {addrStk getStk stk : Nat} (hstk : pollMinStk addrStk getStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128) :
    (sessLoadOutAt A x.call.out ans ∗
      memRegion (s0.sp - 0x1e0#64) 368 ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      (((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
      memRegion (s0.sp - 0x200#64) 8 ∗
      memRegion (s0.sp - 0x070#64) 16 ∗
      savedCalleeSlots s0 ∗
      memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - extHookStack) ∗
      stackAt (s0.sp - 0x350#64) extHookStack ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
      dirAt A x.self x.dir ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      A.pool) ⊢
    sessLoadOutAt A x.call.out ans ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool ∗ stackAt s0.sp stk := by
  have h24 := header3_entails_memRegion24 (s0.sp - 0x1f8#64) (s0.sp - 0x1f0#64) (s0.sp - 0x1e8#64)
    nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24)))) ?_
  have hrstk := restore_pollStack s0 hstk hstk_hi c_sp0 q140
  have hgroup :
      (sessLoadOutAt A x.call.out ans ∗
        memRegion (s0.sp - 0x1e0#64) 368 ∗
        memRegion (s0.sp - 0x348#64) 312 ∗
        memRegion (s0.sp - 0x1f8#64) 24 ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool) =
      ((sessLoadOutAt A x.call.out ans ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - extHookStack) ∗
          stackAt (s0.sp - 0x350#64) extHookStack ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
          memRegion (s0.sp - 0x348#64) 312 ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x1f8#64) 24 ∗
          memRegion (s0.sp - 0x1e0#64) 368 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0)) := by
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right hrstk) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Shared post-`Dir::get` spatial state before inspecting `gr`. -/
@[expose] def postGetCommon (A : RustAlloc) (s0 : State) (x : SessLoadPollGhost)
    (addrStk getStk stk : Nat)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128) : SepProp :=
  memRegion (s0.sp - 0x1b0#64) 320 ∗
  ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
  ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
  ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
  SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
  vecU8Tail A nameCap namePtr nameBs ∗
  ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
  memRegion (s0.sp - 0x348#64) 312 ∗
  ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
  memRegion (s0.sp - 0x200#64) 8 ∗
  memRegion (s0.sp - 0x070#64) 16 ∗
  savedCalleeSlots s0 ∗
  stackAt (s0.sp - 0x350#64) (subMax addrStk getStk) ∗
  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
  memRegion x.call.out 368 ∗
  sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
  dirAt A x.self x.dir ∗
  protocolAddressAt A x.call.addr x.call.addrA ∗
  A.pool

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
