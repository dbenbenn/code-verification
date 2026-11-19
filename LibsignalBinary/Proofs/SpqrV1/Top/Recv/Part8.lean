/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: `Ordering::Greater` Error & `recv_key` Success Continuations

**Checked by Lean.** Pure model bridges, shared error exit (`+2388..+2420 -> +2540`), and
`<Chain>::recv_key` success continuation (`+2184..+2380 -> +1040`) for the `Ordering::Greater`
branch of `spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

@[local simp, local arm64_norm, local wp_norm]
theorem fp_sub_32_eq (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551584#64 = sp0 - 128#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_560_eq_v0 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  change (s0.sp - 688#64) + 560#64 = s0.sp - 128#64
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fp_sub_48_eq (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551568#64 = sp0 - 144#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_544_eq_v0 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  change (s0.sp - 688#64) + 544#64 = s0.sp - 144#64
  bv_omega

/-! ## 1. Pure Model Lemmas for `Ordering::Greater` (`pre.version > 1#8`) -/

theorem decodeState_spqrDeps_eq_of_spqrDecodeState {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {pre_pb : PqRatchetState}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb) :
    decodeState (spqrDeps F K) stateBytes = .ok (pqRatchetStateToPb pre_pb) :=
  decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec

theorem error_isStateDecode_eq (e : Error) :
    e.isStateDecode = (e == .stateDecode) := by
  cases e <;> rfl

theorem spqrV1Recv_gt_chainFrom_err {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hgt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error e) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hvn' : (pqRatchetStateToPb pre_pb).versionNegotiation = some vn := by
    rw [pqRatchetStateToPb_vn, hvn]
  have hinner' := pqRatchetStateToPb_inner_some hinner
  have hchain' : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hrecv := recv_vn_some_inner_some_gt (spqrDeps F K) (spqrHkdfWith F)
    hpre hd hvn' hinner' hge hgt
  rw [hchain', hcf] at hrecv
  rw [← error_isStateDecode_eq]
  exact spqrV1Recv_recv_noPanic_of_err hrecv

theorem spqrV1Recv_gt_recvKey_err {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {chain0 : Chain} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hgt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (hrk : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hvn' : (pqRatchetStateToPb pre_pb).versionNegotiation = some vn := by
    rw [pqRatchetStateToPb_vn, hvn]
  have hinner' := pqRatchetStateToPb_inner_some hinner
  have hchain' : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hrecv := recv_vn_some_inner_some_gt (spqrDeps F K) (spqrHkdfWith F)
    hpre hd hvn' hinner' hge hgt
  rw [hchain', hcf] at hrecv
  dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at hrecv
  rw [hrk] at hrecv
  rw [← error_isStateDecode_eq]
  exact spqrV1Recv_recv_noPanic_of_err hrecv

theorem spqrV1Recv_gt_recvKey_panic {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {chain0 : Chain}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hgt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (hrk : (chain0.recvKey (spqrHkdfWith F) 0#64 pre.index).isPanic = true) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hvn' : (pqRatchetStateToPb pre_pb).versionNegotiation = some vn := by
    rw [pqRatchetStateToPb_vn, hvn]
  have hinner' := pqRatchetStateToPb_inner_some hinner
  have hchain' : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hrecv := recv_vn_some_inner_some_gt (spqrDeps F K) (spqrHkdfWith F)
    hpre hd hvn' hinner' hge hgt
  rw [hchain', hcf] at hrecv
  dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at hrecv
  cases hres : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index with
  | ok _ => rw [hres] at hrk; contradiction
  | error ce =>
    cases ce with
    | err _ => rw [hres] at hrk; contradiction
    | panic p =>
      rw [hres] at hrecv
      exact spqrV1Recv_recvPanics_of_panic hrecv

theorem spqrV1Recv_gt_recvKey_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State}
    {chain0 chain1 : Chain} {rawKey : Bytes}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hgt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (hrk : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey)) :
    (spqrV1Recv F K).recv stateBytes msgBytes =
      .ok (PqRatchetState.encodeRaw {
        versionNegotiation := some vn
        chain := some chain1.intoPb
        inner := some (.v1 pb)
      }, some rawKey) := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hvn' : (pqRatchetStateToPb pre_pb).versionNegotiation = some vn := by
    rw [pqRatchetStateToPb_vn, hvn]
  have hinner' := pqRatchetStateToPb_inner_some hinner
  have hchain' : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hrecv := recv_vn_some_inner_some_gt (spqrDeps F K) (spqrHkdfWith F)
    hpre hd hvn' hinner' hge hgt
  rw [hchain', hcf] at hrecv
  dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at hrecv
  rw [hrk] at hrecv
  exact spqrV1Recv_recv_of_ok hrecv

theorem chainFrom_some_eq {F : ShaCompress} (chainPb : ChainPB) (vn : VersionNegotiationPB) :
    chainFrom (spqrHkdfWith F) (some chainPb) (some vn) =
      Chain.fromPb chainPb := rfl

theorem chainFrom_none_eq {F : ShaCompress} (vn : VersionNegotiationPB) :
    chainFrom (spqrHkdfWith F) none (some vn) =
      chainFromVersionNegotiation (spqrHkdfWith F) vn := rfl

theorem recvPrevFits_of_chainFrom {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {chain0 : Chain}
    (hlen : stateBytes.length < 2 ^ 32)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0) :
    ChainProofs.RecvPrevFits chain0 := by
  intro link hlink
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hraw : StateSize.optRaw StateSize.rawVN (pqRatchetStateToPb pre_pb).versionNegotiation +
      StateSize.optRaw StateSize.rawChain pre_pb.chain +
      StateSize.optRaw StateSize.rawPqInner ((pqRatchetStateToPb pre_pb).inner.map PqRatchetState.Inner.v1) ≤
      201 * stateBytes.length := decodeState_spqrDeps_raw_le hd
  have hcf_raw := chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
  have hchain_le : StateSize.rawChain chain0.intoPb ≤ 201 * stateBytes.length + 296 := by omega
  have hmem_into :
      ({ send := some link.send.intoPb, recv := some link.recv.intoPb } : ChainEpochPB) ∈
        chain0.intoPb.links :=
    List.mem_map.mpr ⟨link, hlink, rfl⟩
  have hmem_map :
      StateSize.rawChainEpoch { send := some link.send.intoPb, recv := some link.recv.intoPb } + 200 ∈
        chain0.intoPb.links.map (fun ep => StateSize.rawChainEpoch ep + 200) :=
    List.mem_map.mpr ⟨_, hmem_into, rfl⟩
  have hle_sum := List.le_sum_of_mem hmem_map
  have hprev_le :
      link.recv.prev.data.length ≤
        StateSize.rawChainEpoch { send := some link.send.intoPb, recv := some link.recv.intoPb } + 200 := by
    dsimp only [StateSize.rawChainEpoch, StateSize.optRaw, ChainEpochDirection.intoPb, StateSize.rawEpochDir]
    omega
  unfold StateSize.rawChain at hchain_le
  omega

theorem encodeRaw_v0_state_len_lt {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State}
    {chain0 chain1 : Chain} {rawKey : Bytes}
    (hst_len : stateBytes.length < 2 ^ 32)
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hgt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (hrk : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey)) :
    (PqRatchetState.encodeRaw {
      versionNegotiation := some vn
      chain := some chain1.intoPb
      inner := some (.v1 pb)
    }).length < 2 ^ 63 := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hvn' : (pqRatchetStateToPb pre_pb).versionNegotiation = some vn := by
    rw [pqRatchetStateToPb_vn, hvn]
  have hinner' := pqRatchetStateToPb_inner_some hinner
  have hchain' : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hrecv := recv_vn_some_inner_some_gt (spqrDeps F K) (spqrHkdfWith F)
    hpre hd hvn' hinner' hge hgt
  rw [hchain', hcf] at hrecv
  dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at hrecv
  rw [hrk] at hrecv
  dsimp only [SpqrApiResult.ofChainResult, Bind.bind, Except.bind] at hrecv
  exact (recv_state_len_lt F K (spqrHkdfWith F) stateBytes msgBytes _ hst_len hrecv).2.2.1

/-! ## 2. Stack Frame Helpers & `step_v0_err_2388` (`+2388 .. +2420 -> +2540`) -/

theorem frame1912_split_err_2388 (sp0 : BitVec 64) :
    memRegion (sp0 - 2008#64) 1912 =
      memRegion (sp0 - 2008#64) 1864 ∗
      (∃∗ d0 : BitVec 64, (sp0 - 144#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp0 - 136#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp0 - 128#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 120#64) 24 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2008#64) (n := 1864) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 24) (k := 24)
        (b' := sp0 - 120#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 (sp0 - 144#64),
      bv_sub_add_lit sp0 144 8,
      bv_sub_add_lit sp0 144 16]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]

theorem frame4544_join_err_2388 (sp0 : BitVec 64) (w0 w1 w2 w3 d0 d1 d2 : BitVec 64) :
    memRegion (sp0 - 4640#64) 2544 ∗
      ((sp0 - 2096#64) ↦₆₄ w0) ∗
      ((sp0 - 2088#64) ↦₆₄ w1) ∗
      ((sp0 - 2080#64) ↦₆₄ w2) ∗
      ((sp0 - 2072#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 2064#64) 56 ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₆₄ d0) ∗
      ((sp0 - 136#64) ↦₆₄ d1) ∗
      ((sp0 - 128#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have h32 :
      ((sp0 - 2096#64) ↦₆₄ w0) ∗ ((sp0 - 2088#64) ↦₆₄ w1) ∗
        ((sp0 - 2080#64) ↦₆₄ w2) ∗ ((sp0 - 2072#64) ↦₆₄ w3) ⊢
      memRegion (sp0 - 2096#64) 32 := by
    have h := words4_to_memRegion_32 (sp0 - 2096#64) w0 w1 w2 w3
    rwa [bv_sub_add_lit sp0 2096 8, bv_sub_add_lit sp0 2096 16, bv_sub_add_lit sp0 2096 24] at h
  have h24 :
      ((sp0 - 144#64) ↦₆₄ d0) ∗ ((sp0 - 136#64) ↦₆₄ d1) ∗ ((sp0 - 128#64) ↦₆₄ d2) ⊢
      memRegion (sp0 - 144#64) 24 := by
    have h := words3_to_memRegion_24 (sp0 - 144#64) d0 d1 d2
    rwa [bv_sub_add_lit sp0 144 8, bv_sub_add_lit sp0 144 16] at h
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4640#64) 2544 ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗
        ((sp0 - 2088#64) ↦₆₄ w1) ∗
        ((sp0 - 2080#64) ↦₆₄ w2) ∗
        ((sp0 - 2072#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 2064#64) 56 ∗
        memRegion (sp0 - 2008#64) 1864 ∗
        ((sp0 - 144#64) ↦₆₄ d0) ∗
        ((sp0 - 136#64) ↦₆₄ d1) ∗
        ((sp0 - 128#64) ↦₆₄ d2) ∗
        memRegion (sp0 - 120#64) 24 =
      memRegion (sp0 - 4640#64) 2544 ∗
        (((sp0 - 2096#64) ↦₆₄ w0) ∗ ((sp0 - 2088#64) ↦₆₄ w1) ∗
          ((sp0 - 2080#64) ↦₆₄ w2) ∗ ((sp0 - 2072#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 2064#64) 56 ∗
        memRegion (sp0 - 2008#64) 1864 ∗
        (((sp0 - 144#64) ↦₆₄ d0) ∗ ((sp0 - 136#64) ↦₆₄ d1) ∗ ((sp0 - 128#64) ↦₆₄ d2)) ∗
        memRegion (sp0 - 120#64) 24 by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono h32
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24))))) ?_
  rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 2544) (k := 2000)
        (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 32) (k := 1968)
        (b' := sp0 - 2064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2064#64) (n := 56) (k := 1912)
        (b' := sp0 - 2008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2008#64) (n := 1864) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 24) (k := 24)
        (b' := sp0 - 120#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

theorem exists_words4_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ out : BitVec 64,
        (out ↦ₛ bs) =
          (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗
          ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) := by
  have h16_lo : (bs.take 16).length = 16 := by simp [h]
  have h16_hi : (bs.drop 16).length = 16 := by simp [h]
  obtain ⟨w0, w1, _, hp_lo⟩ := exists_unpack64_of_length_16 h16_lo
  obtain ⟨w2, w3, _, hp_hi⟩ := exists_unpack64_of_length_16 h16_hi
  refine ⟨w0, w1, w2, w3, fun out => ?_⟩
  conv_lhs => rw [← List.take_append_drop 16 bs]
  rw [pointsToBytes_append, h16_lo, hp_lo out, hp_hi (out + 16#64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_words8_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ d : Words8, ∀ out : BitVec 64, (out ↦ₛ bs) = words8At out d := by
  have h32_lo : (bs.take 32).length = 32 := by simp [h]
  have h32_hi : (bs.drop 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, hp_lo⟩ := exists_words4_of_length_32 h32_lo
  obtain ⟨w4, w5, w6, w7, hp_hi⟩ := exists_words4_of_length_32 h32_hi
  refine ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7⟩, fun out => ?_⟩
  conv_lhs => rw [← List.take_append_drop 32 bs]
  rw [pointsToBytes_append, h32_lo, hp_lo out, hp_hi (out + 32#64)]
  dsimp only [words8At]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_words3_of_length_24 {bs : List (BitVec 8)} (h : bs.length = 24) :
    ∃ w0 w1 w2 : BitVec 64,
      ∀ out : BitVec 64,
        (out ↦ₛ bs) =
          (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) := by
  have h8 : (bs.take 8).length = 8 := by simp [h]
  have h16 : (bs.drop 8).length = 16 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 h8
  obtain ⟨w1, w2, _, hp16⟩ := exists_unpack64_of_length_16 h16
  refine ⟨w0, w1, w2, fun out => ?_⟩
  conv_lhs => rw [← List.take_append_drop 8 bs]
  rw [pointsToBytes_append, h8, hw0, ← pointsTo64_eq_pointsToBytes, hp16 (out + 8#64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_words27_of_length_216 {bs : List (BitVec 8)} (h : bs.length = 216) :
    ∃ d : Words27, ∀ out : BitVec 64, (out ↦ₛ bs) = words27At out d := by
  let bs192 := bs.drop 24
  let bs128 := bs192.drop 64
  have h24 : (bs.take 24).length = 24 := by simp [h]
  have h64_1 : (bs192.take 64).length = 64 := by simp [bs192, h]
  have h64_2 : (bs128.take 64).length = 64 := by simp [bs128, bs192, h]
  have h64_3 : (bs128.drop 64).length = 64 := by simp [bs128, bs192, h]
  obtain ⟨w0, w1, w2, hp24⟩ := exists_words3_of_length_24 h24
  obtain ⟨a, hpa⟩ := exists_words8_of_length_64 h64_1
  obtain ⟨b, hpb⟩ := exists_words8_of_length_64 h64_2
  obtain ⟨c, hpc⟩ := exists_words8_of_length_64 h64_3
  refine ⟨⟨w0, w1, w2,
    a.w0, a.w1, a.w2, a.w3, a.w4, a.w5, a.w6, a.w7,
    b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7,
    c.w0, c.w1, c.w2, c.w3, c.w4, c.w5, c.w6, c.w7⟩, fun out => ?_⟩
  have h1 : (out ↦ₛ bs) = (out ↦ₛ bs.take 24) ∗ ((out + 24#64) ↦ₛ bs192) := by
    conv_lhs => rw [← List.take_append_drop 24 bs]
    rw [pointsToBytes_append, h24]
  have h2 : ((out + 24#64) ↦ₛ bs192) = ((out + 24#64) ↦ₛ bs192.take 64) ∗ ((out + 88#64) ↦ₛ bs128) := by
    conv_lhs => rw [← List.take_append_drop 64 bs192]
    have hadd : (out + 24#64) + BitVec.ofNat 64 (bs192.take 64).length = out + 88#64 := by
      rw [h64_1, BitVec.add_assoc]; rfl
    rw [pointsToBytes_append, hadd]
  have h3 : ((out + 88#64) ↦ₛ bs128) = ((out + 88#64) ↦ₛ bs128.take 64) ∗ ((out + 152#64) ↦ₛ bs128.drop 64) := by
    conv_lhs => rw [← List.take_append_drop 64 bs128]
    have hadd : (out + 88#64) + BitVec.ofNat 64 (bs128.take 64).length = out + 152#64 := by
      rw [h64_2, BitVec.add_assoc]; rfl
    rw [pointsToBytes_append, hadd]
  rw [h1, h2, h3, hp24 out, hpa (out + 24#64), hpb (out + 88#64), hpc (out + 152#64)]
  dsimp only [words8At, words27At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bytes32_expose_words4_move (sp0 : BitVec 64) {bs32 : List (BitVec 8)}
    (hlen32 : bs32.length = 32) :
    ((sp0 - 4976#64) ↦ₛ bs32) ⊢
      ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ⌜((sp0 - 3040#64) ↦₆₄ v2) ∗ ((sp0 - 3032#64) ↦₆₄ v3) ∗
          ((sp0 - 3024#64) ↦₆₄ v4) ∗ ((sp0 - 3016#64) ↦₆₄ v5) =
          ((sp0 - 3040#64) ↦ₛ bs32)⌝ ∗
        ((sp0 - 4976#64) ↦₆₄ v2) ∗ ((sp0 - 4968#64) ↦₆₄ v3) ∗
        ((sp0 - 4960#64) ↦₆₄ v4) ∗ ((sp0 - 4952#64) ↦₆₄ v5) := by
  obtain ⟨v2, v3, v4, v5, hpts32⟩ := exists_words4_of_length_32 hlen32
  have hsrc := hpts32 (sp0 - 4976#64)
  rw [bv_sub_add_lit sp0 4976 8, bv_sub_add_lit sp0 4976 16, bv_sub_add_lit sp0 4976 24] at hsrc
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hsrc
  have hdst := (hpts32 (sp0 - 3040#64)).symm
  rw [bv_sub_add_lit sp0 3040 8, bv_sub_add_lit sp0 3040 16, bv_sub_add_lit sp0 3040 24] at hdst
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hdst
  rw [hsrc]
  refine Entails.sepExists_right v2 (Entails.sepExists_right v3
    (Entails.sepExists_right v4 (Entails.sepExists_right v5 ?_)))
  exact Entails.pure_right hdst (Entails.refl _)

theorem bytes224_expose_words28_move (sp0 : BitVec 64) {bs224 : List (BitVec 8)}
    (hlen224 : bs224.length = 224) :
    ((sp0 - 4864#64) ↦ₛ bs224) ⊢
      ∃∗ w_in0 : BitVec 64, ∃∗ d : Words27,
        ⌜((sp0 - 2928#64) ↦₆₄ w_in0) ∗ words27SubAt sp0 2928 d =
          ((sp0 - 2928#64) ↦ₛ bs224)⌝ ∗
        ((sp0 - 4864#64) ↦₆₄ w_in0) ∗ words27SubAt sp0 4864 d := by
  have h8 : (bs224.take 8).length = 8 := by simp [hlen224]
  have h216 : (bs224.drop 8).length = 216 := by simp [hlen224]
  obtain ⟨w_in0, hw0⟩ := exists_unpack64_of_length_8 h8
  obtain ⟨d, hd⟩ := exists_words27_of_length_216 h216
  have hsrc : ((sp0 - 4864#64) ↦ₛ bs224) =
      ((sp0 - 4864#64) ↦₆₄ w_in0) ∗ words27SubAt sp0 4864 d := by
    conv_lhs => rw [← List.take_append_drop 8 bs224]
    rw [pointsToBytes_append, h8, hw0, ← pointsTo64_eq_pointsToBytes,
        hd ((sp0 - 4864#64) + 8#64),
        words27At_sub_eq sp0 4864 d]
  have hdst : ((sp0 - 2928#64) ↦₆₄ w_in0) ∗ words27SubAt sp0 2928 d =
      ((sp0 - 2928#64) ↦ₛ bs224) := by
    conv_rhs => rw [← List.take_append_drop 8 bs224]
    rw [pointsToBytes_append, h8, hw0, ← pointsTo64_eq_pointsToBytes,
        hd ((sp0 - 2928#64) + 8#64),
        words27At_sub_eq sp0 2928 d]
  rw [hsrc]
  refine Entails.sepExists_right w_in0 (Entails.sepExists_right d ?_)
  exact Entails.pure_right hdst (Entails.refl _)

theorem ret_48_split_6 (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (r + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (r + 16#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (r + 24#64) ↦₆₄ r3) ∗
      (∃∗ r4 : BitVec 64, (r + 32#64) ↦₆₄ r4) ∗
      (∃∗ r5 : BitVec 64, (r + 40#64) ↦₆₄ r5) := by
  rw [ret_48_split r, memRegion_16_split (r + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem vecU8_sub_entails_header_buf (A : RustAlloc) (sp0 : BitVec 64) (m : Nat) (bs : List (BitVec 8))
    (h0 : m < 2 ^ 64 := by decide) (h16 : 16 < m := by decide) :
    vecU8 A (sp0 - BitVec.ofNat 64 m) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp0 - BitVec.ofNat 64 m) ↦₆₄ cap) ∗
        ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ ptr) ∗
        ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs := by
  unfold vecU8
  apply sepExists_left_entails; intro cap
  apply sepExists_left_entails; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [RustHeap.vecU8At_eq_header_sep_buf A (sp0 - BitVec.ofNat 64 m) cap ptr bs]
  dsimp only [RustHeap.vecHeader]
  rw [bv_sub_add_lit sp0 m 8 (by omega) h0, bv_sub_add_lit sp0 m 16 h16 h0]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem recv_ok_some_foldX (A : RustAlloc) (r : BitVec 64)
    (stBytes rawKey : List (BitVec 8))
    (cap_st ptr_st cap_rk ptr_rk : BitVec 64) :
    (r ↦₆₄ cap_st) ∗ ((r + 8#64) ↦₆₄ ptr_st) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((r + 24#64) ↦₆₄ cap_rk) ∗ ((r + 32#64) ↦₆₄ ptr_rk) ∗ ((r + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      RustHeap.vecU8Buf A cap_st ptr_st stBytes ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ⊢
    recvResultExactKeyAt A r (.ok (stBytes, some rawKey)) := by
  have hst :
      ((r ↦₆₄ cap_st) ∗ ((r + 8#64) ↦₆₄ ptr_st) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length)) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes ⊢
      vecU8 A r stBytes := by
    unfold vecU8
    refine Entails.sepExists_right cap_st (Entails.sepExists_right ptr_st ?_)
    rw [RustHeap.vecU8At_eq_header_sep_buf A r cap_st ptr_st stBytes]
    exact Entails.refl _
  have hrk :
      (((r + 24#64) ↦₆₄ cap_rk) ∗ ((r + 32#64) ↦₆₄ ptr_rk) ∗ ((r + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length)) ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ⊢
      optKeyBytesAt A (r + 24#64) (some rawKey) := by
    dsimp only [optKeyBytesAt]
    unfold vecU8
    refine Entails.sepExists_right cap_rk (Entails.sepExists_right ptr_rk ?_)
    rw [RustHeap.vecU8At_eq_header_sep_buf A (r + 24#64) cap_rk ptr_rk rawKey]
    dsimp only [RustHeap.vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  dsimp only [recvResultExactKeyAt]
  refine Entails.trans
    (Entails.of_eq (show
      (r ↦₆₄ cap_st) ∗ ((r + 8#64) ↦₆₄ ptr_st) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((r + 24#64) ↦₆₄ cap_rk) ∗ ((r + 32#64) ↦₆₄ ptr_rk) ∗ ((r + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey =
      (((r ↦₆₄ cap_st) ∗ ((r + 8#64) ↦₆₄ ptr_st) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length)) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes) ∗
      ((((r + 24#64) ↦₆₄ cap_rk) ∗ ((r + 32#64) ↦₆₄ ptr_rk) ∗ ((r + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length)) ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey) by ac_rfl)) ?_
  exact sepConj_mono hst hrk

theorem assemble_pqRatchetStatePBAt_3056 {H_inner : V1InnerHeapPred} {A : RustAlloc}
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) (chPb : ChainPB) (pb : V1State)
    {bs32 bs224 : List (BitVec 8)}
    (hlen32 : bs32.length = 32) (hlen224 : bs224.length = 224) :
    ((sp0 - 3056#64) ↦₆₄ w0) ∗
      ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦ₛ bs32) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 (some vn)).1 bs32 ∗
      ProtoRepr.chainPBAt A (sp0 - 3008#64) chPb ∗
      ((sp0 - 2928#64) ↦ₛ bs224) ∗
      (relocOptProtoPqRatchetInnerAt H_inner A (some (.v1 pb))).1 bs224 ⊢
    Prost.EncodeToVec.pqRatchetStatePBAt A (sp0 - 3056#64)
      { versionNegotiation := some vn, chain := some chPb, inner := some (.v1 pb) } := by
  rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt]
  unfold Drop.protoPqRatchetStateAt
  dsimp only
  have h128 : (sp0 - 3056#64) + 128#64 = sp0 - 2928#64 := bv_sub_add_lit sp0 3056 128
  rw [h128]
  have hvn_of := (relocOptVersionNegotiationPBTailAt A w0 w1 (some vn)).2.of_bytes
    (sp0 - 3040#64) bs32 hlen32
  have hvn_ent :
      ((sp0 - 3056#64) ↦₆₄ w0) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        (((sp0 - 3040#64) ↦ₛ bs32) ∗
          (relocOptVersionNegotiationPBTailAt A w0 w1 (some vn)).1 bs32) ⊢
      ProtoRepr.optVersionNegotiationPBAt A (sp0 - 3056#64) (some vn) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hvn_of)) ?_
    have h8 : (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 := bv_sub_add_lit sp0 3056 8
    have h16 : (sp0 - 3056#64) + 16#64 = sp0 - 3040#64 := bv_sub_add_lit sp0 3056 16
    rw [← h8, ← h16, vnTail_some_eq_versionNegotiationPBAt A (sp0 - 3056#64) w0 w1 vn]
    have hvec : vecU8At A (sp0 - 3056#64) w0 w1 vn.authKey ⊢ rustBytesVecAt A (sp0 - 3056#64) vn.authKey := by
      unfold rustBytesVecAt vecU8
      exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.refl _))
    have hcp : Top.ChainFromVersionNegotiation.optChainParamsPBAt (sp0 - 3056#64 + 24#64) vn.chainParams =
        ProtoRepr.optChainParamsPBAt (sp0 - 3056#64 + 24#64) vn.chainParams := by
      cases vn.chainParams <;> simp [Top.ChainFromVersionNegotiation.optChainParamsPBAt,
        ProtoRepr.optChainParamsPBAt, ProtoRepr.chainParamsPBAt, BitVec.add_assoc]
    dsimp only [Top.ChainFromVersionNegotiation.versionNegotiationPBAt,
      ProtoRepr.optVersionNegotiationPBAt, ProtoRepr.versionNegotiationPBAt]
    rw [hcp]
    exact sepConj_mono_left hvec
  have hch_eq :
      ProtoRepr.chainPBAt A (sp0 - 3008#64) chPb =
        ProtoRepr.optChainPBAt A ((sp0 - 3056#64) + 48#64) (some chPb) := by
    rw [bv_sub_add_lit sp0 3056 48]; rfl
  have hin_of := (relocOptProtoPqRatchetInnerAt H_inner A (some (.v1 pb))).2.of_bytes
    (sp0 - 2928#64) bs224 hlen224
  rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at hin_of
  rw [hch_eq]
  refine Entails.trans
    (Entails.of_eq (show
      ((sp0 - 3056#64) ↦₆₄ w0) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        ((sp0 - 3040#64) ↦ₛ bs32) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 (some vn)).1 bs32 ∗
        ProtoRepr.optChainPBAt A ((sp0 - 3056#64) + 48#64) (some chPb) ∗
        ((sp0 - 2928#64) ↦ₛ bs224) ∗
        (relocOptProtoPqRatchetInnerAt H_inner A (some (.v1 pb))).1 bs224 =
      (((sp0 - 3056#64) ↦₆₄ w0) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        (((sp0 - 3040#64) ↦ₛ bs32) ∗
          (relocOptVersionNegotiationPBTailAt A w0 w1 (some vn)).1 bs32)) ∗
      ProtoRepr.optChainPBAt A ((sp0 - 3056#64) + 48#64) (some chPb) ∗
      (((sp0 - 2928#64) ↦ₛ bs224) ∗
        (relocOptProtoPqRatchetInnerAt H_inner A (some (.v1 pb))).1 bs224) by ac_rfl)) ?_
  exact sepConj_mono hvn_ent (sepConj_mono_right hin_of)

theorem ownFrame_join_4896_ok_2380 (sp0 : BitVec 64)
    (w0 w1 v2 v3 v4 v5 w_in0 : BitVec 64) (d_in : Words27)
    (d880 d888 d896 e0 e1 e2 e3 e4 e5 : BitVec 64) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ v2) ∗
      ((sp0 - 4968#64) ↦₆₄ v3) ∗
      ((sp0 - 4960#64) ↦₆₄ v4) ∗
      ((sp0 - 4952#64) ↦₆₄ v5) ∗
      memRegion (sp0 - 4944#64) 80 ∗
      ((sp0 - 4864#64) ↦₆₄ w_in0) ∗
      words27SubAt sp0 4864 d_in ∗
      memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      ((sp0 - 4112#64) ↦₆₄ d880) ∗
      ((sp0 - 4104#64) ↦₆₄ d888) ∗
      ((sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      memRegion (sp0 - 3056#64) 352 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ e0) ∗
      ((sp0 - 2088#64) ↦₆₄ e1) ∗
      ((sp0 - 2080#64) ↦₆₄ e2) ∗
      ((sp0 - 2072#64) ↦₆₄ e3) ∗
      ((sp0 - 2064#64) ↦₆₄ e4) ∗
      ((sp0 - 2056#64) ↦₆₄ e5) ∗
      memRegion (sp0 - 2048#64) 1952 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  have hsplit (m n k m' : Nat)
      (hmn : m' = m - n) (hm : n < m) (hnk : m < 2 ^ 64) (hr : n + k ≤ 2 ^ 64) :
      memRegion (sp0 - BitVec.ofNat 64 m) (n + k) =
        memRegion (sp0 - BitVec.ofNat 64 m) n ∗
        memRegion (sp0 - BitVec.ofNat 64 m') k := by
    subst hmn
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 m) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 (m - n)) rfl (bv_sub_add_lit sp0 m n hm hnk).symm hr
  have h224 := words27SubAt_to_memRegion_224 sp0 4864 w_in0 d_in
  rw [show (0x1320 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (80 + (224 + (352 + (88 + (88 +
        (8 + (8 + (8 + (1032 + (352 + (608 + (8 + (8 + (8 + (8 + (8 + (8 + 1952)))))))))))))))))))))) by decide,
      hsplit 4992 8 4888 4984 rfl (by decide) (by decide) (by decide),
      hsplit 4984 8 4880 4976 rfl (by decide) (by decide) (by decide),
      hsplit 4976 8 4872 4968 rfl (by decide) (by decide) (by decide),
      hsplit 4968 8 4864 4960 rfl (by decide) (by decide) (by decide),
      hsplit 4960 8 4856 4952 rfl (by decide) (by decide) (by decide),
      hsplit 4952 8 4848 4944 rfl (by decide) (by decide) (by decide),
      hsplit 4944 80 4768 4864 rfl (by decide) (by decide) (by decide),
      hsplit 4864 224 4544 4640 rfl (by decide) (by decide) (by decide),
      hsplit 4640 352 4192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 4104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 4016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 4008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 4000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 3992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 2960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 352 2608 2704 rfl (by decide) (by decide) (by decide),
      hsplit 2704 608 2000 2096 rfl (by decide) (by decide) (by decide),
      hsplit 2096 8 1992 2088 rfl (by decide) (by decide) (by decide),
      hsplit 2088 8 1984 2080 rfl (by decide) (by decide) (by decide),
      hsplit 2080 8 1976 2072 rfl (by decide) (by decide) (by decide),
      hsplit 2072 8 1968 2064 rfl (by decide) (by decide) (by decide),
      hsplit 2064 8 1960 2056 rfl (by decide) (by decide) (by decide),
      hsplit 2056 8 1952 2048 rfl (by decide) (by decide) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ v2) ∗
        ((sp0 - 4968#64) ↦₆₄ v3) ∗
        ((sp0 - 4960#64) ↦₆₄ v4) ∗
        ((sp0 - 4952#64) ↦₆₄ v5) ∗
        memRegion (sp0 - 4944#64) 80 ∗
        ((sp0 - 4864#64) ↦₆₄ w_in0) ∗
        words27SubAt sp0 4864 d_in ∗
        memRegion (sp0 - 4640#64) 352 ∗
        memRegion (sp0 - 4288#64) 88 ∗
        memRegion (sp0 - 4200#64) 88 ∗
        ((sp0 - 4112#64) ↦₆₄ d880) ∗
        ((sp0 - 4104#64) ↦₆₄ d888) ∗
        ((sp0 - 4096#64) ↦₆₄ d896) ∗
        memRegion (sp0 - 4088#64) 1032 ∗
        memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        ((sp0 - 2096#64) ↦₆₄ e0) ∗
        ((sp0 - 2088#64) ↦₆₄ e1) ∗
        ((sp0 - 2080#64) ↦₆₄ e2) ∗
        ((sp0 - 2072#64) ↦₆₄ e3) ∗
        ((sp0 - 2064#64) ↦₆₄ e4) ∗
        ((sp0 - 2056#64) ↦₆₄ e5) ∗
        memRegion (sp0 - 2048#64) 1952 =
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ v2) ∗
        ((sp0 - 4968#64) ↦₆₄ v3) ∗
        ((sp0 - 4960#64) ↦₆₄ v4) ∗
        ((sp0 - 4952#64) ↦₆₄ v5) ∗
        memRegion (sp0 - 4944#64) 80 ∗
        (((sp0 - 4864#64) ↦₆₄ w_in0) ∗ words27SubAt sp0 4864 d_in) ∗
        memRegion (sp0 - 4640#64) 352 ∗
        memRegion (sp0 - 4288#64) 88 ∗
        memRegion (sp0 - 4200#64) 88 ∗
        ((sp0 - 4112#64) ↦₆₄ d880) ∗
        ((sp0 - 4104#64) ↦₆₄ d888) ∗
        ((sp0 - 4096#64) ↦₆₄ d896) ∗
        memRegion (sp0 - 4088#64) 1032 ∗
        memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        ((sp0 - 2096#64) ↦₆₄ e0) ∗
        ((sp0 - 2088#64) ↦₆₄ e1) ∗
        ((sp0 - 2080#64) ↦₆₄ e2) ∗
        ((sp0 - 2072#64) ↦₆₄ e3) ∗
        ((sp0 - 2064#64) ↦₆₄ e4) ∗
        ((sp0 - 2056#64) ↦₆₄ e5) ∗
        memRegion (sp0 - 2048#64) 1952 by ac_rfl)) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right (sepConj_mono h224 ?_)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem words3_sub2096_to_memRegion_24 (sp0 w0 w1 w2 : BitVec 64) :
    ((sp0 - 2096#64) ↦₆₄ w0) ∗
      ((sp0 - 2088#64) ↦₆₄ w1) ∗
      ((sp0 - 2080#64) ↦₆₄ w2) ⊢
    memRegion (sp0 - 2096#64) 24 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 8) (k := 16)
        (b' := sp0 - 2088#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2088#64) (n := 8) (k := 8)
        (b' := sp0 - 2080#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _))

end CryptoVerification.SpqrV1.Top.Recv

