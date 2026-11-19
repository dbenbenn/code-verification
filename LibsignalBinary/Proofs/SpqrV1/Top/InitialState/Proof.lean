/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Steps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Final
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ExtProof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ExtHelpers

/-!
# Verification of `spqr::initial_state` (`0x542d0`)

Proves `InitialStateOkX` and `InitialStateOkXExt` for `spqr::initial_state` (`0x542d0`) by
version dispatch (`p.version = .v0` vs `.v1`), composing `auth_key.to_vec()`, `ChainParams.intoPb`
default elision, `spqr::init_inner`, `<PqRatchetState as prost::Message>::encode_to_vec`, and
`drop_glue::<PqRatchetState>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-! ## 1. Callee contract bundle -/

/-- `csel` default elision at `0x54408..0x54410` matches `cp.intoPb.maxJump`. -/
theorem chainParams_csel_maxJump (cp : ChainParams) :
    (if cp.maxJump = 25000#32 then 0#32 else cp.maxJump) = cp.intoPb.maxJump := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxJump = 25000#32 <;> simp [h]

/-- `csel` default elision at `0x54418..0x54420` matches `cp.intoPb.maxOooKeys`. -/
theorem chainParams_csel_maxOoo (cp : ChainParams) :
    (if cp.maxOooKeys = 2000#32 then 0#32 else cp.maxOooKeys) = cp.intoPb.maxOooKeys := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxOooKeys = 2000#32 <;> simp [h]

/-! ## 4. Version Branches and Layout Bridge -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  Expand.sp_sub_496_eq_esp Expand.sp_add_neg496_eq_esp Expand.esp_add_496_sub_496
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688 Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

private def initialStateSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private theorem initialStateSavedCells_entails_memRegion (s0 : State) :
    initialStateSavedCells s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold initialStateSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))))))))
  exact Entails.of_eq (by simp only [arm64_norm])

private theorem stackAt_initialState_split (sp : BitVec 64) :
    stackAt sp initialStateStack =
      stackAt (sp - 496#64) initialStateCalleeStack ∗
      memRegion (sp - 496#64) 400 ∗
      cells (sp - 96#64) 12 := by
  unfold stackAt initialStateStack initialStateFrame
  rw [ProofLib.memRegion_split'
        (b := sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack))
        (n := initialStateCalleeStack) (k := 496)
        (b' := sp - 496#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 496#64) (n := 400) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : (sp - 496#64) - BitVec.ofNat 64 initialStateCalleeStack =
      sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack) := by
    dsimp only [initialStateCalleeStack, initInnerStack, initInnerFrame, authNewStackX,
      encodeToVecStackX, dropStack96, allocHookStack]
    bv_omega
  rw [hsub]

private theorem stack_restore_initialState (s0 : State) :
    stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
    memRegion (s0.sp - 496#64) 400 ∗
    initialStateSavedCells s0 ⊢
    stackAt s0.sp initialStateStack := by
  rw [stackAt_initialState_split s0.sp, ← ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (initialStateSavedCells_entails_memRegion s0))

private theorem initialStateResultAt_v0_of_cells (A : RustAlloc) (F : ShaCompress)
    (ret : BitVec 64) (p : CryptoVerification.LibsignalSpqrV1.Params) (hv : p.version = .v0) :
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
    ((ret + 16#64) ↦₆₄ 1#64) ∗ ((ret + 24#64) ↦₆₄ 0#64) ⊢
    initialStateResultAt A ret (initialStateValue F p) := by
  unfold initialStateResultAt initialStateValue
  rw [hv]
  dsimp [emptyState]
  have h16 : (ret + 8#64) + 8#64 = ret + 16#64 := by bv_omega
  have h24 : (ret + 8#64) + 16#64 = ret + 24#64 := by bv_omega
  have hvec := vecU8_nil_of_cells A (ret + 8#64)
  rw [h16, h24] at hvec
  exact sepConj_mono_right hvec

private theorem wp6_h61_len_rawV1State_initV1State_le (F : ShaCompress)
    (d : Direction) (authKey : Bytes) :
    CryptoVerification.SpqrV1.Top.StateSize.rawV1State (initV1State F d authKey).into_pb ≤ 424 := by
  have hauth := CryptoVerification.SpqrV1.Top.StateSize.Authenticator.new_rawAuth_le F authKey 1#64
  cases d with
  | a2b =>
    dsimp only [initV1State, States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
      Unchunked.SendEk.KeysUnsampled.into_pb, spqrAuthApi,
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcKeysUnsampled]
    omega
  | b2a =>
    have hdec : CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec
        (spqrPolyApi.decoder_into_pb initHdrDecoder) = 352 := rfl
    dsimp only [initV1State, States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb,
      Unchunked.SendCt.NoHeaderReceived.into_pb, spqrAuthApi,
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcNoHeaderReceived]
    omega

/-- Encoded byte length of `initialStatePB F p` is `< 2 ^ 63` when `p.authKey.length < 2 ^ 32`. -/
theorem initialStatePB_encodeRaw_length_lt (F : ShaCompress)
    (p : CryptoVerification.LibsignalSpqrV1.Params) (hlen : p.authKey.length < 2 ^ 32) :
    (PqRatchetState.encodeRaw (initialStatePB F p)).length < 2 ^ 63 := by
  have h1 : (PqRatchetState.encodeRaw (initialStatePB F p)).length ≤
      CryptoVerification.SpqrV1.Top.StateSize.rawPqState (initialStatePB F p) + 752 :=
    CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState (initialStatePB F p)
  have hraw : CryptoVerification.SpqrV1.Top.StateSize.rawPqState (initialStatePB F p) =
      p.authKey.length + 0 +
        CryptoVerification.SpqrV1.Top.StateSize.rawV1State
          (initV1State F p.direction p.authKey).into_pb := rfl
  have h2 := wp6_h61_len_rawV1State_initV1State_le F p.direction p.authKey
  omega

/-- Assembles the 352-byte `pqRatchetStatePBAt A (sp + 0x28) (initialStatePB F p)` from
`spqr::init_inner`'s output at `sp + 0xa8` and the `VersionNegotiationPB` / `chain = None` stores. -/
theorem initialState_pbAt_of_cells (A : RustAlloc) (F : ShaCompress)
    (p : CryptoVerification.LibsignalSpqrV1.Params) (hv : p.version = .v1)
    (a cap ptr : BitVec 64) :
    (vecU8At A a cap ptr p.authKey ∗
      ((a + 0x18#64) ↦₃₂ 1#32) ∗
      ((a + 0x1c#64) ↦₃₂ p.chainParams.intoPb.maxJump) ∗
      ((a + 0x20#64) ↦₃₂ p.chainParams.intoPb.maxOooKeys) ∗
      ((a + 0x24#64) ↦₃₂ p.direction.toI32) ∗
      ((a + 0x28#64) ↦₃₂ p.minVersion.toI32) ∗
      memRegion (a + 0x2c#64) 4 ∗
      ((a + 0x30#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x38#64) 72 ∗
      initInnerResultAt A (F := F) (a + 0x80#64) .v1 p.direction p.authKey) ⊢
    pqRatchetStatePBAt A a (initialStatePB F p) := by
  have hvec : vecU8At A a cap ptr p.authKey ⊢ vecU8 A a p.authKey :=
    Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hvec) ?_
  dsimp only [pqRatchetStatePBAt, initialStatePB, optVersionNegotiationPBAt, versionNegotiationPBAt,
    initialStateVN, rustBytesVecAt, optChainParamsPBAt, chainParamsPBAt,
    optChainPBAt, optPqRatchetInnerPBAt]
  have h1c : a + 0x18#64 + 4#64 = a + 0x1c#64 := by bv_omega
  have h20 : a + 0x1c#64 + 4#64 = a + 0x20#64 := by bv_omega
  have h38 : a + 48#64 + 8#64 = a + 0x38#64 := by bv_omega
  rw [h1c, h20, h38,
      CryptoVerification.SpqrV1.Top.Recv.v1StatePBAt_eq_optProtoInnerStateAt A (a + 128#64)
        (initV1State F p.direction p.authKey).into_pb,
      initInnerResultAt_v1]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.InitialState
