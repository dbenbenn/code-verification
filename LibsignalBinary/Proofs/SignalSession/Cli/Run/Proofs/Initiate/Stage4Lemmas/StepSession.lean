/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Frames -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Cells
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import Lean
import Lean.Elab.SyntheticMVars
import Lean.Meta.Reduce
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import ProofLib.ProgramReflection
import ProofLib.SepLogic.CodeLookup
import ProofLib.SepLogic.WP.ControlTactics
import ProofLib.VCGen
import ProofLib
import ProofLib.FsTrace
import ProofLib.Placed.Multi
import ProofLib.ProgramReflection.Variant.TrapTransfer
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Stage 4 Segment 3: `SessionState` Construction, Move to `0x460`, and `logOff` Jump (`+4848 → +5252`)

Executes `+4848 → +5252` (`+0x12f0 → +0x1484`): runs `<SessionState>::new`,
`with_receiver_chain`, `with_sender_chain`, and `set_kyber_ciphertext`, moves the `344`-byte
`SessionState` into `[fsp + 0x460, fsp + 0x5b8)` (`[fsp + 0x5b9] := 1#8`), checks `logOff = 0#64`,
and jumps via `b.lo` to `+5252`, folding `sessionStateAt A (fsp + 0x460#64) sg ss`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem vecU8_eq_header_buf (A : RustAlloc) (base : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8 A base bs =
      ∃∗ cap : BitVec 64, ∃∗ bufPtr : BitVec 64,
        (base ↦₆₄ cap) ∗
        ((base + 8#64) ↦₆₄ bufPtr) ∗
        ((base + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap bufPtr bs := by
  unfold RustHeap.vecU8
  refine congrArg sepExists (funext fun cap => congrArg sepExists (funext fun bufPtr => ?_))
  have hhdr : RustHeap.vecU8At A base cap bufPtr bs =
      RustHeap.vecHeader base cap bufPtr (BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap bufPtr bs := by
    unfold RustHeap.vecU8At vecU8Buf; ac_rfl
  rw [hhdr]
  dsimp only [RustHeap.vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem encodeBytesField_len32_pos (tag : BitVec 32) {b : List (BitVec 8)}
    (hb : b.length = 32) :
    (LibsignalSpqrV1.Proto.encodeBytesField tag b).length =
      (LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited).length + 33 := by
  cases b with
  | nil => simp at hb
  | cons _ _ =>
    have hlen : (_ :: _).length = 32 := hb
    unfold LibsignalSpqrV1.Proto.encodeBytesField LibsignalSpqrV1.Proto.encodeBytesUncond
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_append, hlen]
    have hv : (LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 32)).length = 1 := by decide
    rw [hv]

theorem spqrInitialState_pqLen_pos (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (k : BitVec 256) :
    0 < (LibsignalSpqrV1.spqrV1Init F K .a2b k).length := by
  rw [← SpqrV1.Top.InitialState.initialStateValue_libsignal F K .a2b k]
  let au := LibsignalSpqrV1.Authenticator.new F (HMAC.keyToBytes32 k) 1#64
  have hpb : (SpqrV1.Top.InitInner.initV1State F .a2b (HMAC.keyToBytes32 k)).into_pb =
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := au.rootKey, macKey := au.macKey } } }) } := rfl
  have hrk := encodeBytesField_len32_pos 1#32 (b := au.rootKey)
    (by simp [au, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked])
  have hmk := encodeBytesField_len32_pos 2#32 (b := au.macKey)
    (by simp [au, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked])
  have hak := encodeBytesField_len32_pos 1#32 (b := HMAC.keyToBytes32 k)
    (by simp [HMAC.keyToBytes32])
  simp only [LibsignalSpqrV1.libsignalSpqrParams, LibsignalSpqrV1.Direction.ofSpqrDirection,
    SpqrV1.Top.InitialState.initialStateValue, SpqrV1.Top.InitialState.initialStatePB,
    SpqrV1.Top.InitialState.initialStateVN, hpb,
    LibsignalSpqrV1.PqRatchetState.encodeRaw, LibsignalSpqrV1.PqRatchetState.Inner.encode,
    LibsignalSpqrV1.V1State.encodeRaw, LibsignalSpqrV1.V1State.InnerState.encode,
    LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw,
    LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.encodeRaw,
    LibsignalSpqrV1.ProtoAuthenticator.encodeRaw, LibsignalSpqrV1.VersionNegotiationPB.encodeRaw,
    LibsignalSpqrV1.ChainParamsPB.encodeRaw, LibsignalSpqrV1.Proto.encodeOptMessage,
    LibsignalSpqrV1.Proto.encodeMessage, LibsignalSpqrV1.Proto.encodeUint32Field,
    LibsignalSpqrV1.Proto.encodeUint64Field, List.length_append, hrk, hmk, hak]
  decide

theorem aliceSession344_split_7words_288
    (base p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck : BitVec 64)
    (pad_f4 : BitVec 32) (pad40 : List (BitVec 8))
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) :
    let bs := aliceSession344Bv8 p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck
      pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144
    (base ↦ₛ bs) =
      (base ↦₆₄ 33#64) ∗
      ((base + 8#64) ↦₆₄ p1) ∗
      ((base + 16#64) ↦₆₄ 33#64) ∗
      ((base + 24#64) ↦₆₄ 33#64) ∗
      ((base + 32#64) ↦₆₄ p2) ∗
      ((base + 40#64) ↦₆₄ 33#64) ∗
      ((base + 48#64) ↦₆₄ 32#64) ∗
      ((base + 56#64) ↦ₛ bs.drop 56) := by
  intro bs
  let pre56 : List (BitVec 8) :=
    unpack64 33#64 ++ unpack64 p1 ++ unpack64 33#64 ++
      unpack64 33#64 ++ unpack64 p2 ++ unpack64 33#64 ++ unpack64 32#64
  let rest288 : List (BitVec 8) :=
    (unpack64 p3 ++ unpack64 32#64) ++
      receiverChainVecBytes24 cb ++
      aliceMid48Bv8 p4 c5 p5 l5 ++
      senderChainBytes100 spub spriv sck 0#32 ++
      aliceTail100Bv8 pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144
  have hpre56 : pre56.length = 56 := by simp [pre56, unpack64]
  have hbs_eq : bs = pre56 ++ rest288 := by
    dsimp only [bs, aliceSession344Bv8, aliceHead144Bv8, alicePre72Bv8, pre56, rest288]
    simp only [List.append_assoc]
  have hdrop : bs.drop 56 = rest288 := by
    rw [hbs_eq]
    exact List.drop_left' hpre56
  conv => lhs; rw [hbs_eq]
  rw [pointsToBytes_append, hpre56, ← hdrop]
  dsimp only [pre56]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes, sepConj_assoc]

theorem pointsToBytes32_entails_memRegion32 (base : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 32) :
    (base ↦ₛ bs) ⊢ memRegion base 32 :=
  h ▸ pointsToBytes_entails_memRegion base bs

theorem keyAndIdx_entails_memRegion36 (base : BitVec 64) (k : BitVec 256) (idx : BitVec 32) :
    (base ↦ₛ keyToBytes32 k) ∗ ((base + 32#64) ↦₃₂ idx) ⊢ memRegion base 36 := by
  have hlen : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
  rw [ProofLib.memRegion_split' (b := base) (n := 32) (k := 4)
        (b' := base + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (hlen ▸ pointsToBytes_entails_memRegion base (keyToBytes32 k))
    (pointsTo32_entails_memRegion (base + 32#64) idx)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
