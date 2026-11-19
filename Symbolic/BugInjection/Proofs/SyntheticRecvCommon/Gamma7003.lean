/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PtNoCollision7003
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# `gamma compI7003` Unfoldings, Setup Characterization, and Invisible-Step Preservation

Provides:
1. Term-level `@[simp]` / rewrite lemmas for `gamma compI7003 S g` across all 13 `Composed`
   subfunctors, plus `compLookupDh_variantBytes` (`agree` invariance under `Variant.SubF`).
2. Setup characterization for any `ProtocolSetup` satisfying `compFitsPinned7003 setup7003 compI7003 r`.
3. Preservation of states, protocol events, and `bobDoneBaseKeys` across invisible (`Step.network`)
   prefixes in `MatchesEventsAt`.
4. Protobuf field-extraction (`preKeyWire_msg_inj_7003`, `trWireBytes_pq_inj_7003`) and
   `DrawsMatch` coin-slicing lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003

open ByteSpecs (hmacWith)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux encodeBytesField encodeUint32Field)
open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (WireFields FieldItem EncodingVariation canonicalVariation paddedVarint encodeField
   x25519PublicKeySymbol x25519AgreementSymbol aesCbcEncryptSymbol sha256CompressFunction)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent agree)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol PreKeyProto versionByte wirePrekeyTag)
open DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo isCurrentSnapshot)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.COMPOSED.CompTrace (NetE at?_append_of_lt)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux (pack_of_view_eq_some)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next invisible_eq_network)
open Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003

/-! ## 1. `gamma compI7003` Unfoldings -/

section GammaUnfold
unseal DY.Bytes

theorem rec_eq_concretizeAll
    {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm) (x : F DY.Bytes)
    (hsub : DY.Bytes.SubFunction pf (concretizeAll i S g) := by
      refine @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => ?_⟩
      simp -failIfUnchanged only [concretizeAll,
        DY.Libsignal.Composed.Refinement.allFuns,
        DY.Libsignal.Composed.Refinement.litFuns,
        DY.Libsignal.Composed.Refinement.concatFuns,
        DY.Libsignal.Composed.Refinement.dhFuns,
        DY.Libsignal.Composed.Refinement.kdfFuns,
        DY.Libsignal.Composed.Refinement.symFuns,
        DY.Libsignal.Composed.Refinement.truncFuns,
        DY.Libsignal.Composed.Refinement.x25519Funs,
        DY.Libsignal.Composed.Refinement.kemFuns,
        DY.Libsignal.Composed.Refinement.sigFuns,
        DY.Libsignal.Composed.Refinement.spqrFuns,
        DY.Libsignal.Composed.Refinement.trWireFuns,
        Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
      rfl) :
    DY.Bytes.rec (concretizeAll i S g) (DY.BytesView.pack x) =
      pf x (fun y _ => DY.Bytes.rec (concretizeAll i S g) y) := by
  have := hsub
  exact DY.Bytes.rec_eq pf (concretizeAll i S g) x

theorem gamma_randTerm_pos (S : OpaqueSymbolSemantics) (g : Ghost) (ts n : Nat) (hn : n ≠ 0) :
    gamma compI7003 S g (randTerm ts n) = g.σ ts n := by
  unfold gamma gamma' randTerm
  rw [rec_eq_concretizeAll (concretizeRandom g) ({ timestamp := ts, size := n } : DY.Random.Random DY.Bytes)]
  simp [concretizeRandom, hn, node]

@[simp]
theorem gamma_randTerm_zero (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) :
    gamma compI7003 S g (randTerm ts 0) = [] := by
  unfold gamma gamma' randTerm
  rw [rec_eq_concretizeAll (concretizeRandom g) ({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes)]
  rfl

@[simp]
theorem gamma_literalToBytes (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    gamma compI7003 S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma'
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll concretizeLit]
  rfl

@[simp]
theorem gamma_concat (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma compI7003 S g (DY.Concat.concat a b) =
      gamma compI7003 S g a ++ gamma compI7003 S g b := by
  unfold gamma gamma'
  show ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll concretizeConcat]
  rfl

@[simp]
theorem gamma_dhPk (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    gamma compI7003 S g (DY.DiffieHellman.dhPk sk) =
      compLookupPub (clamp (gamma compI7003 S g sk)) := by
  unfold gamma gamma'
  show ((({ sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeDhPk compI7003)]
  dsimp only [concretizeDhPk, node]
  rw [compI7003_publicKey, Option.getD_some]

private theorem gamma_dh_pack (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    gamma compI7003 S g (({ pk, sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      compLookupDh (clamp (gamma compI7003 S g sk)) (gamma compI7003 S g pk) := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeDh compI7003) ({ pk, sk } : DY.DiffieHellman.Dh.SubF DY.Bytes)]
  dsimp only [concretizeDh, node]
  rw [compI7003_agreement, Option.getD_some]

@[simp]
theorem gamma_dh (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    gamma compI7003 S g (DY.DiffieHellman.dh pk sk) =
      compLookupDh (clamp (gamma compI7003 S g sk)) (gamma compI7003 S g pk) := by
  unfold DY.DiffieHellman.dh DY.DiffieHellman.instCanDHBytes
  dsimp only
  cases hv : pk.view? DY.DiffieHellman.DhPk.SubF with
  | none => exact gamma_dh_pack S g pk sk
  | some x =>
    rcases x with ⟨sk2⟩
    dsimp only
    rcases pack_of_view_eq_some hv with rfl
    change _ = compLookupDh (clamp (gamma compI7003 S g sk))
      (gamma compI7003 S g (DY.DiffieHellman.dhPk sk2))
    have hpk2 : ({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack =
        DY.DiffieHellman.dhPk sk2 := rfl
    have hpk1 : ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack =
        DY.DiffieHellman.dhPk sk := rfl
    rw [hpk2, hpk1]
    split
    · exact gamma_dh_pack S g (DY.DiffieHellman.dhPk sk2) sk
    · rw [gamma_dh_pack S g (DY.DiffieHellman.dhPk sk) sk2, gamma_dhPk, gamma_dhPk]
      exact compLookupDh_comm _ _

@[simp]
theorem gamma_variant_pack (S : OpaqueSymbolSemantics) (g : Ghost)
    (x : DY.X25519.Variant.SubF DY.Bytes) :
    gamma compI7003 S g x.pack = variantBytes (gamma compI7003 S g x.key) x.variation := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeVariant compI7003) x]
  dsimp only [concretizeVariant, node]
  rw [torsionShift_compI7003]

@[simp]
theorem gamma_kdfExtract (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma compI7003 S g (DY.KdfExtract.kdfExtract a b) =
      hmacWith F7 (gamma compI7003 S g a) (gamma compI7003 S g b) := by
  unfold gamma gamma'
  show ((({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeKdf compI7003)]
  rfl

@[simp]
theorem gamma_symEnc (S : OpaqueSymbolSemantics) (g : Ghost) (k iv m : DY.Bytes) :
    gamma compI7003 S g (DY.SymEnc.symEnc k iv m) =
      compAesPerm (gamma compI7003 S g k) ((gamma compI7003 S g iv).take 16)
        (gamma compI7003 S g m) := by
  unfold gamma gamma'
  show ((({ key := k, iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeSym compI7003)]
  dsimp only [concretizeSym, node]
  rw [compI7003_aesEncrypt, Option.getD_some]

@[simp]
theorem gamma_trunc8 (S : OpaqueSymbolSemantics) (g : Ghost) (a : DY.Bytes) :
    gamma compI7003 S g (DY.Trunc.trunc8 a) = (gamma compI7003 S g a).take 8 := by
  unfold gamma gamma'
  show ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll concretizeTrunc]
  rfl

theorem gamma_trWireMsg (S : OpaqueSymbolSemantics) (g : Ghost)
    (ver : UInt8) (rk : DY.Bytes) (cnt pcnt : UInt32) (ct pq : DY.Bytes)
    (ev : EncodingVariation) :
    gamma compI7003 S g (DY.TrWire.trWireMsg ver rk cnt pcnt ct pq ev) =
      trWireBytes (g.addr (DY.TrWire.trWireMsg ver rk cnt pcnt ct pq ev)) ev
        { version := ver.toNat, ratchetKey := gamma compI7003 S g rk,
          counter := cnt.toNat, previousCounter := pcnt.toNat,
          ciphertext := gamma compI7003 S g ct }
        (gamma compI7003 S g pq) := by
  unfold gamma gamma'
  show ((({ version := ver, senderRatchetKey := rk, counter := cnt, previousCounter := pcnt,
            ciphertext := ct, pqRatchet := pq, encodingVariation := ev } :
      DY.TrWire.TrWireMsg.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeTrWire g)]
  rfl

@[simp]
theorem gamma_kemPk (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    gamma compI7003 S g (DY.PQKem.kemPk sk) = S.kemPk (gamma compI7003 S g sk) := by
  unfold gamma gamma'
  show ((({ sk } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeKemPk S)]
  rfl

theorem gamma_kemEncap_fst_32 (S : OpaqueSymbolSemantics) (g : Ghost) (pk e : DY.Bytes)
    (he : (gamma compI7003 S g e).length = 32) :
    gamma compI7003 S g (DY.PQKem.kemEncap pk e).1 =
      (compKyberEncaps (gamma compI7003 S g e)).take 1568 := by
  unfold gamma gamma'
  show ((({ pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeKemEncap compI7003)]
  dsimp only [concretizeKemEncap]
  have he' : ((e.rec (concretizeAll compI7003 S g)).bytes).length = 32 := he
  simp only [he', ↓reduceIte, node, compI7003_kyberEncaps, Option.getD_some]

theorem gamma_kemEncap_snd_32 (S : OpaqueSymbolSemantics) (g : Ghost) (pk e : DY.Bytes)
    (he : (gamma compI7003 S g e).length = 32) :
    gamma compI7003 S g (DY.PQKem.kemEncap pk e).2 =
      (compKyberEncaps (gamma compI7003 S g e)).drop 1568 := by
  unfold gamma gamma'
  show ((({ pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (concretizeKemSS compI7003 S)]
  dsimp only [concretizeKemSS]
  have he' : ((e.rec (concretizeAll compI7003 S g)).bytes).length = 32 := he
  simp only [he', ↓reduceIte, node, compI7003_kyberEncaps, Option.getD_some]

@[simp]
theorem gamma_spqrInit (S : OpaqueSymbolSemantics) (g : Ghost) (k p : DY.Bytes) :
    gamma compI7003 S g (DY.Spqr.spqrInit k p) =
      S.init (gamma compI7003 S g k) (gamma compI7003 S g p) := by
  unfold gamma gamma' DY.Spqr.spqrInit
  rw [rec_eq_concretizeAll (concretizeSpqrInit S) ({ authKey := k, params := p } : DY.Spqr.InitState.SubF DY.Bytes)]
  rfl

@[simp]
theorem gamma_spqrChainKey (S : OpaqueSymbolSemantics) (g : Ghost) (k p idx : DY.Bytes) :
    gamma compI7003 S g (DY.Spqr.spqrChainKey k p idx) =
      spqrKeyBytes (S.chainKey (gamma compI7003 S g k) (gamma compI7003 S g p) (gamma compI7003 S g idx)) := by
  unfold gamma gamma' DY.Spqr.spqrChainKey
  rw [rec_eq_concretizeAll (concretizeSpqrChainKey S)
    ({ authKey := k, params := p, idx } : DY.Spqr.ChainKey.SubF DY.Bytes)]
  rfl

@[simp]
theorem gamma_spqrSendState (S : OpaqueSymbolSemantics) (g : Ghost) (st c : DY.Bytes) :
    gamma compI7003 S g (({ st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes).pack) =
      S.sendState (gamma compI7003 S g st) (gamma compI7003 S g c) := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeSpqrSendState S) ({ st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes)]
  rfl

@[simp]
theorem gamma_spqrSendKey (S : OpaqueSymbolSemantics) (g : Ghost) (st c : DY.Bytes) :
    gamma compI7003 S g (({ st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack) =
      spqrKeyBytes (S.sendKey (gamma compI7003 S g st) (gamma compI7003 S g c)) := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeSpqrSendKey S) ({ st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes)]
  rfl

@[simp]
theorem gamma_spqrSendMsg (S : OpaqueSymbolSemantics) (g : Ghost) (st c : DY.Bytes) :
    gamma compI7003 S g (({ st, coins := c } : DY.Spqr.SendMsg.SubF DY.Bytes).pack) =
      S.sendMsg (gamma compI7003 S g st) (gamma compI7003 S g c) := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeSpqrSendMsg S) ({ st, coins := c } : DY.Spqr.SendMsg.SubF DY.Bytes)]
  rfl

@[simp]
theorem gamma_spqrRecvState (S : OpaqueSymbolSemantics) (g : Ghost) (st m : DY.Bytes) :
    gamma compI7003 S g (({ st, msg := m } : DY.Spqr.RecvState.SubF DY.Bytes).pack) =
      S.recvState (gamma compI7003 S g st) (gamma compI7003 S g m) := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeSpqrRecvState S) ({ st, msg := m } : DY.Spqr.RecvState.SubF DY.Bytes)]
  rfl

@[simp]
theorem gamma_spqrRecvKey (S : OpaqueSymbolSemantics) (g : Ghost) (st m : DY.Bytes) :
    gamma compI7003 S g (({ st, msg := m } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) =
      spqrKeyBytes (S.recvKey (gamma compI7003 S g st) (gamma compI7003 S g m)) := by
  unfold gamma gamma'
  rw [rec_eq_concretizeAll (concretizeSpqrRecvKey S) ({ st, msg := m } : DY.Spqr.RecvKey.SubF DY.Bytes)]
  rfl

end GammaUnfold

/-! ## 2. X25519 `agree` Variant Invariance -/

private theorem pow256_pos : ∀ n : Nat, 0 < 256 ^ n
  | 0 => by decide
  | n + 1 => by have := pow256_pos n; rw [Nat.pow_succ]; omega

private theorem mod_256_mul (w m : Nat) (hm : 0 < m) :
    w % 256 + 256 * (w / 256 % m) = w % (m * 256) := by
  have hr_lt : w % 256 < 256 := Nat.mod_lt w (by decide)
  have hq2_lt : w / 256 % m < m := Nat.mod_lt (w / 256) hm
  have hdiv1 := Nat.div_add_mod w 256
  have hdiv2 := Nat.div_add_mod (w / 256) m
  have hlin : 256 * (w / 256) = 256 * (m * (w / 256 / m)) + 256 * (w / 256 % m) := by
    rw [← Nat.left_distrib, hdiv2]
  have hmul : 256 * (m * (w / 256 / m)) = m * 256 * (w / 256 / m) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 256 m]
  have hw_eq : w = m * 256 * (w / 256 / m) + (w % 256 + 256 * (w / 256 % m)) := by omega
  have hlt : w % 256 + 256 * (w / 256 % m) < m * 256 := by omega
  calc w % 256 + 256 * (w / 256 % m)
      = (w % 256 + 256 * (w / 256 % m)) % (m * 256) := (Nat.mod_eq_of_lt hlt).symm
    _ = (m * 256 * (w / 256 / m) + (w % 256 + 256 * (w / 256 % m))) % (m * 256) :=
        (Nat.mul_add_mod (m * 256) (w / 256 / m) _).symm
    _ = w % (m * 256) := by rw [← hw_eq]

private theorem leValue_leBytes :
    ∀ (n w : Nat), DY.X25519.leValue ((leBytes n w).map BitVec.toNat) = w % 256 ^ n
  | 0, _ => by simp [leBytes, DY.X25519.leValue, Nat.mod_one]
  | n + 1, w => by
    simp only [leBytes, List.map_cons, DY.X25519.leValue, Nat.pow_succ, leValue_leBytes n (w / 256)]
    have hb : (BitVec.ofNat 8 w).toNat = w % 256 := BitVec.toNat_ofNat w 8
    rw [hb]
    exact mod_256_mul w (256 ^ n) (pow256_pos n)

theorem x25519UCoord_variantBytes (b : HwBytes) (v : Fin 4) (hb : b.length = 32) :
    x25519UCoord (variantBytes b v) = x25519UCoord b := by
  unfold variantBytes
  simp only [hb, ↓reduceIte]
  set u := x25519UCoord b
  have hu_lt : u < DY.X25519.p25519 := by
    unfold u x25519UCoord DY.X25519.uCoord
    exact Nat.mod_lt _ (by unfold DY.X25519.p25519; omega)
  set u' := if v.val / 2 = 1 ∧ u + DY.X25519.p25519 < 2 ^ 255 then u + DY.X25519.p25519 else u
  have hu'_lt : u' < 2 ^ 255 := by
    dsimp only [u']; split
    · next h => exact h.2
    · unfold DY.X25519.p25519 at hu_lt; omega
  have hu'_mod : u' % DY.X25519.p25519 = u := by
    dsimp only [u']; split
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hu_lt]
    · exact Nat.mod_eq_of_lt hu_lt
  set w := if v.val % 2 = 1 then u' + 2 ^ 255 else u'
  have hw_lt : w < 256 ^ 32 := by
    have hpow : 256 ^ 32 = 2 ^ 256 := by decide
    rw [hpow]; dsimp only [w]; split <;> omega
  unfold x25519UCoord DY.X25519.uCoord
  rw [leValue_leBytes 32 w, Nat.mod_eq_of_lt hw_lt]
  have hw_mod : w % 2 ^ 255 = u' := by
    dsimp only [w]; split
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hu'_lt]
    · exact Nat.mod_eq_of_lt hu'_lt
  rw [hw_mod, hu'_mod]

theorem compLookupDh_variantBytes (s b : HwBytes) (v : Fin 4) :
    compLookupDh s (variantBytes b v) = compLookupDh s b := by
  by_cases hb : b.length = 32
  · have hvb : (variantBytes b v).length = 32 := by
      unfold variantBytes; simp only [hb, ↓reduceIte]; exact leBytes_length 32 _
    have hu := x25519UCoord_variantBytes b v hb
    have req := compI7003_cryptoEquationsHold.x25519_agreement_reads_u_coordinate s
      (variantBytes b v) b hvb hb hu
    simpa [compI7003_agreement] using req
  · unfold variantBytes; simp only [hb, ↓reduceIte]

@[simp]
theorem gamma_agree (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    gamma compI7003 S g (agree pk sk) =
      compLookupDh (clamp (gamma compI7003 S g sk)) (gamma compI7003 S g pk) := by
  unfold agree DY.X25519.normalizeX25519Key
  cases hv : pk.view? DY.X25519.Variant.SubF with
  | none => rw [gamma_dh]
  | some x =>
    rcases pack_of_view_eq_some hv with rfl
    rw [gamma_dh, gamma_variant_pack, compLookupDh_variantBytes]

/-! ## 3. Pinned Setup Characterization (`setup7003`) -/

theorem setupTrace_eq_7003 {r : ProtocolSetup}
    (hf : compFitsPinned7003 setup7003 compI7003 r) :
    setupTrace r = Symbolic.Swarm.CREF.b1_setupTr4 "alice" "bob" := by
  obtain ⟨⟨hwf, hopk, _, _, _, _, _⟩, _, _, ⟨ha, hb⟩, _⟩ := hf
  rw [Symbolic.Swarm.CREF.b1_setupTrace_eq r hwf.1, hopk, ha, hb]
  rfl

theorem setup_ids_7003 {r : ProtocolSetup}
    (hf : compFitsPinned7003 setup7003 compI7003 r) :
    r.alice = "alice" ∧ r.bob = "bob" ∧ r.withOpk = false ∧
    r.regIdA = 1111 ∧ r.regIdB = 2222 ∧ r.spkId = 7 ∧ r.kpkId = 9 := by
  obtain ⟨⟨_, hopk, hra, hrb, hspk, hkpk, _⟩, _, _, ⟨ha, hb⟩, _⟩ := hf
  exact ⟨ha, hb, hopk, hra, hrb, hspk, hkpk⟩

theorem setup_secrets_7003 {r : ProtocolSetup}
    (hf : compFitsPinned7003 setup7003 compI7003 r) :
    secretBytes r 0 = setup7003.aliceId ∧
    secretBytes r 1 = setup7003.bobId ∧
    secretBytes r 2 = setup7003.spk ∧
    secretBytes r 3 = fillFresh 11 64 ∧
    secretBytes r 4 = fillFresh 16 64 ∧
    secretBytes r 5 = fillFresh 17 64 ∧
    r.kyberSecB = setup7003.kyberSec ∧
    r.opaqueBytes (setupPublic r 5) = setup7003.spkSig ∧
    r.opaqueBytes (setupPublic r 6) = setup7003.kyberPk ∧
    r.opaqueBytes (setupPublic r 7) = setup7003.kyberPkSig := by
  obtain ⟨⟨_, _, _, _, _, _, hs0, hs1, hs2, ho5, ho6, ho7, hsec, _⟩, _, ⟨hs3, hs4, hs5⟩, _⟩ := hf
  exact ⟨hs0, hs1, hs2, hs3, hs4, hs5, hsec, ho5, ho6, ho7⟩

theorem pubBytes_ikA_7003 {r : ProtocolSetup}
    (hf : compFitsPinned7003 setup7003 compI7003 r) :
    pubBytes compI7003 (secretBytes r 0) = compPubOfIdx 0 := by
  rw [(setup_secrets_7003 hf).1]
  unfold pubBytes
  rw [compI7003_publicKey, Option.getD_some]
  unfold compLookupPub
  rw [coins_secret_indices.2.2.2.2.1]
  rfl

theorem gamma_setup_keys_7003 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hgs : GhostAndSemMatchSetup compI7003 r S g) :
    gamma compI7003 S g (randTerm 0 32) = setup7003.aliceId ∧
    gamma compI7003 S g (randTerm 5 32) = setup7003.bobId ∧
    gamma compI7003 S g (randTerm 10 32) = setup7003.spk ∧
    gamma compI7003 S g (randTerm 16 64) = fillFresh 16 64 ∧
    gamma compI7003 S g (DY.DiffieHellman.dhPk (randTerm 0 32)) = compPubOfIdx 0 ∧
    gamma compI7003 S g (DY.DiffieHellman.dhPk (randTerm 5 32)) = compPubOfIdx 1 ∧
    gamma compI7003 S g (DY.DiffieHellman.dhPk (randTerm 10 32)) = compPubOfIdx 2 ∧
    gamma compI7003 S g (DY.PQKem.kemPk (randTerm 16 64)) = setup7003.kyberPk ∧
    S.kemDecap setup7003.kyberPk kyberCt0Bytes = kyberSs0Bytes := by
  obtain ⟨hσ, hopq, hdec⟩ := hgs
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨hs0, hs1, hs2, _, hs4, _, _, _, ho6, _⟩ := setup_secrets_7003 hf
  have hne : r.alice ≠ r.bob := by rw [ha, hb]; decide
  have hrat : setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hne, hopk]; rfl
  have hg0 : gamma compI7003 S g (randTerm 0 32) = setup7003.aliceId := by
    rw [gamma_randTerm_pos S g 0 32 (by decide), hσ (0, 32) (by rw [hrat]; simp)]
    simpa [secretBytes, hrat] using hs0
  have hg5 : gamma compI7003 S g (randTerm 5 32) = setup7003.bobId := by
    rw [gamma_randTerm_pos S g 5 32 (by decide), hσ (5, 32) (by rw [hrat]; simp)]
    simpa [secretBytes, hrat] using hs1
  have hg10 : gamma compI7003 S g (randTerm 10 32) = setup7003.spk := by
    rw [gamma_randTerm_pos S g 10 32 (by decide), hσ (10, 32) (by rw [hrat]; simp)]
    simpa [secretBytes, hrat] using hs2
  have hg16 : gamma compI7003 S g (randTerm 16 64) = fillFresh 16 64 := by
    rw [gamma_randTerm_pos S g 16 64 (by decide), hσ (16, 64) (by rw [hrat]; simp)]
    simpa [secretBytes, hrat] using hs4
  have hp6 : setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) :=
    Symbolic.Swarm.CREF.b1_setupPublic_6 r hne
  have hkpk : gamma compI7003 S g (DY.PQKem.kemPk (randTerm 16 64)) = setup7003.kyberPk := by
    rw [← hp6]; exact (hopq r.pqpkPubTerm (by simp)).trans ho6
  have hkd : S.kemDecap setup7003.kyberPk kyberCt0Bytes = kyberSs0Bytes := by
    have h1 := hdec kyberCt0Bytes
    have ho6' : r.opaqueBytes r.pqpkPubTerm = setup7003.kyberPk := ho6
    rw [ho6'] at h1
    rw [h1]
    unfold kyberDecapsBytes
    rw [compI7003_kyberDecaps, Option.getD_some, coins_secret_indices.2.2.2.2.2.2.2.2.2.2.2]
  refine ⟨hg0, hg5, hg10, hg16, ?_, ?_, ?_, hkpk, hkd⟩
  · rw [gamma_dhPk, hg0]; unfold compLookupPub; rw [coins_secret_indices.2.2.2.2.1]; rfl
  · rw [gamma_dhPk, hg5]; unfold compLookupPub; rw [coins_secret_indices.2.2.2.2.2.1]; rfl
  · rw [gamma_dhPk, hg10]; unfold compLookupPub; rw [coins_secret_indices.2.2.2.2.2.2.1]; rfl

/-! ## 4. Invisible (`Step.network`) Prefix Preservation -/

theorem step_network_next (msg : DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).next tr = tr.append (NetE msg) := by
  rw [show (Step.network msg).next tr =
      ((DY.Network.sendMessage msg).run tr).2.val from
    stepIn_next DY.Network.reachability msg tr]
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]

theorem runSteps_invisible_eq_append_nets {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) :
    ∃ msgs : List DY.Bytes,
      runSteps pre tr = msgs.foldl (fun t m => t.append (NetE m)) tr := by
  induction pre generalizing tr with
  | nil => exact ⟨[], rfl⟩
  | cons s ss ih =>
    obtain ⟨m, rfl⟩ := invisible_eq_network (hinv s List.mem_cons_self)
    obtain ⟨ms, hms⟩ := ih
      (fun x hx => hinv x (List.mem_cons_of_mem _ hx)) ((Step.network m).next tr)
    refine ⟨m :: ms, ?_⟩
    dsimp only [runSteps, List.foldl_cons]
    rw [hms, step_network_next]

private theorem append_net_at?_nonNet {E : Type} [ExecTraceTypes.Has E]
    (hnone : ∀ (m : DY.Bytes),
      (TraceEntryHas.proj (TraceEntryHas.inj (NetE m) : ExecTrace.Entry) : Option E) = none)
    (tr : ExecTrace) (m : DY.Bytes) (i : Nat) :
    ((tr.append (NetE m)).at? i : Option E) = (tr.at? i : Option E) := by
  by_cases hi : i < tr.length
  · exact at?_append_of_lt tr (NetE m) hi
  · by_cases heq : i = tr.length
    · subst heq
      have hlt : tr.length < (tr.append (NetE m)).length := by
        simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hnlt : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [DY.Trace.at?, hlt, hnlt, ↓reduceDIte]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2,
        ↓reduceDIte]
      exact hnone m
    · have hnlt1 : ¬ i < (tr.append (NetE m)).length := by
        simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      simp only [DY.Trace.at?, hnlt1, hi, ↓reduceDIte]

theorem runSteps_invisible_at?_nonNet {E : Type} [ExecTraceTypes.Has E]
    (hnone : ∀ (m : DY.Bytes),
      (TraceEntryHas.proj (TraceEntryHas.inj (NetE m) : ExecTrace.Entry) : Option E) = none)
    {pre : List Step} (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) (i : Nat) :
    ((runSteps pre tr).at? i : Option E) = (tr.at? i : Option E) := by
  obtain ⟨msgs, hfold⟩ := runSteps_invisible_eq_append_nets hinv tr
  rw [hfold]; clear hfold
  induction msgs generalizing tr with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldl_cons, ih, append_net_at?_nonNet hnone]

theorem runSteps_invisible_at?_trState {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) (i : Nat) :
    ((runSteps pre tr).at? i : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState))) = tr.at? i :=
  runSteps_invisible_at?_nonNet (fun _ => rfl) hinv tr i

theorem runSteps_invisible_at?_pqxdhState {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) (i : Nat) :
    ((runSteps pre tr).at? i : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState PQXDHState))) = tr.at? i :=
  runSteps_invisible_at?_nonNet (fun _ => rfl) hinv tr i

theorem runSteps_invisible_getEventAt_pqxdh {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) (i : Nat) :
    (runSteps pre tr).getEventAt PQXDHEvent i = tr.getEventAt PQXDHEvent i := by
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
    runSteps_invisible_at?_nonNet (fun _ => rfl) hinv]

theorem runSteps_invisible_getEventAt_tr {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) (i : Nat) :
    (runSteps pre tr).getEventAt TREvent i = tr.getEventAt TREvent i := by
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
    runSteps_invisible_at?_nonNet (fun _ => rfl) hinv]

theorem runSteps_invisible_getEventAt_comp {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) (i : Nat) :
    (runSteps pre tr).getEventAt ComposedEvent i = tr.getEventAt ComposedEvent i := by
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
    runSteps_invisible_at?_nonNet (fun _ => rfl) hinv]

theorem runSteps_invisible_length_le {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) :
    tr.length ≤ (runSteps pre tr).length := by
  obtain ⟨msgs, hfold⟩ := runSteps_invisible_eq_append_nets hinv tr
  rw [hfold]; clear hfold
  induction msgs generalizing tr with
  | nil => exact Nat.le_refl _
  | cons m ms ih =>
    rw [List.foldl_cons]
    refine Nat.le_trans ?_ (ih _)
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem range_split_le {a b : Nat} (h : a ≤ b) :
    List.range b = List.range a ++ List.range' a (b - a) := by
  induction h with
  | refl => simp
  | @step m hm ih =>
    have hle : a ≤ m := hm
    have hsub : m + 1 - a = (m - a) + 1 := by omega
    rw [List.range_succ, ih, hsub, List.range'_concat, List.append_assoc, Nat.one_mul,
      Nat.add_sub_cancel' hle]

theorem runSteps_invisible_bobDoneBaseKeys {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (tr : ExecTrace) :
    bobDoneBaseKeys (runSteps pre tr) = bobDoneBaseKeys tr := by
  unfold bobDoneBaseKeys
  have hle := runSteps_invisible_length_le hinv tr
  let f : Nat → Option DY.Bytes := fun i =>
    match (runSteps pre tr).getEventAt PQXDHEvent i with
    | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
    | _ => none
  change (List.range (runSteps pre tr).length).filterMap f = _
  rw [range_split_le hle, List.filterMap_append]
  have htail : (List.range' tr.length ((runSteps pre tr).length - tr.length)).filterMap f = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro i hi
    rw [List.mem_range'_1] at hi
    dsimp only [f]
    rw [runSteps_invisible_getEventAt_pqxdh hinv, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    have hnlt : ¬ i < tr.length := by omega
    have hnone : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
      simp [DY.Trace.at?, hnlt]
    rw [hnone]
  rw [htail, List.append_nil]
  refine List.filterMap_congr fun i _ => ?_
  dsimp only [f]
  rw [runSteps_invisible_getEventAt_pqxdh hinv]
  rfl

/-! ## 5. Protobuf Field-Extraction & `DrawsMatch` Slicing Helpers -/

private theorem encodeVarint_pos (v : BitVec 64) : 1 ≤ (encodeVarint v).length := by
  cases h : encodeVarint v with
  | nil => unfold encodeVarint encodeVarintAux at h; split at h <;> cases h
  | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

private theorem paddedVarint_pos (n pad : Nat) : 1 ≤ (paddedVarint n pad).length := by
  cases h : paddedVarint n pad with
  | nil => rw [paddedVarint] at h; split at h <;> cases h
  | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

theorem preKeyWire_msg_inj {pkId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32}
    {ik ek ct msg w : HwBytes} (hw : w.length = 159)
    (heq : preKeyWire pkId spkId kpkId regId ik ek ct msg =
      preKeyWire pkId spkId kpkId regId ik ek ct w) :
    msg = w := by
  unfold preKeyWire PreKeyProto.encode at heq
  have heq0 := (List.cons.inj (List.cons.inj heq).2).2
  have h1 := List.append_cancel_right (List.append_cancel_right
    (List.append_cancel_right (List.append_cancel_right heq0)))
  simp only [List.append_assoc] at h1
  have h2 := List.append_cancel_left (List.append_cancel_left (List.append_cancel_left h1))
  unfold encodeBytesField at h2
  dsimp only at h2
  simp only [List.append_assoc] at h2
  have h3 := List.append_cancel_left h2
  have hlen := congrArg List.length h3
  simp only [List.length_append, hw] at hlen
  have h159 : (encodeVarint (BitVec.ofNat 64 159)).length = 2 := by decide
  rw [h159] at hlen
  have hpos := encodeVarint_pos (BitVec.ofNat 64 msg.length)
  have hlt : msg.length < 161 := by omega
  have hmlen : msg.length = 159 := by
    have hmem : msg.length ∈ List.range 161 := List.mem_range.mpr hlt
    have hall : ∀ k ∈ List.range 161,
        (encodeVarint (BitVec.ofNat 64 k)).length + k = 161 → k = 159 := by decide
    exact hall msg.length hmem (by omega)
  rw [hmlen, ← hw] at h3
  exact List.append_cancel_left h3

theorem preKeyWire_msg_inj_7003 {msg w : HwBytes} (hw : w.length = 159)
    (heq : preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0)) (compPubOfIdx 3)
      kyberCt0Bytes msg =
      preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0)) (compPubOfIdx 3)
      kyberCt0Bytes w) :
    msg = w :=
  preKeyWire_msg_inj hw heq

theorem trWireBytes_pq_inj_7003 {addr : HwBytes} {f : WireFields} {pq w : HwBytes}
    (hw_pos : 0 < w.length) (hw_lt : w.length < 64)
    (heq : trWireBytes addr canonicalVariation f pq =
      trWireBytes addr canonicalVariation f w) :
    pq = w := by
  unfold trWireBytes trFields honestTrItems at heq
  simp only [↓reduceIte, List.flatMap_append] at heq
  have heq0 := (List.cons.inj heq).2
  have hpre : canonicalVariation.fields.flatMap (trItemEncode addr canonicalVariation f pq) =
      canonicalVariation.fields.flatMap (trItemEncode addr canonicalVariation f w) := by
    refine List.flatMap_congr fun it hit => ?_
    have h1 : canonicalVariation.fields = [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0] := rfl
    rw [h1] at hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl | rfl <;> rfl
  have hsfx : (if addr = [] then ([] : List FieldItem) else [.known 6 0 0]).flatMap
      (trItemEncode addr canonicalVariation f pq) =
      (if addr = [] then ([] : List FieldItem) else [.known 6 0 0]).flatMap
      (trItemEncode addr canonicalVariation f w) := by
    split <;> rfl
  rw [hpre, hsfx] at heq0
  have hmid := List.append_cancel_right (List.append_cancel_left heq0)
  have hw_ne : w ≠ [] := by intro h; simp [h] at hw_pos
  simp only [hw_ne, ↓reduceIte] at hmid
  by_cases hpq : pq = []
  · subst hpq
    simp only [↓reduceIte, List.flatMap_nil, List.flatMap_cons, List.append_nil,
      trItemEncode, encodeField] at hmid
    have hlen := congrArg List.length hmid
    simp only [List.length_nil, List.length_append] at hlen
    have hp := paddedVarint_pos (5 * 8 + 2) 0
    omega
  · simp only [hpq, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      trItemEncode, encodeField, List.append_assoc] at hmid
    have h1 := List.append_cancel_left hmid
    have hlen := congrArg List.length h1
    simp only [List.length_append] at hlen
    have hw_pv : paddedVarint w.length 0 = [BitVec.ofNat 8 w.length] := by
      rw [paddedVarint]; simp [show w.length < 128 by omega]
    rw [hw_pv, List.length_singleton] at hlen
    have hpos := paddedVarint_pos pq.length 0
    have hpq_lt : pq.length < 128 := by omega
    have hpq_pv : paddedVarint pq.length 0 = [BitVec.ofNat 8 pq.length] := by
      rw [paddedVarint]; simp [hpq_lt]
    rw [hpq_pv, hw_pv] at h1
    exact (List.cons.inj h1).2

theorem drawsMatch_nil_or_single {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts cl : Nat} {coins : HwBytes}
    (hgwf : ∀ v : VisEntry, v = rngEntry (randTerm ts cl) →
      cl ≠ 0 → (g.σ ts cl).length = cl)
    (hdm : DrawsMatch compI7003 r S g
      (if cl = 0 then [] else [rngEntry (randTerm ts cl)]) coins) :
    cl ≤ coins.length ∧ gamma compI7003 S g (randTerm ts cl) = coins.take cl := by
  by_cases hcl : cl = 0
  · subst hcl
    exact ⟨Nat.zero_le _, by simp [gamma_randTerm_zero]⟩
  · simp only [hcl, ↓reduceIte] at hdm
    obtain ⟨pieces, _, hpref, hf2⟩ := hdm
    rcases pieces with _ | ⟨p0, _ | ⟨p1, rest⟩⟩
    · cases hf2
    · cases hf2 with
      | cons hbm _ =>
        dsimp only [BytesMatchEntry, rngEntry, List.map_cons, List.map_nil] at hbm
        have hp0 : gamma compI7003 S g (randTerm ts cl) = p0 := List.singleton_injective hbm.2
        have hp0_len : p0.length = cl := by
          rw [← hp0, gamma_randTerm_pos S g ts cl hcl]
          exact hgwf _ rfl hcl
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hpref
        obtain ⟨_, rfl⟩ := hpref
        refine ⟨by simp [hp0_len], ?_⟩
        rw [hp0, ← hp0_len, List.take_left]
    · cases hf2 with
      | cons _ hf0 => cases hf0

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
