/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step1Ev1

/-!
# Call-2 Send Collision Discharge (`¬ NextEventCollides` at `ev2`)
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

def MemoInjNe6 (S : OpaqueSymbolSemantics) (g : Ghost) (t : DY.Bytes) : Prop :=
  ∀ x ∈ (gamma' compI0 S g t).memo, assumedInjective x.1 = true → x.2.2.length ≠ 6

theorem memoInjNe6_of_gt7 {S : OpaqueSymbolSemantics} {g : Ghost} {t : DY.Bytes}
    (h : MemoInjGt7 S g t) : MemoInjNe6 S g t :=
  fun x hx hinj => by have := h x hx hinj; omega

theorem memoInjGt7_kemEncap_fst {S : OpaqueSymbolSemantics} {g : Ghost} {pk e : DY.Bytes}
    (hpk : MemoInjGt7 S g pk) (he : MemoInjGt7 S g e) :
    MemoInjGt7 S g (DY.PQKem.kemEncap pk e).1 := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show (DY.PQKem.kemEncap pk e).1 = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKemEncap compI0) (concretizeAll compI0 S g)] at hx
  dsimp only [concretizeKemEncap] at hx
  split_ifs at hx with helen
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
      List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe
    · change 7 < (((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [_, _]).getD []).take 1568).length
      rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compI0_kyberEncaps,
        Option.getD_some, List.length_take,
        Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compKyberEncaps_length]; decide
    · exact hpk x hxpk hinj
    · exact he x hxe hinj
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hpk x h hinj) (fun h => he x h hinj)

theorem memoInjNe6_lit (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    MemoInjNe6 S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) :=
  memoInjNe6_of_gt7 (memoInjGt7_lit S g b)

theorem memoInjNe6_randTerm {S : OpaqueSymbolSemantics} {g : Ghost} {idx sz : Nat}
    (h : sz = 0 ∨ (g.σ idx sz).length ≠ 6) :
    MemoInjNe6 S g (randTerm idx sz) := by
  intro x hx _
  unfold gamma' randTerm at hx
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI0 S g)] at hx
  dsimp only [concretizeRandom] at hx
  split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl
    exact h.resolve_left hsz

theorem memoInjNe6_concat {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (ha : MemoInjNe6 S g a) (hb : MemoInjNe6 S g b) :
    MemoInjNe6 S g (DY.Concat.concat a b) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq concretizeConcat (concretizeAll compI0 S g)] at hx
  simp only [concretizeConcat, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · rw [assumedInjective_concat] at hinj; cases hinj
  · exact ha x hxa hinj
  · exact hb x hxb hinj

theorem memoInjNe6_of_concat {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (h : MemoInjNe6 S g (DY.Concat.concat a b)) :
    MemoInjNe6 S g a ∧ MemoInjNe6 S g b := by
  have hp : gamma' compI0 S g (DY.Concat.concat a b) =
      concretizeConcat { lhs := a, rhs := b } (fun y _ => gamma' compI0 S g y) := by
    unfold gamma'
    rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq concretizeConcat (concretizeAll compI0 S g)]
  simp only [concretizeConcat, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hp
  refine ⟨fun x hx hinj => h x ?_ hinj, fun x hx hinj => h x ?_ hinj⟩
  · rw [hp]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  · rw [hp]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)

instance instBytesCompatiblePredMemoInjNe6 (S : OpaqueSymbolSemantics) (g : Ghost) :
    Comparse.BytesCompatiblePred (MemoInjNe6 S g) where
  pred_empty := memoInjNe6_lit S g .empty
  pred_concat _ _ hl hr := memoInjNe6_concat hl hr
  pred_split buf n hbuf := by
    cases hsp : Comparse.BytesLike.split buf n with
    | none => trivial
    | some p =>
      rw [← DY.Concat.concat_split buf n p.1 p.2 hsp] at hbuf
      exact memoInjNe6_of_concat hbuf
  pred_fromByteArray b := memoInjNe6_lit S g b

theorem memoInjNe6_serialize_local_tr {S : OpaqueSymbolSemantics} {g : Ghost}
    {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState}
    (hmyIk : MemoInjNe6 S g ls.state.myIk) (hpeerIk : MemoInjNe6 S g ls.state.peerIk)
    (hrk : MemoInjNe6 S g ls.state.rk) (hdhs : MemoInjNe6 S g ls.state.dhs)
    (hcks : MemoInjNe6 S g ls.state.cks) (hsid : MemoInjNe6 S g ls.state.sid)
    (hspqr : MemoInjNe6 S g ls.state.spqr)
    (hrecv : ∀ d ∈ ls.state.recv, MemoInjNe6 S g d.ratchetKey ∧ MemoInjNe6 S g d.chainKey) :
    MemoInjNe6 S g (DY.Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (MemoInjNe6 S g) ls]
  simpa [DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
    hmyIk, hpeerIk, hrk, hdhs, hcks, hsid, hspqr] using hrecv

theorem memoInjNe6_hmac {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (ha : MemoInjNe6 S g a) (hb : MemoInjNe6 S g b) :
    MemoInjNe6 S g (DY.Libsignal.TripleRatchet.hmac a b) := by
  intro x hx hinj
  unfold gamma' DY.Libsignal.TripleRatchet.hmac at hx
  rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKdf compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeKdf, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · dsimp only; rw [length_byteSpecs_hmacWith]; decide
  · exact ha x hxa hinj
  · exact hb x hxb hinj

theorem memoInjNe6_hkdfBlock1 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjNe6 S g prk) (hinfo : MemoInjNe6 S g info) :
    MemoInjNe6 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) :=
  memoInjNe6_hmac hprk (memoInjNe6_concat hinfo (memoInjNe6_lit S g _))

theorem memoInjNe6_hkdfBlock2 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjNe6 S g prk) (hinfo : MemoInjNe6 S g info) :
    MemoInjNe6 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) :=
  memoInjNe6_hmac hprk (memoInjNe6_concat (memoInjNe6_hkdfBlock1 hprk hinfo) (memoInjNe6_concat hinfo (memoInjNe6_lit S g _)))

theorem memoInjNe6_hkdfBlock3 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjNe6 S g prk) (hinfo : MemoInjNe6 S g info) :
    MemoInjNe6 S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) :=
  memoInjNe6_hmac hprk (memoInjNe6_concat (memoInjNe6_hkdfBlock2 hprk hinfo) (memoInjNe6_concat hinfo (memoInjNe6_lit S g _)))

theorem memoInjNe6_of_spqrInit {S : OpaqueSymbolSemantics} {g : Ghost} {a p : DY.Bytes}
    (h : MemoInjNe6 S g (DY.Spqr.spqrInit a p)) :
    MemoInjNe6 S g a ∧ MemoInjNe6 S g p := by
  have hp : gamma' compI0 S g (DY.Spqr.spqrInit a p) =
      concretizeSpqrInit S { authKey := a, params := p } (fun y _ => gamma' compI0 S g y) := by
    unfold gamma' DY.Spqr.spqrInit
    rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll compI0 S g)]
  simp only [concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hp
  refine ⟨fun x hx hinj => h x ?_ hinj, fun x hx hinj => h x ?_ hinj⟩
  · rw [hp]; exact List.mem_append_left _ hx
  · rw [hp]; exact List.mem_append_right _ hx

theorem memoInjNe6_spqrSend {S : OpaqueSymbolSemantics} {g : Ghost} {st coins : DY.Bytes}
    (hst : MemoInjNe6 S g st) (hcoins : MemoInjNe6 S g coins) :
    MemoInjNe6 S g (DY.Spqr.spqrSend st coins).1 ∧
    MemoInjNe6 S g (DY.Spqr.spqrSend st coins).2.1 ∧
    MemoInjNe6 S g (DY.Spqr.spqrSend st coins).2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hinj
    unfold gamma' DY.Spqr.spqrSend at hx
    dsimp only at hx
    rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll compI0 S g)] at hx
    simp only [concretizeSpqrSendState, opaqueNode, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hst x h hinj) (fun h => hcoins x h hinj)
  · have hv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
    unfold DY.Spqr.spqrSend
    dsimp only
    split
    · rename_i a p heq
      rw [heq] at hv; simp only at hv
      have hst' : MemoInjNe6 S g (DY.Spqr.spqrInit a p) := by
        unfold DY.Spqr.spqrInit DY.Spqr.InitState.SubF.pack
        rwa [hv]
      have ⟨ha, hp⟩ := memoInjNe6_of_spqrInit hst'
      intro x hx hinj
      unfold gamma' DY.Spqr.spqrChainKey at hx
      rw [DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll compI0 S g)] at hx
      simp only [concretizeSpqrChainKey, spqrKeyNode, opaqueNode, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
      rcases hx with hxa | hxp | hxi
      · exact ha x hxa hinj
      · exact hp x hxp hinj
      · exact memoInjNe6_lit S g _ x hxi hinj
    · intro x hx hinj
      unfold gamma' at hx
      rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll compI0 S g)] at hx
      simp only [concretizeSpqrSendKey, spqrKeyNode, opaqueNode, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
      exact hx.elim (fun h => hst x h hinj) (fun h => hcoins x h hinj)
  · intro x hx hinj
    unfold gamma' DY.Spqr.spqrSend at hx
    dsimp only at hx
    rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll compI0 S g)] at hx
    simp only [concretizeSpqrSendMsg, opaqueNode, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hst x h hinj) (fun h => hcoins x h hinj)

theorem memoInjNe6_symEnc {S : OpaqueSymbolSemantics} {g : Ghost} {k iv m : DY.Bytes}
    (hk : MemoInjNe6 S g k) (hiv : MemoInjNe6 S g iv) (hm : MemoInjNe6 S g m) :
    MemoInjNe6 S g (DY.SymEnc.symEnc k iv m) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeSym compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSym, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxk | hxiv | hxm
  · change (((compI0 DY.Libsignal.Refinement.aesCbcEncryptSymbol [_, _, _]).getD []).length) ≠ 6
    rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compI0_aesEncrypt, Option.getD_some]
    have hge := Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compAesPerm_length_ge_16
      (gamma' compI0 S g k).bytes ((gamma' compI0 S g iv).bytes.take 16) (gamma' compI0 S g m).bytes
    omega
  · exact hk x hxk hinj
  · exact hiv x hxiv hinj
  · exact hm x hxm hinj

theorem assumedInjective_trWire (x : DY.TrWire.TrWireMsg.SubF DY.Bytes) :
    assumedInjective x.pack = false := by
  unfold assumedInjective DY.TrWire.TrWireMsg.SubF.pack
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF x]
  rfl

theorem memoInjNe6_trHonestWireMsg {S : OpaqueSymbolSemantics} {g : Ghost}
    {rk ct pq : DY.Bytes} {ns pn : UInt32}
    (hrk : MemoInjNe6 S g rk) (hct : MemoInjNe6 S g ct) (hpq : MemoInjNe6 S g pq) :
    MemoInjNe6 S g (DY.Libsignal.TripleRatchet.trHonestWireMsg rk ns pn ct pq) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show DY.Libsignal.TripleRatchet.trHonestWireMsg rk ns pn ct pq =
      ({ version := DY.Libsignal.TripleRatchet.messageVersion, senderRatchetKey := rk,
         counter := ns, previousCounter := pn, ciphertext := ct, pqRatchet := pq,
         encodingVariation := DY.TrWire.canonicalVariation } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll compI0 S g)] at hx
  simp only [concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxrk | hxct | hxpq
  · rw [assumedInjective_trWire] at hinj; cases hinj
  · exact hrk x hxrk hinj
  · exact hct x hxct hinj
  · exact hpq x hxpq hinj

theorem gamma'_hmac_bytes_len (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    (gamma' compI0 S g (DY.Libsignal.TripleRatchet.hmac a b)).bytes.length = 32 := by
  unfold gamma' DY.Libsignal.TripleRatchet.hmac
  rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKdf compI0) (concretizeAll compI0 S g)]
  dsimp only [concretizeKdf, node]
  exact length_byteSpecs_hmacWith _ _ _

theorem memoInjNe6_computeMac {S : OpaqueSymbolSemantics} {g : Ghost}
    {mk sIk rIk wire : DY.Bytes}
    (hmk : MemoInjNe6 S g mk) (hsIk : MemoInjNe6 S g sIk)
    (hrIk : MemoInjNe6 S g rIk) (hwire : MemoInjNe6 S g wire) :
    MemoInjNe6 S g (DY.Libsignal.TripleRatchet.computeMac mk sIk rIk wire) := by
  set inner := DY.Libsignal.TripleRatchet.hmac mk (DY.Concat.concat sIk (DY.Concat.concat rIk wire))
  have hinner : MemoInjNe6 S g inner :=
    memoInjNe6_hmac hmk (memoInjNe6_concat hsIk (memoInjNe6_concat hrIk hwire))
  intro x hx hinj
  unfold gamma' DY.Libsignal.TripleRatchet.computeMac at hx
  rw [show DY.Trunc.trunc8 inner = ({ input := inner } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq concretizeTrunc (concretizeAll compI0 S g)] at hx
  simp only [concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hx_in
  · dsimp only
    rw [List.length_take, gamma'_hmac_bytes_len]; decide
  · exact hinner x hx_in hinj

def localEncState (st : DY.Libsignal.TripleRatchet.TRState) (coins : DY.Bytes) :
    DY.Libsignal.TripleRatchet.TRState :=
  { st with cks := (DY.Libsignal.TripleRatchet.kdfCk st.cks).1, ns := st.ns + 1,
            spqr := (DY.Spqr.spqrSend st.spqr coins).1 }

def localEncMsg (st : DY.Libsignal.TripleRatchet.TRState) (coins pqSalt m : DY.Bytes) :
    DY.Bytes :=
  let (_, seed) := DY.Libsignal.TripleRatchet.kdfCk st.cks
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg
    (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn (DY.SymEnc.symEnc keys.cipherKey keys.iv m)
    (DY.Spqr.spqrSend st.spqr coins).2.2
  DY.Concat.concat wire (DY.Libsignal.TripleRatchet.computeMac keys.macKey st.myIk st.peerIk wire)

def localEncTr (tr : ExecTrace) (me : DY.Participant) (stIdx cl : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (pqSalt : DY.Bytes) : ExecTrace :=
  let m := randTerm tr.length 32
  let coins := randTerm (tr.length + 1) cl
  ((((((tr.append (CompTrace.RndE 32)).append (CompTrace.RndE cl)).append
    (CompTrace.NetE (DY.Spqr.spqrSend st.spqr coins).2.1)).append
    (CompTrace.TREvE (.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m))).append
    (CompTrace.TREvE (.MessageKey (st.sessionInfo me) .sender
      (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pqSalt st.ns st.rIdx stIdx))).append
    (CompTrace.TRStE me (localEncState st coins))).append
    (CompTrace.NetE (localEncMsg st coins pqSalt m))

local macro "at?_localEncTr_tac" : tactic =>
  `(tactic| (dsimp only [localEncTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))

theorem newIndices_localEncTr (tr : ExecTrace) (me : DY.Participant) (stIdx cl : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (pqSalt : DY.Bytes) :
    newIndices tr (localEncTr tr me stIdx cl st pqSalt) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3,
       tr.length + 4, tr.length + 5, tr.length + 6] := by
  unfold newIndices
  have hlen : (localEncTr tr me stIdx cl st pqSalt).length = tr.length + 7 := by
    dsimp only [localEncTr]; simp only [length_append_entry]
  rw [hlen, Nat.add_sub_cancel_left]; simp [List.range', Nat.add_assoc]

theorem newRandoms_localEncTr (tr : ExecTrace) (me : DY.Participant) (stIdx cl : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (pqSalt : DY.Bytes) :
    newRandoms tr (localEncTr tr me stIdx cl st pqSalt) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
  unfold newRandoms; rw [newIndices_localEncTr]
  have h0 : ((localEncTr tr me stIdx cl st pqSalt).at? tr.length : Option DY.Random.ExecEntryT) = some (CompTrace.RndE 32) := by at?_localEncTr_tac
  have h1 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (CompTrace.RndE cl) := by at?_localEncTr_tac
  have h2 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = none := by at?_localEncTr_tac
  have h3 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by at?_localEncTr_tac
  have h4 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by at?_localEncTr_tac
  have h5 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by at?_localEncTr_tac
  have h6 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by at?_localEncTr_tac
  simp [h0, h1, h2, h3, h4, h5, h6, CompTrace.RndE]

theorem exposures_localEncTr (tr : ExecTrace) (me : DY.Participant) (stIdx cl : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (pqSalt : DY.Bytes) :
    exposures tr (localEncTr tr me stIdx cl st pqSalt) = [] := by
  unfold exposures; rw [newIndices_localEncTr]
  have p0 : ((localEncTr tr me stIdx cl st pqSalt).at? tr.length : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have p1 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 1) : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have p2 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 2) : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have p3 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 3) : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have p4 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 4) : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have p5 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 5) : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have p6 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 6) : Option CompTrace.PQXDHEntry) = none := by at?_localEncTr_tac
  have t0 : ((localEncTr tr me stIdx cl st pqSalt).at? tr.length : Option CompTrace.TREntry) = none := by at?_localEncTr_tac
  have t1 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 1) : Option CompTrace.TREntry) = none := by at?_localEncTr_tac
  have t2 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 2) : Option CompTrace.TREntry) = none := by at?_localEncTr_tac
  have t3 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 3) : Option CompTrace.TREntry) =
      some (CompTrace.TREvE (.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns (randTerm tr.length 32))) := by at?_localEncTr_tac
  have t4 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 4) : Option CompTrace.TREntry) =
      some (CompTrace.TREvE (.MessageKey (st.sessionInfo me) .sender
        (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pqSalt st.ns st.rIdx stIdx)) := by at?_localEncTr_tac
  have t5 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 5) : Option CompTrace.TREntry) = none := by at?_localEncTr_tac
  have t6 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 6) : Option CompTrace.TREntry) = none := by at?_localEncTr_tac
  simp [pqExposureAt, trExposureAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
    p0, p1, p2, p3, p4, p5, p6, t0, t1, t2, t3, t4, t5, t6, CompTrace.TREvE]

theorem lastSent_localEncTr (tr : ExecTrace) (me : DY.Participant) (stIdx cl : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (pqSalt : DY.Bytes) :
    lastSent tr (localEncTr tr me stIdx cl st pqSalt) =
      some (localEncMsg st (randTerm (tr.length + 1) cl) pqSalt (randTerm tr.length 32)) := by
  unfold lastSent
  have hlen : (localEncTr tr me stIdx cl st pqSalt).length = tr.length + 7 := by
    dsimp only [localEncTr]; simp only [length_append_entry]
  have hlt : tr.length < (localEncTr tr me stIdx cl st pqSalt).length := by omega
  rw [ite_eq_left_iff.mpr (fun h => absurd hlt h)]
  have hsub : (localEncTr tr me stIdx cl st pqSalt).length - 1 = tr.length + 6 := by omega
  rw [hsub, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  have hat6 : ((localEncTr tr me stIdx cl st pqSalt).at? (tr.length + 6) : Option DY.Network.ExecEntryT) =
      some (CompTrace.NetE (localEncMsg st (randTerm (tr.length + 1) cl) pqSalt (randTerm tr.length 32))) := by
    at?_localEncTr_tac
  simp [hat6, CompTrace.NetE]

theorem receiveMessage_run (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).1 =
      ((tr.at? idx : Option DY.Network.ExecEntryT).map (·.msg)) ∧
    ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1, CompTrace.run_bind_fst, CompTrace.run_bind_snd,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact ⟨by cases (tr.at? idx : Option DY.Network.ExecEntryT) <;> rfl,
         by cases (tr.at? idx : Option DY.Network.ExecEntryT) <;> rfl⟩

theorem messageEncrypt_ok_eq_localEncTr {tr : ExecTrace}
    {me : DY.Participant} {stIdx cl pqIdx : Nat}
    (hok : (Step.messageEncrypt me stIdx cl pqIdx).ok tr = true)
    (hlok : (Step.messageEncrypt me stIdx cl pqIdx).LocalOk tr) :
    ∃ st : DY.Libsignal.TripleRatchet.TRState,
      (tr.at? stIdx : Option CompTrace.TRStEntry) = some (CompTrace.TRStE me st) ∧
      (cl = 0 ∨ cl = 32 ∨ cl = 64) ∧
      (Step.messageEncrypt me stIdx cl pqIdx).next tr =
        localEncTr tr me stIdx cl st
          (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1 := by
  have hnext_eq : (Step.messageEncrypt me stIdx cl pqIdx).next tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt me stIdx cl pqIdx).run tr).2.val :=
    stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stIdx, cl, pqIdx) tr
  have hok_eq : ((DY.Libsignal.TripleRatchet.messageEncrypt me stIdx cl pqIdx).run tr).1.isSome = true :=
    (stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stIdx, cl, pqIdx) tr).symm.trans hok
  obtain ⟨hcl, hpq_cases⟩ := hlok
  rw [hnext_eq]
  unfold DY.Libsignal.TripleRatchet.messageEncrypt at hok_eq ⊢
  obtain ⟨st, hst, h1, htr1⟩ := run_bind_isSome hok_eq
  rw [CompTrace.getLocalState_tr_snd] at h1 htr1
  have hst_at : (tr.at? stIdx : Option CompTrace.TRStEntry) = some (CompTrace.TRStE me st) :=
    getLocalState_tr_some hst
  obtain ⟨_, hgns, h2, htr2⟩ := run_bind_isSome h1
  have hg_snd := (guard_some (Option.isSome_iff_exists.mpr ⟨_, hgns⟩)).2
  rw [hg_snd] at h2 htr2
  obtain ⟨m, hm, h3, htr3⟩ := run_bind_isSome h2
  have hm_run := genRand_run 32 tr
  have hm_eq : m = randTerm tr.length 32 := by
    rw [hm_run.1] at hm; injection hm with h; exact h.symm
  rw [hm_run.2, hm_eq] at h3 htr3
  set trM := tr.append (CompTrace.RndE 32)
  obtain ⟨coins, hc, h4, htr4⟩ := run_bind_isSome h3
  have hc_run := genRand_run cl trM
  have htrM_len : trM.length = tr.length + 1 := length_append_entry tr _
  have hc_eq : coins = randTerm (tr.length + 1) cl := by
    rw [hc_run.1, htrM_len] at hc; injection hc with h; exact h.symm
  rw [hc_run.2, hc_eq] at h4 htr4
  dsimp only at h4 htr4
  set trC := trM.append (CompTrace.RndE cl)
  obtain ⟨_, hsk, h5, htr5⟩ := run_bind_isSome h4
  rw [(sendMessage_run _ trC).2] at h5 htr5
  obtain ⟨pqSalt, hpq, h6, htr6⟩ := run_bind_isSome h5
  rw [(receiveMessage_run pqIdx _).1] at hpq
  rw [(receiveMessage_run pqIdx _).2] at htr6
  have hpq_eq : pqSalt = (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1 := by
    rcases hpq_cases with rfl | rfl
    · unfold encryptOwnSpqrKeyIdx at hpq
      rw [at?_append_eq_of_eq trC _ (by dsimp only [trC, trM]; simp only [length_append_entry])] at hpq
      injection hpq with h; exact h.symm
    · unfold encryptAbortAfterSpqrIdx at hpq
      rw [Symbolic.Swarm.CREF.at?_ge_length _
        (by dsimp only [trC, trM]; simp only [length_append_entry]; omega)] at hpq
      cases hpq
  rw [hpq_eq] at htr6
  refine ⟨st, hst_at, hcl, ?_⟩
  rw [htr1, htr2, htr3, htr4, htr5, htr6]
  dsimp only [DY.Libsignal.TripleRatchet.logMessageKeyAndStore, DY.Spqr.spqrSend]
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    CompTrace.run_bind_fst, CompTrace.run_bind_snd, DY.Traceful.run_mk, DY.Traceful.run_pure]
  rfl

def NoAliceDone (tr : ExecTrace) : Prop :=
  ∀ j a b ikA ikB spk pq opk ek ct keys,
    (tr.at? j : Option CompTrace.PQXDHEntry) ≠
      some (CompTrace.PQEvE (.AliceDone a b ikA ikB spk pq opk ek ct keys))

theorem noAliceDone_setupTrace (r : ProtocolSetup) : NoAliceDone (setupTrace r) := by
  have hnil : NoAliceDone (DY.Trace.nil : ExecTrace) := fun j _ _ _ _ _ _ _ _ _ _ h => by
    rw [Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
      (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])] at h
    cases h
  have hother {E : Type} [DY.ExecTraceTypes.Has E] {tr : ExecTrace} (h : NoAliceDone tr) (e : E)
      (hn : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option CompTrace.PQXDHEntry) = none) : NoAliceDone (tr.append e) := by
    intro j a b ikA ikB spk pq opk ek ct keys hat
    rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h j a b ikA ikB spk pq opk ek ct keys h0
    · rw [hn] at hp; cases hp
  have hpq {tr : ExecTrace} (h : NoAliceDone tr) (ev : DY.Libsignal.PQXDH.PQXDHEvent)
      (hev : ∀ a b ikA ikB spk pq opk ek ct keys,
        ev ≠ .AliceDone a b ikA ikB spk pq opk ek ct keys) :
      NoAliceDone (tr.append (CompTrace.PQEvE ev)) := by
    intro j a b ikA ikB spk pq opk ek ct keys hat
    rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h j a b ikA ikB spk pq opk ek ct keys h0
    · rw [Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq] at hp
      injection hp with hp'; injection hp' with hp''; exact hev _ _ _ _ _ _ _ _ _ _ hp''
  have hgen (n : Nat) : CompTrace.Preserves NoAliceDone (DY.Random.genRand n) :=
    fun tr h => (genRand_run n tr).2 ▸ hother h (CompTrace.RndE n) rfl
  have hsend (m : DY.Bytes) : CompTrace.Preserves NoAliceDone (DY.Network.sendMessage m) :=
    fun tr h => (sendMessage_run m tr).2 ▸ hother h (CompTrace.NetE m) rfl
  have hst (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
      CompTrace.Preserves NoAliceDone (DY.PersistentLocalState.storeLocalState me st) :=
    fun tr h => (storeLocalState_pq_run me st tr).2 ▸ hother h (CompTrace.PQStE me st) rfl
  have hlog (ev : DY.Libsignal.PQXDH.PQXDHEvent)
      (hev : ∀ a b ikA ikB spk pq opk ek ct keys, ev ≠ .AliceDone a b ikA ikB spk pq opk ek ct keys) :
      CompTrace.Preserves NoAliceDone (DY.ProtocolEvent.logEvent ev) :=
    fun tr h => (logEvent_pq_run ev tr).2 ▸ hpq h ev hev
  have hgk (p : Participant) (idx : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
      CompTrace.Preserves NoAliceDone (DY.Libsignal.PQXDH.getKey p idx k) := by
    unfold DY.Libsignal.PQXDH.getKey
    exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p idx) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
  have hreg (p : Participant) : CompTrace.Preserves NoAliceDone (DY.Libsignal.PQXDH.registerIdentity p) := by
    unfold DY.Libsignal.PQXDH.registerIdentity
    exact CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
      CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hlog _ (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => hst p _
  have hspk (b : Participant) (idS : Nat) : CompTrace.Preserves NoAliceDone (DY.Libsignal.PQXDH.genSignedPrekey b idS) := by
    unfold DY.Libsignal.PQXDH.genSignedPrekey
    exact CompTrace.Preserves.bind (hgk b idS .identity) fun _ =>
      CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hlog _ (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hpqk (b : Participant) (idS : Nat) : CompTrace.Preserves NoAliceDone (DY.Libsignal.PQXDH.genPQPrekey b idS) := by
    unfold DY.Libsignal.PQXDH.genPQPrekey
    exact CompTrace.Preserves.bind (hgk b idS .identity) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hlog _ (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hopk (b : Participant) : CompTrace.Preserves NoAliceDone (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
    unfold DY.Libsignal.PQXDH.genOneTimePrekey
    exact CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hlog _ (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hact : CompTrace.Preserves NoAliceDone (setupAct r.alice r.bob r.withOpk) := by
    unfold setupAct
    refine CompTrace.Preserves.bind (hreg r.alice) fun _ => ?_
    refine CompTrace.Preserves.bind (hreg r.bob) fun hB => ?_
    refine CompTrace.Preserves.bind (hspk r.bob hB) fun _ => ?_
    refine CompTrace.Preserves.bind (hpqk r.bob hB) fun _ => ?_
    cases r.withOpk
    · exact CompTrace.Preserves.pure ()
    · simp only [↓reduceIte]
      exact CompTrace.Preserves.bind (hopk r.bob) fun _ => CompTrace.Preserves.pure ()
  exact hact DY.Trace.nil hnil

theorem aliceDone_on_tr2_eq
    {r : ProtocolSetup} {tr₁ tr₂ : ExecTrace} {pre mid : List Step}
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (hmid_inv : ∀ x ∈ mid, x.cls = .invisible)
    (htr₁ : tr₁ = runSteps pre (setupTrace r))
    (a : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    (htr₂ : tr₂ = runSteps mid (localAliceStartTr tr₁ a r.bob o))
    {d : Nat} {a' b' : DY.Participant} {ikA' ikB' spk' pq' : DY.Bytes}
    {opk' : Option DY.Bytes} {ek' ct' : DY.Bytes} {keys' : DY.Libsignal.PQXDH.HandshakeKeys}
    (hev : tr₂.getEventAt DY.Libsignal.PQXDH.PQXDHEvent d =
      some (.AliceDone a' b' ikA' ikB' spk' pq' opk' ek' ct' keys')) :
    ek' = o.ek ∧ ct' = o.ct := by
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
  rw [htr₂, at?_runSteps_invisible (fun _ => rfl) _ hmid_inv d] at hev
  rcases hd_opt : ((localAliceStartTr tr₁ a r.bob o).at? d : Option CompTrace.PQXDHEntry) with _ | ⟨⟨ev_d⟩⟩
  · simp [hd_opt] at hev
  · simp only [hd_opt, Option.some.injEq] at hev
    subst hev
    by_cases hd_lt : d < tr₁.length
    · exfalso
      have hat₁ : (tr₁.at? d : Option CompTrace.PQXDHEntry) =
          some (CompTrace.PQEvE (.AliceDone a' b' ikA' ikB' spk' pq' opk' ek' ct' keys')) := by
        dsimp only [localAliceStartTr] at hd_opt
        rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hd_lt] at hd_opt
        exact hd_opt
      rw [htr₁, at?_runSteps_invisible (fun _ => rfl) (setupTrace r) hpre_inv d] at hat₁
      exact noAliceDone_setupTrace r d a' b' ikA' ikB' spk' pq' opk' ek' ct' keys' hat₁
    · have hd_lt2 : d < tr₁.length + 9 := by
        by_contra hge
        rw [Symbolic.Swarm.CREF.at?_ge_length _ (by dsimp only [localAliceStartTr]; simp only [length_append_entry]; omega)] at hd_opt
        cases hd_opt
      obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := getEventAt_pq_localAliceStartTr tr₁ a r.bob o
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at p0 p1 p2 p3 p4 p5 p6 p7 p8
      have hcases : d = tr₁.length ∨ d = tr₁.length + 1 ∨ d = tr₁.length + 2 ∨ d = tr₁.length + 3 ∨
          d = tr₁.length + 4 ∨ d = tr₁.length + 5 ∨ d = tr₁.length + 6 ∨ d = tr₁.length + 7 ∨
          d = tr₁.length + 8 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hd_opt] at p0; cases p0
      · rw [hd_opt] at p1; cases p1
      · rw [hd_opt] at p2; cases p2
      · rw [hd_opt] at p3; cases p3
      · rw [hd_opt] at p4; cases p4
      · rw [hd_opt] at p5; simp only [Option.some.injEq] at p5
        injection p5 with _ _ _ _ _ _ _ hek hct _
        exact ⟨hek, hct⟩
      · rw [hd_opt] at p6; cases p6
      · rw [hd_opt] at p7; cases p7
      · rw [hd_opt] at p8; cases p8

theorem pendingPreKey_tr2_memoInjNe6
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr₁ tr₂ : ExecTrace} {pre mid : List Step}
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (hmid_inv : ∀ x ∈ mid, x.cls = .invisible)
    (htr₁ : tr₁ = runSteps pre (setupTrace r))
    (a : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    (htr₂ : tr₂ = runSteps mid (localAliceStartTr tr₁ a r.bob o))
    (hek_ne6 : MemoInjNe6 S g o.ek) (hct_ne6 : MemoInjNe6 S g o.ct)
    {stIdx : Nat} {ek ct : DY.Bytes}
    (hpp : pendingPreKey tr₂ stIdx = some (ek, ct)) :
    MemoInjNe6 S g ek ∧ MemoInjNe6 S g ct := by
  unfold pendingPreKey at hpp
  rcases hls : tr₂.getLocalStateAt DY.Libsignal.TripleRatchet.TRState stIdx with _ | ls
  · simp [hls] at hpp
  · simp only [hls] at hpp
    split_ifs at hpp with hdec
    obtain ⟨ev, hev_mem, hev_some⟩ := List.exists_of_findSome?_eq_some hpp
    unfold sessionHandshakeEvents at hev_mem
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hev_mem
    rcases hce : tr₂.getEventAt DY.Libsignal.Composed.ComposedEvent i with _ | ce
    · simp [hce] at hi
    · cases ce with
      | HandshakeSession s d =>
        simp only [hce] at hi
        split_ifs at hi with hs
        cases ev <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hev_some
        obtain ⟨hek_s, hct_s⟩ := hev_some
        obtain ⟨hek_eq, hct_eq⟩ := aliceDone_on_tr2_eq hpre_inv hmid_inv htr₁ a o htr₂ hi
        exact ⟨(hek_s.symm.trans hek_eq) ▸ hek_ne6, (hct_s.symm.trans hct_eq) ▸ hct_ne6⟩

theorem prefixTerms_memoInjNe6_ev0_ev1
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1]) :
    ∀ t ∈ prefixTerms r (runTrace r ss) vis, MemoInjNe6 S g t := by
  obtain ⟨hcompat, hgwf, ⟨_, hreach₀, hswf, _⟩, hme⟩ := hex
  set tr₀ := setupTrace r
  obtain ⟨pre, s₀, ss₁, v₀, vs₁, hss_eq₀, hvis_eq₀, hpre_inv, hRun₀, hM₁⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hme
  obtain ⟨mid, s₁, post, v₁, vs₂, hss₁_eq, hvs₁_eq, hmid_inv, hRun₁, hM₂⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hM₁
  have ⟨hpost_inv, hvs₂_nil⟩ : (∀ x ∈ post, x.cls = .invisible) ∧ vs₂ = [] := by
    cases hM₂ with
    | nil hp => exact ⟨hp, rfl⟩
  subst hvs₂_nil
  rw [List.append_nil] at hvs₁_eq
  subst hvs₁_eq hss₁_eq hss_eq₀ hvis_eq₀
  set tr₁ := runSteps pre tr₀ with htr₁_def
  obtain ⟨hswf_pre, hs₀_pre, _, hswf_after₀⟩ := stepsWF_split pre (s₀ :: mid ++ s₁ :: post) tr₀ hswf
  obtain ⟨hswf_mid, hs₁_pre, hs₁_lok, _⟩ := stepsWF_split mid (s₁ :: post) (s₀.next tr₁) hswf_after₀
  have hreach₁ : tr₁.Reachable reachability := reachable_of_stepsWF pre hreach₀ hswf_pre
  have hreach_s₀ : (s₀.next tr₁).Reachable reachability :=
    DY.Trace.Reachable.Step s₀.toInput hs₀_pre hreach₁
  obtain ⟨_, _, hfits₀, hpeer₀, hok₀, _, hv₀_eq, inp₀, drs₀, outs₀, hv₀_split, hinp₀, _⟩ := hRun₀
  have ⟨addr₀, pth₀, hcmd₀⟩ : ∃ addr pth, ev0.cmd = .init addr pth := ⟨_, _, rfl⟩
  rw [hcmd₀] at hfits₀
  cases hs₀_eq : s₀ with
  | aliceStart a b idS regB hb =>
    rw [hs₀_eq] at hpeer₀ hok₀ hv₀_eq hreach_s₀ hswf_mid hs₁_pre hs₁_lok hRun₁
    have hb_eq : b = r.bob := hpeer₀
    subst hb_eq
    obtain ⟨ikA, ikB, spk, spkSig, pqpk, pqpkSig, opk,
      hspk, hspkSig, hpq, hpqSig, hopk, hnext₀⟩ := aliceStart_ok_eq_localAliceStartTr hok₀
    set o₀ := CompTrace.aliceOut tr₁ ikA ikB spk pqpk opk
    have hreach_la : (localAliceStartTr tr₁ a r.bob o₀).Reachable reachability := by
      rwa [← hnext₀]
    dsimp only [stepView] at hv₀_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok₀ h), hnext₀,
      exposures_localAliceStartTr, List.append_nil] at hv₀_eq
    have hopk_none : opk = none := by
      rcases hopk with ⟨_, hopk_n⟩ | ⟨idx, u, hhb_s, _, hu⟩
      · exact hopk_n
      · exfalso
        have hv_al := hv₀_eq.trans (aliceVis_localAliceStartTr tr₁ a r.bob o₀ hb)
        rw [hv₀_split] at hv_al
        injection hv_al with hinp_eq _
        have hkind₀ : inputKind ev0 = .recv := rfl
        rw [hkind₀, hinp_eq] at hinp₀
        have hrec5 : received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) =
            [spk, spkSig, pqpk, pqpkSig, u] := by
          rw [hhb_s]
          change received tr₁ [hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig, idx] = [spk, spkSig, pqpk, pqpkSig, u]
          simp only [received, List.filterMap_cons, List.filterMap_nil,
            getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig,
            getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig,
            getMessageSentAt_of_netMsgAt hu]
        have hbm := hinp₀.2
        dsimp only at hbm
        rw [hrec5] at hbm
        exact ev0_input_getElem4_ne_one hbm.2.1
    subst hopk_none
    set o := CompTrace.aliceOut tr₁ ikA ikB spk pqpk none
    have hv₀_al : v₀ =
        { kind := .recv, terms := received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList),
          layout := .bundle, anchor := none } ::
        rngEntry (randTerm tr₁.length 32) ::
        (kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
          [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }]) :=
      hv₀_eq.trans (aliceVis_localAliceStartTr tr₁ a r.bob o hb)
    have hmem_ek : rngEntry (randTerm tr₁.length 32) ∈ v₀ ++ vs₁ := by
      apply List.mem_append_left; rw [hv₀_al]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hek_gt7 : MemoInjGt7 S g (randTerm tr₁.length 32) := by
      have hlen := hgwf.1 _ hmem_ek rfl tr₁.length 32 (by decide) (List.mem_singleton.mpr rfl)
      exact memoInjGt7_randTerm (.inr (by omega))
    have hmem_ent : (⟨.rng, [randTerm (tr₁.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ v₀ ++ vs₁ := by
      apply List.mem_append_left; rw [hv₀_al]
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
      unfold kyberCoinEntries
      exact List.mem_map.mpr ⟨0, by decide, rfl⟩
    have hent_gt7 : MemoInjGt7 S g (randTerm (tr₁.length + 1) 32) := by
      have hlen := hgwf.1 _ hmem_ent rfl (tr₁.length + 1) 32 (by decide) (List.mem_singleton.mpr rfl)
      exact memoInjGt7_randTerm (.inr (by omega))
    have hmem_dhs : ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry) ∈ v₀ ++ vs₁ := by
      apply List.mem_append_left; rw [hv₀_al]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    have hdhs_gt7 : MemoInjGt7 S g (randTerm (tr₁.length + 2) 32) := by
      have hlen := hgwf.1 _ hmem_dhs rfl (tr₁.length + 2) 32 (by decide) (List.mem_singleton.mpr rfl)
      exact memoInjGt7_randTerm (.inr (by omega))
    have hncb₁ : NoCompOrBreak tr₁ := by
      intro j ev hat
      rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv j] at hat
      exact noCompOrBreak_setupTrace r j ev hat
    have hncb₂ : NoCompOrBreak (localAliceStartTr tr₁ a r.bob o) := by
      dsimp only [localAliceStartTr]
      refine noCompOrBreak_append_other ?_ _ rfl
      refine noCompOrBreak_append_other ?_ _ rfl
      refine noCompOrBreak_append_other ?_ _ rfl
      refine noCompOrBreak_append_pqEv ?_ _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩
      refine noCompOrBreak_append_other ?_ _ rfl
      refine noCompOrBreak_append_other ?_ _ rfl
      refine noCompOrBreak_append_other ?_ _ rfl
      refine noCompOrBreak_append_other ?_ _ rfl
      exact noCompOrBreak_append_other hncb₁ _ rfl
    have hik_gt7 : ∀ p s_ik,
        Symbolic.Swarm.COMPOSED.CompInv.IKAt (localAliceStartTr tr₁ a r.bob o) p s_ik →
        MemoInjGt7 S g s_ik := by
      rintro p _ ⟨idx, rfl, hr, hev⟩
      have ⟨_, hk₁⟩ := pqEv_before_localAliceStartTr hpre_inv htr₁_def a r.bob o hev
        (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
      exact memoInjGt7_of_setupRandAt hwf hcompat (.inl rfl)
        (randAt_before_localAliceStartTr hpre_inv htr₁_def a r.bob o (by omega) hr)
    have hspk_gt7 : ∀ p s_spk,
        Symbolic.Swarm.COMPOSED.CompInv.SPKAt (localAliceStartTr tr₁ a r.bob o) p s_spk →
        MemoInjGt7 S g s_spk := by
      rintro p _ ⟨idx, rfl, hr, _, hev⟩
      have ⟨_, hk₁⟩ := pqEv_before_localAliceStartTr hpre_inv htr₁_def a r.bob o hev
        (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
      exact memoInjGt7_of_setupRandAt hwf hcompat (.inl rfl)
        (randAt_before_localAliceStartTr hpre_inv htr₁_def a r.bob o (by omega) hr)
    have hpq_gt7 : ∀ p s_pq,
        Symbolic.Swarm.COMPOSED.CompInv.PQAt (localAliceStartTr tr₁ a r.bob o) p s_pq →
        MemoInjGt7 S g s_pq := by
      rintro p _ ⟨idx, rfl, hr, _, hev⟩
      have ⟨_, hk₁⟩ := pqEv_before_localAliceStartTr hpre_inv htr₁_def a r.bob o hev
        (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
      exact memoInjGt7_of_setupRandAt hwf hcompat (.inr rfl)
        (randAt_before_localAliceStartTr hpre_inv htr₁_def a r.bob o (by omega) hr)
    have had_ev : (localAliceStartTr tr₁ a r.bob o).EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a r.bob o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) (tr₁.length + 5) := by
      have hp5 := (getEventAt_pq_localAliceStartTr tr₁ a r.bob o).2.2.2.2.2.1
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hp5
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      cases hp : ((localAliceStartTr tr₁ a r.bob o).at? (tr₁.length + 5) : Option CompTrace.PQXDHEntry) with
      | none => rw [hp] at hp5; cases hp5
      | some e =>
        rcases e with ⟨ev'⟩
        rw [hp] at hp5; injection hp5 with hev'; subst hev'; rfl
    obtain ⟨_, sA, _, _, hsA_at, hikA_eq, _, _, hbun_ok⟩ :=
      (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach_la).aliceDone
        a r.bob o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys (tr₁.length + 5) had_ev
    have hsA_gt7 : MemoInjGt7 S g sA := hik_gt7 a sA hsA_at
    have ho_ikA_gt7 : MemoInjGt7 S g o.ikA := hikA_eq ▸ memoInjGt7_dhPk hsA_gt7
    have hikA_sk_gt7 : MemoInjGt7 S g ikA := memoInjGt7_of_dhPk ho_ikA_gt7
    have ⟨ho_ikB_gt7, ho_spk_gt7, ho_pqpk_gt7⟩ :
        MemoInjGt7 S g o.ikB ∧ MemoInjGt7 S g o.spk ∧ MemoInjGt7 S g o.pqpk := by
      rcases hbun_ok with ⟨sB, sS, sQ, hsB, hikB_eq, hsS, hspk_eq, hsQ, hpq_eq⟩ |
          ⟨j, hj, _⟩ | ⟨j, hj, _⟩
      · exact ⟨hikB_eq ▸ memoInjGt7_dhPk (hik_gt7 r.bob sB hsB),
          hspk_eq ▸ memoInjGt7_dhPk (hspk_gt7 r.bob sS hsS),
          hpq_eq ▸ memoInjGt7_kemPk (hpq_gt7 r.bob sQ hsQ)⟩
      · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj
        exact False.elim ((hncb₂ j _ hj).1 r.bob o.ikB rfl)
      · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj
        exact False.elim ((hncb₂ j _ hj).2 rfl)
    have hkeys_gt7 : MemoInjGt7 S g o.keys.rk ∧ MemoInjGt7 S g o.keys.ck ∧ MemoInjGt7 S g o.keys.pqr :=
      memoInjGt7_pqxdhKdf_none
        (memoInjGt7_agree ho_spk_gt7 hikA_sk_gt7)
        (memoInjGt7_agree ho_ikB_gt7 hek_gt7)
        (memoInjGt7_agree ho_spk_gt7 hek_gt7)
        (memoInjGt7_kemEncap_snd ho_pqpk_gt7 hent_gt7)
    have ho_ct_ne6 : MemoInjNe6 S g o.ct :=
      memoInjNe6_of_gt7 (memoInjGt7_kemEncap_fst ho_pqpk_gt7 hent_gt7)
    have ho_ek_ne6 : MemoInjNe6 S g o.ek := memoInjNe6_of_gt7 (memoInjGt7_dhPk hek_gt7)
    -- Now analyze `s₁` (`ev1`) run from `tr₂ := runSteps mid (localAliceStartTr tr₁ a r.bob o)`
    rw [hnext₀] at hs₁_pre hs₁_lok hRun₁
    set tr₂ := runSteps mid (localAliceStartTr tr₁ a r.bob o) with htr₂_def
    obtain ⟨_, _, hfits₁, _, hok₁, _, hv₁_eq, inp₁, drs₁, outs₁, hv₁_split, hinp₁, _⟩ := hRun₁
    have ⟨addr₁, hcmd₁⟩ : ∃ addr, ev1.cmd = .send addr := ⟨_, rfl⟩
    rw [hcmd₁] at hfits₁
    cases hs₁_eq : s₁ with
    | messageEncryptAbort me₁ stIdx₁ =>
      rw [hs₁_eq] at hok₁
      have habort_eq : (Step.messageEncryptAbort me₁ stIdx₁).ok tr₂ =
          ((DY.Libsignal.TripleRatchet.messageEncryptAbort me₁ stIdx₁).run tr₂).1.isSome :=
        stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me₁, stIdx₁) tr₂
      rw [habort_eq] at hok₁
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort at hok₁
      obtain ⟨_, _, h1, _⟩ := run_bind_isSome hok₁
      obtain ⟨_, _, h2, _⟩ := run_bind_isSome h1
      rw [DY.Traceful.run_failure] at h2; cases h2
    | messageEncrypt me₁ stIdx₁ cl₀ pqIdx₁ =>
      rw [hs₁_eq] at hok₁ hs₁_lok hv₁_eq
      obtain ⟨st₁, hst₁_at, hcl₀, hnext₁⟩ := messageEncrypt_ok_eq_localEncTr hok₁ hs₁_lok
      have hnoTR₁ : NoTRState tr₁ := fun k => by
        rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv k]
        exact noTRState_setupTrace r k
      have hat_tr₂ : ∀ j, (tr₂.at? j : Option CompTrace.TRStEntry) =
          if j = tr₁.length + 8 then some (CompTrace.TRStE a (localAliceStartState tr₁ r.bob o)) else none := by
        intro j
        rw [htr₂_def, at?_runSteps_invisible (fun _ => rfl) _ hmid_inv j,
          at?_trSt_localAliceStartTr_of_noTRState hnoTR₁ a r.bob o j]
      rw [hat_tr₂ stIdx₁] at hst₁_at
      have hstIdx₁_eq : stIdx₁ = tr₁.length + 8 := by
        by_contra hne; simp [hne] at hst₁_at
      rw [hstIdx₁_eq] at hst₁_at
      simp only [↓reduceIte, Option.some.injEq] at hst₁_at
      cases hst₁_at
      set stA₀ := localAliceStartState tr₁ r.bob o
      set m₁ := randTerm tr₂.length 32
      set coins₁ := randTerm (tr₂.length + 1) cl₀
      set pqSalt₁ := (DY.Spqr.spqrSend stA₀.spqr coins₁).2.1
      dsimp only [stepView] at hv₁_eq
      rw [ite_eq_left_iff.mpr (fun h => absurd hok₁ h), hnext₁,
        exposures_localEncTr, List.append_nil, newRandoms_localEncTr] at hv₁_eq
      have hm₁_ne6 : MemoInjNe6 S g m₁ := by
        have hv₁_head := hv₁_split.symm.trans hv₁_eq
        dsimp only [encDraws, List.cons_append] at hv₁_head
        injection hv₁_head with hinp₁_eq _
        have hkind₁ : inputKind ev1 = .pt := rfl
        rw [hkind₁, hinp₁_eq] at hinp₁
        have hbm₁ := hinp₁.2
        dsimp only [List.map_cons, List.map_nil] at hbm₁
        have hrand_m₁ := gamma'_randTerm compI0 S g tr₂.length 32 (by decide)
        change [(gamma' compI0 S g m₁).bytes] = [ev1.input] at hbm₁
        rw [hrand_m₁] at hbm₁
        injection hbm₁ with hσ_m₁
        dsimp only at hσ_m₁
        have hlen_m₁ : (g.σ tr₂.length 32).length = 5 := by rw [hσ_m₁, ev1_input_len]
        exact memoInjNe6_randTerm (.inr (by omega))
      have hcoins₁_ne6 : MemoInjNe6 S g coins₁ := by
        change MemoInjNe6 S g (randTerm (tr₂.length + 1) cl₀)
        rcases hcl₀ with rfl | rfl | rfl
        · exact memoInjNe6_randTerm (.inl rfl)
        · have hmem_c : rngEntry (randTerm (tr₂.length + 1) 32) ∈ v₀ ++ vs₁ := by
            apply List.mem_append_right; rw [hv₁_eq]
            dsimp only [encDraws, List.filter_cons, List.filter_nil]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (by simp))
          have hlen := hgwf.1 (rngEntry (randTerm (tr₂.length + 1) 32)) hmem_c rfl (tr₂.length + 1) 32 (by decide) (by simp [rngEntry])
          exact memoInjNe6_randTerm (.inr (by omega))
        · have hmem_c : rngEntry (randTerm (tr₂.length + 1) 64) ∈ v₀ ++ vs₁ := by
            apply List.mem_append_right; rw [hv₁_eq]
            dsimp only [encDraws, List.filter_cons, List.filter_nil]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (by simp))
          have hlen := hgwf.1 (rngEntry (randTerm (tr₂.length + 1) 64)) hmem_c rfl (tr₂.length + 1) 64 (by decide) (by simp [rngEntry])
          exact memoInjNe6_randTerm (.inr (by omega))
      have hcc := memoInjGt7_createChain hkeys_gt7.1 ho_spk_gt7 hdhs_gt7
      have hmyIk_ne6 : MemoInjNe6 S g stA₀.myIk := memoInjNe6_of_gt7 (memoInjGt7_serializedIk ho_ikA_gt7)
      have hpeerIk_ne6 : MemoInjNe6 S g stA₀.peerIk := memoInjNe6_of_gt7 (memoInjGt7_serializedIk ho_ikB_gt7)
      have hrk_ne6 : MemoInjNe6 S g stA₀.rk := memoInjNe6_of_gt7 hcc.1
      have hdhs_ne6 : MemoInjNe6 S g stA₀.dhs := memoInjNe6_of_gt7 hdhs_gt7
      have hdhs_pk_ne6 : MemoInjNe6 S g (DY.DiffieHellman.dhPk stA₀.dhs) :=
        memoInjNe6_of_gt7 (memoInjGt7_dhPk hdhs_gt7)
      have hcks_ne6 : MemoInjNe6 S g stA₀.cks := memoInjNe6_of_gt7 hcc.2
      have hsid_ne6 : MemoInjNe6 S g stA₀.sid :=
        memoInjNe6_of_gt7 (memoInjGt7_concat (memoInjGt7_dhPk hdhs_gt7) hkeys_gt7.1)
      have hspqr₀_ne6 : MemoInjNe6 S g stA₀.spqr :=
        memoInjNe6_of_gt7 (memoInjGt7_spqrInit hkeys_gt7.2.2 (memoInjGt7_lit S g _))
      have hspqr₁ := memoInjNe6_spqrSend hspqr₀_ne6 hcoins₁_ne6
      have hck1_ne6 : MemoInjNe6 S g (DY.Libsignal.TripleRatchet.kdfCk stA₀.cks).1 :=
        memoInjNe6_hmac hcks_ne6 (memoInjNe6_lit S g _)
      have hseed1_ne6 : MemoInjNe6 S g (DY.Libsignal.TripleRatchet.kdfCk stA₀.cks).2 :=
        memoInjNe6_hmac hcks_ne6 (memoInjNe6_lit S g _)
      have hstA₁_ser_ne6 : MemoInjNe6 S g (DY.Comparse.serialize
          (⟨a, localEncState stA₀ coins₁⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
        refine memoInjNe6_serialize_local_tr hmyIk_ne6 hpeerIk_ne6 hrk_ne6 hdhs_ne6
          hck1_ne6 hsid_ne6 hspqr₁.1 (fun d hd => ?_)
        simp only [localEncState] at hd
        rcases List.mem_singleton.mp hd with rfl
        exact ⟨memoInjNe6_of_gt7 ho_spk_gt7, memoInjNe6_of_gt7 hkeys_gt7.2.1⟩
      have hmsg₁_ne6 : MemoInjNe6 S g (localEncMsg stA₀ coins₁ pqSalt₁ m₁) := by
        unfold localEncMsg
        dsimp only
        have hprk := memoInjNe6_hmac hspqr₁.2.1 hseed1_ne6
        have hinfo : MemoInjNe6 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := memoInjNe6_lit S g _
        have hwire := memoInjNe6_trHonestWireMsg (ns := stA₀.ns) (pn := stA₀.pn) hdhs_pk_ne6
          (memoInjNe6_symEnc (memoInjNe6_hkdfBlock1 hprk hinfo) (memoInjNe6_hkdfBlock3 hprk hinfo) hm₁_ne6)
          hspqr₁.2.2
        exact memoInjNe6_concat hwire
          (memoInjNe6_computeMac (memoInjNe6_hkdfBlock2 hprk hinfo) hmyIk_ne6 hpeerIk_ne6 hwire)
      have htr₄_eq : runTrace r (pre ++ Step.aliceStart a r.bob idS regB hb ::
          (mid ++ Step.messageEncrypt a stIdx₁ cl₀ pqIdx₁ :: post)) =
          runSteps post (localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁) := by
        unfold runTrace
        rw [runSteps_append_local]
        change runSteps (Step.aliceStart a r.bob idS regB hb ::
          (mid ++ Step.messageEncrypt a stIdx₁ cl₀ pqIdx₁ :: post)) tr₁ = _
        dsimp only [runSteps]
        rw [hnext₀, runSteps_append_local]
        change runSteps (Step.messageEncrypt a stIdx₁ cl₀ pqIdx₁ :: post) tr₂ = _
        dsimp only [runSteps]
        rw [hnext₁]
      rw [htr₄_eq]
      set tr₄ := runSteps post (localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁) with htr₄_def
      have hv₀_not_send_pt : ∀ w ∈ v₀, w.kind ≠ .send ∧ w.kind ≠ .pt := by
        intro w hw
        rw [hv₀_al] at hw
        rcases List.mem_cons.mp hw with rfl | hw1
        · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · rcases List.mem_cons.mp hw1 with rfl | hw2
          · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
          · rcases List.mem_append.mp hw2 with hkc | hdhs_w
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc
              exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
            · rw [List.mem_singleton] at hdhs_w; subst hdhs_w
              exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      intro t ht
      unfold prefixTerms principalTerms at ht
      rcases List.mem_append.mp ht with hprin | hpt
      · rcases List.mem_append.mp hprin with h12 | hsec
        · rcases List.mem_append.mp h12 with hsend | hst
          · obtain ⟨w, hw_f, ht_w⟩ := List.mem_flatMap.mp hsend
            obtain ⟨hw_v, hw_k⟩ := List.mem_filter.mp hw_f
            simp only [beq_iff_eq] at hw_k
            rcases List.mem_append.mp hw_v with hw₀ | hw₁
            · exact False.elim ((hv₀_not_send_pt w hw₀).1 hw_k)
            · rw [hv₁_eq] at hw₁
              rcases List.mem_append.mp hw₁ with hw_dr | hw_se
              · dsimp only [encDraws] at hw_dr
                rcases List.mem_cons.mp hw_dr with rfl | hw_rng
                · cases hw_k
                · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw_rng
                  cases hw_k
              · unfold encSendEntry at hw_se
                rw [lastSent_localEncTr] at hw_se
                rw [runWrapped_ev1_fast] at hw_se
                dsimp only at hw_se
                rcases hpp : pendingPreKey tr₂ stIdx₁ with _ | ⟨ek_p, ct_p⟩ <;>
                  simp only [hpp] at hw_se
                · cases hw_se
                · rcases List.mem_singleton.mp hw_se with rfl
                  have ⟨hek_p, hct_p⟩ := pendingPreKey_tr2_memoInjNe6 hpre_inv hmid_inv
                    htr₁_def a o htr₂_def ho_ek_ne6 ho_ct_ne6 hpp
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht_w
                  rcases ht_w with rfl | rfl | rfl
                  · exact hek_p
                  · exact hct_p
                  · exact hmsg₁_ne6
          · obtain ⟨ls, hls_mem, rfl⟩ := List.mem_map.mp hst
            unfold storedStates at hls_mem
            obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hls_mem
            unfold ExecTrace.getLocalStateAt at hj
            change ((tr₄.at? j : Option CompTrace.TRStEntry).map (·.st)) = some ls at hj
            rw [htr₄_def, at?_runSteps_invisible (fun _ => rfl) _ hpost_inv j] at hj
            by_cases hj_lt : j < tr₂.length
            · have hat_lt : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? j : Option CompTrace.TRStEntry) =
                  (tr₂.at? j : Option CompTrace.TRStEntry) := by
                dsimp only [localEncTr]
                rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
                  Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
                  Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
                  Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
                  Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
                  Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
                  Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hj_lt]
              rw [hat_lt, hat_tr₂ j] at hj
              by_cases hj8 : j = tr₁.length + 8
              · simp only [hj8, ↓reduceIte, Option.map_some, Option.some.injEq] at hj
                subst hj
                exact memoInjNe6_of_gt7 (memoInjGt7_iniAliceStartState tr₁ a r.bob o
                  ho_ikA_gt7 ho_ikB_gt7 ho_spk_gt7 hkeys_gt7.1 hkeys_gt7.2.1 hkeys_gt7.2.2 hdhs_gt7)
              · simp only [hj8, ↓reduceIte, Option.map_none] at hj; cases hj
            · by_cases hj5 : j = tr₂.length + 5
              · subst hj5
                have hat5 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? (tr₂.length + 5) : Option CompTrace.TRStEntry) =
                    some (CompTrace.TRStE a (localEncState stA₀ coins₁)) := by at?_localEncTr_tac
                rw [hat5] at hj
                simp only [Option.map_some, Option.some.injEq] at hj
                subst hj
                exact hstA₁_ser_ne6
              · have hlen_enc : (localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).length = tr₂.length + 7 := by
                  dsimp only [localEncTr]; simp only [length_append_entry]
                by_cases hj_ge7 : tr₂.length + 7 ≤ j
                · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by omega)] at hj; simp at hj
                · have hcases : j = tr₂.length ∨ j = tr₂.length + 1 ∨ j = tr₂.length + 2 ∨
                      j = tr₂.length + 3 ∨ j = tr₂.length + 4 ∨ j = tr₂.length + 6 := by omega
                  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
                  · have h0 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? tr₂.length : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                    rw [h0] at hj; simp at hj
                  · have h1 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? (tr₂.length + 1) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                    rw [h1] at hj; simp at hj
                  · have h2 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? (tr₂.length + 2) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                    rw [h2] at hj; simp at hj
                  · have h3 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? (tr₂.length + 3) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                    rw [h3] at hj; simp at hj
                  · have h4 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? (tr₂.length + 4) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                    rw [h4] at hj; simp at hj
                  · have h6 : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? (tr₂.length + 6) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                    rw [h6] at hj; simp at hj
        · unfold storedSecrets at hsec
          obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hsec
          unfold ExecTrace.getLocalStateAt at hi
          have hat_pq_enc : ((localEncTr tr₂ a stIdx₁ cl₀ stA₀ pqSalt₁).at? i : Option CompTrace.PQXDHStEntry) =
              (tr₂.at? i : Option CompTrace.PQXDHStEntry) := by
            dsimp only [localEncTr]
            rw [at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
              at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
              at?_append_other_eq _ _ rfl]
          have hat_pq : (tr₄.at? i : Option CompTrace.PQXDHStEntry) = (tr₀.at? i : Option CompTrace.PQXDHStEntry) := by
            rw [htr₄_def, at?_runSteps_invisible (fun _ => rfl) _ hpost_inv i, hat_pq_enc,
              htr₂_def, at?_runSteps_invisible (fun _ => rfl) _ hmid_inv i,
              (at?_pqSt_localAliceStartTr tr₁ a r.bob o i).2,
              htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv i]
          change (((tr₄.at? i : Option CompTrace.PQXDHStEntry).map (·.st)).map DY.Comparse.serialize) = some t at hi
          rw [hat_pq] at hi
          rcases hat₀ : (tr₀.at? i : Option CompTrace.PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
          · simp [hat₀] at hi
          · simp only [hat₀, Option.map_some, Option.some.injEq] at hi
            subst hi
            have hkind := (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr₀ hreach₀).stOK
              p st i hat₀
            apply memoInjNe6_of_gt7
            apply memoInjGt7_serialize_local_pqxdh
            rcases st with ⟨kind, sk⟩
            cases kind
            · obtain ⟨idx, rfl, hr, _⟩ := hkind
              exact memoInjGt7_of_setupRandAt hwf hcompat (.inl rfl) hr
            · obtain ⟨idx, rfl, hr, _⟩ := hkind
              exact memoInjGt7_of_setupRandAt hwf hcompat (.inl rfl) hr
            · obtain ⟨idx, rfl, hr, _⟩ := hkind
              exact memoInjGt7_of_setupRandAt hwf hcompat (.inr rfl) hr
            · obtain ⟨idx, rfl, hr, _⟩ := hkind
              exact memoInjGt7_of_setupRandAt hwf hcompat (.inl rfl) hr
      · unfold plaintextTerms at hpt
        obtain ⟨w, hw_f, ht_w⟩ := List.mem_flatMap.mp hpt
        obtain ⟨hw_v, hw_k⟩ := List.mem_filter.mp hw_f
        simp only [beq_iff_eq] at hw_k
        rcases List.mem_append.mp hw_v with hw₀ | hw₁
        · exact False.elim ((hv₀_not_send_pt w hw₀).2 hw_k)
        · rw [hv₁_eq] at hw₁
          rcases List.mem_append.mp hw₁ with hw_dr | hw_se
          · dsimp only [encDraws] at hw_dr
            rcases List.mem_cons.mp hw_dr with rfl | hw_rng
            · rcases List.mem_singleton.mp ht_w with rfl
              exact hm₁_ne6
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw_rng
              cases hw_k
          · unfold encSendEntry at hw_se
            rw [lastSent_localEncTr] at hw_se
            rw [runWrapped_ev1_fast] at hw_se
            dsimp only at hw_se
            rcases hpp : pendingPreKey tr₂ stIdx₁ with _ | ⟨_, _⟩ <;>
              simp only [hpp] at hw_se
            · cases hw_se
            · rcases List.mem_singleton.mp hw_se with rfl; cases hw_k
    | _ => rw [hs₁_eq] at hfits₁; cases hfits₁
  | _ => rw [hs₀_eq] at hfits₀; cases hfits₀

/-- Split 2 (`ev2`, `"second"`, 6B `.send`): all `assumedInjective` memo entries in `prefixTerms`
on `[.run ev0, .run ev1]` have length `≠ 6`, contradicting `ev2.input.length = 6`. -/
theorem not_nextEventCollides_ev2 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1]) :
    ¬ NextEventCollides compI0 r S g ss vis [.run ev0, .run ev1] ev2 := by
  intro hcol
  have hcmd : ev2.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  set tr := runTrace r ss
  have hrand : gamma' compI0 S g (randTerm tr.length 32) =
      { bytes := g.σ tr.length 32, shape := randTerm tr.length 32,
        memo := [(randTerm tr.length 32, randTerm tr.length 32, g.σ tr.length 32)] } :=
    gamma'_randTerm compI0 S g tr.length 32 (by decide)
  have hσ_ev2 : g.σ tr.length 32 = ev2.input := by
    have hbme := hcol.1.2
    dsimp only [ptEntryAt, List.map_cons, List.map_nil] at hbme
    change [ (gamma' compI0 S g (randTerm tr.length 32)).bytes ] = [ev2.input] at hbme
    rw [hrand] at hbme
    injection hbme with hhead _
  have hmc := hcol.2 g ⟨rfl, vis, hex⟩
  dsimp only [ptEntryAt] at hmc
  obtain ⟨x₁, hx₁, x₂, hx₂, hsh_ne, _, hpts₁, _, hbytes_eq⟩ := hmc
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hrand, List.mem_singleton] at hx₁
  subst hx₁
  have hx₁_pts : randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨_, hinj₂, _⟩ := hpts₁ hx₁_pts
  rcases List.mem_append.mp hx₂ with hx₂_pfx | hx₂_new
  · obtain ⟨t, ht_mem, hx₂_mem⟩ := List.mem_flatMap.mp hx₂_pfx
    have hne6 : x₂.2.2.length ≠ 6 :=
      prefixTerms_memoInjNe6_ev0_ev1 hf.1.1.1 hex t ht_mem x₂ hx₂_mem hinj₂
    have hlen6 : x₂.2.2.length = 6 := by
      rw [← hbytes_eq, hσ_ev2, ev2_input_len]
    exact hne6 hlen6
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hrand, List.mem_singleton] at hx₂_new
    subst hx₂_new
    exact hsh_ne rfl


end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
