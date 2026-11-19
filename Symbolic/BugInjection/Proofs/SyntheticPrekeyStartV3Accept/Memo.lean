/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Defs

/-!
# Handshake Memo Length Bounds for `synthetic-prekey-start-v3-accept`

Establishes `MemoInjGt9` subterm length bounds (`> 9` bytes on `assumedInjective` subterms)
across `aliceStart` for `Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Top`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

namespace Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open scoped DY.Libsignal.Composed
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compI0 compLookupPub compLookupDh compKyberEncaps)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
open Symbolic.Swarm.COMPOSED.CompTrace

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-! ### 4a. Self-contained `MemoInjGt` (> 9 bytes) invariant on `[.run ev0]` -/

theorem bytes_rec_gAll (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u : DY.Bytes) : u.rec (concretizeAll i S g) = gamma' i S g u := rfl

theorem gamma'_randTerm (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts sz : Nat) (hsz : sz ≠ 0) :
    gamma' i S g (randTerm ts sz) =
      { bytes := g.σ ts sz, shape := randTerm ts sz, memo := [(randTerm ts sz, randTerm ts sz, g.σ ts sz)] } := by
  unfold gamma' randTerm
  show ((({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll i S g)) = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  simp only [concretizeRandom, node, List.flatMap_nil, hsz, ↓reduceIte]

def MemoInjGt9 (S : OpaqueSymbolSemantics) (g : Ghost) (t : DY.Bytes) : Prop :=
  ∀ x ∈ (gamma' compI0 S g t).memo, assumedInjective x.1 = true → 9 < x.2.2.length

theorem assumedInjective_lit (x : DY.Literal.Literal.SubF DY.Bytes) :
    assumedInjective x.pack = false := by
  unfold assumedInjective DY.Literal.Literal.SubF.pack
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF x]
  rfl

theorem assumedInjective_concat (x : DY.Concat.Concat.SubF DY.Bytes) :
    assumedInjective x.pack = false := by
  unfold assumedInjective DY.Concat.Concat.SubF.pack
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF x]
  rfl

theorem memoInjGt9_lit (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    MemoInjGt9 S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S g)] at hx
  rcases List.mem_singleton.mp hx with rfl
  rw [assumedInjective_lit] at hinj
  cases hinj

theorem memoInjGt9_literalToBytes (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    MemoInjGt9 S g (DY.Literal.literalToBytes b) :=
  memoInjGt9_lit S g b

theorem memoInjGt9_randTerm {S : OpaqueSymbolSemantics} {g : Ghost} {idx sz : Nat}
    (h : sz = 0 ∨ 9 < (g.σ idx sz).length) :
    MemoInjGt9 S g (randTerm idx sz) := by
  intro x hx _
  unfold gamma' randTerm at hx
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI0 S g)] at hx
  dsimp only [concretizeRandom] at hx
  split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl
    exact h.resolve_left hsz

theorem memoInjGt9_concat {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (ha : MemoInjGt9 S g a) (hb : MemoInjGt9 S g b) :
    MemoInjGt9 S g (DY.Concat.concat a b) := by
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

theorem memoInjGt9_of_concat {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (h : MemoInjGt9 S g (DY.Concat.concat a b)) :
    MemoInjGt9 S g a ∧ MemoInjGt9 S g b := by
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

instance instBytesCompatiblePredMemoInjGt9 (S : OpaqueSymbolSemantics) (g : Ghost) :
    Comparse.BytesCompatiblePred (MemoInjGt9 S g) where
  pred_empty := memoInjGt9_lit S g .empty
  pred_concat _ _ hl hr := memoInjGt9_concat hl hr
  pred_split buf n hbuf := by
    cases hsp : Comparse.BytesLike.split buf n with
    | none => trivial
    | some p =>
      rw [← DY.Concat.concat_split buf n p.1 p.2 hsp] at hbuf
      exact memoInjGt9_of_concat hbuf
  pred_fromByteArray b := memoInjGt9_lit S g b

theorem memoInjGt9_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {sk : DY.Bytes}
    (hsk : MemoInjGt9 S g sk) : MemoInjGt9 S g (DY.DiffieHellman.dhPk sk) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk
  · change 9 < (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupPub _).length
    rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compLookupPub_length]; decide
  · exact hsk x hxsk hinj

theorem memoInjGt9_of_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {sk : DY.Bytes}
    (h : MemoInjGt9 S g (DY.DiffieHellman.dhPk sk)) : MemoInjGt9 S g sk := by
  intro x hx hinj
  apply h x _ hinj
  unfold gamma'
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g)]
  exact List.mem_cons_of_mem _ (by simpa [concretizeDhPk, node, bytes_rec_gAll] using hx)

theorem memoInjGt9_dh_pack {S : OpaqueSymbolSemantics} {g : Ghost} {pk sk : DY.Bytes}
    (hpk : MemoInjGt9 S g pk) (hsk : MemoInjGt9 S g sk) :
    MemoInjGt9 S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [DY.Bytes.rec_eq (concretizeDh compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeDh, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxpk | hxsk
  · change 9 < (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupDh _ _).length
    rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compLookupDh_length]; decide
  · exact hpk x hxpk hinj
  · exact hsk x hxsk hinj

theorem memoInjGt9_dh {S : OpaqueSymbolSemantics} {g : Ghost} {pk sk : DY.Bytes}
    (hpk : MemoInjGt9 S g pk) (hsk : MemoInjGt9 S g sk) :
    MemoInjGt9 S g (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    have hsk2 := memoInjGt9_of_dhPk hpk
    split
    · exact memoInjGt9_dh_pack hpk hsk
    · exact memoInjGt9_dh_pack (memoInjGt9_dhPk hsk) hsk2
  · exact memoInjGt9_dh_pack hpk hsk

theorem length_flatMap_toBEBytes4 :
    ∀ l : List (BitVec 32), (l.flatMap (ByteSpecs.toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: ws => by
    simp only [List.flatMap_cons, List.length_append, ByteSpecs.toBEBytes, List.length_ofFn,
      length_flatMap_toBEBytes4 ws, List.length_cons]
    omega

theorem length_byteSpecs_hmacWith
    (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState) (k m : HwBytes) :
    (ByteSpecs.hmacWith F k m).length = 32 := by
  unfold ByteSpecs.hmacWith ByteSpecs.sha256With
  rw [length_flatMap_toBEBytes4, List.Vector.toList_length]

theorem memoInjGt9_hmac {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (ha : MemoInjGt9 S g a) (hb : MemoInjGt9 S g b) :
    MemoInjGt9 S g (DY.Libsignal.TripleRatchet.hmac a b) := by
  intro x hx hinj
  unfold gamma' DY.Libsignal.TripleRatchet.hmac at hx
  rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKdf compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeKdf, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · dsimp only
    rw [length_byteSpecs_hmacWith]; decide
  · exact ha x hxa hinj
  · exact hb x hxb hinj

theorem memoInjGt9_hkdfBlock1 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjGt9 S g prk) (hinfo : MemoInjGt9 S g info) :
    MemoInjGt9 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) :=
  memoInjGt9_hmac hprk (memoInjGt9_concat hinfo (memoInjGt9_lit S g _))

theorem memoInjGt9_hkdfBlock2 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjGt9 S g prk) (hinfo : MemoInjGt9 S g info) :
    MemoInjGt9 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) :=
  memoInjGt9_hmac hprk (memoInjGt9_concat (memoInjGt9_hkdfBlock1 hprk hinfo) (memoInjGt9_concat hinfo (memoInjGt9_lit S g _)))

theorem memoInjGt9_hkdfBlock3 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjGt9 S g prk) (hinfo : MemoInjGt9 S g info) :
    MemoInjGt9 S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) :=
  memoInjGt9_hmac hprk (memoInjGt9_concat (memoInjGt9_hkdfBlock2 hprk hinfo) (memoInjGt9_concat hinfo (memoInjGt9_lit S g _)))

unseal DY.Bytes in
instance localSubVariant (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant compI0) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubKemPk (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubKemSS (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS compI0 S) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem memoInjGt9_normalizeX25519Key {S : OpaqueSymbolSemantics} {g : Ghost} {pk : DY.Bytes}
    (hpk : MemoInjGt9 S g pk) : MemoInjGt9 S g (DY.X25519.normalizeX25519Key pk) := by
  have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
  unfold DY.X25519.normalizeX25519Key
  split
  · rename_i v heq
    rw [heq] at hv; simp only at hv; subst hv
    intro x hx hinj
    apply hpk x _ hinj
    unfold gamma'
    rw [DY.Bytes.rec_eq (concretizeVariant compI0) (concretizeAll compI0 S g)]
    exact List.mem_cons_of_mem _ (by simpa [concretizeVariant, node, gamma'] using hx)
  · exact hpk

theorem memoInjGt9_agree {S : OpaqueSymbolSemantics} {g : Ghost} {pk sk : DY.Bytes}
    (hpk : MemoInjGt9 S g pk) (hsk : MemoInjGt9 S g sk) :
    MemoInjGt9 S g (DY.X25519.agree pk sk) :=
  memoInjGt9_dh (memoInjGt9_normalizeX25519Key hpk) hsk

theorem memoInjGt9_kemPk {S : OpaqueSymbolSemantics} {g : Ghost} {sk : DY.Bytes}
    (hsk : MemoInjGt9 S g sk) : MemoInjGt9 S g (DY.PQKem.kemPk sk) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show DY.PQKem.kemPk sk = ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeKemPk, opaqueNode, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hx
  exact hsk x hx hinj

theorem compKyberCt0_len :
    Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberCt0.length = 1568 :=
  Symbolic.BugInjection.Proofs.Common443.CompI0Laws.leBytes_length 1568 _
theorem compKyberCt1_len :
    Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberCt1.length = 1568 :=
  Symbolic.BugInjection.Proofs.Common443.CompI0Laws.leBytes_length 1568 _
theorem compKyberCt2_len :
    Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberCt2.length = 1568 :=
  Symbolic.BugInjection.Proofs.Common443.CompI0Laws.leBytes_length 1568 _
theorem compDefaultKyberCt_len :
    Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compDefaultKyberCt.length = 1568 :=
  List.length_replicate
theorem drop_append_eq_of_len {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) :
    (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left

theorem compKyberEncaps_drop_length (e : HwBytes) :
    ((Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberEncaps e).drop 1568).length = 32 := by
  unfold Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberEncaps
  split
  · rw [drop_append_eq_of_len compKyberCt0_len]; rfl
  · split
    · rw [drop_append_eq_of_len compKyberCt1_len]; rfl
    · split
      · rw [drop_append_eq_of_len compKyberCt2_len]; rfl
      · rw [drop_append_eq_of_len compDefaultKyberCt_len]; rfl

theorem memoInjGt9_kemEncap_snd {S : OpaqueSymbolSemantics} {g : Ghost} {pk e : DY.Bytes}
    (hpk : MemoInjGt9 S g pk) (he : MemoInjGt9 S g e) :
    MemoInjGt9 S g (DY.PQKem.kemEncap pk e).2 := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKemSS compI0 S) (concretizeAll compI0 S g)] at hx
  dsimp only [concretizeKemSS] at hx
  split_ifs at hx with helen
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
      List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe
    · change 9 < (((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [_, _]).getD []).drop 1568).length
      rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compI0_kyberEncaps,
        Option.getD_some, compKyberEncaps_drop_length]; decide
    · exact hpk x hxpk hinj
    · exact he x hxe hinj
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hpk x h hinj) (fun h => he x h hinj)

theorem memoInjGt9_spqrInit {S : OpaqueSymbolSemantics} {g : Ghost} {a p : DY.Bytes}
    (ha : MemoInjGt9 S g a) (hp : MemoInjGt9 S g p) :
    MemoInjGt9 S g (DY.Spqr.spqrInit a p) := by
  intro x hx hinj
  unfold gamma' DY.Spqr.spqrInit at hx
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  exact hx.elim (fun h => ha x h hinj) (fun h => hp x h hinj)

theorem memoInjGt9_serialize_local_pqxdh {S : OpaqueSymbolSemantics} {g : Ghost}
    {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState}
    (hsk : MemoInjGt9 S g ls.state.sk) : MemoInjGt9 S g (DY.Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (MemoInjGt9 S g) ls]
  simpa [DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf] using hsk

theorem memoInjGt9_serialize_local_tr {S : OpaqueSymbolSemantics} {g : Ghost}
    {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState}
    (hmyIk : MemoInjGt9 S g ls.state.myIk) (hpeerIk : MemoInjGt9 S g ls.state.peerIk)
    (hrk : MemoInjGt9 S g ls.state.rk) (hdhs : MemoInjGt9 S g ls.state.dhs)
    (hcks : MemoInjGt9 S g ls.state.cks) (hsid : MemoInjGt9 S g ls.state.sid)
    (hspqr : MemoInjGt9 S g ls.state.spqr)
    (hrecv : ∀ d ∈ ls.state.recv, MemoInjGt9 S g d.ratchetKey ∧ MemoInjGt9 S g d.chainKey) :
    MemoInjGt9 S g (DY.Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (MemoInjGt9 S g) ls]
  simpa [DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
    hmyIk, hpeerIk, hrk, hdhs, hcks, hsid, hspqr] using hrecv

theorem memoInjGt9_serializedIk {S : OpaqueSymbolSemantics} {g : Ghost} {ik : DY.Bytes}
    (hik : MemoInjGt9 S g ik) : MemoInjGt9 S g (DY.Libsignal.PQXDH.serializedIk ik) :=
  memoInjGt9_concat (memoInjGt9_lit S g _) hik

theorem memoInjGt9_pqxdhKdf_none {S : OpaqueSymbolSemantics} {g : Ghost}
    {dh1 dh2 dh3 ss₀ : DY.Bytes}
    (hdh1 : MemoInjGt9 S g dh1) (hdh2 : MemoInjGt9 S g dh2)
    (hdh3 : MemoInjGt9 S g dh3) (hss₀ : MemoInjGt9 S g ss₀) :
    let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss₀)
    MemoInjGt9 S g keys.rk ∧ MemoInjGt9 S g keys.ck ∧ MemoInjGt9 S g keys.pqr := by
  have hprk : MemoInjGt9 S g
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt
        (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss₀)) :=
    memoInjGt9_hmac (memoInjGt9_lit S g _)
      (memoInjGt9_concat (memoInjGt9_lit S g _)
        (memoInjGt9_concat hdh1 (memoInjGt9_concat hdh2 (memoInjGt9_concat hdh3 hss₀))))
  have hinfo : MemoInjGt9 S g DY.Libsignal.PQXDH.pqxdhLabel := memoInjGt9_lit S g _
  exact ⟨memoInjGt9_hkdfBlock1 hprk hinfo, memoInjGt9_hkdfBlock2 hprk hinfo, memoInjGt9_hkdfBlock3 hprk hinfo⟩

theorem memoInjGt9_createChain {S : OpaqueSymbolSemantics} {g : Ghost} {rk pk sk : DY.Bytes}
    (hrk : MemoInjGt9 S g rk) (hpk : MemoInjGt9 S g pk) (hsk : MemoInjGt9 S g sk) :
    MemoInjGt9 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧
    MemoInjGt9 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hprk := memoInjGt9_hmac hrk (memoInjGt9_agree hpk hsk)
  have hinfo : MemoInjGt9 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := memoInjGt9_lit S g _
  exact ⟨memoInjGt9_hkdfBlock1 hprk hinfo, memoInjGt9_hkdfBlock2 hprk hinfo⟩

def localAliceStartState (tr : ExecTrace) (b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : DY.Libsignal.TripleRatchet.TRState :=
  let dhsA := randTerm (tr.length + 2) 32
  let (rkA, cksA) := DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk dhsA
  { peer := b
    myIk := DY.Libsignal.PQXDH.serializedIk o.ikA
    peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB
    rk := rkA
    dhs := dhsA
    cks := cksA
    ns := 0
    pn := 0
    sid := DY.Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk
    initiator := true
    rIdx := 1
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }]
    spqr := DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }

def localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : ExecTrace :=
  let dhsA := randTerm (tr.length + 2) 32
  let stA := localAliceStartState tr b o
  ((((((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)).append
    (NetE o.ct)).append
    (PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (TREvE (.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk))).append
    (CEvE (.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append (TRStE a stA)

theorem length_append_entry {T : Type} [DY.ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) :
    (tr.append x).length = tr.length + 1 := by
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem at?_append_eq_of_eq {T S : Type} [DY.ExecTraceTypes.Has T] [DY.ExecTraceTypes.Has S]
    (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) :
    ((tr.append x).at? i : Option T) = DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x

local macro "at?_localAliceStartTr_tac" : tactic =>
  `(tactic| (dsimp only [localAliceStartTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))

theorem newIndices_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    newIndices tr (localAliceStartTr tr a b o) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4,
       tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := by
  unfold newIndices
  have hlen : (localAliceStartTr tr a b o).length = tr.length + 9 := by
    dsimp only [localAliceStartTr]; simp only [length_append_entry]
  rw [hlen, Nat.add_sub_cancel_left]; simp [List.range', Nat.add_assoc]

theorem newRandoms_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    newRandoms tr (localAliceStartTr tr a b o) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32), (randTerm (tr.length + 2) 32, 32)] := by
  unfold newRandoms; rw [newIndices_localAliceStartTr]
  have h0 : ((localAliceStartTr tr a b o).at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_localAliceStartTr_tac
  have h1 : ((localAliceStartTr tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_localAliceStartTr_tac
  have h2 : ((localAliceStartTr tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_localAliceStartTr_tac
  have h3 : ((localAliceStartTr tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h4 : ((localAliceStartTr tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h5 : ((localAliceStartTr tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h6 : ((localAliceStartTr tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h7 : ((localAliceStartTr tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h8 : ((localAliceStartTr tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, RndE]

theorem getEventAt_pq_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    let tr' := localAliceStartTr tr a b o
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent tr.length = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 1) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 2) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 3) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 4) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 5) =
      some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 6) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 7) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((localAliceStartTr tr a b o).at? tr.length : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h1 : ((localAliceStartTr tr a b o).at? (tr.length + 1) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h2 : ((localAliceStartTr tr a b o).at? (tr.length + 2) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h3 : ((localAliceStartTr tr a b o).at? (tr.length + 3) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h4 : ((localAliceStartTr tr a b o).at? (tr.length + 4) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h5 : ((localAliceStartTr tr a b o).at? (tr.length + 5) : Option PQXDHEntry) =
      some (PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by at?_localAliceStartTr_tac
  have h6 : ((localAliceStartTr tr a b o).at? (tr.length + 6) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h7 : ((localAliceStartTr tr a b o).at? (tr.length + 7) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h8 : ((localAliceStartTr tr a b o).at? (tr.length + 8) : Option PQXDHEntry) = none := by at?_localAliceStartTr_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, PQEvE]

theorem getEventAt_tr_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    let tr' := localAliceStartTr tr a b o
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent tr.length = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 1) = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 2) = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 3) = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 4) = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 5) = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 6) =
      some (.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk) ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 7) = none ∧
    tr'.getEventAt DY.Libsignal.TripleRatchet.TREvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((localAliceStartTr tr a b o).at? tr.length : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h1 : ((localAliceStartTr tr a b o).at? (tr.length + 1) : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h2 : ((localAliceStartTr tr a b o).at? (tr.length + 2) : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h3 : ((localAliceStartTr tr a b o).at? (tr.length + 3) : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h4 : ((localAliceStartTr tr a b o).at? (tr.length + 4) : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h5 : ((localAliceStartTr tr a b o).at? (tr.length + 5) : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h6 : ((localAliceStartTr tr a b o).at? (tr.length + 6) : Option TREntry) =
      some (TREvE (.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk)) := by at?_localAliceStartTr_tac
  have h7 : ((localAliceStartTr tr a b o).at? (tr.length + 7) : Option TREntry) = none := by at?_localAliceStartTr_tac
  have h8 : ((localAliceStartTr tr a b o).at? (tr.length + 8) : Option TREntry) = none := by at?_localAliceStartTr_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, TREvE]

theorem eventIdx_isAliceDone_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    eventIdx isAliceDone tr (localAliceStartTr tr a b o) = some (tr.length + 5) := by
  unfold eventIdx; rw [newIndices_localAliceStartTr]
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := getEventAt_pq_localAliceStartTr tr a b o
  simp [h0, h1, h2, h3, h4, h5, isAliceDone]

theorem aliceVis_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hb : DY.Libsignal.PQXDH.BundleHandles) :
    aliceVis tr (localAliceStartTr tr a b o) hb =
      { kind := .recv, terms := received tr ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList),
        layout := .bundle, anchor := none } ::
      rngEntry (randTerm tr.length 32) ::
      (kyberCoinEntries (randTerm (tr.length + 1) 32) ++
        [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  simp [aliceVis, aliceDraws, newRandoms_localAliceStartTr, eventIdx_isAliceDone_localAliceStartTr]

theorem exposures_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    exposures tr (localAliceStartTr tr a b o) = [] := by
  unfold exposures
  rw [newIndices_localAliceStartTr]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := getEventAt_pq_localAliceStartTr tr a b o
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8⟩ := getEventAt_tr_localAliceStartTr tr a b o
  simp [pqExposureAt, trExposureAt, p0, p1, p2, p3, p4, p5, p6, p7, p8,
    t0, t1, t2, t3, t4, t5, t6, t7, t8]

theorem isSome_bind_local {α β : Type} {x : DY.Traceful α} {f : α → DY.Traceful β}
    {tr : ExecTrace} (h : ((x >>= f).run tr).1.isSome = true) :
    ∃ a, (x.run tr).1 = some a ∧ ((f a).run (x.run tr).2.val).1.isSome = true := by
  rw [run_bind_fst] at h
  rcases hx : (x.run tr).1 with _ | a
  · rw [hx] at h; cases h
  · rw [hx] at h; exact ⟨a, rfl, h⟩

theorem bind_aliceHandshake_at_local {Inv : ExecTrace → Prop} {α : Type}
    (a b : DY.Participant) (idStateIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles)
    {f : DY.Libsignal.PQXDH.AliceHandshakeOut → DY.Traceful α}
    (tr : ExecTrace) (hInv : Inv tr) (habort : Inv (tr.append (RndE 32)))
    (hf : ∀ (ikA ikB _vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (_honest : Bool),
      NetMsgAt spk bh.spk tr → NetMsgAt spkSig bh.spkSig tr →
      NetMsgAt pqpk bh.pqpk tr → NetMsgAt pqpkSig bh.pqpkSig tr →
      ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) →
      Inv ((f (aliceOut tr ikA ikB spk pqpk opk)).run ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    Inv (((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  rw [run_bind_assoc_snd]; apply bind_getKey_at a idStateIdx .identity tr hInv; intro ikA _
  rw [run_bind_assoc_snd]; apply bind_lookupIdentity_at b regIdxB tr hInv; intro ikB vkB honest _
  rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.spk tr hInv; intro spk hspk _
  rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.spkSig tr hInv; intro spkSig hspkSig _
  rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.pqpk tr hInv; intro pqpk hpq _
  rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.pqpkSig tr hInv; intro pqpkSig hpqSig _
  rw [run_bind_assoc_snd]; apply bind_guardP_at _ tr hInv; intro _
  rw [run_bind_assoc_snd]; apply bind_guardP_at _ tr hInv; intro _
  rcases hbh : bh.opk with _ | opkIdx
  · change Inv ((((Pure.pure none : DY.Traceful (Option DY.Bytes)) >>=
      aliceHandshakeJp ikA ikB spk pqpk >>= f).run tr).2.val)
    rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk none tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig none honest hspk hspkSig hpq hpqSig (.inl ⟨hbh, rfl⟩)
  · change Inv ((((DY.Network.receiveMessage opkIdx >>= fun o =>
        (Pure.pure (some o) : DY.Traceful (Option DY.Bytes)) >>=
          aliceHandshakeJp ikA ikB spk pqpk) >>= f).run tr).2.val)
    rw [run_bind_assoc_snd]; apply bind_receiveMessage_at opkIdx tr hInv; intro o hopk _
    rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk (some o) tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig (some o) honest hspk hspkSig hpq hpqSig
        (.inr ⟨opkIdx, o, hbh, rfl, hopk⟩)

theorem aliceStart_ok_eq_localAliceStartTr {tr : ExecTrace} {a b : DY.Participant}
    {idStateIdx regIdxB : Nat} {bh : DY.Libsignal.PQXDH.BundleHandles}
    (hok : (Step.aliceStart a b idStateIdx regIdxB bh).ok tr = true) :
    ∃ ikA ikB spk spkSig pqpk pqpkSig opk,
      NetMsgAt spk bh.spk tr ∧ NetMsgAt spkSig bh.spkSig tr ∧
      NetMsgAt pqpk bh.pqpk tr ∧ NetMsgAt pqpkSig bh.pqpkSig tr ∧
      ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) ∧
      (Step.aliceStart a b idStateIdx regIdxB bh).next tr =
        localAliceStartTr tr a b (aliceOut tr ikA ikB spk pqpk opk) := by
  have hnext_eq : (Step.aliceStart a b idStateIdx regIdxB bh).next tr =
      ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val :=
    Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_next
      DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, bh) tr
  have hok_eq : ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).1.isSome = true :=
    (Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_ok
      DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, bh) tr).symm.trans hok
  rw [hnext_eq]
  have hP : tr.length + 7 ≤ ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val.length →
      ∃ ikA ikB spk spkSig pqpk pqpkSig opk,
        NetMsgAt spk bh.spk tr ∧ NetMsgAt spkSig bh.spkSig tr ∧
        NetMsgAt pqpk bh.pqpk tr ∧ NetMsgAt pqpkSig bh.pqpkSig tr ∧
        ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) ∧
        ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val =
          localAliceStartTr tr a b (aliceOut tr ikA ikB spk pqpk opk) := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false })
      only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine bind_aliceHandshake_at_local
      (Inv := fun t => tr.length + 7 ≤ t.length →
        ∃ ikA ikB spk spkSig pqpk pqpkSig opk,
          NetMsgAt spk bh.spk tr ∧ NetMsgAt spkSig bh.spkSig tr ∧
          NetMsgAt pqpk bh.pqpk tr ∧ NetMsgAt pqpkSig bh.pqpkSig tr ∧
          ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) ∧
          t = localAliceStartTr tr a b (aliceOut tr ikA ikB spk pqpk opk))
      a b idStateIdx regIdxB bh tr (fun h => by omega)
      (fun h => by simp only [length_append_entry] at h; omega) ?_
    intro ikA ikB _ spk spkSig pqpk pqpkSig opk _ hspk hspkSig hpq hpqSig hopk _
    refine ⟨ikA, ikB, spk, spkSig, pqpk, pqpkSig, opk, hspk, hspkSig, hpq, hpqSig, hopk, ?_⟩
    simp only [DY.Libsignal.TripleRatchet.traceLength,
      Symbolic.DYBridge.DY.Random.genRand_eq_1,
      Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      run_bind_fst, run_bind_snd, DY.Traceful.run_mk, DY.Traceful.run_pure,
      length_append_entry, Nat.add_assoc]
    rfl
  refine hP ?_
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false })
    only [DY.Libsignal.Composed.aliceStart_eq_inline] at hok_eq ⊢
  obtain ⟨w, hhs, _⟩ := isSome_bind_local hok_eq
  rw [run_bind_snd, hhs]
  set t_hs := ((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.val
  have hle : tr.length ≤ t_hs.length :=
    DY.Trace.length_le _ _ ((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.property
  dsimp only
  simp only [DY.Libsignal.TripleRatchet.traceLength,
    Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    run_bind_fst, run_bind_snd, DY.Traceful.run_mk, DY.Traceful.run_pure, length_append_entry]
  omega

theorem memoInjGt9_iniAliceStartState {S : OpaqueSymbolSemantics} {g : Ghost}
    (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    (hikA : MemoInjGt9 S g o.ikA) (hikB : MemoInjGt9 S g o.ikB)
    (hspk : MemoInjGt9 S g o.spk)
    (hrk : MemoInjGt9 S g o.keys.rk) (hck : MemoInjGt9 S g o.keys.ck) (hpqr : MemoInjGt9 S g o.keys.pqr)
    (hdhsA : MemoInjGt9 S g (randTerm (tr.length + 2) 32)) :
    MemoInjGt9 S g (DY.Comparse.serialize
      (⟨a, localAliceStartState tr b o⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  have hcc := memoInjGt9_createChain hrk hspk hdhsA
  refine memoInjGt9_serialize_local_tr (memoInjGt9_serializedIk hikA) (memoInjGt9_serializedIk hikB)
    hcc.1 hdhsA hcc.2 (memoInjGt9_concat (memoInjGt9_dhPk hdhsA) hrk)
    (memoInjGt9_spqrInit hpqr (memoInjGt9_lit S g _)) (fun d hd => ?_)
  simp only [localAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨hspk, hck⟩


end
end Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept
