/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.NoFullExplains

/-!
# Call-1 Send Collision Discharge (`¬ NextEventCollides` at `ev1`)
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

/-! ## Prefix Collision Excuse Dischargers (`¬ CollisionAfterExplainedPrefix`) -/

def ev0InHexStr : String := "ae08000000000000000000000000000000000000000000000000000000000000000000000000000000000700000005b6b88896bce6c272053abf1c7717aca151d472728303ff4cea12496c9fe3141869bd5891fb74c6ab969cbb275643757eb87c43d18ff4a4f96475aa80e253966864eacf3f8ca74482c929aff17f29f29d6d65e2e8b1512e773bbd4c0a99aac10a0900000008a8730e936458010cbc88c960d7a881b950bc17a672b3fac32a101b1f71999337b6e9e6a5e9e0cd84f17c3bf26762c49d9638829de6a1a1f77453744234a8b4af726b649007d42a68edc976345c23a459c23264aa159791038345a7c27a5c509fa9fb3ba171b34e6a7815f93ba5f67dfeca5ad7dc4d176c432d07786f116e203174fb7820529314bcc0a68d11a25e7a5d9adca5608966b64cb8ac3672ef6a85e79421cb25175a4727fe185598677c5d6666d6021e1f171147f0b543d7b4ae224674e7377d5914e665644743a178fc6e5cea0d715cbb5c219d87c17016e03d8c76a8edc084edb28d748a6dd97b11e596bf67937ca8289f9b7c1ab3c709ac25ca09ac33289b4f86241206b22bdcd82e35f0235278409e81748d19358cf52b4be4565f84b4dc368771e4b12259bc0a3b11270b26f1027d32f5587316a4c2555e0f4537af0815a6fc6c58e590d2a4206d5c297221076c57b8d8312fec25c0f091798c61b5040962d06100c31687a50aa3ac81b99bf049e77a227e5c1eb2523a6a11b34d86c76249976e41487185841be414243b7e52c84fbe667583073b2d5852cfe9747ae705ad2394ef520946ab538ab6a09c535961749e96126e9830741e6481a22808b889b77267853ec56a02da16987c1b61c850d5dbc84ee31131b332055549566033619c7a8eec2ca2e130c19881b130b48242643e5c62c5f37288b401e537b648a445702135d28143f109ba0c6acdbe193b52862b054633c060ce18905783d732bce07b7068746cf033e394ab000152887638e3f13465341fe9c3297e5c2cdca7b63b26526b250580b67451550ca05531bcb5ad2703265e644af5e5ca67b374778b7d913bb337165ce5c78cb91c5d8a7acff257118da58fa5a5266312c6697a25feb2ae4206c841299eb74c53ae607c85f721602c9825218961654f4716003af2905f69add5ca5ee8f44477264255e14a83693a282616930bac094095ca61c10ec1a4c243a4bef60d41d796b92659dd4b67a6b87815949462664bc1868ff04941f6e1aa69e44005171971b2cd5f7a10a969bbcc888ca6792892d715ad29a6bd219e3228287a28ad875726de89225815797e8097d67070c13abfb3979892596448095fc0bb775d86a8a5bc162292424cb26fec92929bac02db3bcba5fc9fe5142af9967ab202708f356a3542498692af1b1461fce48f6fc42a4c13161319642f6310b5806ad89928b32a1bea507c9951b458bb609a41a1a35bc63ac01c568c3188b61041625016840f07782e9bc986c61516a4037cf7273d5c9c6b1a0a664443b7b288353c81798b37cea23c3ab53b1893264bc83b726d3150420b0d86ecbffaf30c48abb58d46020b2c63f961459925a54d1b5aed591e0580aed62b288806ac5f668c535107de569d880ccaff8b1150f824dd68b8f8bab78f9922d94686a893a25b265279f16f329a5a0e9960edc4154a3455d173479ddaca879292b38cb5fbb1bb316662dbe31217518636171eff503f5a32582ffcc1ac0234acea7e385442844051a4d44b8ea2576976743e3092b2e50c1064a74115afe0dc310fb38d47875f10430e3d9386a8f6c30f87253762bfd13b5b486947a12b3eb996a336e259d982272caacd0b2c4a73e8a6ebc8062a25cba4d477aadbbdb103afc766c9df6a625144a6f3783fa8fb4191bc5ec1083b8a73388c86ab13e93ed48712e6f1037390421c1420f10a41f120424613594ed66b20b9c33351c986538fa1d88e2aac22867c63cbe93b6fb790f3a8bc2ce35860f69f336a794e8780b9e65d47926ccb491316d414e8e235b88bcd2f07553933c9025a95723c115dfaad6829895175a5d26527b9581703e2c47c5282a0aa627040c6f7908dbf26cfc56234f1f9367239994fab555e92038d6c50966abf0fc924df048b02349a4bc59c0829b8d82c42cfa17bbf21cf82eb1bcb831d861a48dc3923ed84cce4a615c26b70b789b91db06a9cc7324c8baa0fd86a52d4b2903b015d8bb4b609851c83827f61caea67589d1276875b1ae8357ce642a518a60eed25a2fc38aca90b6f1359877b4a45b92b725e75879ba2affc0509e4896a4c5c7b28d6379136596c0a0c8e6852e0bc0ae8da3b390a9d5535c4bff1ad3018492d1aa7990646e22a7e799537aa50c6bf4264bf61989f8970009132541c7a43c12b7870f8696f7897bdbfd21a75192619a4446a9f08c71920b06b6b8fa823fe8e9f5be716f812b65c57f00bd46aba4abb8012a4f95d32fe23831c670012de11b2bef6a62c66f235c0673a229a13bc0a258da1a2750505f76d50f376882c6ffbadce584c2428aa82e885e515b532c0b04803ff8bac7f62"
def ev0Wrap : HwBytes := hexBytes ev0InHexStr
def ev0InChars : List Char := chars_of_hex_def ev0Wrap
theorem ev0InHexStr_eq : ev0InHexStr = String.ofList ev0InChars := rfl
def ev0InFast : HwBytes := hexBytes.go hexDigit ev0InChars
theorem ev0_input_eq_fast : ev0.input = ev0InFast := by
  change hexBytes ev0InHexStr = _
  rw [ev0InHexStr_eq, hexBytes_ofList]; rfl

theorem bundlePreKeyIds_ev0 : bundlePreKeyIds ev0.input = bundlePreKeyIds ev0InFast := by
  rw [ev0_input_eq_fast]

theorem ev0_input_getElem4_ne_one : ev0.input[4]? ≠ some 1 := by
  rw [ev0_input_eq_fast]; decide +kernel

theorem ev1_input_len : ev1.input.length = 5 := by
  have h : ev1.input = hexBytes.go hexDigit ['6','6','6','9','7','2','7','3','7','4'] := by
    change hexBytes "6669727374" = _
    rw [show "6669727374" = String.ofList ['6','6','6','9','7','2','7','3','7','4'] from rfl, hexBytes_ofList]
  rw [h]; rfl

theorem ev2_input_len : ev2.input.length = 6 := by
  have h : ev2.input = hexBytes.go hexDigit ['7','3','6','5','6','3','6','f','6','e','6','4'] := by
    change hexBytes "7365636f6e64" = _
    rw [show "7365636f6e64" = String.ofList ['7','3','6','5','6','3','6','f','6','e','6','4'] from rfl, hexBytes_ofList]
  rw [h]; rfl

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

def MemoInjGt7 (S : OpaqueSymbolSemantics) (g : Ghost) (t : DY.Bytes) : Prop :=
  ∀ x ∈ (gamma' compI0 S g t).memo, assumedInjective x.1 = true → 7 < x.2.2.length

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

theorem memoInjGt7_lit (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    MemoInjGt7 S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S g)] at hx
  rcases List.mem_singleton.mp hx with rfl
  rw [assumedInjective_lit] at hinj
  cases hinj

theorem memoInjGt7_randTerm {S : OpaqueSymbolSemantics} {g : Ghost} {idx sz : Nat}
    (h : sz = 0 ∨ 7 < (g.σ idx sz).length) :
    MemoInjGt7 S g (randTerm idx sz) := by
  intro x hx _
  unfold gamma' randTerm at hx
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI0 S g)] at hx
  dsimp only [concretizeRandom] at hx
  split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl
    exact h.resolve_left hsz

theorem memoInjGt7_concat {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (ha : MemoInjGt7 S g a) (hb : MemoInjGt7 S g b) :
    MemoInjGt7 S g (DY.Concat.concat a b) := by
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

theorem memoInjGt7_of_concat {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (h : MemoInjGt7 S g (DY.Concat.concat a b)) :
    MemoInjGt7 S g a ∧ MemoInjGt7 S g b := by
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

instance instBytesCompatiblePredMemoInjGt7 (S : OpaqueSymbolSemantics) (g : Ghost) :
    Comparse.BytesCompatiblePred (MemoInjGt7 S g) where
  pred_empty := memoInjGt7_lit S g .empty
  pred_concat _ _ hl hr := memoInjGt7_concat hl hr
  pred_split buf n hbuf := by
    cases hsp : Comparse.BytesLike.split buf n with
    | none => trivial
    | some p =>
      rw [← DY.Concat.concat_split buf n p.1 p.2 hsp] at hbuf
      exact memoInjGt7_of_concat hbuf
  pred_fromByteArray b := memoInjGt7_lit S g b

theorem memoInjGt7_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {sk : DY.Bytes}
    (hsk : MemoInjGt7 S g sk) : MemoInjGt7 S g (DY.DiffieHellman.dhPk sk) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk
  · change 7 < (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupPub _).length
    rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compLookupPub_length]; decide
  · exact hsk x hxsk hinj

theorem memoInjGt7_of_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {sk : DY.Bytes}
    (h : MemoInjGt7 S g (DY.DiffieHellman.dhPk sk)) : MemoInjGt7 S g sk := by
  intro x hx hinj
  apply h x _ hinj
  unfold gamma'
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g)]
  exact List.mem_cons_of_mem _ (by simpa [concretizeDhPk, node, bytes_rec_gAll] using hx)

theorem memoInjGt7_dh_pack {S : OpaqueSymbolSemantics} {g : Ghost} {pk sk : DY.Bytes}
    (hpk : MemoInjGt7 S g pk) (hsk : MemoInjGt7 S g sk) :
    MemoInjGt7 S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro x hx hinj
  unfold gamma' at hx
  rw [DY.Bytes.rec_eq (concretizeDh compI0) (concretizeAll compI0 S g)] at hx
  simp only [concretizeDh, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxpk | hxsk
  · change 7 < (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupDh _ _).length
    rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compLookupDh_length]; decide
  · exact hpk x hxpk hinj
  · exact hsk x hxsk hinj

theorem memoInjGt7_dh {S : OpaqueSymbolSemantics} {g : Ghost} {pk sk : DY.Bytes}
    (hpk : MemoInjGt7 S g pk) (hsk : MemoInjGt7 S g sk) :
    MemoInjGt7 S g (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    have hsk2 := memoInjGt7_of_dhPk hpk
    split
    · exact memoInjGt7_dh_pack hpk hsk
    · exact memoInjGt7_dh_pack (memoInjGt7_dhPk hsk) hsk2
  · exact memoInjGt7_dh_pack hpk hsk

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

theorem memoInjGt7_hmac {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    (ha : MemoInjGt7 S g a) (hb : MemoInjGt7 S g b) :
    MemoInjGt7 S g (DY.Libsignal.TripleRatchet.hmac a b) := by
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

theorem memoInjGt7_hkdfBlock1 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjGt7 S g prk) (hinfo : MemoInjGt7 S g info) :
    MemoInjGt7 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) :=
  memoInjGt7_hmac hprk (memoInjGt7_concat hinfo (memoInjGt7_lit S g _))

theorem memoInjGt7_hkdfBlock2 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjGt7 S g prk) (hinfo : MemoInjGt7 S g info) :
    MemoInjGt7 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) :=
  memoInjGt7_hmac hprk (memoInjGt7_concat (memoInjGt7_hkdfBlock1 hprk hinfo) (memoInjGt7_concat hinfo (memoInjGt7_lit S g _)))

theorem memoInjGt7_hkdfBlock3 {S : OpaqueSymbolSemantics} {g : Ghost} {prk info : DY.Bytes}
    (hprk : MemoInjGt7 S g prk) (hinfo : MemoInjGt7 S g info) :
    MemoInjGt7 S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) :=
  memoInjGt7_hmac hprk (memoInjGt7_concat (memoInjGt7_hkdfBlock2 hprk hinfo) (memoInjGt7_concat hinfo (memoInjGt7_lit S g _)))

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

theorem memoInjGt7_normalizeX25519Key {S : OpaqueSymbolSemantics} {g : Ghost} {pk : DY.Bytes}
    (hpk : MemoInjGt7 S g pk) : MemoInjGt7 S g (DY.X25519.normalizeX25519Key pk) := by
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

theorem memoInjGt7_agree {S : OpaqueSymbolSemantics} {g : Ghost} {pk sk : DY.Bytes}
    (hpk : MemoInjGt7 S g pk) (hsk : MemoInjGt7 S g sk) :
    MemoInjGt7 S g (DY.X25519.agree pk sk) :=
  memoInjGt7_dh (memoInjGt7_normalizeX25519Key hpk) hsk

theorem memoInjGt7_kemPk {S : OpaqueSymbolSemantics} {g : Ghost} {sk : DY.Bytes}
    (hsk : MemoInjGt7 S g sk) : MemoInjGt7 S g (DY.PQKem.kemPk sk) := by
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

theorem memoInjGt7_kemEncap_snd {S : OpaqueSymbolSemantics} {g : Ghost} {pk e : DY.Bytes}
    (hpk : MemoInjGt7 S g pk) (he : MemoInjGt7 S g e) :
    MemoInjGt7 S g (DY.PQKem.kemEncap pk e).2 := by
  intro x hx hinj
  unfold gamma' at hx
  rw [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKemSS compI0 S) (concretizeAll compI0 S g)] at hx
  dsimp only [concretizeKemSS] at hx
  split_ifs at hx with helen
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
      List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe
    · change 7 < (((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [_, _]).getD []).drop 1568).length
      rw [Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compI0_kyberEncaps,
        Option.getD_some, compKyberEncaps_drop_length]; decide
    · exact hpk x hxpk hinj
    · exact he x hxe hinj
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hpk x h hinj) (fun h => he x h hinj)

theorem memoInjGt7_spqrInit {S : OpaqueSymbolSemantics} {g : Ghost} {a p : DY.Bytes}
    (ha : MemoInjGt7 S g a) (hp : MemoInjGt7 S g p) :
    MemoInjGt7 S g (DY.Spqr.spqrInit a p) := by
  intro x hx hinj
  unfold gamma' DY.Spqr.spqrInit at hx
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  exact hx.elim (fun h => ha x h hinj) (fun h => hp x h hinj)

theorem memoInjGt7_serialize_local_pqxdh {S : OpaqueSymbolSemantics} {g : Ghost}
    {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState}
    (hsk : MemoInjGt7 S g ls.state.sk) : MemoInjGt7 S g (DY.Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (MemoInjGt7 S g) ls]
  simpa [DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf] using hsk

theorem memoInjGt7_serialize_local_tr {S : OpaqueSymbolSemantics} {g : Ghost}
    {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState}
    (hmyIk : MemoInjGt7 S g ls.state.myIk) (hpeerIk : MemoInjGt7 S g ls.state.peerIk)
    (hrk : MemoInjGt7 S g ls.state.rk) (hdhs : MemoInjGt7 S g ls.state.dhs)
    (hcks : MemoInjGt7 S g ls.state.cks) (hsid : MemoInjGt7 S g ls.state.sid)
    (hspqr : MemoInjGt7 S g ls.state.spqr)
    (hrecv : ∀ d ∈ ls.state.recv, MemoInjGt7 S g d.ratchetKey ∧ MemoInjGt7 S g d.chainKey) :
    MemoInjGt7 S g (DY.Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (MemoInjGt7 S g) ls]
  simpa [DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
    hmyIk, hpeerIk, hrk, hdhs, hcks, hsid, hspqr] using hrecv

theorem memoInjGt7_serializedIk {S : OpaqueSymbolSemantics} {g : Ghost} {ik : DY.Bytes}
    (hik : MemoInjGt7 S g ik) : MemoInjGt7 S g (DY.Libsignal.PQXDH.serializedIk ik) :=
  memoInjGt7_concat (memoInjGt7_lit S g _) hik

theorem memoInjGt7_pqxdhKdf_none {S : OpaqueSymbolSemantics} {g : Ghost}
    {dh1 dh2 dh3 ss₀ : DY.Bytes}
    (hdh1 : MemoInjGt7 S g dh1) (hdh2 : MemoInjGt7 S g dh2)
    (hdh3 : MemoInjGt7 S g dh3) (hss₀ : MemoInjGt7 S g ss₀) :
    let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss₀)
    MemoInjGt7 S g keys.rk ∧ MemoInjGt7 S g keys.ck ∧ MemoInjGt7 S g keys.pqr := by
  have hprk : MemoInjGt7 S g
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt
        (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss₀)) :=
    memoInjGt7_hmac (memoInjGt7_lit S g _)
      (memoInjGt7_concat (memoInjGt7_lit S g _)
        (memoInjGt7_concat hdh1 (memoInjGt7_concat hdh2 (memoInjGt7_concat hdh3 hss₀))))
  have hinfo : MemoInjGt7 S g DY.Libsignal.PQXDH.pqxdhLabel := memoInjGt7_lit S g _
  exact ⟨memoInjGt7_hkdfBlock1 hprk hinfo, memoInjGt7_hkdfBlock2 hprk hinfo, memoInjGt7_hkdfBlock3 hprk hinfo⟩

theorem memoInjGt7_createChain {S : OpaqueSymbolSemantics} {g : Ghost} {rk pk sk : DY.Bytes}
    (hrk : MemoInjGt7 S g rk) (hpk : MemoInjGt7 S g pk) (hsk : MemoInjGt7 S g sk) :
    MemoInjGt7 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧
    MemoInjGt7 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hprk := memoInjGt7_hmac hrk (memoInjGt7_agree hpk hsk)
  have hinfo : MemoInjGt7 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := memoInjGt7_lit S g _
  exact ⟨memoInjGt7_hkdfBlock1 hprk hinfo, memoInjGt7_hkdfBlock2 hprk hinfo⟩

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
  ((((((((tr.append (CompTrace.RndE 32)).append (CompTrace.RndE 32)).append (CompTrace.RndE 32)).append
    (CompTrace.NetE o.ek)).append (CompTrace.NetE o.ct)).append
    (CompTrace.PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (CompTrace.TREvE (.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk))).append
    (CompTrace.CEvE (.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append (CompTrace.TRStE a stA)

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
  have h0 : ((localAliceStartTr tr a b o).at? tr.length : Option DY.Random.ExecEntryT) = some (CompTrace.RndE 32) := by at?_localAliceStartTr_tac
  have h1 : ((localAliceStartTr tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (CompTrace.RndE 32) := by at?_localAliceStartTr_tac
  have h2 : ((localAliceStartTr tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = some (CompTrace.RndE 32) := by at?_localAliceStartTr_tac
  have h3 : ((localAliceStartTr tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h4 : ((localAliceStartTr tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h5 : ((localAliceStartTr tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h6 : ((localAliceStartTr tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h7 : ((localAliceStartTr tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  have h8 : ((localAliceStartTr tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := by at?_localAliceStartTr_tac
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, CompTrace.RndE]

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
  have h0 : ((localAliceStartTr tr a b o).at? tr.length : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h1 : ((localAliceStartTr tr a b o).at? (tr.length + 1) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h2 : ((localAliceStartTr tr a b o).at? (tr.length + 2) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h3 : ((localAliceStartTr tr a b o).at? (tr.length + 3) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h4 : ((localAliceStartTr tr a b o).at? (tr.length + 4) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h5 : ((localAliceStartTr tr a b o).at? (tr.length + 5) : Option CompTrace.PQXDHEntry) =
      some (CompTrace.PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by at?_localAliceStartTr_tac
  have h6 : ((localAliceStartTr tr a b o).at? (tr.length + 6) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h7 : ((localAliceStartTr tr a b o).at? (tr.length + 7) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  have h8 : ((localAliceStartTr tr a b o).at? (tr.length + 8) : Option CompTrace.PQXDHEntry) = none := by at?_localAliceStartTr_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, CompTrace.PQEvE]

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
  have h0 : ((localAliceStartTr tr a b o).at? tr.length : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h1 : ((localAliceStartTr tr a b o).at? (tr.length + 1) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h2 : ((localAliceStartTr tr a b o).at? (tr.length + 2) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h3 : ((localAliceStartTr tr a b o).at? (tr.length + 3) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h4 : ((localAliceStartTr tr a b o).at? (tr.length + 4) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h5 : ((localAliceStartTr tr a b o).at? (tr.length + 5) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h6 : ((localAliceStartTr tr a b o).at? (tr.length + 6) : Option CompTrace.TREntry) =
      some (CompTrace.TREvE (.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk)) := by at?_localAliceStartTr_tac
  have h7 : ((localAliceStartTr tr a b o).at? (tr.length + 7) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  have h8 : ((localAliceStartTr tr a b o).at? (tr.length + 8) : Option CompTrace.TREntry) = none := by at?_localAliceStartTr_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, CompTrace.TREvE]

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

theorem bind_aliceHandshake_at_local {Inv : ExecTrace → Prop} {α : Type}
    (a b : DY.Participant) (idStateIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles)
    {f : DY.Libsignal.PQXDH.AliceHandshakeOut → DY.Traceful α}
    (tr : ExecTrace) (hInv : Inv tr) (habort : Inv (tr.append (CompTrace.RndE 32)))
    (hf : ∀ (ikA ikB _vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (_honest : Bool),
      CompTrace.NetMsgAt spk bh.spk tr → CompTrace.NetMsgAt spkSig bh.spkSig tr →
      CompTrace.NetMsgAt pqpk bh.pqpk tr → CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr →
      ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ CompTrace.NetMsgAt o idx tr)) →
      Inv ((f (CompTrace.aliceOut tr ikA ikB spk pqpk opk)).run ((tr.append (CompTrace.RndE 32)).append (CompTrace.RndE 32))).2.val) :
    Inv (((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_getKey_at a idStateIdx .identity tr hInv; intro ikA _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_lookupIdentity_at b regIdxB tr hInv; intro ikB vkB honest _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_receiveMessage_at bh.spk tr hInv; intro spk hspk _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_receiveMessage_at bh.spkSig tr hInv; intro spkSig hspkSig _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_receiveMessage_at bh.pqpk tr hInv; intro pqpk hpq _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_receiveMessage_at bh.pqpkSig tr hInv; intro pqpkSig hpqSig _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_guardP_at _ tr hInv; intro _
  rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_guardP_at _ tr hInv; intro _
  rcases hbh : bh.opk with _ | opkIdx
  · change Inv ((((Pure.pure none : DY.Traceful (Option DY.Bytes)) >>=
      CompTrace.aliceHandshakeJp ikA ikB spk pqpk >>= f).run tr).2.val)
    rw [CompTrace.run_bind_assoc_snd, CompTrace.run_pure_bind_snd]
    exact CompTrace.bind_aliceHandshakeJp_at ikA ikB spk pqpk none tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig none honest hspk hspkSig hpq hpqSig (.inl ⟨hbh, rfl⟩)
  · change Inv ((((DY.Network.receiveMessage opkIdx >>= fun o =>
        (Pure.pure (some o) : DY.Traceful (Option DY.Bytes)) >>=
          CompTrace.aliceHandshakeJp ikA ikB spk pqpk) >>= f).run tr).2.val)
    rw [CompTrace.run_bind_assoc_snd]; apply CompTrace.bind_receiveMessage_at opkIdx tr hInv; intro o hopk _
    rw [CompTrace.run_bind_assoc_snd, CompTrace.run_pure_bind_snd]
    exact CompTrace.bind_aliceHandshakeJp_at ikA ikB spk pqpk (some o) tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig (some o) honest hspk hspkSig hpq hpqSig
        (.inr ⟨opkIdx, o, hbh, rfl, hopk⟩)

theorem aliceStart_ok_eq_localAliceStartTr {tr : ExecTrace} {a b : DY.Participant}
    {idStateIdx regIdxB : Nat} {bh : DY.Libsignal.PQXDH.BundleHandles}
    (hok : (Step.aliceStart a b idStateIdx regIdxB bh).ok tr = true) :
    ∃ ikA ikB spk spkSig pqpk pqpkSig opk,
      CompTrace.NetMsgAt spk bh.spk tr ∧ CompTrace.NetMsgAt spkSig bh.spkSig tr ∧
      CompTrace.NetMsgAt pqpk bh.pqpk tr ∧ CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr ∧
      ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ CompTrace.NetMsgAt o idx tr)) ∧
      (Step.aliceStart a b idStateIdx regIdxB bh).next tr =
        localAliceStartTr tr a b (CompTrace.aliceOut tr ikA ikB spk pqpk opk) := by
  have hnext_eq : (Step.aliceStart a b idStateIdx regIdxB bh).next tr =
      ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val :=
    stepIn_next DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, bh) tr
  have hok_eq : ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).1.isSome = true :=
    (stepIn_ok DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, bh) tr).symm.trans hok
  rw [hnext_eq]
  have hP : tr.length + 7 ≤ ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val.length →
      ∃ ikA ikB spk spkSig pqpk pqpkSig opk,
        CompTrace.NetMsgAt spk bh.spk tr ∧ CompTrace.NetMsgAt spkSig bh.spkSig tr ∧
        CompTrace.NetMsgAt pqpk bh.pqpk tr ∧ CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr ∧
        ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ CompTrace.NetMsgAt o idx tr)) ∧
        ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val =
          localAliceStartTr tr a b (CompTrace.aliceOut tr ikA ikB spk pqpk opk) := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false })
      only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine bind_aliceHandshake_at_local
      (Inv := fun t => tr.length + 7 ≤ t.length →
        ∃ ikA ikB spk spkSig pqpk pqpkSig opk,
          CompTrace.NetMsgAt spk bh.spk tr ∧ CompTrace.NetMsgAt spkSig bh.spkSig tr ∧
          CompTrace.NetMsgAt pqpk bh.pqpk tr ∧ CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr ∧
          ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ CompTrace.NetMsgAt o idx tr)) ∧
          t = localAliceStartTr tr a b (CompTrace.aliceOut tr ikA ikB spk pqpk opk))
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
      CompTrace.run_bind_fst, CompTrace.run_bind_snd, DY.Traceful.run_mk, DY.Traceful.run_pure,
      length_append_entry, Nat.add_assoc]
    rfl
  refine hP ?_
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false })
    only [DY.Libsignal.Composed.aliceStart_eq_inline] at hok_eq ⊢
  obtain ⟨w, hhs, _, _⟩ := run_bind_isSome hok_eq
  rw [CompTrace.run_bind_snd, hhs]
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
    CompTrace.run_bind_fst, CompTrace.run_bind_snd, DY.Traceful.run_mk, DY.Traceful.run_pure, length_append_entry]
  omega

theorem memoInjGt7_iniAliceStartState {S : OpaqueSymbolSemantics} {g : Ghost}
    (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    (hikA : MemoInjGt7 S g o.ikA) (hikB : MemoInjGt7 S g o.ikB)
    (hspk : MemoInjGt7 S g o.spk)
    (hrk : MemoInjGt7 S g o.keys.rk) (hck : MemoInjGt7 S g o.keys.ck) (hpqr : MemoInjGt7 S g o.keys.pqr)
    (hdhsA : MemoInjGt7 S g (randTerm (tr.length + 2) 32)) :
    MemoInjGt7 S g (DY.Comparse.serialize
      (⟨a, localAliceStartState tr b o⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  have hcc := memoInjGt7_createChain hrk hspk hdhsA
  refine memoInjGt7_serialize_local_tr (memoInjGt7_serializedIk hikA) (memoInjGt7_serializedIk hikB)
    hcc.1 hdhsA hcc.2 (memoInjGt7_concat (memoInjGt7_dhPk hdhsA) hrk)
    (memoInjGt7_spqrInit hpqr (memoInjGt7_lit S g _)) (fun d hd => ?_)
  simp only [localAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨hspk, hck⟩

theorem runSteps_append_local : ∀ (xs ys : List Step) (tr : ExecTrace),
    runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr)
  | [], _, _ => rfl
  | _ :: xs, ys, _ => runSteps_append_local xs ys _

theorem stepsWF_split : ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
    StepsWF (ss₁ ++ ss₂) tr → StepsWF ss₁ tr ∧ StepsWF ss₂ (runSteps ss₁ tr)
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: ss₁, ss₂, _, ⟨hp, hl, hrest⟩ =>
    let ⟨h1, h2⟩ := stepsWF_split ss₁ ss₂ _ hrest
    ⟨⟨hp, hl, h1⟩, h2⟩

theorem reachable_of_stepsWF : ∀ (xs : List Step) {tr : ExecTrace},
    tr.Reachable DY.Libsignal.Composed.reachability →
    StepsWF xs tr →
    (runSteps xs tr).Reachable DY.Libsignal.Composed.reachability
  | [], _, hr, _ => hr
  | x :: xs, _, hr, ⟨hp, _, hrest⟩ =>
    reachable_of_stepsWF xs (DY.Trace.Reachable.Step x.toInput hp hr) hrest

theorem at?_append_other_eq {E E' : Type}
    [DY.ExecTraceTypes.Has E] [DY.ExecTraceTypes.Has E']
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E') = none)
    (j : Nat) : ((tr.append e).at? j : Option E') = (tr.at? j : Option E') := by
  by_cases hj : j < tr.length
  · exact Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr e hj
  · by_cases hjeq : j = tr.length
    · subst hjeq
      rw [Symbolic.Swarm.CREF.at?_append_length, hnone,
        Symbolic.Swarm.CREF.at?_ge_length tr (Nat.le_refl _)]
    · have hlen : (tr.append e).length = tr.length + 1 := length_append_entry tr e
      rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) (by omega),
        Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]

theorem at?_runSteps_invisible {E : Type} [DY.ExecTraceTypes.Has E]
    (hnone : ∀ m : DY.Bytes,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (⟨m⟩ : DY.Network.ExecEntryT) : ExecTrace.Entry) :
        Option E) = none) :
    ∀ {xs : List Step} (tr : ExecTrace),
      (∀ x ∈ xs, x.cls = .invisible) →
      ∀ j : Nat, ((runSteps xs tr).at? j : Option E) = (tr.at? j : Option E)
  | [], _, _, _ => rfl
  | x :: xs, tr, hinv, j => by
    obtain ⟨m, rfl⟩ := invisible_step_eq_network (hinv x List.mem_cons_self)
    simp only [runSteps, Symbolic.Proofs.Swarm.UA.BI.Step.next_network]
    rw [at?_runSteps_invisible hnone _ (fun y hy => hinv y (List.mem_cons_of_mem _ hy)) j,
      at?_append_other_eq tr (⟨m⟩ : DY.Network.ExecEntryT) (hnone m) j]

def NoTRState (tr : ExecTrace) : Prop :=
  ∀ j : Nat, (tr.at? j : Option CompTrace.TRStEntry) = none

theorem noTRState_nil : NoTRState (DY.Trace.nil : ExecTrace) := by
  intro j
  exact Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
    (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])

theorem noTRState_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : NoTRState tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none) :
    NoTRState (tr.append e) :=
  fun j => (at?_append_other_eq tr e hnone j).trans (h j)

theorem noTRState_setupTrace (r : ProtocolSetup) : NoTRState (setupTrace r) := by
  have hgen (n : Nat) : CompTrace.Preserves NoTRState (DY.Random.genRand n) :=
    fun tr h => (genRand_run n tr).2 ▸ noTRState_append_other h (CompTrace.RndE n) rfl
  have hsend (m : DY.Bytes) : CompTrace.Preserves NoTRState (DY.Network.sendMessage m) :=
    fun tr h => (sendMessage_run m tr).2 ▸ noTRState_append_other h (CompTrace.NetE m) rfl
  have hlog (ev : DY.Libsignal.PQXDH.PQXDHEvent) : CompTrace.Preserves NoTRState (DY.ProtocolEvent.logEvent ev) :=
    fun tr h => (logEvent_pq_run ev tr).2 ▸ noTRState_append_other h (CompTrace.PQEvE ev) rfl
  have hst (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
      CompTrace.Preserves NoTRState (DY.PersistentLocalState.storeLocalState me st) :=
    fun tr h => (storeLocalState_pq_run me st tr).2 ▸ noTRState_append_other h (CompTrace.PQStE me st) rfl
  have hgk (p : Participant) (idx : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
      CompTrace.Preserves NoTRState (DY.Libsignal.PQXDH.getKey p idx k) := by
    unfold DY.Libsignal.PQXDH.getKey
    exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p idx) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
  have hreg (p : Participant) : CompTrace.Preserves NoTRState (DY.Libsignal.PQXDH.registerIdentity p) := by
    unfold DY.Libsignal.PQXDH.registerIdentity
    exact CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
      CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hlog _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => hst p _
  have hspk (b : Participant) (idS : Nat) : CompTrace.Preserves NoTRState (DY.Libsignal.PQXDH.genSignedPrekey b idS) := by
    unfold DY.Libsignal.PQXDH.genSignedPrekey
    exact CompTrace.Preserves.bind (hgk b idS .identity) fun _ =>
      CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hlog _) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hpq (b : Participant) (idS : Nat) : CompTrace.Preserves NoTRState (DY.Libsignal.PQXDH.genPQPrekey b idS) := by
    unfold DY.Libsignal.PQXDH.genPQPrekey
    exact CompTrace.Preserves.bind (hgk b idS .identity) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hlog _) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hopk (b : Participant) : CompTrace.Preserves NoTRState (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
    unfold DY.Libsignal.PQXDH.genOneTimePrekey
    exact CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hlog _) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hact : CompTrace.Preserves NoTRState (setupAct r.alice r.bob r.withOpk) := by
    unfold setupAct
    refine CompTrace.Preserves.bind (hreg r.alice) fun _ => ?_
    refine CompTrace.Preserves.bind (hreg r.bob) fun hB => ?_
    refine CompTrace.Preserves.bind (hspk r.bob hB) fun _ => ?_
    refine CompTrace.Preserves.bind (hpq r.bob hB) fun _ => ?_
    cases r.withOpk
    · exact CompTrace.Preserves.pure ()
    · simp only [↓reduceIte]
      exact CompTrace.Preserves.bind (hopk r.bob) fun _ => CompTrace.Preserves.pure ()
  exact hact DY.Trace.nil noTRState_nil

theorem at?_trSt_localAliceStartTr_of_noTRState {tr : ExecTrace} (htr : NoTRState tr)
    (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) :
    ((localAliceStartTr tr a b o).at? j : Option CompTrace.TRStEntry) =
      if j = tr.length + 8 then some (CompTrace.TRStE a (localAliceStartState tr b o)) else none := by
  by_cases hj : j = tr.length + 8
  · subst hj; simp only [↓reduceIte]; at?_localAliceStartTr_tac
  · simp only [hj, ↓reduceIte]
    by_cases hlt : j < tr.length + 8
    · dsimp only [localAliceStartTr]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
        at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
        at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
        at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, htr j]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by dsimp only [localAliceStartTr]; simp only [length_append_entry]; omega)]

def NoCompOrBreak (tr : ExecTrace) : Prop :=
  ∀ j ev, (tr.at? j : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev) →
    (∀ b ik, ev ≠ .CompromisedIK b ik) ∧ ev ≠ .BrokenDH

theorem noCompOrBreak_nil : NoCompOrBreak (DY.Trace.nil : ExecTrace) := by
  intro j ev h
  rw [Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
    (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])] at h
  cases h

theorem noCompOrBreak_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : NoCompOrBreak tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.PQXDHEntry) = none) :
    NoCompOrBreak (tr.append e) := by
  intro j ev hat
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h j ev h0
  · rw [hnone] at hp; cases hp

theorem noCompOrBreak_append_pqEv {tr : ExecTrace} (h : NoCompOrBreak tr)
    (ev₀ : DY.Libsignal.PQXDH.PQXDHEvent)
    (h₀ : (∀ b ik, ev₀ ≠ .CompromisedIK b ik) ∧ ev₀ ≠ .BrokenDH) :
    NoCompOrBreak (tr.append (CompTrace.PQEvE ev₀)) := by
  intro j ev hat
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h j ev h0
  · rw [Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq] at hp
    cases hp; exact h₀

theorem noCompOrBreak_setupTrace (r : ProtocolSetup) : NoCompOrBreak (setupTrace r) := by
  have hgen (n : Nat) : CompTrace.Preserves NoCompOrBreak (DY.Random.genRand n) :=
    fun tr h => (genRand_run n tr).2 ▸ noCompOrBreak_append_other h (CompTrace.RndE n) rfl
  have hsend (m : DY.Bytes) : CompTrace.Preserves NoCompOrBreak (DY.Network.sendMessage m) :=
    fun tr h => (sendMessage_run m tr).2 ▸ noCompOrBreak_append_other h (CompTrace.NetE m) rfl
  have hst (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
      CompTrace.Preserves NoCompOrBreak (DY.PersistentLocalState.storeLocalState me st) :=
    fun tr h => (storeLocalState_pq_run me st tr).2 ▸ noCompOrBreak_append_other h (CompTrace.PQStE me st) rfl
  have hlog (ev : DY.Libsignal.PQXDH.PQXDHEvent) (hev : (∀ b ik, ev ≠ .CompromisedIK b ik) ∧ ev ≠ .BrokenDH) :
      CompTrace.Preserves NoCompOrBreak (DY.ProtocolEvent.logEvent ev) :=
    fun tr h => (logEvent_pq_run ev tr).2 ▸ noCompOrBreak_append_pqEv h ev hev
  have hgk (p : Participant) (idx : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
      CompTrace.Preserves NoCompOrBreak (DY.Libsignal.PQXDH.getKey p idx k) := by
    unfold DY.Libsignal.PQXDH.getKey
    exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p idx) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
  have hreg (p : Participant) : CompTrace.Preserves NoCompOrBreak (DY.Libsignal.PQXDH.registerIdentity p) := by
    unfold DY.Libsignal.PQXDH.registerIdentity
    exact CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
      CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hlog _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => hst p _
  have hspk (b : Participant) (idS : Nat) : CompTrace.Preserves NoCompOrBreak (DY.Libsignal.PQXDH.genSignedPrekey b idS) := by
    unfold DY.Libsignal.PQXDH.genSignedPrekey
    exact CompTrace.Preserves.bind (hgk b idS .identity) fun _ =>
      CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hlog _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hpq (b : Participant) (idS : Nat) : CompTrace.Preserves NoCompOrBreak (DY.Libsignal.PQXDH.genPQPrekey b idS) := by
    unfold DY.Libsignal.PQXDH.genPQPrekey
    exact CompTrace.Preserves.bind (hgk b idS .identity) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hgen 64) fun _ =>
      CompTrace.Preserves.bind (hlog _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hopk (b : Participant) : CompTrace.Preserves NoCompOrBreak (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
    unfold DY.Libsignal.PQXDH.genOneTimePrekey
    exact CompTrace.Preserves.bind (hgen 32) fun _ =>
      CompTrace.Preserves.bind (hlog _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ =>
      CompTrace.Preserves.bind (hst b _) fun _ =>
      CompTrace.Preserves.bind (hsend _) fun _ => CompTrace.Preserves.pure _
  have hact : CompTrace.Preserves NoCompOrBreak (setupAct r.alice r.bob r.withOpk) := by
    unfold setupAct
    refine CompTrace.Preserves.bind (hreg r.alice) fun _ => ?_
    refine CompTrace.Preserves.bind (hreg r.bob) fun hB => ?_
    refine CompTrace.Preserves.bind (hspk r.bob hB) fun _ => ?_
    refine CompTrace.Preserves.bind (hpq r.bob hB) fun _ => ?_
    cases r.withOpk
    · exact CompTrace.Preserves.pure ()
    · simp only [↓reduceIte]
      exact CompTrace.Preserves.bind (hopk r.bob) fun _ => CompTrace.Preserves.pure ()
  exact hact DY.Trace.nil noCompOrBreak_nil

theorem getMessageSentAt_of_netMsgAt {tr : ExecTrace} {idx : Nat} {m : DY.Bytes}
    (h : CompTrace.NetMsgAt m idx tr) : tr.getMessageSentAt idx = some m := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  unfold CompTrace.NetMsgAt at h
  simp [h]

theorem at?_pqSt_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) :
    ((localAliceStartTr tr a b o).at? j : Option CompTrace.PQXDHEntry) =
      ((localAliceStartTr tr a b o).at? j : Option CompTrace.PQXDHEntry) ∧
    ((localAliceStartTr tr a b o).at? j : Option CompTrace.PQXDHStEntry) =
      (tr.at? j : Option CompTrace.PQXDHStEntry) := by
  refine ⟨rfl, ?_⟩
  dsimp only [localAliceStartTr]
  rw [at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
    at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
    at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl]

theorem memoInjGt7_of_setupRandAt
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hwf : ProtocolSetupWF r) (hcompat : GhostAndSemMatchSetup compI0 r S g)
    {idx sz : Nat} (hsz : sz = 32 ∨ sz = 64)
    (hrand : Symbolic.Swarm.COMPOSED.CompInv.RandAt (setupTrace r) idx sz) :
    MemoInjGt7 S g (randTerm idx sz) := by
  have hlt : idx < (setupTrace r).length :=
    Nat.lt_of_not_ge fun hge => by
      unfold Symbolic.Swarm.COMPOSED.CompInv.RandAt at hrand
      rw [Symbolic.Swarm.CREF.at?_ge_length (setupTrace r) hge] at hrand
      cases hrand
  have hni : idx ∈ newIndices DY.Trace.nil (setupTrace r) := by
    unfold newIndices
    have h0 : (DY.Trace.nil : ExecTrace).length = 0 := by
      simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
    rw [h0, Nat.sub_zero]
    exact List.mem_range'.mpr ⟨idx, hlt, by omega⟩
  have hmem_sr : (idx, sz) ∈ setupRandomsAt r := by
    unfold setupRandomsAt
    refine List.mem_filterMap.mpr ⟨idx, hni, ?_⟩
    unfold Symbolic.Swarm.COMPOSED.CompInv.RandAt at hrand
    simp [hrand]
  have hσ_eq := hcompat.1 (idx, sz) hmem_sr
  have hfr_len := hwf.2.1 (idx, sz) hmem_sr
  have hgt7 : 7 < (g.σ idx sz).length := by
    rw [hσ_eq, hfr_len]
    rcases hsz with rfl | rfl <;> omega
  exact memoInjGt7_randTerm (.inr hgt7)

theorem pqEv_before_localAliceStartTr
    {tr₀ tr₁ : ExecTrace} {pre : List Step}
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (htr₁ : tr₁ = runSteps pre tr₀)
    (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    {ev : DY.Libsignal.PQXDH.PQXDHEvent} {k : Nat}
    (hev : (localAliceStartTr tr₁ a b o).EventLoggedAt ev k)
    (hne : ∀ a' b' ikA' ikB' spk' pq' opk' ek' ct' keys',
      ev ≠ .AliceDone a' b' ikA' ikB' spk' pq' opk' ek' ct' keys') :
    k < tr₀.length ∧ k < tr₁.length := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  have hk_lt_tr₂ : k < (localAliceStartTr tr₁ a b o).length :=
    Nat.lt_of_not_ge fun hge => by
      rw [Symbolic.Swarm.CREF.at?_ge_length _ hge] at hev; cases hev
  have hlen₂ : (localAliceStartTr tr₁ a b o).length = tr₁.length + 9 := by
    dsimp only [localAliceStartTr]; simp only [length_append_entry]
  have hk_lt_tr₁ : k < tr₁.length := by
    by_contra hge₁
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := getEventAt_pq_localAliceStartTr tr₁ a b o
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at p0 p1 p2 p3 p4 p5 p6 p7 p8
    have hd : k = tr₁.length ∨ k = tr₁.length + 1 ∨ k = tr₁.length + 2 ∨ k = tr₁.length + 3 ∨
        k = tr₁.length + 4 ∨ k = tr₁.length + 5 ∨ k = tr₁.length + 6 ∨ k = tr₁.length + 7 ∨
        k = tr₁.length + 8 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hev] at p0; cases p0
    · rw [hev] at p1; cases p1
    · rw [hev] at p2; cases p2
    · rw [hev] at p3; cases p3
    · rw [hev] at p4; cases p4
    · rw [hev] at p5; injection p5 with hp5; exact hne _ _ _ _ _ _ _ _ _ _ hp5
    · rw [hev] at p6; cases p6
    · rw [hev] at p7; cases p7
    · rw [hev] at p8; cases p8
  have hat₁ : (tr₁.at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev) := by
    dsimp only [localAliceStartTr] at hev
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by omega)] at hev
    exact hev
  have hat₀ : (tr₀.at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev) := by
    rw [htr₁, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv k] at hat₁
    exact hat₁
  have hk_lt_tr₀ : k < tr₀.length :=
    Nat.lt_of_not_ge fun hge => by
      rw [Symbolic.Swarm.CREF.at?_ge_length tr₀ hge] at hat₀; cases hat₀
  exact ⟨hk_lt_tr₀, hk_lt_tr₁⟩

theorem randAt_before_localAliceStartTr
    {tr₀ tr₁ : ExecTrace} {pre : List Step}
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (htr₁ : tr₁ = runSteps pre tr₀)
    (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    {idx sz : Nat} (hlt₁ : idx < tr₁.length)
    (hr : Symbolic.Swarm.COMPOSED.CompInv.RandAt (localAliceStartTr tr₁ a b o) idx sz) :
    Symbolic.Swarm.COMPOSED.CompInv.RandAt tr₀ idx sz := by
  unfold Symbolic.Swarm.COMPOSED.CompInv.RandAt at hr ⊢
  dsimp only [localAliceStartTr] at hr
  rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by omega)] at hr
  rw [htr₁, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv idx] at hr
  exact hr

theorem matchesEvents_singleton_run
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr₀ : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (hme : MatchesEvents compI0 r S g tr₀ ss [.run ev0] vis) :
    ∃ pre s post,
      ss = pre ++ s :: post ∧
      (∀ x ∈ pre, x.cls = .invisible) ∧
      (∀ x ∈ post, x.cls = .invisible) ∧
      RunMatches compI0 r S g (runSteps pre tr₀) s ev0 vis none := by
  cases hme with
  | run0 _ hRej _ => exact False.elim (no_runRejected_ev0 hRej)
  | run1 hpre_inv hRun hRest =>
    cases hRest with
    | nil hpost_inv =>
      rw [List.append_nil]
      exact ⟨_, _, _, rfl, hpre_inv, hpost_inv, hRun⟩

theorem prefixTerms_memoInjGt7_ev0
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hex : Explains compI0 r S g ss vis [.run ev0]) :
    ∀ t ∈ prefixTerms r (runTrace r ss) vis, MemoInjGt7 S g t := by
  obtain ⟨hcompat, hgwf, ⟨_, hreach₀, hswf, _⟩, hme⟩ := hex
  set tr₀ := setupTrace r
  obtain ⟨pre, s, post, rfl, hpre_inv, hpost_inv, hRun⟩ := matchesEvents_singleton_run hme
  set v := vis
  set tr₁ := runSteps pre tr₀ with htr₁_def
  obtain ⟨hswf_pre, hs_pre, _, _⟩ := stepsWF_split pre (s :: post) tr₀ hswf
  have hreach₁ : tr₁.Reachable reachability := reachable_of_stepsWF pre hreach₀ hswf_pre
  have hreach₂ : (s.next tr₁).Reachable reachability :=
    DY.Trace.Reachable.Step s.toInput hs_pre hreach₁
  obtain ⟨_, _, hfits, hpeer, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, _⟩ := hRun
  have ⟨addr₀, pth₀, hcmd₀⟩ : ∃ addr pth, ev0.cmd = .init addr pth := ⟨_, _, rfl⟩
  rw [hcmd₀] at hfits
  cases hs_eq : s with
  | aliceStart a b idS regB hb =>
    rw [hs_eq] at hpeer hok hv_eq hreach₂
    have hb_eq : b = r.bob := hpeer
    subst hb_eq
    obtain ⟨ikA, ikB, spk, spkSig, pqpk, pqpkSig, opk,
      hspk, hspkSig, hpq, hpqSig, hopk, hnext⟩ := aliceStart_ok_eq_localAliceStartTr hok
    set o₀ := CompTrace.aliceOut tr₁ ikA ikB spk pqpk opk
    have hreach_la : (localAliceStartTr tr₁ a r.bob o₀).Reachable reachability := by
      rwa [← hnext]
    dsimp only [stepView] at hv_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h), hnext,
      exposures_localAliceStartTr, List.append_nil] at hv_eq
    have hopk_none : opk = none := by
      rcases hopk with ⟨_, hopk_n⟩ | ⟨idx, u, hhb_s, _, hu⟩
      · exact hopk_n
      · exfalso
        have hv_al := hv_eq.trans (aliceVis_localAliceStartTr tr₁ a r.bob o₀ hb)
        rw [hv_split] at hv_al
        injection hv_al with hinp_eq _
        have hkind₀ : inputKind ev0 = .recv := rfl
        rw [hkind₀, hinp_eq] at hinp
        have hrec5 : received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) =
            [spk, spkSig, pqpk, pqpkSig, u] := by
          rw [hhb_s]
          change received tr₁ [hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig, idx] = [spk, spkSig, pqpk, pqpkSig, u]
          simp only [received, List.filterMap_cons, List.filterMap_nil,
            getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig,
            getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig,
            getMessageSentAt_of_netMsgAt hu]
        have hbm := hinp.2
        dsimp only at hbm
        rw [hrec5] at hbm
        exact ev0_input_getElem4_ne_one hbm.2.1
    subst hopk_none
    set o := CompTrace.aliceOut tr₁ ikA ikB spk pqpk none
    have hv_al : v =
        { kind := .recv, terms := received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList),
          layout := .bundle, anchor := none } ::
        rngEntry (randTerm tr₁.length 32) ::
        (kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
          [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }]) :=
      hv_eq.trans (aliceVis_localAliceStartTr tr₁ a r.bob o hb)
    have hmem_ek : rngEntry (randTerm tr₁.length 32) ∈ v := by
      rw [hv_al]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hek_gt7 : MemoInjGt7 S g (randTerm tr₁.length 32) := by
      have hlen := hgwf.1 _ hmem_ek rfl tr₁.length 32 (by decide) (List.mem_singleton.mpr rfl)
      exact memoInjGt7_randTerm (.inr (by omega))
    have hmem_ent : (⟨.rng, [randTerm (tr₁.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ v := by
      rw [hv_al]
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
      unfold kyberCoinEntries
      exact List.mem_map.mpr ⟨0, by decide, rfl⟩
    have hent_gt7 : MemoInjGt7 S g (randTerm (tr₁.length + 1) 32) := by
      have hlen := hgwf.1 _ hmem_ent rfl (tr₁.length + 1) 32 (by decide) (List.mem_singleton.mpr rfl)
      exact memoInjGt7_randTerm (.inr (by omega))
    have hmem_dhs : ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry) ∈ v := by
      rw [hv_al]
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
    have htr₃_eq : runTrace r (pre ++ Step.aliceStart a r.bob idS regB hb :: post) =
        runSteps post (localAliceStartTr tr₁ a r.bob o) := by
      unfold runTrace
      rw [runSteps_append_local]
      change runSteps (Step.aliceStart a r.bob idS regB hb :: post) tr₁ = _
      dsimp only [runSteps]
      rw [hnext]
    rw [htr₃_eq]
    set tr₃ := runSteps post (localAliceStartTr tr₁ a r.bob o) with htr₃_def
    have hv_not_send_pt : ∀ w ∈ v, w.kind ≠ .send ∧ w.kind ≠ .pt := by
      intro w hw
      rw [hv_al] at hw
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
        · obtain ⟨w, hw_f, _⟩ := List.mem_flatMap.mp hsend
          obtain ⟨hw_v, hw_k⟩ := List.mem_filter.mp hw_f
          simp only [beq_iff_eq] at hw_k
          exact False.elim ((hv_not_send_pt w hw_v).1 hw_k)
        · obtain ⟨ls, hls_mem, rfl⟩ := List.mem_map.mp hst
          unfold storedStates at hls_mem
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hls_mem
          unfold ExecTrace.getLocalStateAt at hj
          have hnoTR₁ : NoTRState tr₁ := fun k => by
            rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv k]
            exact noTRState_setupTrace r k
          have hat_tr : (tr₃.at? j : Option CompTrace.TRStEntry) =
              if j = tr₁.length + 8 then some (CompTrace.TRStE a (localAliceStartState tr₁ r.bob o)) else none := by
            rw [htr₃_def, at?_runSteps_invisible (fun _ => rfl) _ hpost_inv j,
              at?_trSt_localAliceStartTr_of_noTRState hnoTR₁ a r.bob o j]
          change ((tr₃.at? j : Option CompTrace.TRStEntry).map (·.st)) = some ls at hj
          rw [hat_tr] at hj
          by_cases hj8 : j = tr₁.length + 8
          · simp only [hj8, ↓reduceIte, Option.map_some, Option.some.injEq] at hj
            subst hj
            exact memoInjGt7_iniAliceStartState tr₁ a r.bob o
              ho_ikA_gt7 ho_ikB_gt7 ho_spk_gt7 hkeys_gt7.1 hkeys_gt7.2.1 hkeys_gt7.2.2 hdhs_gt7
          · simp only [hj8, ↓reduceIte, Option.map_none] at hj; cases hj
      · unfold storedSecrets at hsec
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hsec
        unfold ExecTrace.getLocalStateAt at hi
        have hat_pq : (tr₃.at? i : Option CompTrace.PQXDHStEntry) = (tr₀.at? i : Option CompTrace.PQXDHStEntry) := by
          rw [htr₃_def, at?_runSteps_invisible (fun _ => rfl) _ hpost_inv i,
            (at?_pqSt_localAliceStartTr tr₁ a r.bob o i).2,
            htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv i]
        change (((tr₃.at? i : Option CompTrace.PQXDHStEntry).map (·.st)).map DY.Comparse.serialize) = some t at hi
        rw [hat_pq] at hi
        rcases hat₀ : (tr₀.at? i : Option CompTrace.PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
        · simp [hat₀] at hi
        · simp only [hat₀, Option.map_some, Option.some.injEq] at hi
          subst hi
          have hkind := (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr₀ hreach₀).stOK
            p st i hat₀
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
      obtain ⟨w, hw_f, _⟩ := List.mem_flatMap.mp hpt
      obtain ⟨hw_v, hw_k⟩ := List.mem_filter.mp hw_f
      simp only [beq_iff_eq] at hw_k
      exact False.elim ((hv_not_send_pt w hw_v).2 hw_k)
  | _ => rw [hs_eq] at hfits; cases hfits

/-- Split 1 (`ev1`, `"first"`, 5B `.send`): all `assumedInjective` memo entries in `prefixTerms`
on `[.run ev0]` have length `> 7`, contradicting `ev1.input.length = 5`. -/
theorem not_nextEventCollides_ev1
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hex : Explains compI0 r S g ss vis [.run ev0]) :
    ¬ NextEventCollides compI0 r S g ss vis [.run ev0] ev1 := by
  intro hcol
  have hcmd : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  set tr := runTrace r ss
  have hrand : gamma' compI0 S g (randTerm tr.length 32) =
      { bytes := g.σ tr.length 32, shape := randTerm tr.length 32,
        memo := [(randTerm tr.length 32, randTerm tr.length 32, g.σ tr.length 32)] } :=
    gamma'_randTerm compI0 S g tr.length 32 (by decide)
  have hσ_ev1 : g.σ tr.length 32 = ev1.input := by
    have hbme := hcol.1.2
    dsimp only [ptEntryAt, List.map_cons, List.map_nil] at hbme
    change [ (gamma' compI0 S g (randTerm tr.length 32)).bytes ] = [ev1.input] at hbme
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
    have hgt : 7 < x₂.2.2.length := prefixTerms_memoInjGt7_ev0 hwf hex t ht_mem x₂ hx₂_mem hinj₂
    have hlen5 : x₂.2.2.length = 5 := by
      rw [← hbytes_eq, hσ_ev1, ev1_input_len]
    omega
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hrand, List.mem_singleton] at hx₂_new
    subst hx₂_new
    exact hsh_ne rfl

unseal DY.Bytes in
instance localSubSym (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSym compI0) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubTrunc (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubTrWire (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubKemEncap (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap compI0) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubSpqrSendState (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubSpqrSendKey (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubSpqrSendMsg (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance localSubSpqrChainKey (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll compI0 S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩


end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
