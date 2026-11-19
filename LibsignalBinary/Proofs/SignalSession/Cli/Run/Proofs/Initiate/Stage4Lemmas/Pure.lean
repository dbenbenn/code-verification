/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAlice -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Stage 4 Pure Algebra, Model Agreement, and Callee Bridges

Symbolic-address resolution, `TraceFsSound` segment lifts, stack-frame arithmetic, SPQR initial
state length bounds, non-contributory DH model agreement, and contract-parameterized (`Ext`)
Stage 4 cut-point and callee bundles.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Symbolic Offset and Call-Target Address Resolution -/

theorem bv64_ofNat_add_eq_of_mod {a b c : Nat}
    (h : (a + b) % 2 ^ 64 = c % 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod, h]

@[simp 2000]
theorem s4_sepExists_left {α : Type _} (f : α → SepProp) (Q : SepProp) :
    (sepExists f) ∗ Q = sepExists (fun a => f a ∗ Q) :=
  sepExists_sepConj_left f Q

macro "s4_elim_exists " x:ident : tactic =>
  `(tactic| (
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    conv => arg 4; repeat rw [sepExists_sepConj_left]
    conv => arg 4; repeat rw [sepExists_sepConj_right]
    refine SepWPp.exists_elim fun $x => ?_))

theorem s4_pure_swap (P : SepProp) (φ : Prop) (Q : SepProp) :
    P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) := by ac_rfl

theorem s4_pure_tail (P : SepProp) (φ : Prop) :
    P ∗ ⌜φ⌝ = ⌜φ⌝ ∗ P := sepConj_comm P ⌜φ⌝

macro "s4_pure_elim" : tactic =>
  `(tactic| (
    conv => arg 4; simp only [sepConj_assoc]
    conv => arg 4; try rw [s4_pure_tail]
    conv => arg 4; repeat rw [s4_pure_swap]
    apply SepWPp.pure_elim))

theorem s4_ex_left {α : Type _} (f : α → SepProp) (Q : SepProp) :
    (sepExists f) ∗ Q = sepExists (fun a => f a ∗ Q) :=
  sepExists_sepConj_left f Q

theorem s4_ex_after64 {α : Type _} (a : BitVec 64) (v : BitVec 64) (f : α → SepProp) :
    (a ↦₆₄ v) ∗ (sepExists f) = sepExists (fun x => (a ↦₆₄ v) ∗ f x) :=
  sepExists_sepConj_right (a ↦₆₄ v) f

theorem s4_ex_after32 {α : Type _} (a : BitVec 64) (v : BitVec 32) (f : α → SepProp) :
    (a ↦₃₂ v) ∗ (sepExists f) = sepExists (fun x => (a ↦₃₂ v) ∗ f x) :=
  sepExists_sepConj_right (a ↦₃₂ v) f

macro "s4_exists_eq" : tactic =>
  `(tactic| simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    s4_ex_left, s4_ex_after64, s4_ex_after32])

abbrev S4CsIdx := { n : Nat // 19 ≤ n ∧ n ≤ 29 }

theorem _root_.Arm64.CalleeSavedPreserved.gpr {s0 sf : Arm64.State}
    (h : Arm64.CalleeSavedPreserved s0 sf) (idx : S4CsIdx) :
    sf.readReg64 (.gpr (BitVec.ofNat 5 idx.val)) =
      s0.readReg64 (.gpr (BitVec.ofNat 5 idx.val)) := by
  rcases h with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, _⟩
  rcases idx with ⟨n, hn1, hn2⟩
  have hcases :
      n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
      n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29

theorem files_eq_of_steps_trace_eq {P : Program} (hP : TraceFsSound P)
    {s0 sf : State} (hst : Steps P s0 sf) (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  hP.files_eq hst (by simpa only [List.append_nil] using htr) NoFsEv.nil

theorem sepWPp_steps_post {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post post' Qp : State → SepProp → Prop} {Qo : State → SepProp}
    (hwp : SepWPp prog target s P post Qp Qo)
    (himp : ∀ sf Pf, Steps prog s sf → post sf Pf → post' sf Pf) :
    SepWPp prog target s P post' Qp Qo := by
  intro R hm hL
  obtain ⟨sf, hst, hres⟩ := hwp R hm hL
  refine ⟨sf, hst, ?_⟩
  rcases hres with ⟨hpc, hrun, Pf, hmf, hpost⟩ | rest
  · exact Or.inl ⟨hpc, hrun, Pf, hmf, himp sf Pf hst hpost⟩
  · exact Or.inr rest

theorem sepWPp_seq_files {prog : Program} (hP : TraceFsSound prog)
    {mid target : BitVec 64} {s : State} {P : SepProp}
    {Qm post Qp : State → SepProp → Prop} {Qo : State → SepProp}
    (h1 : SepWPp prog mid s P Qm Qp Qo)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      (sm.trace = s.trace → sm.fs.files = s.fs.files) → Qm sm Pm →
      SepWPp prog target sm Pm post Qp Qo) :
    SepWPp prog target s P post Qp Qo := by
  intro R hm hL
  obtain ⟨sm, hst1, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | rest⟩ := h1 R hm hL
  · have hfs : sm.trace = s.trace → sm.fs.files = s.fs.files :=
      files_eq_of_steps_trace_eq hP hst1
    obtain ⟨sf, hst2, hout⟩ := h2 sm Pm hpcm hrunm hfs hQ R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr rest⟩

/-! ## Stack Budget, Alignment, and Frame Slot Arithmetic -/

theorem stk_sub_le_63 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 63 := by
  omega

theorem coinsFill_stk_le {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    cliCoinsFillStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have hext : extHookStack ≤ 65536 := by decide
  unfold cliCoinsFillStack
  omega

theorem extHook_stk_le {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    extHookStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have hext : extHookStack ≤ 65536 := by decide
  omega

theorem createChain_stk_le {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    createChainStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have hc : createChainStack ≤ 65536 := by decide
  omega

theorem initialState_stk_le {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    CryptoVerification.SpqrV1.Top.InitialState.initialStateStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have hi : CryptoVerification.SpqrV1.Top.InitialState.initialStateStack ≤ 262144 := by decide
  omega

theorem sessionBuild_stk_le {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    Pqxdh.Initiator.sessionBuildStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have hs : Pqxdh.Initiator.sessionBuildStack ≤ 65536 := by decide
  omega

theorem fsp_add_ne_zero {B : RunBudgets} {stk : Nat} {s0 : State}
    (hstk : cliInitiateNeed B ≤ stk) (hspk : stk ≤ s0.sp.toNat)
    (k : Nat) (hk : k < cliInitiateFrame) :
    (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + BitVec.ofNat 64 k ≠ 0#64 := by
  have hge : 524288 ≤ s0.sp.toNat := by
    have h0 : 524288 ≤ cliInitiateNeed B := Nat.le_max_left _ _
    omega
  have hlt : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hframe : cliInitiateFrame = 7408 := rfl
  have hsub : (s0.sp - 7408#64).toNat = s0.sp.toNat - 7408 :=
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
  intro hzero
  have ht := congrArg BitVec.toNat hzero
  rw [hframe] at hk ht
  simp only [BitVec.toNat_add, hsub, BitVec.toNat_ofNat] at ht
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem fsp_aligned_of_s0 {B : RunBudgets} {stk : Nat} {s0 s : State}
    (_hstk : cliInitiateNeed B ≤ stk) (_hspk : stk ≤ s0.sp.toNat)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hal : s0.spAligned = true) :
    s.spAligned = true := by
  have hframe : cliInitiateFrame = 7408 := rfl
  simp only [State.spAligned, hsp, hframe] at hal ⊢
  exact ProofLib.spAligned_sub s0.sp 7408#64 hal (by decide)

/-! ## `hkSlotBytes`, `dk` Lengths, and SPQR State Length Bound -/

theorem dk_lengths_of_keysOk {X : UnreachedPqxdhPrimitives} {W : PEParams} {me : LocalIdentity} {be : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen}
    {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    (h : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me be t) = some (dk, hdr)) :
    (ofU8 dk.rootKey).length = 32 ∧
      (ofU8 dk.pqrKey).length = 32 ∧
      (ofU8 dk.chainKey).length = 32 ∧
      hdr.ekAPk = (modelPrims X W).x25519Base (initiateInput W me be t).ekASk := by
  have hb := Pqxdh.Initiator.Model.initiateKeys_ofSignalPqxdhPrimitives
    (modelPrims X W) (initiateInput W me be t)
  rw [h, Option.map_some] at hb
  have hwf := Pqxdh.Initiator.structuralPrims_initiatorModelPrims X W
  unfold Pqxdh.Initiator.Model.initiateKeys at hb
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hb
  rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2⟩
  generalize Pqxdh.Initiator.buildSecrets _ _ _ _ _ = secrets at h1
  have hlen := Pqxdh.Initiator.deriveDRKeys_lengths (Pqxdh.Initiator.initiatorModelPrims X W) hwf secrets
  dsimp only [Pqxdh.Initiator.Model.deriveDRKeys, Pqxdh.Initiator.initiatorModelPrims] at hlen
  rw [h1] at hlen
  have hek : (Pqxdh.Initiator.ofSignalPqxdhHdr hdr).ekAPk =
      (Pqxdh.Initiator.initiatorModelPrims X W).x25519Base
        (Pqxdh.Initiator.ofSignalPqxdhInitiateKeysInput (initiateInput W me be t)).ekASk := by
    rw [← h2]
  dsimp only [Pqxdh.Initiator.ofSignalPqxdhDRKey, Pqxdh.Initiator.ofSignalPqxdhHdr,
    Pqxdh.Initiator.initiatorModelPrims, Pqxdh.ResponderCore.ofSignalPqxdhPrimitives,
    Pqxdh.Initiator.ofSignalPqxdhInitiateKeysInput] at hlen hek
  simp only [ofU8, List.length_map]
  exact ⟨hlen.1, hlen.2.1, hlen.2.2, hek⟩

theorem hkSlotBytes_eq_append (dk : SignalPqxdh.DRKey) :
    ofU8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++ [0, 0, 0, 0]) =
      ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32 := by
  simp only [ofU8, List.map_append]
  rfl

private theorem encodeBytesField_len_of_len32 (tag : BitVec 32) {b : List (BitVec 8)}
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

theorem spqrInitialState_pqLen_le_1208 (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (k : BitVec 256) :
    (LibsignalSpqrV1.spqrV1Init F K .a2b k).length ≤ 1208 := by
  rw [← SpqrV1.Top.InitialState.initialStateValue_libsignal F K .a2b k]
  let au := LibsignalSpqrV1.Authenticator.new F (HMAC.keyToBytes32 k) 1#64
  have hpb : (SpqrV1.Top.InitInner.initV1State F .a2b (HMAC.keyToBytes32 k)).into_pb =
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := au.rootKey, macKey := au.macKey } } }) } := rfl
  have hrk := encodeBytesField_len_of_len32 1#32 (b := au.rootKey)
    (by simp [au, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked])
  have hmk := encodeBytesField_len_of_len32 2#32 (b := au.macKey)
    (by simp [au, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked])
  have hak := encodeBytesField_len_of_len32 1#32 (b := HMAC.keyToBytes32 k)
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

/-! ## Non-Contributory DH Error Model Agreement -/

/-- When `SignalPqxdh.Model.initiateKeys` produces `(dk, hdr)` and `rootCreateChain` returns
`.error .invalidKeyAgreement`, the top-level model `initiateState` returns `none`, so
`initDef` evaluates to `some none` (`Err` / rejection). -/
theorem initDef_eq_some_none_of_createChain_err
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {F : FsFiles} {peer me : AddrVal}
    {b : BundleV} {coins : List (BitVec 8)} {be : PreKeyBundleFields}
    {kp : IdentityKeyPair} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    (hbe : bundleEOf? b = some be)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X W)
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)) = some (dk, hdr))
    (hcc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 dk.rootKey))
      ⟨be.spkPub⟩
      ⟨Ratchet.clampScalar ⟨((padCoins coins).toList.drop 160).take 32, by simp; decide⟩⟩ =
      .error .invalidKeyAgreement) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  rw [hbe, htrust, hkp]
  cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
  | error _ => rfl
  | ok reg =>
    dsimp only
    have hkeys_reg : SignalPqxdh.Model.initiateKeys (modelPrims X W)
        (initiateInput W ⟨kp.privateKey.bytes, reg⟩ be (padCoins coins)) = some (dk, hdr) :=
      hkeys
    have heph :
        (KeyPair.generate W.C (HKDF.bytesToKey32
          (((padCoins coins).toList.drop 160).take 32))).privateKey =
        ⟨Ratchet.clampScalar ⟨((padCoins coins).toList.drop 160).take 32, by simp; decide⟩⟩ := by
      unfold KeyPair.generate
      dsimp only
      congr 2
      apply Subtype.ext
      exact Keys.keyToBytes32_bytesToKey32 (((padCoins coins).toList.drop 160).take 32)
        (by simp; decide)
    have hnone : initiateState X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ be (padCoins coins) =
        none := by
      unfold initiateState initializeInitiatorSession
      rw [hkeys_reg]
      dsimp only
      rw [heph, hcc]
      rfl
    rw [hnone]

/-! ## Contract-Parameterized (`Ext`) Cut Points and Callee Bundles -/

theorem createChainStackX_le_stk_sub {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) :
    createChainStackX ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : createChainStackX = 17120 := by decide
  omega

theorem zeroizeSecretSpec_to_cliExt {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry zeroizeSecretSpec) :
    subroutine_ok prog entry CliExt.zeroizeSpec := by
  refine subroutine_ok_map h ?_
  intro a R s0 hpre
  dsimp only [CliExt.zeroizeSpec, CliExt.withStack] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨ha, hpre⟩
  refine ⟨a, stackAt s0.sp extHookStack ∗ R, ?_, ?_⟩
  · dsimp only [zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨ha, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [zeroizeSecretSpec, CliExt.zeroizeSpec, CliExt.withStack] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem derivePublicKeyBytesSpec_to_ext {prog : Program} {entry : BitVec 64} {pubKey : PubKeyFn}
    (h : subroutine_ok prog entry (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok prog entry (derivePublicKeyBytesStackSpec pubKey extHookStack) := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  dsimp only [derivePublicKeyBytesStackSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx, hpre⟩
  refine ⟨x, stackAt s0.sp extHookStack ∗ R, ?_, ?_⟩
  · dsimp only [derivePublicKeyBytesSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [derivePublicKeyBytesSpec, derivePublicKeyBytesStackSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem stackAt_createChainX_split (sp : BitVec 64) :
    stackAt sp createChainStackX =
      stackAt sp createChainStack ∗ memRegion (sp - 17120#64) 12288 := by
  have h1 := Pqxdh.Initiator.stackAt_split_top sp 12288 createChainStack (by decide)
  have h2 : (12288 + createChainStack : Nat) = createChainStackX := by decide
  have h3 : BitVec.ofNat 64 (12288 + createChainStack) = 17120#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

theorem stackAt_createChainExtX_split (sp : BitVec 64) :
    stackAt sp (576 + extractStackExt) =
      stackAt sp createChainStackX ∗ memRegion (sp - 17936#64) 816 := by
  have h1 := Pqxdh.Initiator.stackAt_split_top sp 816 createChainStackX (by decide)
  have h2 : (816 + createChainStackX : Nat) = 576 + extractStackExt := by decide
  have h3 : BitVec.ofNat 64 (816 + createChainStackX) = 17936#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

theorem stackAt_initialStateExt_split (sp : BitVec 64) :
    stackAt sp CryptoVerification.SpqrV1.Top.InitialState.initialStateStackExt =
      stackAt sp CryptoVerification.SpqrV1.Top.InitialState.initialStateStack ∗
        memRegion (sp - 19408#64) 1232 := by
  have h1 := Pqxdh.Initiator.stackAt_split_top sp 1232
    CryptoVerification.SpqrV1.Top.InitialState.initialStateStack (by decide)
  have h2 : (1232 + CryptoVerification.SpqrV1.Top.InitialState.initialStateStack : Nat) =
      CryptoVerification.SpqrV1.Top.InitialState.initialStateStackExt := by decide
  have h3 : BitVec.ofNat 64
      (1232 + CryptoVerification.SpqrV1.Top.InitialState.initialStateStack) = 19408#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
