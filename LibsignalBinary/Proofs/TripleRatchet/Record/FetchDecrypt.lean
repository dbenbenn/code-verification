/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import ProofLib.Sep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

/-!
# Instruction Fetches and `recErrAt` Helpers for `SegDecrypt` and `SegMismatch`

Instruction decode lemmas, fetch macros, `RecordDecryptGhost` model bridges, and 6-word (`words6At`)
spatial decompositions of `speAt` / `recErrAt` for the decrypt and version-mismatch segments of
`session_message_decrypt_signal` (`0x3a4a8`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open Lean Elab Tactic in
/-- `segDecrypt_code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "segDecrypt_code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

namespace SegDecryptFacts

/-! ## Model bridges (`RecordDecryptGhost.model` and `RecordDecryptGhost.draws`) -/

theorem model_of_version_ne (C : Crypto) (S : SpqrModel)
    (x : RecordDecryptGhost) (hne : x.st.version.toNat ≠ x.msg.messageVersion.toNat) :
    (x.model C S uuidTryParse).1 = .error (.invalidMessage .whisper .decryptionFailed) := by
  dsimp [RecordDecryptGhost.model, SessionState.tryDecryptFromRecord, Mut.exec, StateT.run,
    ExceptT.run, ExceptT.mk, pure, Except.pure, Bind.bind, Monad.toBind, ExceptT.bind,
    ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, StateT.lift, throw, throwThe, MonadExceptOf.throw]
  simp [hne]

theorem draws_of_version_ne (C : Crypto) (x : RecordDecryptGhost)
    (hne : x.st.version.toNat ≠ x.msg.messageVersion.toNat) :
    x.draws C = 0 := by
  simp [RecordDecryptGhost.draws, hne]

theorem tapeAfter_zero (ctl : BitVec 64) (cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  simp [tapeAfter, tapeAt]
  exact Entails.pure_left fun _ => Entails.refl _

/-- Ghost state passed to `try_decrypt_with_state` from `VState`. -/
@[expose] def mkTryDecryptGhost (sp : BitVec 64) (x : RecordDecryptGhost) (G₁ : SessionGhost) :
    TryDecryptGhost where
  ret := sp + 0x4b0#64
  ss := sp + 0xca0#64
  G := G₁
  st := x.st
  remA := x.remA
  rem := x.rem
  locA := x.locA
  loc := x.loc
  msgA := x.msgA
  msgG := x.msgG
  msg := x.msg
  msgType := .whisper
  cur := x.cur
  rest := x.rest

theorem draws_eq_tryDecrypt_of_version_eq (C : Crypto) (sp : BitVec 64)
    (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat) :
    x.draws C =
      decryptDraws C (mkTryDecryptGhost sp x G₁).st
        (mkTryDecryptGhost sp x G₁).msg.senderRatchetKey (mkTryDecryptGhost sp x G₁).rest := by
  simp [RecordDecryptGhost.draws, mkTryDecryptGhost, heq]

theorem model_eq_of_version_eq (C : Crypto) (S : SpqrModel)
    (sp : BitVec 64) (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat) :
    x.model C S uuidTryParse =
      match (mkTryDecryptGhost sp x G₁).model C S uuidTryParse with
      | (.ok pt, st') => (.ok pt, st')
      | (.error e, _) => (.error (SessionState.recordError .whisper e), x.st) := by
  dsimp [RecordDecryptGhost.model, TryDecryptGhost.model, mkTryDecryptGhost,
    SessionState.tryDecryptFromRecord, Mut.exec, StateT.run, ExceptT.run, ExceptT.mk,
    pure, Except.pure, Bind.bind, Monad.toBind, ExceptT.bind, ExceptT.bindCont,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, StateT.lift, throw, throwThe, MonadExceptOf.throw]
  simp [heq]
  rcases hrun :
    SessionState.tryDecryptWithState C S.spqr
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc) x.msg .whisper (coinsOf x.rest) x.st with ⟨res, st'⟩
  cases res <;> rfl

theorem model_ok_of_tryDecrypt_ok (C : Crypto) (S : SpqrModel)
    (sp : BitVec 64) (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    {pt : List (BitVec 8)} {st' : SessionState (List (BitVec 8))}
    (h : (mkTryDecryptGhost sp x G₁).model C S uuidTryParse = (.ok pt, st')) :
    x.model C S uuidTryParse = (.ok pt, st') := by
  rw [model_eq_of_version_eq C S sp x G₁ heq, h]

theorem model_err_of_tryDecrypt_err (C : Crypto) (S : SpqrModel)
    (sp : BitVec 64) (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    {e : SignalProtocolError} {st' : SessionState (List (BitVec 8))}
    (h : (mkTryDecryptGhost sp x G₁).model C S uuidTryParse = (.error e, st')) :
    x.model C S uuidTryParse = (.error (SessionState.recordError .whisper e), x.st) := by
  rw [model_eq_of_version_eq C S sp x G₁ heq, h]

theorem model_panic_of_tryDecrypt_panic (C : Crypto) (S : SpqrModel)
    (sp : BitVec 64) (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (h : ((mkTryDecryptGhost sp x G₁).model C S uuidTryParse).1 = .error .panic) :
    (x.model C S uuidTryParse).1 = .error .panic := by
  rw [model_eq_of_version_eq C S sp x G₁ heq]
  rcases hm : (mkTryDecryptGhost sp x G₁).model C S uuidTryParse with ⟨res, st'⟩
  rw [hm] at h
  cases res with
  | ok _ => cases h
  | error e =>
    cases h
    rfl

/-! ## 48-byte `recErrAt` and `speAt` 6-word decomposition lemmas -/

/-- Six consecutive 64-bit words starting at `a` (`48` bytes). -/
@[expose] def words6At (a w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

theorem words6At_entails_memRegion (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    words6At a w0 w1 w2 w3 w4 w5 ⊢ memRegion a 48 := by
  sep_interval

theorem memRegion48_eq_words6At (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        words6At a w0 w1 w2 w3 w4 w5 := by
  unfold words6At
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells a 6 (by decide)]
  repeat (first | rw [cells_succ] | rw [cells_zero])
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]

theorem version_words6At_entails_recErrAt (A : RustAlloc) (a : BitVec 64)
    (v hi : BitVec 32) (w2 w3 w4 w5 : BitVec 64) :
    words6At a (speWord 6) (hi ++ v) w2 w3 w4 w5 ⊢ recErrAt A a (.version v) := by
  unfold words6At recErrAt
  rw [← pointsTo32_pair (a + 8#64) v hi, show a + 8#64 + 4#64 = a + 12#64 by bv_kernel]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (by sep_interval))

/-- Discriminant word 0 of a `SignalProtocolError`. -/
@[expose] def speTag : SignalProtocolError → BitVec 64
  | .invalidState => speWord 1
  | .invalidProtobufEncoding => speWord 2
  | .ciphertextMessageTooShort _ => speWord 3
  | .legacyCiphertextVersion _ => speWord 4
  | .unrecognizedCiphertextVersion _ => speWord 5
  | .noKeyTypeIdentifier => speWord 7
  | .badKeyType _ => speWord 8
  | .badKeyLength _ => speWord 9
  | .invalidKeyAgreement => speWord 10
  | .invalidSessionStructure _ => speWord 20
  | .duplicatedMessage _ _ => speWord 23
  | .invalidMessage _ _ => speWord 24
  | .panic => 0#64

theorem speTag_ne_okTagVec {e : SignalProtocolError} (hne : e ≠ .panic) :
    speTag e ≠ okTagVec := by
  cases e <;> first | exact absurd rfl hne | (dsimp [speTag]; decide)

theorem speTag_eq_speWord23_iff {e : SignalProtocolError} :
    speTag e = speWord 23 ↔ ∃ i c, e = .duplicatedMessage i c := by
  cases e <;> simp [speTag, speWord]

theorem recordError_of_speTag_ne_speWord23 {e : SignalProtocolError}
    (hne : e ≠ .panic) (h23 : speTag e ≠ speWord 23) :
    SessionState.recordError .whisper e = .invalidMessage .whisper .decryptionFailed := by
  cases e with
  | panic => exact absurd rfl hne
  | duplicatedMessage i c => exact absurd rfl h23
  | _ => rfl

private theorem vecU8_eq_bytes24_sep_buf (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦ₛ vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length)) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8
  congr 1; funext cap; congr 1; funext ptr
  exact vecU8At_eq_bytes_sep_buf A a cap ptr bs

private theorem strRefAt_eq_bytes16_sep_ro (a : BitVec 64) (lit : List (BitVec 8)) :
    strRefAt a lit =
      ∃∗ p : BitVec 64,
        (a ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 lit.length))) ∗ (p ↦ᵣ lit) := by
  unfold strRefAt
  congr 1; funext p
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes, sepConj_assoc]

attribute [local irreducible] vecU8Buf

private theorem speAt_tag_region40 (w0 : BitVec 64) (a : BitVec 64) :
    ((a ↦₆₄ w0) ∗ memRegion (a + 8#64) 40) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢ (b ↦₆₄ w0) ∗ memRegion (b + 8#64) 40⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  rw [memRegion_eq_exists_bytes (a + 8#64) 40 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbs
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  refine Entails.pure_right ⟨hbs, fun b => ?_⟩ (by bi_entail)
  rw [sepConj_emp]
  exact sepConj_mono_right (hbs ▸ pointsToBytes_entails_memRegion (b + 8#64) bs)

private theorem speAt_tag_word_region32 (w0 w1 : BitVec 64) (a : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢
          (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ memRegion (b + 16#64) 32⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  rw [pointsTo64_eq_pointsToBytes (a + 8#64),
      memRegion_eq_exists_bytes (a + 16#64) 32 (by decide),
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  have ha16 : ∀ c : BitVec 64, c + 8#64 + BitVec.ofNat 64 (unpack64 w1).length = c + 16#64 := by
    intro c; change c + 8#64 + 8#64 = c + 16#64; bv_kernel
  conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro htail
  refine Entails.sepExists_right (unpack64 w1 ++ tail) (Entails.sepExists_right emp ?_)
  rw [pointsToBytes_append, ha16 a]
  refine Entails.pure_right ⟨by simp [htail], fun b => ?_⟩ (by bi_entail)
  simp only [pointsToBytes_append, ha16 b, ← pointsTo64_eq_pointsToBytes, sepConj_emp]
  exact sepConj_mono_right (sepConj_mono_right (htail ▸ pointsToBytes_entails_memRegion (b + 16#64) tail))

private theorem speAt_tag_byte_region39 (w0 : BitVec 64) (v : BitVec 8) (a : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢
          (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₈ v) ∗ memRegion (b + 9#64) 39⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  rw [memRegion_eq_exists_bytes (a + 9#64) 39 (by decide),
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  have hcons : ∀ d : BitVec 64, ((d + 8#64) ↦₈ v) ∗ ((d + 9#64) ↦ₛ tail) = ((d + 8#64) ↦ₛ (v :: tail)) := by
    intro d
    have hd9 : d + 9#64 = d + 8#64 + 1#64 := by bv_kernel
    rw [hd9, ← pointsToBytes_cons]
  conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro htail
  rw [hcons a]
  refine Entails.sepExists_right (v :: tail) (Entails.sepExists_right emp ?_)
  refine Entails.pure_right ⟨by simp [htail], fun b => ?_⟩ (by bi_entail)
  simp only [← hcons b, sepConj_emp]
  exact sepConj_mono_right (sepConj_mono_right (htail ▸ pointsToBytes_entails_memRegion (b + 9#64) tail))

private theorem speAt_inline_bytes (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (e : SignalProtocolError) (hne : e ≠ .panic) :
    speAt A fnName a e ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ speTag e) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢ speAt A fnName b e⌝ ∗
        (a ↦₆₄ speTag e) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  cases e with
  | panic => exact absurd rfl hne
  | invalidProtobufEncoding | noKeyTypeIdentifier | invalidKeyAgreement =>
    exact speAt_tag_region40 _ a
  | ciphertextMessageTooShort n | badKeyLength n =>
    exact speAt_tag_word_region32 _ _ a
  | duplicatedMessage i c =>
    dsimp only [speAt, speTag]
    have hp : ∀ d : BitVec 64,
        ((d ↦₆₄ speWord 23) ∗ ((d + 8#64) ↦₃₂ i) ∗ ((d + 12#64) ↦₃₂ c) ∗ memRegion (d + 16#64) 32) =
        ((d ↦₆₄ speWord 23) ∗ ((d + 8#64) ↦₆₄ (c ++ i)) ∗ memRegion (d + 16#64) 32) := by
      intro d
      have hd12 : d + 12#64 = d + 8#64 + 4#64 := by bv_kernel
      rw [← sepConj_assoc ((d + 8#64) ↦₃₂ i), hd12, pointsTo32_pair]
    rw [hp a]
    simpa only [hp] using speAt_tag_word_region32 (speWord 23) (c ++ i) a
  | legacyCiphertextVersion v | unrecognizedCiphertextVersion v | badKeyType v =>
    exact speAt_tag_byte_region39 _ v a
  | invalidSessionStructure r =>
    dsimp only [speAt, speTag]
    rw [strRefAt_eq_bytes16_sep_ro (a + 8#64) (invalidSessionStructureStr r),
        memRegion_eq_exists_bytes (a + 24#64) 24 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro p
    have ha24 : ∀ d : BitVec 64,
        d + 8#64 + BitVec.ofNat 64 (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length)).length = d + 24#64 := by
      intro d; change d + 8#64 + 16#64 = d + 24#64; bv_kernel
    conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
    apply Entails.pure_left; intro htail
    refine Entails.sepExists_right (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length) ++ tail)
      (Entails.sepExists_right (p ↦ᵣ invalidSessionStructureStr r) ?_)
    rw [pointsToBytes_append (a + 8#64) (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length)) tail, ha24 a]
    refine Entails.pure_right ⟨by simp [htail], fun b => ?_⟩ (by bi_entail)
    rw [pointsToBytes_append (b + 8#64) (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length)) tail,
        ha24 b, strRefAt_eq_bytes16_sep_ro (b + 8#64) (invalidSessionStructureStr r)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right p ?_
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right
      (htail ▸ pointsToBytes_entails_memRegion (b + 24#64) tail)))
    bi_entail
  | invalidState =>
    dsimp only [speAt, speTag]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    rw [vecU8_eq_bytes24_sep_buf A (a + 8#64) bs, strRefAt_eq_bytes16_sep_ro (a + 32#64) fnName]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro p
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    have ha32 : ∀ d : BitVec 64,
        d + 8#64 + BitVec.ofNat 64 (vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length)).length = d + 32#64 := by
      intro d; change d + 8#64 + 24#64 = d + 32#64; bv_kernel
    refine Entails.sepExists_right
      (vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length) ++
        (unpack64 p ++ unpack64 (BitVec.ofNat 64 fnName.length)))
      (Entails.sepExists_right (vecU8Buf A cap ptr bs ∗ (p ↦ᵣ fnName)) ?_)
    rw [pointsToBytes_append (a + 8#64) (vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length))
          (unpack64 p ++ unpack64 (BitVec.ofNat 64 fnName.length)),
        ha32 a]
    refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (by bi_entail)
    rw [pointsToBytes_append (b + 8#64) (vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length))
          (unpack64 p ++ unpack64 (BitVec.ofNat 64 fnName.length)),
        ha32 b]
    refine Entails.sepExists_right bs ?_
    rw [vecU8_eq_bytes24_sep_buf A (b + 8#64) bs, strRefAt_eq_bytes16_sep_ro (b + 32#64) fnName]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right p (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_))
    bi_entail
  | invalidMessage t r =>
    dsimp only [speAt, speTag]
    have hstr : ∀ d : BitVec 64,
        invalidMessageStrAt A d r ⊢
          ∃∗ bs : List (BitVec 8),
            ⌜∀ c : BitVec 64, vecU8 A c bs ⊢ invalidMessageStrAt A c r⌝ ∗ vecU8 A d bs := by
      intro d
      cases r with
      | tooFarInFuture =>
        exact Entails.sepExists_right tooFarInFutureStr
          (Entails.pure_right (fun _ => Entails.refl _) (Entails.refl _))
      | macFailed =>
        exact Entails.sepExists_right macFailedStr
          (Entails.pure_right (fun _ => Entails.refl _) (Entails.refl _))
      | pqRatchet =>
        apply Entails.sepExists_elim; intro bs
        exact Entails.sepExists_right bs
          (Entails.pure_right (fun c => Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _))
      | badCiphertext =>
        apply Entails.sepExists_elim; intro bs
        exact Entails.sepExists_right bs
          (Entails.pure_right (fun c => Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _))
      | decryptionFailed =>
        dsimp only [invalidMessageStrAt]
        rw [← sepConj_emp (⌜False⌝)]
        exact Entails.pure_left fun h => False.elim h
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (hstr (a + 8#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
    apply Entails.pure_left; intro hr
    rw [vecU8_eq_bytes24_sep_buf A (a + 8#64) bs,
        memRegion_eq_exists_bytes (a + 33#64) 15 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
    apply Entails.pure_left; intro htail
    have ha32 : ∀ d : BitVec 64,
        d + 8#64 + BitVec.ofNat 64 (vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length)).length = d + 32#64 := by
      intro d; change d + 8#64 + 24#64 = d + 32#64; bv_kernel
    have hcons : ∀ d : BitVec 64,
        ((d + 32#64) ↦₈ msgTypeByte t) ∗ ((d + 33#64) ↦ₛ tail) =
          ((d + 32#64) ↦ₛ (msgTypeByte t :: tail)) := by
      intro d
      have hd33 : d + 33#64 = d + 32#64 + 1#64 := by bv_kernel
      rw [hd33, ← pointsToBytes_cons]
    refine Entails.sepExists_right
      (vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length) ++ (msgTypeByte t :: tail))
      (Entails.sepExists_right (vecU8Buf A cap ptr bs) ?_)
    rw [pointsToBytes_append, ha32 a, ← hcons a]
    refine Entails.pure_right ⟨by simp [vecHeaderBytes, htail], fun b => ?_⟩ (by bi_entail)
    rw [pointsToBytes_append, ha32 b, ← hcons b]
    have hvec : ((b + 8#64) ↦ₛ vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length)) ∗ vecU8Buf A cap ptr bs ⊢
        invalidMessageStrAt A (b + 8#64) r := by
      refine Entails.trans ?_ (hr (b + 8#64))
      rw [vecU8_eq_bytes24_sep_buf A (b + 8#64) bs]
      exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono hvec (sepConj_mono_right
      (htail ▸ pointsToBytes_entails_memRegion (b + 33#64) tail))))
    bi_entail

/-- Every non-panic `SignalProtocolError` at `a` decomposes into 6 inline 64-bit words
    `words6At a (speTag e) w1 w2 w3 w4 w5` and a detached heap predicate `H` that can be reassembled
    into `speAt A fnName b e` at any address `b`. -/
theorem speAt_decomp6 (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (e : SignalProtocolError) (hne : e ≠ .panic) :
    speAt A fnName a e ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64, (words6At b (speTag e) w1 w2 w3 w4 w5 ∗ H) ⊢ speAt A fnName b e⌝ ∗
        words6At a (speTag e) w1 w2 w3 w4 w5 ∗ H := by
  refine Entails.trans (speAt_inline_bytes A fnName a e hne) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hbs, hreassemble⟩
  have h0 : (bs.take 32).length = 32 := by simp [hbs]
  have h1 : (bs.drop 32).length = 8 := by simp [hbs]
  obtain ⟨w1, w2, w3, w4, _, hp32⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 h1
  have hwords : ∀ c : BitVec 64,
      ((c ↦₆₄ speTag e) ∗ ((c + 8#64) ↦ₛ bs)) = words6At c (speTag e) w1 w2 w3 w4 w5 := by
    intro c
    have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    conv_lhs => rw [hsplit, pointsToBytes_append, h0, hp32 (c + 8#64), hw5,
      ← pointsTo64_eq_pointsToBytes]
    unfold words6At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [← sepConj_assoc (a ↦₆₄ speTag e) ((a + 8#64) ↦ₛ bs), hwords a]
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right H ?_)))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _)
  rw [← hwords b, sepConj_assoc]
  exact hreassemble b

end SegDecryptFacts

end CryptoVerification.LibsignalTripleRatchet.Record
