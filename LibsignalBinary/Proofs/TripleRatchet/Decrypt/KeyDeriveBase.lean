/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import all Init.Data.String.Defs
import ProofLib.Sep
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

/-!
# Shared Separation-Logic, Panic-Bridge, and `SepWPp` Helpers for `KeyDerive`

Shared representation splittings, bitvector lemmas, panic-outcome bridges (`format_inner`,
`spqr::recv`), and relocatable `[LibsignalPlacement]` `SepWPp` stepping combinators for segments
`S4`–`S6` (`ConsumeMsgKey`, `PqRecv`, `DeriveKeys`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc

namespace KeyDeriveCallees

def fnOff_spqrRecv : Unit := ()
def fnOff_formatInner : Unit := ()
def fnOff_addrDisplay : Unit := ()
def lt_two_pow_64_of_lt_text : Unit := ()

theorem utf8_decrypt_len : (utf8 "decrypt").length = 7 := by
  decide +kernel

end KeyDeriveCallees

theorem pointsTo64_split32 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) :=
  ProofLib.pointsTo64_split32' a v

theorem pointsTo32_merge64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32]
  have h1 : (hi ++ lo).truncate 32 = lo := by bv_kernel
  have h2 : (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel
  rw [h1, h2]

theorem pts64_to_mr (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  sep_interval

macro "fold_mr8 " addr:term : tactic =>
  `(tactic| refine SepWP.focus_weaken (pts64_to_mr $addr _) (by sep_focus) ?_)

@[local simp, local wp_norm, local arm64_norm]
theorem extractLsb0_8_append56 (hi : BitVec 56) (d : BitVec 8) :
    (hi ++ d).extractLsb' 0 8 = d := by bv_kernel

theorem pointsTo8_memRegion7_to_64 (a : BitVec 64) (d : BitVec 8) :
    ((a ↦₈ d) ∗ memRegion (a + 1#64) 7) ⊢ ∃∗ hi : BitVec 56, a ↦₆₄ (hi ++ d) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hbs => ?_
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;> simp at hbs
  rw [← pointsToBytes_cons]
  refine Entails.trans (Entails.of_eq ?_) (Entails.sepExists_intro (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1))
  rw [pointsTo64_eq_pointsToBytes]
  congr 1
  simp only [unpack64, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_kernel

theorem pointsTo64_to_8_memRegion7 (a : BitVec 64) (hi : BitVec 56) (d : BitVec 8) :
    (a ↦₆₄ (hi ++ d)) ⊢ (a ↦₈ d) ∗ memRegion (a + 1#64) 7 := by
  simpa only [extractLsb0_8_append56] using ProofLib.cell_entails_lowByte_pad a (hi ++ d)

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem stackAt_sub (sp : BitVec 64) (N K : Nat) (hK : K ≤ N := by decide)
    (hN : N < 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) (N - K) ∗ stackAt sp K := by
  simp only [stackAt]
  refine memRegion_split' (by omega) ?_ (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : N % 2 ^ 64 = N := Nat.mod_eq_of_lt hN
  have h2 : (N - K) % 2 ^ 64 = N - K := Nat.mod_eq_of_lt (by omega)
  have h3 : K % 2 ^ 64 = K := Nat.mod_eq_of_lt (by omega)
  omega

@[expose] def optKeyRest (A : RustAlloc) (w0 w1 w2 : BitVec 64) (x : Salt) : SepProp :=
  match x with
  | none =>
    ∃∗ isNiche : Bool,
      if isNiche then ⌜w0 = noneCap⌝
      else
        ⌜w0.toNat < 2 ^ 63 ∧ w1 ≠ 0#64 ∧ w2 = 0#64⌝ ∗
        (if w0 = 0#64 then emp else A.live w1 w0.toNat 1 ∗ memRegion w1 w0.toNat)
  | some k =>
    ⌜k.toList.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0#64 ∧
      w2 = BitVec.ofNat 64 k.toList.length⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ k.toList) ∗
       memRegion (w1 + BitVec.ofNat 64 k.toList.length) (w0.toNat - k.toList.length))

theorem optKeyAt_split (A : RustAlloc) (a : BitVec 64) (x : Salt) :
    spqrRecvKeyAt A a x ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        optKeyRest A w0 w1 w2 x ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  cases x with
  | none =>
    simp only [spqrRecvKeyAt, optKeyRest]
    refine Entails.sepExists_elim fun isNiche => ?_
    cases isNiche
    · simp only [Bool.false_eq_true, ↓reduceIte, vecU8, vecU8At, vecHeader,
        List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat, pointsToBytes_nil,
        emp_sepConj, BitVec.add_zero, sepConj_assoc, sepConj_pure_left_comm]
      refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      refine Entails.pure_left fun ⟨_, hs, hp⟩ => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap)
      refine Entails.trans ?_ (Entails.sepExists_intro ptr)
      refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
      rw [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine Entails.pure_right ⟨hs, hp, trivial⟩ ?_
      rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm]
      simp only [sepConj_assoc]
      exact Entails.refl _
    · simp only [↓reduceIte]
      rw [memRegion_split (a + 8#64) 8 8 (by decide),
        BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by rfl,
        memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
      rw [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun w1 => ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun w2 => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro noneCap)
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      refine Entails.trans ?_ (Entails.sepExists_intro w2)
      rw [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro true)
      simp only [↓reduceIte]
      refine Entails.pure_right trivial ?_
      exact Entails.refl _
  | some k =>
    simp only [spqrRecvKeyAt, optKeyRest, vecU8, vecU8At, vecHeader]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Entails.pure_left fun h => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro cap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 k.toList.length))
    refine Entails.pure_right ⟨h.1, h.2.1, h.2.2, rfl⟩ ?_
    rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm]
    simp only [sepConj_assoc]
    exact Entails.refl _

theorem optKeyAt_fold (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (x : Salt) :
    optKeyRest A w0 w1 w2 x ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
    spqrRecvKeyAt A a x := by
  cases x with
  | none =>
    simp only [spqrRecvKeyAt, optKeyRest, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun isNiche => ?_
    cases isNiche
    · simp only [Bool.false_eq_true, ↓reduceIte, vecU8, vecU8At, vecHeader,
        List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat, pointsToBytes_nil,
        emp_sepConj, BitVec.add_zero, sepConj_assoc]
      refine Entails.pure_left fun ⟨hs, hp, hw2⟩ => ?_
      subst hw2
      refine Entails.sepExists_right false (Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_))
      have h0 : (0 : Nat) ≤ w0.toNat := Nat.zero_le _
      bi_entail
    · simp only [↓reduceIte]
      refine Entails.pure_left fun hw0 => ?_
      subst hw0
      refine Entails.sepExists_right true ?_
      simp only [↓reduceIte]; sep_interval
  | some k =>
    simp only [spqrRecvKeyAt, optKeyRest, vecU8, vecU8At, vecHeader, sepConj_assoc]
    refine Entails.pure_left fun ⟨h1, h2, h3, hw2⟩ => ?_
    subst hw2
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_)
    simp only [sepConj_pure_left_comm]
    exact Entails.pure_right ⟨h1, h2, h3⟩ (by sep_interval)

theorem mkgAt_fold (A : RustAlloc) (r seedCap seedPtr : BitVec 64) (pad1 pad2 : BitVec 32)
    (mkg : MessageKeyGenerator)
    (hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0) :
    (r ↦₃₂ 1#32) ∗ ((r + 4#64) ↦₃₂ pad1) ∗
    ((r + 8#64) ↦₆₄ seedCap) ∗ ((r + 16#64) ↦₆₄ seedPtr) ∗
    ((r + 24#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
    (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
      (seedPtr ↦ₛ mkg.seed) ∗
      memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
    ((r + 32#64) ↦₆₄ (pad2 ++ mkg.counter)) ⊢
    mkgAt A r mkg := by
  unfold mkgAt vecU8 vecU8At vecHeader
  rw [← pointsTo32_merge64 (r + 32#64) mkg.counter pad2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right seedCap (Entails.sepExists_right seedPtr ?_)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  exact Entails.pure_right hseed (by sep_interval)

theorem reaches_pc_of_sepWP {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hwp : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target_pc s Q := by
  intro hL
  rcases hwp.elim hmem hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hq hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

@[expose] def tryDecryptMidMetaCore (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 1504#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

def reaches_pc_of_sepWP_frozen : Unit := ()
def reaches_pc_midMeta : Unit := ()
def steps_of_sepWP : Unit := ()
def steps_done_of_sepWP_midMeta : Unit := ()
def steps_call : Unit := ()

theorem mr_cut (sp : BitVec 64) (c n k m : Nat) (c' : BitVec 64)
    (hm : m = n + k := by rfl)
    (hc : BitVec.ofNat 64 (c + n) = c' := by rfl)
    (h : n + k ≤ 2 ^ 64 := by decide) :
    memRegion (sp + BitVec.ofNat 64 c) m =
      memRegion (sp + BitVec.ofNat 64 c) n ∗ memRegion (sp + c') k := by
  subst hm hc
  exact mr_cut_add sp c n k h

@[expose] def trRestAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
    ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
    ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

theorem trAt_split_pq (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
      trRestAt A sp trG tr := by
  unfold trAt trRestAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 0xb0#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xc8#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xe8#64 = 288#64 by rfl]
  ac_rfl

@[expose] def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_split_pq (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
      signalMessageRestAt A g a m := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

theorem onPanic_drop_frame [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Unit}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R := by
  have _ := img
  dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩

theorem pointsToBytes_to_mr (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length :=
  ProofLib.pointsToBytes_entails_memRegion a bs

theorem buf_to_mr (ptr : BitVec 64) (bs : List (BitVec 8)) (cap : Nat)
    (h1 : bs.length ≤ cap) (h2 : cap < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length) ⊢
    memRegion ptr cap := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_to_mr ptr bs)) ?_
  rw [← memRegion_split ptr bs.length (cap - bs.length) (by omega), Nat.add_sub_of_le h1]
  exact Entails.refl _

theorem sp56_weaken (sp seedPtr seedCap : BitVec 64) :
    memRegion sp 16 ∗
    ((sp + 16#64) ↦₆₄ seedPtr) ∗
    memRegion (sp + 24#64) 16 ∗
    ((sp + 40#64) ↦₆₄ seedCap) ∗
    memRegion (sp + 48#64) 8 ⊢
    memRegion sp 56 := by
  sep_interval

theorem sepWP_8_mr7_to_64 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {lo : BitVec 8} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ hi : BitVec 56, SepWP prog target s ((a ↦₆₄ (hi ++ lo)) ∗ F) post) :
    SepWP prog target s ((a ↦₈ lo) ∗ memRegion (a + 1#64) 7 ∗ F) post := by
  refine SepWP.focus_weaken (pointsTo8_memRegion7_to_64 a lo) (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  wp_pull_exists
  exact h _

theorem pts8_mr7_to_mr8 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢ memRegion a 8 := by
  sep_interval

theorem extractLsb56_append_setWidth8 (w : BitVec 64) :
    w.extractLsb' 8 56 ++ w.setWidth 8 = w := by
  bv_kernel

theorem pointsTo64_to_8_mr7 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.setWidth 8) ∗ memRegion (a + 1#64) 7 := by
  have h := pointsTo64_to_8_memRegion7 a (w.extractLsb' 8 56) (w.setWidth 8)
  rwa [extractLsb56_append_setWidth8] at h

theorem sp_fp_eq {sp0 sp : BitVec 64} (h : sp0 - 1504#64 = sp) :
    sp0 - 96#64 = sp + 1408#64 := by
  subst h; bv_kernel

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

theorem byte_ne_zero_cbz32 {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 d == 0#32) = false := by
  revert h; bv_kernel

theorem byte_ne_zero_cbz64_32 {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false := by
  revert h; bv_kernel

theorem concat56_8_cbz64_zero (hi : BitVec 56) :
    (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ 0#8)) == 0#64) = true := by
  bv_kernel

theorem concat56_8_cbz64_ne_zero (hi : BitVec 56) {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ d)) == 0#64) = false := by
  revert h; bv_kernel

theorem concat56_8_cbz32_ne_zero (hi : BitVec 56) {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ d))) == 0#32) = false := by
  revert h; bv_kernel

theorem speBodyAt_invalidState_fold (A : RustAlloc) (sp fmtCap fmtPtr p : BitVec 64)
    (fmtBs : List (BitVec 8))
    (hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0) :
    ((sp + 360#64) ↦₆₄ fmtCap) ∗
    ((sp + 368#64) ↦₆₄ fmtPtr) ∗
    ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 fmtBs.length) ∗
    (if fmtCap = 0 then emp else A.live fmtPtr fmtCap.toNat 1 ∗
      (fmtPtr ↦ₛ fmtBs) ∗
      memRegion (fmtPtr + BitVec.ofNat 64 fmtBs.length) (fmtCap.toNat - fmtBs.length)) ∗
    ((sp + 384#64) ↦₆₄ p) ∗
    ((sp + 392#64) ↦₆₄ 7#64) ∗
    (p ↦ᵣ utf8 "decrypt") ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) .invalidState := by
  unfold speBodyAt strRefAt vecU8 vecU8At vecHeader
  rw [show BitVec.ofNat 64 (utf8 "decrypt").length = 7#64 by decide +kernel]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
  refine Entails.sepExists_right fmtBs (Entails.sepExists_right fmtCap (Entails.sepExists_right fmtPtr ?_))
  rcases hfb with ⟨h1, h2, h3⟩
  bi_entail

theorem speBodyAt_pqRatchet_fold (A : RustAlloc) (sp fmtCap fmtPtr w392 : BitVec 64)
    (fmtBs : List (BitVec 8)) (mt : MessageType)
    (hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0) :
    ((sp + 360#64) ↦₆₄ fmtCap) ∗
    ((sp + 368#64) ↦₆₄ fmtPtr) ∗
    ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 fmtBs.length) ∗
    (if fmtCap = 0 then emp else A.live fmtPtr fmtCap.toNat 1 ∗
      (fmtPtr ↦ₛ fmtBs) ∗
      memRegion (fmtPtr + BitVec.ofNat 64 fmtBs.length) (fmtCap.toNat - fmtBs.length)) ∗
    ((sp + 384#64) ↦₈ msgTypeByte mt) ∗
    memRegion ((sp + 384#64) + 1#64) 7 ∗
    ((sp + 392#64) ↦₆₄ w392) ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) (.invalidMessage mt .pqRatchet) := by
  unfold speBodyAt invalidMessageStrAt vecU8 vecU8At vecHeader
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
  refine Entails.sepExists_right fmtBs (Entails.sepExists_right fmtCap (Entails.sepExists_right fmtPtr ?_))
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  exact Entails.pure_right hfb (by sep_interval)

/-! ## Relocatable `[LibsignalPlacement]` Helpers for KeyDerive Segments -/

theorem reaches_pc_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm P_mid (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    rcases (h2 sm hpc hrun (hcl.of_keepsFrozen hsteps.keepsFrozen) hReg).elim
        hmm' (hsteps.codeLoaded hL) with ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem tryDecryptMidMetaPlaced_of_core [LibsignalPlacement] {s0 s : State}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : tryDecryptMidMetaCore s0 s) : tryDecryptMidMetaPlaced s0 s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, hcl, h7⟩

theorem reaches_pc_midMeta_placed [LibsignalPlacement] {prog : Program} {target : BitVec 64}
    {s0 s : State} {Rest : State → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : reaches_pc prog target s (fun sf => sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    reaches_pc prog target s (fun sf => sf.pc = target ∧ tryDecryptMidMetaPlaced s0 sf ∧ Rest sf) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, hpc', hcore, hrest⟩ | hoom⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hpc',
      tryDecryptMidMetaPlaced_of_core (hcl.of_keepsFrozen hsteps.keepsFrozen) hcore,
      hrest⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

theorem steps_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {mid : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Out : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → RegMid sm → (sm.mem ⊨ P_mid ∗ R) →
      ∃ s', Steps prog sm s' ∧ Out s') :
    ∃ s', Steps prog s s' ∧ Out s' := by
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    obtain ⟨s', hsteps', hout⟩ :=
      h2 sm hpc hrun (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.codeLoaded hL) hReg hmm'
    exact ⟨s', hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_done_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {target : BitVec 64} {s : State} {P R : SepProp}
    {QCore NormalOut PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (himp : ∀ sf, LibsignalCodeRoLoaded lsmpl sf.mem → QCore sf → NormalOut sf)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → QCore sf)) :
    ∃ s', Steps prog s s' ∧ (NormalOut s' ∨ PanicOut s') := by
  rcases hwp.elim hmem hL with ⟨sf, hsteps, ⟨_, _, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl (himp sf (hcl.of_keepsFrozen hsteps.keepsFrozen) (hq hmf))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_done_of_sepWP_midMeta_placed [LibsignalPlacement] {prog : Program}
    {target : BitVec 64} {s0 s : State} {P R : SepProp}
    {Rest PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
      sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    ∃ s', Steps prog s s' ∧
      ((s'.pc = target ∧ tryDecryptMidMetaPlaced s0 s' ∧ Rest s') ∨ PanicOut s') := by
  refine steps_done_of_sepWP_placed hmem hL hcl ?_ hwp
  intro sf hclf ⟨hpc', hcore, hrest⟩
  exact ⟨hpc', tryDecryptMidMetaPlaced_of_core hclf hcore, hrest⟩

theorem steps_call_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  obtain ⟨sf, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) sm hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcf
    have hsp_alf : sf.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hspf]; exact hsp
    obtain ⟨s', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf hsp_alf hcsf
        (hcl.of_keepsFrozen hsteps.keepsFrozen) (hsteps.codeLoaded hL) hpost
    exact ⟨s', hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sf, hsteps, Or.inr (hpanic sf hpan hpost)⟩
  · exact (hexit sf code (F ∗ R) hpost).elim
  · exact (hoom sf (F ∗ R) hpost).elim

theorem reaches_pc_of_sepWP_placed_cro [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ P_mid)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    have hmm'' : sm.mem ⊨ (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ P_mid) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hclm, hmm'⟩
    rcases (h2 sm hpc hrun hclm hReg).elim hmm'' (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_call_placed_cro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  have hpre' : sm.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact steps_call_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

theorem steps_call_placed_cl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  have hpre' : sm.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl.1, hpre⟩
  exact steps_call_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

theorem onPanic_of_spqrRecv_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpecQF (fun _ => True) (fun _ => True) emp
      { pre := fun _ _ => emp
        post := fun _ _ _ => emp
        onPanic := fun (st, msg, _) s0 sf =>
          ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
            anyHeap }).onPanic
      (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  have _ := A; have _ := ctl; have _ := ret
  dsimp only [spqrRecvSpecQF, tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [hst, hmsg, allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, hpref⟩, ?_⟩
  · rcases hpan with ha | hp
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl hp)
  · exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem onPanic_of_formatInner_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  have _ := ctl
  dsimp only [formatInnerSpec, tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem onPanic_of_spqrRecv_fn_placed [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpecQF (fun _ => True) (fun _ => True) emp
      { pre := fun _ _ => emp
        post := fun _ _ _ => emp
        onPanic := fun (st, msg, _) s0 sf =>
          ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
            anyHeap }).onPanic
      (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  have _ := A; have _ := ctl; have _ := ret
  dsimp only [spqrRecvSpecQF, tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [hst, hmsg, allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, hpref⟩, ?_⟩
  · rcases hpan with ha | hp
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl hp)
  · exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem onPanic_of_formatInner_fn_placed [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  have _ := ctl
  dsimp only [formatInnerSpec, tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

private theorem exec_bind_panic_eq {σ α β : Type} (m : Mut σ α) (f₁ f₂ : α → Mut σ β) (s : σ)
    (h : ∀ a s', ((Mut.exec (f₁ a) s').1 = .error .panic) = ((Mut.exec (f₂ a) s').1 = .error .panic)) :
    ((Mut.exec (m >>= f₁) s).1 = .error .panic) = ((Mut.exec (m >>= f₂) s).1 = .error .panic) := by
  dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run, ExceptT.mk, ExceptT.bindCont]
  cases m s with
  | mk res s' =>
    cases res with
    | error e => rfl
    | ok a => exact h a s'

theorem decryptFn_error_panic_eq {PQ PQC : Type} (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : TripleRatchet PQ) :
    ((Mut.exec (TripleRatchet.decryptFn C decFn spqr expected ciphertext msgType coins) s).1 = .error .panic) =
      ((Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) s).1 = .error .panic) := by
  unfold TripleRatchet.decryptFn TripleRatchet.decrypt
  refine exec_bind_panic_eq _ _ _ s fun chainKey s1 => ?_
  refine exec_bind_panic_eq _ _ _ s1 fun messageKeyGen s2 => ?_
  refine exec_bind_panic_eq _ _ _ s2 fun t s3 => ?_
  dsimp only
  cases spqr.recvPanics t.pqrState ciphertext.pqRatchet with
  | true => rfl
  | false =>
    cases spqr.recv t.pqrState ciphertext.pqRatchet with
    | error sd => cases sd <;> rfl
    | ok r =>
      rcases r with ⟨newPqrState, pqrKey⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run,
        pure, ExceptT.pure, StateT.pure, ExceptT.mk, ExceptT.bindCont]
      cases SignalMessage.verifyMacWithAddresses C.F ciphertext expected
          t.remoteIdentityKey t.localIdentityKey
          (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).macKey with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decFn ciphertext.ciphertext
            (keyToBytes32 (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey)
            (CBC.blockToBytesLE (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv) <;>
          cases aesCbcDecrypt C.D
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv
            ciphertext.ciphertext <;>
          exact propext ⟨nofun, nofun⟩

private theorem exec_liftE_tail_panic_eq {PQ : Type} [Inhabited PQ]
    (r : Except SignalProtocolError (List (BitVec 8))) (session : TripleRatchet PQ)
    (s : SessionState PQ) :
    ((Mut.exec (do
      let ptext ← liftE r
      modify fun st => (session.applyToSessionState st).clearUnacknowledgedPreKeyMessage
      return ptext) s).1 = .error .panic) = (r = .error .panic) := by
  cases r with
  | error e => rfl
  | ok ptext => rfl

theorem tryDecryptWithStateFn_error_panic_eq {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : SessionState PQ) :
    ((Mut.exec (SessionState.tryDecryptWithStateFn C decFn spqr expected ciphertext msgType coins) s).1 = .error .panic) =
      ((Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) s).1 = .error .panic) := by
  unfold SessionState.tryDecryptWithStateFn SessionState.tryDecryptWithState
  refine exec_bind_panic_eq _ _ _ s fun session s1 => ?_
  dsimp only
  rw [exec_liftE_tail_panic_eq, exec_liftE_tail_panic_eq]
  exact decryptFn_error_panic_eq C decFn spqr expected ciphertext msgType coins session

theorem modelFn_error_panic_eq (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel) (parse : UuidParser) (x : TryDecryptGhost) :
    ((x.modelFn C decFn S parse).1 = .error .panic) =
      ((x.model C S parse).1 = .error .panic) :=
  tryDecryptWithStateFn_error_panic_eq C decFn S.spqr
    (serializeAddresses (serviceIdParse parse) x.rem x.loc) x.msg x.msgType (coinsOf x.rest) x.st

theorem tryDecryptFnSpecPlaced_onPanic_eq [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) :
    (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic =
      (tryDecryptSpecPlaced C A ctl parse S).onPanic := by
  funext x s0 sf
  dsimp only [tryDecryptFnSpecPlaced, tryDecryptSpecPlaced, withLsCodeRoLoaded,
    tryDecryptFnRawSpecPlaced, tryDecryptRawSpecPlaced]
  rw [modelFn_error_panic_eq]

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
