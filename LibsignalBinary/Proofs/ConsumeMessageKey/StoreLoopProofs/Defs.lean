/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import ProofLib.SepLogic.WPp

/-!
# Shared Definitions and Sub-Segment Contracts for the `consume_message_key` Store Loop

Defines extern stub hooks, internal store-loop checkpoint PCs (`+0x394`, `+0x3fc`, `+0x474`),
intermediate states, and the placed sub-segment contracts along with their composition.
-/

public section

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

abbrev cmkSym : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-! ## Extern Stub Hooks -/

@[expose] def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

/-! ## Cryptographic and Byte-Representation Helpers -/

theorem sha256With_length (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize ((chunks64 (sha256Pad m)).foldl F sha256IV) = st
  rcases st with ⟨l, hl⟩
  have h4 : ∀ x : BitVec 32, (toBEBytes 4 x).length = 4 := fun _ => by
    simp [toBEBytes]
  simp [List.length_flatMap, h4, hl]

theorem hmacWith_length (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith
  exact sha256With_length F _

theorem chainStep_length (F : ShaState → List (BitVec 8) → ShaState) (ck : BitVec 256) (b : BitVec 8) :
    (Ratchet.chainHmac F ck b).length = 32 :=
  hmacWith_length F (keyToBytes32 ck) [b]

theorem messageKeys_seed_eq (F : ShaState → List (BitVec 8) → ShaState)
    (ck : CryptoGames.LibsignalSession.ChainKey) :
    (ck.messageKeys F).seed = hmacWith F (keyToBytes32 ck.key) [1#8] := rfl

theorem messageKeys_seed_length (F : ShaState → List (BitVec 8) → ShaState)
    (ck : CryptoGames.LibsignalSession.ChainKey) :
    (ck.messageKeys F).seed.length = 32 :=
  chainStep_length F ck.key Ratchet.messageKeySeed

theorem messageKeys_counter_eq (F : ShaState → List (BitVec 8) → ShaState)
    (ck : CryptoGames.LibsignalSession.ChainKey) :
    (ck.messageKeys F).counter = ck.index := rfl

theorem keyToBytes32_length (k : BitVec 256) :
    (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem nextChainKey_eq_ok (F : ShaState → List (BitVec 8) → ShaState)
    (ck : CryptoGames.LibsignalSession.ChainKey)
    (h : ck.index ≠ BitVec.allOnes 32) :
    ck.nextChainKey F =
      .ok ⟨bytesToKey32 (hmacWith F (keyToBytes32 ck.key) [2#8]), ck.index + 1⟩ := by
  unfold ChainKey.nextChainKey
  rw [ite_eq_right_iff.mpr fun h1 => False.elim (h h1)]
  rfl

theorem index_ne_allOnes_of_lt {idx ctr : BitVec 32} (h : idx < ctr) :
    idx ≠ BitVec.allOnes 32 := by
  intro heq
  subst heq
  have h1 : (BitVec.allOnes 32).toNat < ctr.toNat := BitVec.lt_def.mp h
  have h2 : ctr.toNat < 2 ^ 32 := ctr.isLt
  have h3 : (BitVec.allOnes 32).toNat = 2 ^ 32 - 1 := rfl
  omega

/-! ## Store-Loop Sub-Segment Checkpoints and States -/

/-- The ghost of a newly created skipped `MessageKey` with 32-byte `seed` at `seedPtr`
and empty `cipher`, `mac`, `iv` buffers (`cap = 0, ptr = 1`). -/
@[expose] def newMsgKeyGhost (seedPtr : BitVec 64) : MessageKeyGhost :=
  { cipher := ⟨0#64, 1#64⟩
    mac    := ⟨0#64, 1#64⟩
    iv     := ⟨0#64, 1#64⟩
    seed   := ⟨32#64, seedPtr⟩ }

/-- Updated `ReceiverChain` after inserting `ckc.messageKeys F` at the front and truncating to `2000`. -/
@[expose] def updatedReceiverChain (F : ShaState → List (BitVec 8) → ShaState)
    (chc : ReceiverChain) (ckc : CryptoGames.LibsignalSession.ChainKey) : ReceiverChain :=
  { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }

@[expose] def updatedRatchetState (F : ShaState → List (BitVec 8) → ShaState)
    (stc : RatchetState) (ci : Nat) (chc : ReceiverChain)
    (ckc : CryptoGames.LibsignalSession.ChainKey) : RatchetState :=
  { stc with receiverChains := stc.receiverChains.set ci (updatedReceiverChain F chc ckc) }

@[expose] def InsertKeyRegs (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (seedPtr : BitVec 64) (s0 s : State) : Prop :=
  s.readReg64 .x1 = BitVec.ofNat 64 ci ∧
  s.readReg64 .x19 = 1#64 ∧
  s.readReg64 .x20 = seedPtr ∧
  s.readReg64 .x21 = x.ckA ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x25 = Gc.chainsPtr ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = ckc.index.zeroExtend 64

@[expose] def EvictOldestKeyRegs (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (_mkPtr1 : BitVec 64) (s : State) : Prop :=
  s.readReg64 .x19 = 1#64 ∧
  s.readReg64 .x21 = x.ckA ∧
  s.readReg64 .x22 = x.theirA ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
  s.readReg64 .x26 = 2000#64 ∧
  s.readReg64 .x28 = ckc.index.zeroExtend 64

/-- The rest of `ratchetAt A self G st` when receiver chain `i` is split out. -/
@[expose] def ratchetContextAt (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) (i : Nat) : SepProp :=
  ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
    st.maxForwardJumps < 2 ^ 64 ∧
    st.receiverChains.length ≤ G.chainsCap.toNat ∧
    G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0 ∧ G.chainsCap ≠ 0⌝ ∗
  vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
  A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
  arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
  arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
    ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
  memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
    ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
  ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
  ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

/-- Heap layout at `cmkEvictOldestKeyPC` (`+0x3fc`) with 2001 elements prior to popping index 2000. -/
@[expose] def evictOldestKeyHeap [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) (img : Unit)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 2001#64 ∗
  vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1 gks1 ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

@[expose] def evictOldestKeyHeapAt (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 2001#64 ∗
  vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1 gks1 ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

@[expose] def AdvanceChainKeyRegs (x : ConsumeMessageKeyGhost) (s0 s : State) : Prop :=
  s.readReg64 .x19 = 1#64 ∧
  s.readReg64 .x21 = x.ckA ∧
  s.readReg64 .x22 = x.theirA ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x27 = s0.sp - 224#64

end CryptoVerification.LibsignalSession.StoreLoop

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

@[expose] def GrowOnePlacedOk [LibsignalPlacement] (H : String → Option (State → State)) (A : RustAlloc) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 43)
    (withLsCodeLoaded lsmpl (growOneSpec A))

@[expose] def StoreLoopIterPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedOk H F → GrowOnePlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A x G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 s' ∗ R)))

@[expose] def StoreLoopPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedOk H F → GrowOnePlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A x G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 s' ∗ R)))

private theorem take_append_take_of_le_placed {α : Type} :
    ∀ (xs ys : List α) {m k : Nat}, m ≤ k →
      (xs ++ ys.take k).take m = (xs ++ ys).take m
  | [], ys, m, k, hmk => by simp [List.take_take, Nat.min_eq_left hmk]
  | x :: xs, ys, 0, k, _ => rfl
  | x :: xs, ys, m + 1, k, hmk => by
    simp only [List.cons_append, List.take_succ_cons]
    exact congrArg (x :: ·) (take_append_take_of_le_placed xs ys (Nat.le_of_succ_le hmk))

private theorem take_append_take_eq_placed {α : Type} (xs ys : List α) (m : Nat) :
    (xs ++ ys.take m).take m = (xs ++ ys).take m :=
  take_append_take_of_le_placed xs ys (Nat.le_refl m)

private theorem set_set_same_placed {α : Type} (xs : List α) (i : Nat) (a b : α) :
    (xs.set i a).set i b = xs.set i b := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem getElem?_set_self_placed {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) (a : α) :
    (xs.set i a)[i]? = some a := by
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_set_self]

private theorem storeLoop_placed_loop_ind [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hiter : StoreLoopIterPlacedSpec F A H)
    (hA : CmkAllocHooks A H) (hmm : H "memmove" = some hookMemmove)
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F) (hgrow : GrowOnePlacedOk H A)
    (x : ConsumeMessageKeyGhost) (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A x G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 s' ∗ R)))
  | 0, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkEpiloguePC_placed := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨G', hG', hst'⟩ | hpan⟩ :=
      hiter hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst'
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, G', hG', ?_⟩⟩
      simpa [chainStepN, skippedKeys] using hst'
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkLoopPC_placed := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨G1, hG1, hst1⟩ | hpan1⟩ :=
      hiter hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self_placed hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_placed_loop_ind F A H hiter hA hmm hfind hhmac hgrow x ci R s0
          k G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1 (hsteps1.codeLoaded hL)
      · refine ⟨s2, hsteps1.trans hsteps2, Or.inl ⟨hck_end, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same_placed]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (Ratchet.chainHmac F ckc.key Ratchet.chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq_placed]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem storeLoop_placed_of_iter [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hiter : StoreLoopIterPlacedSpec F A H) : StoreLoopPlacedSpec F A H := by
  intro hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 := ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk]
  exact storeLoop_placed_loop_ind F A H hiter hA hmm hfind hhmac hgrow x ci R s0
    k Gc stc ckc chc s hlt hk hci hchc hstate hL

@[expose] def StoreLoopIterPlacedRoSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F → GrowOnePlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A x G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 s' ∗ R)))

@[expose] def StoreLoopPlacedRoSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F → GrowOnePlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A x G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 s' ∗ R)))

private theorem storeLoop_placed_ro_loop_ind [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hiter : StoreLoopIterPlacedRoSpec F A H)
    (hA : CmkAllocHooks A H) (hmm : H "memmove" = some hookMemmove)
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F) (hgrow : GrowOnePlacedOk H A)
    (x : ConsumeMessageKeyGhost) (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter → (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci → stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A x G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 s' ∗ R)))
  | 0, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL, hro => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq; change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkEpiloguePC_placed := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨G', hG', hst'⟩ | hpan⟩ :=
      hiter hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
    · rw [hpc_eq] at hst'
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, G', hG', ?_⟩⟩
      simpa [chainStepN, skippedKeys] using hst'
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL, hro => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkLoopPC_placed := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨G1, hG1, hst1⟩ | hpan1⟩ :=
      hiter hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self_placed hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]; exact hci
      obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_placed_ro_loop_ind F A H hiter hA hmm hfind hhmac hgrow x ci R s0
          k G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1 (hsteps1.codeLoaded hL)
          (libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen)
      · refine ⟨s2, hsteps1.trans hsteps2, Or.inl ⟨hck_end, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]; rw [set_set_same_placed]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (Ratchet.chainHmac F ckc.key Ratchet.chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq_placed]; simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem storeLoop_placed_ro_of_iter [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hiter : StoreLoopIterPlacedRoSpec F A H) : StoreLoopPlacedRoSpec F A H := by
  intro hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]; omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 := ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only; rw [hk]
  exact storeLoop_placed_ro_loop_ind F A H hiter hA hmm hfind hhmac hgrow x ci R s0
    k Gc stc ckc chc s hlt hk hci hchc hstate hL hro

end CryptoVerification.LibsignalSession

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

/-! ## Relocatable `[LibsignalPlacement]` Definitions and Composition (Block 24) -/

abbrev cmkInsertKeyPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x394#64
abbrev cmkEvictOldestKeyPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x3fc#64
abbrev cmkAdvanceChainKeyPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x474#64

theorem sepWP_elim_inv_placed [LibsignalPlacement] {prog : Program} {mid : BitVec 64}
    {s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWP prog mid s P post) :
    ∃ sm, Steps prog s sm ∧ sm.pc = mid ∧ sm.status = .Running ∧
      LibsignalCodeLoaded lsmpl sm.mem ∧
      prog.CodeLoaded sm.mem ∧
      ∃ Pm, (sm.mem ⊨ Pm ∗ R) ∧ post sm Pm := by
  rcases hwp.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sm, hsteps, hpc, hrun, hcl.of_keepsFrozen hsteps.keepsFrozen,
      hsteps.codeLoaded hL, Pm, hmm, hpost⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_of_sepWPp_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P R : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    ∃ sf, Steps prog s sf ∧
      ((sf.pc = ret ∧ sf.status = .Running ∧ LibsignalCodeLoaded lsmpl sf.mem ∧
        ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ Q sf P_f) ∨
       (sf.status = .Panicked ∧ ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ Qp sf P_f)) := by
  rcases hwp R hm hL with
    ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hcl.of_keepsFrozen hsteps.keepsFrozen,
      P_f, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, P_f, hmf, hqp⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_seq_lscl {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

theorem introduce_withLsCodeLoaded {α : Type} {pl : Obj.MultiPlacement} {spec : Spec α}
    {x : α} {R : SepProp} {s : State}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm (spec.pre x s), satisfies_pure_sepConj]
  exact ⟨hcl, h⟩

theorem hmac_placed_ok_at_state [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {s : State}
    (hhmac : HmacPlacedOk H F)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73)
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
        post := (hmacSpec F).post } := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine subroutine_ok.mono_outcome hhmac (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
  dsimp only [hmacSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem findIndex_placed_ok_at_state [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {s : State}
    (hfind : FindIndexPlacedOk H A)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (findIndexPlacedSpec A).post } := by
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp => ?_
  refine subroutine_ok.mono_outcome hfind (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
  dsimp only [findIndexPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

@[expose] def InsertKeyState_placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (seedPtr : BitVec 64)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = cmkInsertKeyPC_placed ∧
  cmkMidMeta_placed s0 s ∧
  InsertKeyRegs x Gc ckc ci seedPtr s0 s ∧
  seedPtr ≠ 0#64 ∧
  (s.mem ⊨
    (cmkLoopHeap_placed A x Gc stc ckc s0 ∗
     vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ∗ R)

@[expose] def evictOldestKeyHeap_placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  evictOldestKeyHeapAt F A lsLogFilterAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0

@[expose] def EvictOldestKeyState_placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = cmkEvictOldestKeyPC_placed ∧
  cmkMidMeta_placed s0 s ∧
  EvictOldestKeyRegs x Gc ckc ci mkPtr1 s ∧
  (∃ hci : ci < Gc.chains.length, cg = Gc.chains[ci]) ∧
  PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
  chc.messageKeys.length = 2000 ∧
  cg.keys.length = 2000 ∧
  2001 ≤ mkCap1.toNat ∧
  mkCap1.toNat * 104 < 2 ^ 63 ∧
  mkPtr1 ≠ 0#64 ∧
  (s.mem ⊨ evictOldestKeyHeap_placed F A x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R)

@[expose] def AdvanceChainKeyState_placed [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = cmkAdvanceChainKeyPC_placed ∧
  cmkMidMeta_placed s0 s ∧
  AdvanceChainKeyRegs x s0 s ∧
  (s.mem ⊨ cmkLoopHeap_placed A x G' st' ckc s0 ∗ R)

@[expose] def DeriveSeedPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s sA ∧
        ((∃ seedPtr, InsertKeyState_placed F A x Gc stc ckc ci seedPtr R s0 sA) ∨
         (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sA ∗ R)))

@[expose] def InsertKeyPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  H "memmove" = some hookMemmove → GrowOnePlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (seedPtr : BitVec 64) (R : SepProp) (s0 sA : State),
      stc.receiverChains[ci]? = some chc →
      InsertKeyState_placed F A x Gc stc ckc ci seedPtr R s0 sA →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sA.mem →
      ∃ sB, Steps ((blkPC_24).rebase (blkPl_24).base H) sA sB ∧
        ((∃ G', Gc.AgreeExcept G' (some ci) ∧
            AdvanceChainKeyState_placed A x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB) ∨
         (∃ cg mkCap1 mkPtr1,
            EvictOldestKeyState_placed F A x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB) ∨
         (sB.status = .Panicked ∧ (sB.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sB ∗ R)))

@[expose] def EvictOldestKeyPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64)
      (R : SepProp) (s0 sB : State),
      stc.receiverChains[ci]? = some chc →
      EvictOldestKeyState_placed F A x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sB.mem →
      ∃ sC, Steps ((blkPC_24).rebase (blkPl_24).base H) sB sC ∧
        ∃ G', Gc.AgreeExcept G' (some ci) ∧
          AdvanceChainKeyState_placed A x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC

@[expose] def AdvanceChainKeyPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (R : SepProp) (s0 sD : State),
      ckc.index < x.counter →
      AdvanceChainKeyState_placed A x G' st' ckc R s0 sD →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem →
      let ck' := chainStepN F 1 ckc
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
        CmkLoopState_placed A x G' st' ck' R nextPC s0 s'

theorem storeLoop_iter_placed_of_parts [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hA_part : DeriveSeedPlacedSpec F A H)
    (hB_part : InsertKeyPlacedSpec F A H)
    (hC_part : EvictOldestKeyPlacedSpec F A H)
    (hD_part : AdvanceChainKeyPlacedSpec F A H) :
    StoreLoopIterPlacedSpec F A H := by
  intro hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  obtain ⟨sA, hstepsA, ⟨seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA hfind hhmac x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  · have hLA := hstepsA.codeLoaded hL
    obtain ⟨sB, hstepsB, ⟨G', hG', hsD⟩ | ⟨cg, mkCap1, mkPtr1, hsC⟩ | hpanB⟩ :=
      hB_part hmm hgrow x Gc stc ckc ci chc seedPtr R s0 sA hchc hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD hLB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨G', hG', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      obtain ⟨sC, hstepsC, G', hG', hsD⟩ :=
        hC_part hA x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB hchc hsC hLB
      have hLC := hstepsC.codeLoaded hLB
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD, Or.inl ⟨G', hG', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

@[expose] def hmacAtStateSpec (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, ka, key, ia, inp) s' =>
    ⌜s'.mem = s.mem ∧
      s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
      s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
      inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
  post := (hmacSpec F).post

theorem hmac_placed_ro_ok_at_state [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {s : State}
    (hhmac : HmacPlacedRoOk H F)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s) := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [hmacAtStateSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hcl) ?_
  dsimp only
  rw [sepConj_assoc, sepConj_left_comm ((hmacSpec F).pre (out, ka, key, ia, inp) s0),
      satisfies_pure_sepConj]
  refine ⟨hmem ▸ hro, ?_⟩
  dsimp only [hmacSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

@[expose] def DeriveSeedPlacedRoSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s sA ∧
        ((∃ seedPtr, InsertKeyState_placed F A x Gc stc ckc ci seedPtr R s0 sA) ∨
         (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sA ∗ R)))

@[expose] def AdvanceChainKeyPlacedRoSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (R : SepProp) (s0 sD : State),
      ckc.index < x.counter →
      AdvanceChainKeyState_placed A x G' st' ckc R s0 sD →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem →
      LibsignalRoLoaded lsmpl sD.mem →
      let ck' := chainStepN F 1 ckc
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
        CmkLoopState_placed A x G' st' ck' R nextPC s0 s'

theorem storeLoop_iter_placed_ro_of_parts [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hA_part : DeriveSeedPlacedRoSpec F A H)
    (hB_part : InsertKeyPlacedSpec F A H)
    (hC_part : EvictOldestKeyPlacedSpec F A H)
    (hD_part : AdvanceChainKeyPlacedRoSpec F A H) :
    StoreLoopIterPlacedRoSpec F A H := by
  intro hA hmm hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  obtain ⟨sA, hstepsA, ⟨seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA hfind hhmac x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  · have hLA := hstepsA.codeLoaded hL
    have hroA := libsignalRoLoaded_of_keepsFrozen hro hstepsA.keepsFrozen
    obtain ⟨sB, hstepsB, ⟨G', hG', hsD⟩ | ⟨cg, mkCap1, mkPtr1, hsC⟩ | hpanB⟩ :=
      hB_part hmm hgrow x Gc stc ckc ci chc seedPtr R s0 sA hchc hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      have hroB := libsignalRoLoaded_of_keepsFrozen hroA hstepsB.keepsFrozen
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD hLB hroB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨G', hG', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      have hroB := libsignalRoLoaded_of_keepsFrozen hroA hstepsB.keepsFrozen
      obtain ⟨sC, hstepsC, G', hG', hsD⟩ :=
        hC_part hA x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB hchc hsC hLB
      have hLC := hstepsC.codeLoaded hLB
      have hroC := libsignalRoLoaded_of_keepsFrozen hroB hstepsC.keepsFrozen
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC hroC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD, Or.inl ⟨G', hG', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

end CryptoVerification.LibsignalSession.StoreLoop
