/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import ProofLib.VCGen

/-!
# Seam State Predicates and Heap Helpers for `RatchetState::consume_message_key`

Shared stack frame layout, register invariants, heap footprints (`cmkPreLoopHeap`,
`cmkLoopHeap`), and `chainsOk_of_ratchetAt` for `RatchetState::consume_message_key`.
-/

public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

/-! ## Stack Frame Layout and Seam State Predicates -/

/-- Callee-saved register save area `[sp0 - 96#64 .. sp0]` (`[sp + 0x180 .. sp + 0x1e0]`, 96 bytes)
written by the prologue `+0x004 .. +0x018` and restored by `+0x77c .. +0x790`. -/
@[expose] def cmkSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Local frame `[sp0 - 480#64 .. sp0 - 96#64]` (`[sp .. sp + 0x180]`, 384 bytes) during S3/S4/S5:
`[sp + 0x70] = sp0 - 368#64` holds `x.ret` (stored at `+0x328`, read at `+0x5c8`) and
`[sp + 0x7c] = sp0 - 356#64` holds `x.counter` (stored at `+0x03c`, read at `+0x4a8`).
The 256-byte region `[sp0 - 352#64 .. sp0 - 96#64]` covers the 1-byte/32-byte scratch at
`sp + 0xa0 = sp0 - 320#64` and the 32-byte `hmac_sha256` output buffer at `x27 = sp + 0x100 = sp0 - 224#64`. -/
@[expose] def cmkLoopFrame (sp0 ret : BitVec 64) (counter : BitVec 32) : SepProp :=
  memRegion (sp0 - 480#64) 112 ∗
  ((sp0 - 368#64) ↦₆₄ ret) ∗
  memRegion (sp0 - 360#64) 4 ∗
  ((sp0 - 356#64) ↦₃₂ counter) ∗
  memRegion (sp0 - 352#64) 256

@[expose] def CmkTakeRegs (x : ConsumeMessageKeyGhost) (s0 s : State) : Prop :=
  s.readReg64 .x0 = x.G.chainsPtr ∧
  s.readReg64 .x1 = BitVec.ofNat 64 x.st.receiverChains.length ∧
  s.readReg64 .x2 = x.theirA ∧
  s.readReg64 .x20 = x.counter.zeroExtend 64 ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.st.receiverChains.length ∧
  s.readReg64 .x22 = x.ret ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x24 = x.G.chainsPtr ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = x.ck.index.zeroExtend 64

@[expose] def cmkPreLoopHeap [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

@[expose] def cmkPreLoopHeapAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

/-- Live registers at `+0x170` (S2 entry, `ck.index ≤ counter`).
`x9 = jump` is set by `subs w9, w3, w28` (`+0x38`); `msgType` is still in `x4` (copied to `w19` at
`+0x188` on the too-far path); `ckA` is still in `x2` (`mov x21, x2` only at `+0x278`). -/
@[expose] def CmkTooFarRegs (x : ConsumeMessageKeyGhost) (s0 s : State) : Prop :=
  s.readReg64 .x2 = x.ckA ∧
  (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x9 = (x.counter - x.ck.index).zeroExtend 64 ∧
  s.readReg64 .x20 = x.counter.zeroExtend 64 ∧
  s.readReg64 .x22 = x.ret ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = x.ck.index.zeroExtend 64

/-- Live registers at `+0x334` (S3/S5) and `+0x4dc` (S4/S5) for current chain key `ckc`. -/
@[expose] def CmkLoopRegs (x : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State) : Prop :=
  s.readReg64 .x21 = x.ckA ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = ckc.index.zeroExtend 64

@[expose] def cmkLoopHeap [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) : SepProp :=
  ratchetAt A x.self Gc stc ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

@[expose] def cmkLoopHeapAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) : SepProp :=
  ratchetAt A x.self Gc stc ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

/-! ## `ChainsOk` Helpers -/

theorem forall_of_arrayAt {α : Type} {elem : α → BitVec 64 → SepProp} {stride : Nat}
    {P : α → Prop} (helem : ∀ x a R m, (m ⊨ elem x a ∗ R) → P x) :
    ∀ (xs : List α) (base : BitVec 64) (R : SepProp) (m : Memory),
      (m ⊨ arrayAt elem stride base xs ∗ R) → ∀ x ∈ xs, P x
  | [], _, _, _, _, _, hx => by cases hx
  | x :: xs, base, R, m, hm, y, hy => by
    simp only [arrayAt, sepConj_assoc] at hm
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact helem y base _ m hm
    · rw [sepConj_left_comm] at hm
      exact forall_of_arrayAt helem xs (base + BitVec.ofNat 64 stride) (elem x base ∗ R) m hm y hy'

theorem forall_of_vecAt {α : Type} {A : RustAlloc} {stride align : Nat}
    {elem : α → BitVec 64 → SepProp} {P : α → Prop}
    (helem : ∀ x a R m, (m ⊨ elem x a ∗ R) → P x)
    {v cap ptr : BitVec 64} {xs : List α} {R : SepProp} {m : Memory}
    (h : m ⊨ vecAt A stride align elem v cap ptr xs ∗ R) :
    ∀ x ∈ xs, P x := by
  unfold vecAt vecBuf at h
  have h' : m ⊨ ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
       (if cap = 0 then emp
        else A.live ptr (cap.toNat * stride) align ∗ arrayAt elem stride ptr xs ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) ∗ R) :=
    Satisfies.of_eq h
  rw [satisfies_pure_sepConj] at h'
  rcases h' with ⟨⟨hlen, _, _⟩, h'⟩
  by_cases hcap : cap = 0
  · subst hcap
    have h0 : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst h0
    intro _ hx; cases hx
  · simp only [hcap, ↓reduceIte] at h'
    have harr : m ⊨ arrayAt elem stride ptr xs ∗
        (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
         A.live ptr (cap.toNat * stride) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride) ∗ R) :=
      Satisfies.of_eq h'
    exact forall_of_arrayAt helem xs ptr _ m harr

/-- Every state satisfying `ratchetAt A self G st ∗ R` satisfies `ChainsOk st`. -/
theorem chainsOk_of_ratchetAt {A : RustAlloc} {self : BitVec 64} {G : RatchetGhost}
    {st : RatchetState} {R : SepProp} {m : Memory}
    (h : m ⊨ ratchetAt A self G st ∗ R) : ChainsOk st := by
  unfold ratchetAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hlen, _, _⟩, hvec⟩
  have hvec' : m ⊨ vecAt A 104 8 (chainAt A) self G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
      (((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
       ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
       ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4 ∗ R) :=
    Satisfies.of_eq hvec
  have hchains := forall_of_vecAt (P := fun gc : ChainGhost × ReceiverChain =>
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ ∀ k ∈ gc.2.messageKeys, k.seed ≠ [])
    (fun gc a R' m' hc => by
      unfold chainAt at hc
      rw [sepConj_assoc, satisfies_pure_sepConj] at hc
      rcases hc with ⟨⟨_, hmk_le, hkeys_len, _, _⟩, hc_rest⟩
      refine ⟨hmk_le, ?_⟩
      have hmk_vec : m' ⊨ vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (gc.1.keys.zip gc.2.messageKeys) ∗
          (vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
           optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗ R') :=
        Satisfies.of_eq hc_rest
      have hkeys := forall_of_vecAt (P := fun gk : MessageKeyGhost × MessageKeyGenerator => gk.2.seed ≠ [])
        (fun gk b R'' m'' hk => by
          unfold messageKeyAt at hk
          rw [sepConj_assoc, satisfies_pure_sepConj] at hk
          exact hk.1)
        hmk_vec
      intro k hk
      rw [List.mem_iff_getElem] at hk
      rcases hk with ⟨i, hi, rfl⟩
      have hi' : i < gc.1.keys.length := hkeys_len.symm ▸ hi
      exact hkeys (gc.1.keys[i], gc.2.messageKeys[i])
        (by
          rw [List.mem_iff_getElem]
          refine ⟨i, by simp [hi, hi'], by simp⟩))
    hvec'
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hi' : i < G.chains.length := hlen.symm ▸ hi
  exact hchains (G.chains[i], st.receiverChains[i])
    (by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [hi, hi'], by simp⟩)

theorem map_snd_zip_chains {G : RatchetGhost} {st : RatchetState}
    (h : G.chains.length = st.receiverChains.length) :
    (G.chains.zip st.receiverChains).map (·.2) = st.receiverChains := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp

theorem findReceiverChainIndex_some_getElem? {st : RatchetState} {their : PublicKey}
    {ci : Nat} (h : st.findReceiverChainIndex their = some ci) :
    ∃ ch, st.receiverChains[ci]? = some ch := by
  unfold RatchetState.findReceiverChainIndex at h
  have hlt : ci < st.receiverChains.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
  exact ⟨st.receiverChains[ci], List.getElem?_eq_getElem hlt⟩

abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

end CryptoVerification.LibsignalSession
