/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# Shared Helpers for `drop_glue<SessionStructure>` (`0x25b4` and `0x35958`)

Provides separation-logic field-deallocation lemmas, stack splits, and common `SepWPp` helpers
shared by `drop_glue<SessionStructure> [local#1]` and `[local#2]`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DropsCommon

theorem stackAt_split_bottom' (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem dealloc_hookSat_tripleRatchetExterns {A : RustAlloc} (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
  simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
    CryptoVerification.LibsignalSession.sessionExterns, dhName, pubFromSecretName,
    staticDropName, sharedDropName, rngFillName, uuidTryParseName,
    varintSlowName, noHookNames] using hA.dealloc

theorem SepWP.seq_clean {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## Separation-logic deallocation helpers for `SessionStructure` (344 bytes) -/

@[expose] def vecPinDealloc (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

@[expose] def sgnPinDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem slt_one_iff_eq_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]
  unfold BitVec.slt BitVec.toInt
  simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]
  omega

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``vecPinDealloc, #[1]), (``sgnPinDealloc, #[1, 2]), (``vecAt, #[5])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

theorem vecU8At_entails_pin_dealloc (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDealloc
  by_cases h0 : pin.cap = 0
  · simp only [h0, show ((0 : BitVec 64) == 0#64) = true from rfl, ↓reduceIte, sepConj_emp]
    sep_interval
  · have hbeq : (pin.cap == 0#64) = false := beq_eq_false_iff_ne.mpr fun h => h0 h
    simp only [h0, hbeq, Bool.false_eq_true, ↓reduceIte]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _)))) ?_
    bi_entail

theorem vecGhostAt_entails_pin_dealloc (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_dealloc A a ⟨g.cap, g.ptr⟩ g.bytes

theorem header_cells_entails_memRegion_24 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  sep_interval

theorem header_cells_entails_memRegion_32 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16) ⊢ memRegion a 32 := by
  sep_interval

end DropsCommon

theorem header_cells_entails_memRegion_48_shared_lb (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ⊢ memRegion a 48 := by
  sep_interval

namespace DropsCommon

theorem optTailVecAt_entails_dealloc (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        sgnPinDealloc A cap ptr := by
  cases opt with
  | none =>
    unfold optTailVecAt sgnPinDealloc
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    have hslt : noneCap.slt 1#64 = true := by decide
    rw [hsplit, ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
      (b' := a + 16#64) rfl (by bv_omega) (by omega), memRegion_eight (a + 8#64)]
    simp only [hslt, ↓reduceIte]
    bi_entail
  | some g =>
    unfold optTailVecAt sgnPinDealloc
    apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt]
      bi_entail
    refine Entails.trans (sepConj_mono_left hvec) ?_
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
          memRegion (a + 16#64) (size - 16) := by
      rw [show size - 16 = 8 + (size - 24) by omega,
          ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      simpa [htail] using pointsToBytes_entails_memRegion (a + 24#64) g.tail
    refine Entails.sepExists_right g.vec.cap (Entails.sepExists_right g.vec.ptr ?_)
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16)))
    bi_entail

theorem optChainKeyAt_entails_dealloc (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        sgnPinDealloc A cap ptr := by
  cases ck with
  | none =>
    unfold optChainKeyAt sgnPinDealloc
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        memRegion_eight (a + 8#64)]
    simp only [hslt, ↓reduceIte]
    bi_entail
  | some c =>
    unfold optChainKeyAt
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          sgnPinDealloc A pin.cap pin.ptr := by
      unfold sgnPinDealloc
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt]
      bi_entail
    have htail :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ⊢
          memRegion (a + 16#64) 16 := by sep_interval
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr ?_)
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left htail)))
    bi_entail

end DropsCommon

theorem cap_add_one_ne_zero_shared_lb {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have h1 : cap = 0xffffffffffffffff#64 := by
    revert heq; bv_kernel
  subst h1
  revert h; decide

theorem sender_none_entails_memRegion_104_shared_lb (a : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96) ⊢ memRegion a 104 := by
  sep_interval

@[expose] def srkRest_shared_lb (A : RustAlloc) (a : BitVec 64) (g : VecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
    (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
       memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``srkRest_shared_lb, #[1]), (``vecGhostAt, #[2]), (``vecU8At, #[1]), (``optChainKeyAt, #[3]), (``optTailVecAt, #[2]), (``optSenderChainAt, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

theorem vecGhostAt_eq_srkRest_shared_lb (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ srkRest_shared_lb A a g := by
  unfold vecGhostAt vecU8At vecHeader srkRest_shared_lb
  apply Entails.antisymm <;> bi_entail

theorem optSenderChainAt_some_expose_shared_lb (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) ⊢
      ⌜PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey ∧
        g.srk.bytes.length ≤ g.srk.cap.toNat ∧ g.srk.cap.toNat < 2 ^ 63 ∧ g.srk.ptr ≠ 0 ∧
        g.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (a ↦₆₄ g.srk.cap) ∗ srkRest_shared_lb A a g.srk ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + 72#64) := by
  unfold optSenderChainAt
  apply Entails.pure_left; rintro ⟨hpk, _, _, _⟩
  rw [vecGhostAt_eq_srkRest_shared_lb A g.srk a, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr_ne⟩
  refine Entails.pure_right ⟨hpk, hlen, hcap_lt, hptr_ne, cap_add_one_ne_zero_shared_lb hcap_lt⟩ ?_
  bi_entail

theorem chainAt_of_exposed_sender_shared_lb (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain)
    (hpk : PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey)
    (hlen : g.srk.bytes.length ≤ g.srk.cap.toNat)
    (hcap_lt : g.srk.cap.toNat < 2 ^ 63)
    (hptr_ne : g.srk.ptr ≠ 0) :
    (a ↦₆₄ g.srk.cap) ∗ srkRest_shared_lb A a g.srk ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + 72#64) ⊢
    protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
      ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a := by
  unfold protoChainAt
  dsimp only [List.length_nil, List.zip_nil_left]
  refine Entails.pure_right ⟨hpk, by decide, rfl⟩ ?_
  rw [vecGhostAt_eq_srkRest_shared_lb A g.srk a, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_right ⟨hlen, hcap_lt, hptr_ne⟩ ?_
  bi_entail

namespace DropsCommon

theorem optSenderChainAt_some_entails_dealloc1 (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜g.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
        vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗ memRegion (a + 40#64) 8 ∗
        vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
        ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 80#64) ↦₆₄ ckPtr) ∗ memRegion (a + 88#64) 16 ∗
        sgnPinDealloc A ckCap ckPtr := by
  unfold optSenderChainAt
  apply Entails.pure_left; rintro ⟨_, _, _, _⟩
  have h1 : vecGhostAt A g.srk a ⊢
      ⌜g.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ := by
    unfold vecGhostAt
    refine Entails.trans (vecU8At_entails_dealloc A a g.srk.cap g.srk.ptr g.srk.bytes) ?_
    unfold vecHeader vecPinDealloc
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    have hne := cap_add_one_ne_zero_shared_lb hcap_lt
    simp only [beq_iff_eq]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _)))) ?_
    bi_entail
  have h2 := vecGhostAt_entails_pin_dealloc A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_dealloc A g.ck (some sc.chainKey) (a + 72#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  bi_entail

end DropsCommon

theorem sessionTail_entails_memRegion_16_shared_lb (ss : BitVec 64)
    (v1 v2 : BitVec 32) (regIds : List (BitVec 8)) (hreg : regIds.length = 8) :
    ((ss + 0x148#64) ↦₃₂ v1) ∗ ((ss + 0x14c#64) ↦₃₂ v2) ∗ ((ss + 0x150#64) ↦ₛ regIds) ⊢
      memRegion (ss + 328#64) 16 := by
  sep_interval

theorem session_memRegions_entails_344_shared_lb (ss : BitVec 64) :
    memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
      memRegion (ss + 72#64) 24 ∗ memRegion (ss + 96#64) 24 ∗ memRegion (ss + 120#64) 24 ∗
      memRegion (ss + 144#64) 104 ∗ memRegion (ss + 248#64) 48 ∗
      memRegion (ss + 296#64) 32 ∗ memRegion (ss + 328#64) 16 ⊢
      memRegion ss 344 := by
  sep_interval

@[expose, reducible]
def ssFirst3HeadersAt_shared_lb (ss : BitVec 64) (G : SessionGhost) : SepProp :=
  (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8 ∗
  ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗ memRegion (ss + 40#64) 8 ∗
  ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8

namespace DropsCommon

theorem ssFirst3_entails_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    vecGhostAt A G.localIk ss ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ⊢
    ssFirst3HeadersAt_shared_lb ss G ∗
      vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root := by
  refine Entails.trans (sepConj_mono (vecGhostAt_entails_pin_dealloc A G.localIk ss)
    (sepConj_mono (vecGhostAt_entails_pin_dealloc A G.remoteIk (ss + 0x18#64))
      (vecU8At_entails_pin_dealloc A (ss + 0x30#64) G.root (keyToBytes32 st.rootKey)))) ?_
  unfold ssFirst3HeadersAt_shared_lb
  bi_entail

theorem ssFirst3HeadersAt_entails_memRegions (ss : BitVec 64) (G : SessionGhost) :
    ssFirst3HeadersAt_shared_lb ss G ⊢
      memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 := by
  unfold ssFirst3HeadersAt_shared_lb
  sep_interval

end DropsCommon

@[expose, reducible]
def ssTail3HeadersAt_shared_lb (ss : BitVec 64) (pCap pPtr kCap kPtr : BitVec 64)
    (G : SessionGhost) : SepProp :=
  ((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32 ∗
  ((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16 ∗
  ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗ memRegion (ss + 112#64) 8

namespace DropsCommon

theorem ssTail3_entails_dealloc (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost) :
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
    ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
      ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A pCap pPtr ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩ := by
  have h1 := optTailVecAt_entails_dealloc A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have h2 := optTailVecAt_entails_dealloc A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have h3 := vecGhostAt_entails_pin_dealloc A G.alice (ss + 0x60#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  unfold ssTail3HeadersAt_shared_lb
  bi_entail

theorem ssTail3HeadersAt_entails_memRegions (ss : BitVec 64)
    (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) :
    ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ⊢
      memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24 := by
  unfold ssTail3HeadersAt_shared_lb
  sep_interval

theorem sessionStateAt_entails_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
        (ssFirst3HeadersAt_shared_lb ss G ∗
          vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A G.root) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (ss + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
        memRegion (ss + 328#64) 16 := by
  unfold sessionStateAt ssFirst3HeadersAt_shared_lb ssTail3HeadersAt_shared_lb
  apply Entails.pure_left; rintro ⟨_, _, _, _, hreg, _, _⟩
  have h_lik := vecGhostAt_entails_pin_dealloc A G.localIk ss
  have h_rik := vecGhostAt_entails_pin_dealloc A G.remoteIk (ss + 0x18#64)
  have h_rk := vecU8At_entails_pin_dealloc A (ss + 0x30#64) G.root (keyToBytes32 st.rootKey)
  have h_al := vecGhostAt_entails_pin_dealloc A G.alice (ss + 0x60#64)
  have h_pq := vecU8At_entails_pin_dealloc A (ss + 0x78#64) G.pq st.pqRatchetState
  have hp := optTailVecAt_entails_dealloc A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have hk := optTailVecAt_entails_dealloc A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have htail := sessionTail_entails_memRegion_16_shared_lb ss st.sessionVersion st.previousCounter
    G.regIds hreg
  refine Entails.trans (sepConj_mono h_lik (sepConj_mono h_rik (sepConj_mono h_rk
    (sepConj_mono_right (sepConj_mono h_al (sepConj_mono h_pq (sepConj_mono_right
      (sepConj_mono hp (sepConj_mono hk htail))))))))) ?_
  bi_entail

end DropsCommon

/-! ## Common WP and stack helpers -/

theorem SepWP_align_pre_shared_lb {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

theorem SepWP_false_elim_left_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

theorem SepWP_false_elim_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post :=
  SepWP.weaken_pre (by bi_entail) SepWP_false_elim_left_shared_lb

namespace DropsCommon

abbrev SepWP.align_pre := @SepWP_align_pre_shared_lb
abbrev SepWP.false_elim := @SepWP_false_elim_shared_lb
abbrev SepWP.false_elim_left := @SepWP_false_elim_left_shared_lb

theorem header24_weaken (v cap ptr : BitVec 64) (Rest : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest ⊢
      memRegion v 24 ∗ Rest := by
  rw [← sepConj_assoc, ← sepConj_assoc]
  exact sepConj_mono_left (by sep_interval)

theorem drop4_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => Satisfies.mono ?_ (h1 hm), h2⟩
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

end DropsCommon

theorem pq_header24_weaken_shared_lb (ss cap ptr : BitVec 64) (Rest : SepProp) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗ Rest ⊢
      memRegion (ss + 120#64) 24 ∗ Rest := by
  rw [← sepConj_assoc, ← sepConj_assoc]
  exact sepConj_mono_left (by sep_interval)

theorem drop6_strengthen_post_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => Satisfies.mono ?_ (h1 hm), h2⟩
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  apply Entails.sepExists_elim; intro x_4; refine Entails.sepExists_right x_4 ?_
  apply Entails.sepExists_elim; intro x_5; refine Entails.sepExists_right x_5 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
