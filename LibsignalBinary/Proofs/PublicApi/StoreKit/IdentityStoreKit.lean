/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit

/-!
# Abstract `IdentityKeyStore` Interface (`IdentityStoreSpec`, `IdentityStoreKitOk`)

Abstract store-kit interface for `dyn IdentityKeyStore` (`is_trusted_identity` at `id_vt + 0x30`
and `save_identity` at `id_vt + 0x28`), bundling vtable and future offsets, separation-logic state
`identityAt`, pure answer relations `trustRel` / `saveRel`, state updates `trustUpdate` /
`saveUpdate`, and trace projections `trustEvs` / `saveEvs`.
-/

/-- Hook bundle for Stage 3 without any session-store or identity-store hooks
    (used by generic MessageDecrypt/MessageEncrypt when both `SessionStore` and `IdentityKeyStore` are parameterized). -/
structure PublicApiHooksNoStores (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S abs where
  timeAdd : HookSat abs timeAddHookName timeAddSpec
  durationSince : HookSat abs durationSinceHookName durationSinceSpec
  stringClone : HookSat abs stringCloneHookName (stringCloneSpec A)

theorem PublicApiHooksNoSessionStore.toNoStores {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : PublicApiHooksNoSessionStore C A S abs) : PublicApiHooksNoStores C A S abs where
  toTripleRatchetHooks := h.toTripleRatchetHooks
  timeAdd := h.timeAdd
  durationSince := h.durationSince
  stringClone := h.stringClone

theorem PublicApiHooks.toNoStores {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (h : PublicApiHooks C A S encRecord abs) : PublicApiHooksNoStores C A S abs :=
  PublicApiHooksNoSessionStore.toNoStores (PublicApiHooks.toNoSessionStore h)

/-- The 48-byte `Poll<Result<bool, SPE>>` written by `is_trusted_identity`'s future poll:
    on `Ok(t)`, word 0 is `-2` (`0xFFFFFFFFFFFFFFFE`), byte 8 is `1` (`true`) or `0` (`false`),
    and bytes `9..48` are uninspected (`memRegion (out + 9) 39`);
    on `Err(())`, word 0 is `speWord 26` followed by the `ApplicationCallbackError` payload. -/
@[expose] def trustPollOutAt (b out : BitVec 64) : Except Unit Bool → SepProp
  | .ok t =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗
      memRegion (out + 9#64) 39
  | .error () =>
    (out ↦₆₄ 0x800000000000001A#64) ∗ ((out + 8#64) ↦₆₄ b) ∗
      errTailAt b out ∗ memRegion (out + 0x28#64) 8

/-- The 48-byte `Poll<Result<IdentityChange, SPE>>` written by `save_identity`'s future poll:
    on `Ok(c)`, word 0 is `-2` (`0xFFFFFFFFFFFFFFFE`), `u32` at `+8` is `1` (`replacedExisting`)
    or `0` (`newOrUnchanged`), and bytes `12..48` are uninspected (`memRegion (out + 0xc) 36`);
    on `Err(())`, word 0 is `speWord 26` followed by the `ApplicationCallbackError` payload. -/
@[expose] def savePollOutAt (b out : BitVec 64) : Except Unit IdentityChange → SepProp
  | .ok c =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      memRegion (out + 0xc#64) 36
  | .error () =>
    (out ↦₆₄ 0x800000000000001A#64) ∗ ((out + 8#64) ↦₆₄ b) ∗
      errTailAt b out ∗ memRegion (out + 0x28#64) 8

/-- Pure data, trace projections, answer relations, and separation-logic predicates of an
    `IdentityKeyStore` implementation. -/
structure IdentityStoreSpec (A : RustAlloc) (b : BitVec 64) where
  /-- `IdentityKeyStore` trait-object vtable address. -/
  id_vt : BitVec 64
  /-- Logical state of the identity store (`Unit` for `E₀`). -/
  IdState : Type
  /-- Separation-logic predicate for the identity store object at `self` (`emp` for `E₀`). -/
  identityAt : BitVec 64 → IdState → SepProp
  /-- Store-side remote address invariant required by `is_trusted_identity` / `save_identity` polls
      (`fun _ => True` for `E₀`, `rem = peer.val` for `InMem`). -/
  addrOk : AddrVal → Prop := fun _ => True
  /-- Files the store's polls read (`True` for `E₀` / `InMem`; `(· = F0)` for the CLI's Files
      kits). See `SessionStoreSpec.envOk`. -/
  envOk : FsFiles → Prop := fun _ => True
  /-- Point-wise file-descriptor predicate carried across the store's ops (`True` by default for
      `E₀` / `InMem`; `FdsGe3Closed` for the CLI's file-backed kits). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Post-`is_trusted_identity` state update (`fun st _ _ _ _ => st` for `E₀`). -/
  trustUpdate : IdState → AddrVal → IdentityKey → Direction → Except Unit Bool → IdState
  /-- Post-`save_identity` state update (`fun st _ _ _ => st` for `E₀`). -/
  saveUpdate : IdState → AddrVal → IdentityKey → Except Unit IdentityChange → IdState
  /-- Pure relation tying the identity store state, remote address, identity key, and direction
      to the `is_trusted_identity` answer (`fun _ _ _ _ _ => True` for `E₀`). -/
  trustRel : IdState → AddrVal → IdentityKey → Direction → Except Unit Bool → Prop
  /-- Pure relation tying the identity store state, remote address, and identity key to the
      `save_identity` answer (`fun _ _ _ _ => True` for `E₀`). -/
  saveRel : IdState → AddrVal → IdentityKey → Except Unit IdentityChange → Prop
  /-- Trace events emitted by an `is_trusted_identity` call (`[trustEvent ...]` for `E₀`, `[]` for `InMem`). -/
  trustEvs : AddrVal → IdentityKey → Direction → Except Unit Bool → List TraceEvent
  /-- Trace events emitted by a `save_identity` call (`[saveEvent ...]` for `E₀`, `[]` for `InMem`). -/
  saveEvs : AddrVal → IdentityKey → Except Unit IdentityChange → List TraceEvent
  /-- Slot target offset for `is_trusted_identity` (`id_vt + 0x30 ↦ b + trustShimOff`). -/
  trustShimOff : BitVec 64
  /-- Future vtable offset for `is_trusted_identity` (`b + trustFutVtOff`). -/
  trustFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `is_trusted_identity` (`b + trustPollOff`). -/
  trustPollOff : BitVec 64
  /-- Drop entrypoint offset for `is_trusted_identity` future (`0x42a44` in `E₀`). -/
  trustFutDropOff : BitVec 64
  /-- Box allocation size in bytes for `is_trusted_identity` future (`32` in `E₀`). -/
  trustBoxSize : Nat
  /-- Slot target offset for `save_identity` (`id_vt + 0x28 ↦ b + saveShimOff`). -/
  saveShimOff : BitVec 64
  /-- Future vtable offset for `save_identity` (`b + saveFutVtOff`). -/
  saveFutVtOff : BitVec 64
  /-- Poll entrypoint offset for `save_identity` (`b + savePollOff`). -/
  savePollOff : BitVec 64
  /-- Drop entrypoint offset for `save_identity` future (`0x42a44` in `E₀`). -/
  saveFutDropOff : BitVec 64
  /-- Box allocation size in bytes for `save_identity` future (`32` in `E₀`). -/
  saveBoxSize : Nat
  /-- Stack budget for `is_trusted_identity` shim. -/
  trustShimStack : Nat
  /-- Stack budget for `is_trusted_identity` poll. -/
  trustPollStack : Nat
  /-- Stack budget for `save_identity` shim. -/
  saveShimStack : Nat
  /-- Stack budget for `save_identity` poll. -/
  savePollStack : Nat
  /-- Separation-logic predicate for the `is_trusted_identity` future box contents (excluding `A.live`). -/
  trustBoxAt : (box self addrA keyA : BitVec 64) → (state dir : BitVec 8) → SepProp
  /-- Separation-logic predicate for the `save_identity` future box contents (excluding `A.live`). -/
  saveBoxAt : (box self addrA keyA : BitVec 64) → (state : BitVec 8) → SepProp
  /-- Any `trustBoxAt` state entails raw `memRegion` of `trustBoxSize` bytes for deallocation. -/
  trustBoxAt_memRegion : ∀ box self addrA keyA st dir,
    trustBoxAt box self addrA keyA st dir ⊢ memRegion box trustBoxSize
  /-- Any `saveBoxAt` state entails raw `memRegion` of `saveBoxSize` bytes for deallocation. -/
  saveBoxAt_memRegion : ∀ box self addrA keyA st,
    saveBoxAt box self addrA keyA st ⊢ memRegion box saveBoxSize
  /-- `trustBoxSize` is non-zero as a 64-bit word (so `__rust_dealloc` is not skipped by `cbz`). -/
  trustBoxSize_ne_zero : BitVec.ofNat 64 trustBoxSize ≠ 0#64
  /-- `saveBoxSize` is non-zero as a 64-bit word (so `__rust_dealloc` is not skipped by `cbz`). -/
  saveBoxSize_ne_zero : BitVec.ofNat 64 saveBoxSize ≠ 0#64
  /-- `trustBoxSize` fits in 64 bits. -/
  trustBoxSize_lt : trustBoxSize < 2 ^ 64
  /-- `saveBoxSize` fits in 64 bits. -/
  saveBoxSize_lt : saveBoxSize < 2 ^ 64
  /-- `b + trustFutDropOff` is non-zero for page-aligned `b` (so `cbz` before `futDrop` does not skip). -/
  trustFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + trustFutDropOff ≠ 0#64
  /-- `b + saveFutDropOff` is non-zero for page-aligned `b` (so `cbz` before `futDrop` does not skip). -/
  saveFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + saveFutDropOff ≠ 0#64

namespace IdentityStoreSpec

variable {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)

/-- Resulting `IdState` after executing a list of `StoreCall`s starting from `ist0`. -/
@[expose] def idFinal (ist0 : ikit.IdState) (ans : StoreAnswers (List (BitVec 8)) Unit) :
    List (StoreCall AddrVal (List (BitVec 8))) → ikit.IdState
  | [] => ist0
  | .isTrustedIdentity rem k dir :: cs =>
      idFinal (ikit.trustUpdate ist0 rem k dir ans.isTrustedIdentity) ans cs
  | .saveIdentity rem k :: cs =>
      idFinal (ikit.saveUpdate ist0 rem k ans.saveIdentity) ans cs
  | _ :: cs => idFinal ist0 ans cs

/-- Pure relation tying `ist0` and `ans` across a list of `StoreCall`s: requires `ikit.trustRel`
    on every `.isTrustedIdentity` call and `ikit.saveRel` on every `.saveIdentity` call
    (threading `trustUpdate` / `saveUpdate` across the call list). -/
@[expose] def idCallsRel (ist0 : ikit.IdState) (ans : StoreAnswers (List (BitVec 8)) Unit) :
    List (StoreCall AddrVal (List (BitVec 8))) → Prop
  | [] => True
  | .isTrustedIdentity rem k dir :: cs =>
      ikit.trustRel ist0 rem k dir ans.isTrustedIdentity ∧
      idCallsRel (ikit.trustUpdate ist0 rem k dir ans.isTrustedIdentity) ans cs
  | .saveIdentity rem k :: cs =>
      ikit.saveRel ist0 rem k ans.saveIdentity ∧
      idCallsRel (ikit.saveUpdate ist0 rem k ans.saveIdentity) ans cs
  | _ :: cs => idCallsRel ist0 ans cs

/-- Combined trace events emitted by a single `StoreCall` under `kit : SessionStoreSpec A b` and
    `ikit : IdentityStoreSpec A b`. -/
@[expose] def callEvs (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    StoreCall AddrVal (List (BitVec 8)) → List TraceEvent
  | .loadSession rem => kit.loadEvs encRecord rem ans.loadSession
  | .isTrustedIdentity rem k dir => ikit.trustEvs rem k dir ans.isTrustedIdentity
  | .saveIdentity rem k => ikit.saveEvs rem k ans.saveIdentity
  | .storeSession rem r' => kit.storeEvs encRecord rem r' ans.storeSession

/-- Combined trace events emitted by a list of `StoreCall`s under `kit` and `ikit`. -/
@[expose] def traceOfWith (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8)))) : List TraceEvent :=
  calls.flatMap (ikit.callEvs kit encRecord ans)

@[simp] theorem traceOfWith_nil (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ikit.traceOfWith kit encRecord ans [] = [] := rfl

@[simp] theorem traceOfWith_load (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rem : AddrVal) :
    ikit.traceOfWith kit encRecord ans [.loadSession rem] =
      kit.loadEvs encRecord rem ans.loadSession := by
  simp [traceOfWith, callEvs]

@[simp] theorem traceOfWith_load_trust (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rem : AddrVal) (k : IdentityKey) (dir : Direction) :
    ikit.traceOfWith kit encRecord ans [.loadSession rem, .isTrustedIdentity rem k dir] =
      kit.loadEvs encRecord rem ans.loadSession ++
      ikit.trustEvs rem k dir ans.isTrustedIdentity := by
  simp [traceOfWith, callEvs]

@[simp] theorem traceOfWith_load_trust_save (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rem : AddrVal) (k : IdentityKey) (dir : Direction) :
    ikit.traceOfWith kit encRecord ans
      [.loadSession rem, .isTrustedIdentity rem k dir, .saveIdentity rem k] =
      kit.loadEvs encRecord rem ans.loadSession ++
      ikit.trustEvs rem k dir ans.isTrustedIdentity ++
      ikit.saveEvs rem k ans.saveIdentity := by
  simp [traceOfWith, callEvs, List.append_assoc]

@[simp] theorem traceOfWith_all4 (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rem : AddrVal) (k : IdentityKey)
    (dir : Direction) (r' : SessionRecord (List (BitVec 8))) :
    ikit.traceOfWith kit encRecord ans
      [.loadSession rem, .isTrustedIdentity rem k dir, .saveIdentity rem k, .storeSession rem r'] =
      kit.loadEvs encRecord rem ans.loadSession ++
      ikit.trustEvs rem k dir ans.isTrustedIdentity ++
      ikit.saveEvs rem k ans.saveIdentity ++
      kit.storeEvs encRecord rem r' ans.storeSession := by
  simp [traceOfWith, callEvs, List.append_assoc]

@[simp] theorem traceOfWith_load_store (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rem : AddrVal)
    (r' : SessionRecord (List (BitVec 8))) :
    ikit.traceOfWith kit encRecord ans [.loadSession rem, .storeSession rem r'] =
      kit.loadEvs encRecord rem ans.loadSession ++
      kit.storeEvs encRecord rem r' ans.storeSession := by
  simp [traceOfWith, callEvs]

end IdentityStoreSpec

theorem hookTrustBoxAt_memRegion (box self addrA keyA : BitVec 64) (st d : BitVec 8) :
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
      ((box + 0x18#64) ↦₈ st) ∗ ((box + 0x19#64) ↦₈ d) ∗
      memRegion (box + 0x1a#64) 6 ⊢ memRegion box 32 := by
  rw [show (32 : Nat) = 8 + (8 + (8 + (1 + (1 + 6)))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64 + 1#64) 1 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))))

theorem hookSaveBoxAt_memRegion (box self addrA keyA : BitVec 64) (st : BitVec 8) :
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
      ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7 ⊢ memRegion box 32 := by
  rw [show (32 : Nat) = 8 + (8 + (8 + (1 + 7))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo8_entails_memRegion _ _))))

/-- Canonical `HookIdentityStore` instance of `IdentityStoreSpec` at a given vtable address `id_vt`
    (`b + 0x4dc20#64` in `E₀`, `b + 0x4dd88#64` in Variant M). -/
@[expose] def hookIdentityStoreSpecAt (A : RustAlloc) (b id_vt : BitVec 64) : IdentityStoreSpec A b where
  id_vt := id_vt
  IdState := Unit
  identityAt := fun _ _ => .emp
  trustUpdate := fun _ _ _ _ _ => ()
  saveUpdate := fun _ _ _ _ => ()
  trustRel := fun _ _ _ _ _ => True
  saveRel := fun _ _ _ _ => True
  trustEvs := fun rem k dir ans => [trustEvent rem k dir ans]
  saveEvs := fun rem k ans => [saveEvent rem k ans]
  trustShimOff := 0#64
  trustFutVtOff := 0#64
  trustPollOff := 0#64
  trustFutDropOff := 256#64
  trustBoxSize := 32
  saveShimOff := 0#64
  saveFutVtOff := 0#64
  savePollOff := 0#64
  saveFutDropOff := 256#64
  saveBoxSize := 32
  trustShimStack := identityShimStack
  trustPollStack := identityPollStack
  saveShimStack := identityShimStack
  savePollStack := identityPollStack
  trustBoxAt := fun box self addrA keyA st d =>
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
      ((box + 0x18#64) ↦₈ st) ∗ ((box + 0x19#64) ↦₈ d) ∗
      memRegion (box + 0x1a#64) 6
  saveBoxAt := fun box self addrA keyA st =>
    (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
      ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7
  trustBoxAt_memRegion := hookTrustBoxAt_memRegion
  saveBoxAt_memRegion := hookSaveBoxAt_memRegion
  trustBoxSize_ne_zero := by decide
  saveBoxSize_ne_zero := by decide
  trustBoxSize_lt := by decide
  saveBoxSize_lt := by decide
  trustFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - 256#64 by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  saveFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - 256#64 by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

/-- Canonical `E₀` (`HookIdentityStore`) instance of `IdentityStoreSpec`. -/
abbrev hookIdentityStoreSpec (A : RustAlloc) (b : BitVec 64) : IdentityStoreSpec A b :=
  hookIdentityStoreSpecAt A b b

theorem hookIdentityStoreSpecAt_idCallsRel_true {A : RustAlloc} {b id_vt : BitVec 64}
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ calls, (hookIdentityStoreSpecAt A b id_vt).idCallsRel () ans calls := by
  intro calls
  induction calls with
  | nil => trivial
  | cons c cs ih =>
    cases c
    · exact ih
    · exact ⟨trivial, ih⟩
    · exact ⟨trivial, ih⟩
    · exact ih

theorem hookIdentityStoreSpec_idCallsRel_true {A : RustAlloc} {b : BitVec 64}
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ calls, (hookIdentityStoreSpec A b).idCallsRel () ans calls :=
  hookIdentityStoreSpecAt_idCallsRel_true ans

theorem hookIdentityStoreSpecAt_traceOfWith_eq_hook {A : RustAlloc} {b id_vt : BitVec 64}
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (hookIdentityStoreSpecAt A b id_vt).traceOfWith (hookSessionStoreSpec A b) encRecord ans calls =
      calls.map (storeEvent encRecord ans) := by
  induction calls with
  | nil => rfl
  | cons c cs ih =>
    unfold IdentityStoreSpec.traceOfWith at ih ⊢
    rw [List.flatMap_cons, ih, List.map_cons]
    cases c <;> rfl

/-- Generic `is_trusted_identity` shim spec parameterized by `ikit : IdentityStoreSpec A b`. -/
@[expose] def kitTrustShimSpec {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    Spec (IdentityShimCall × BitVec 8) where
  pre := fun (x, d) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
      (s.readReg64 .x3).setWidth 8 = d⌝ ∗ A.pool ∗ stackAt s.sp ikit.trustShimStack
  post := fun (x, d) s0 sf =>
    ⌜sf.readReg64 .x1 = b + ikit.trustFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) ikit.trustBoxSize 8 ∗
      ikit.trustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
      A.pool ∗ stackAt s0.sp ikit.trustShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `save_identity` shim spec parameterized by `ikit : IdentityStoreSpec A b`. -/
@[expose] def kitSaveShimSpec {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    Spec IdentityShimCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA⌝ ∗
      A.pool ∗ stackAt s.sp ikit.saveShimStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = b + ikit.saveFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) ikit.saveBoxSize 8 ∗
      ikit.saveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
      A.pool ∗ stackAt s0.sp ikit.saveShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `is_trusted_identity` poll spec parameterized by `ikit : IdentityStoreSpec A b`. -/
@[expose] def kitTrustPollSpec {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState) where
  pre := fun (x, d, self, ist0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp ikit.trustPollStack
  post := fun (x, d, self, ist0) s0 sf =>
    ∃∗ ans : Except Unit Bool,
      ⌜ikit.trustRel ist0 x.call.addr.val x.call.key d ans ∧
        sf.trace = s0.trace ++ ikit.trustEvs x.call.addr.val x.call.key d ans⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
      ikit.identityAt self (ikit.trustUpdate ist0 x.call.addr.val x.call.key d ans) ∗
      trustPollOutAt b x.out ans ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp ikit.trustPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `save_identity` poll spec parameterized by `ikit : IdentityStoreSpec A b`. -/
@[expose] def kitSavePollSpec {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState) where
  pre := fun (x, self, ist0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp ikit.savePollStack
  post := fun (x, self, ist0) s0 sf =>
    ∃∗ ans : Except Unit IdentityChange,
      ⌜ikit.saveRel ist0 x.call.addr.val x.call.key ans ∧
        sf.trace = s0.trace ++ ikit.saveEvs x.call.addr.val x.call.key ans⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
      ikit.identityAt self (ikit.saveUpdate ist0 x.call.addr.val x.call.key ans) ∗
      savePollOutAt b x.out ans ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp ikit.savePollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- The `is_trusted_identity` poll spec with `ikit.envOk` on the entry files. -/
abbrev kitTrustPollSpecE {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitTrustPollSpec ikit) fun s => ikit.envOk s.fs.files

/-- The `save_identity` poll spec with `ikit.envOk` on the entry files. -/
abbrev kitSavePollSpecE {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitSavePollSpec ikit) fun s => ikit.envOk s.fs.files

/-- The identity store's own trace events contain no file system event (`FsCtx`'s `Q`). -/
@[expose] def IdentityStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : Prop :=
  (∀ rem k dir ans, NoFsEv (ikit.trustEvs rem k dir ans)) ∧
    (∀ rem k ans, NoFsEv (ikit.saveEvs rem k ans))

end CryptoVerification.LibsignalPublicApi.StoreKit.Identity

namespace CryptoVerification.LibsignalPublicApi.StoreKit

export Identity
  (PublicApiHooksNoStores PublicApiHooksNoSessionStore.toNoStores PublicApiHooks.toNoStores
   trustPollOutAt savePollOutAt
   IdentityStoreSpec
   hookIdentityStoreSpecAt hookIdentityStoreSpec
   hookIdentityStoreSpecAt_idCallsRel_true hookIdentityStoreSpec_idCallsRel_true
   hookIdentityStoreSpecAt_traceOfWith_eq_hook
   kitTrustShimSpec kitSaveShimSpec
   kitTrustPollSpec kitSavePollSpec kitTrustPollSpecE kitSavePollSpecE)

end CryptoVerification.LibsignalPublicApi.StoreKit
