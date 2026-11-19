/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty
public import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Skeleton
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Self-Identity Store Kit (`IdentitySelfStoreSpec`, `IdentitySelfStoreKitOkI`)

Store-kit contracts for the self-identity methods on `dyn IdentityKeyStore` invoked during
`decrypt_prekey`:
* `get_identity_key_pair` (`ikit.id_vt + 0x18`), writing 72-byte
  `Poll::Ready<Result<IdentityKeyPair, SignalProtocolError>>`;
* `get_local_registration_id` (`ikit.id_vt + 0x20`), writing 48-byte niche-encoded
  `Poll::Ready<Result<u32, SignalProtocolError>>`.

Parameterized over an existing `ikit : IdentityStoreSpec A b` so self-identity and peer-identity
operations share `ikit.id_vt`, `ikit.IdState`, `ikit.identityAt`, and `ikit.envOk`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApiRepr (storeHookStr)
open CryptoVerification.LibsignalTripleRatchet
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-! ## `IdentitySelfStoreSpec` -/

/-- The self-identity methods (`get_identity_key_pair` at `ikit.id_vt + 0x18`,
`get_local_registration_id` at `ikit.id_vt + 0x20`) of an identity store whose state is
`ikit.IdState`. -/
structure IdentitySelfStoreSpec {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) where
  /-- Point-wise file-descriptor predicate carried across the self-identity ops (`True` by default
      for in-memory stores; `FdsGe3Closed` for the CLI's file-backed store). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Kit witness type for `get_identity_key_pair` `Err` returns (`PEmpty` when infallible). -/
  KpErr : Type
  /-- Kit witness type for `get_local_registration_id` `Err` returns (`PEmpty` when infallible). -/
  RegIdErr : Type
  /-- 48-byte `SignalProtocolError` layout for `KpErr`. -/
  kpErr : SpeErrSpec KpErr
  /-- 48-byte `SignalProtocolError` layout for `RegIdErr`. -/
  regIdErr : SpeErrSpec RegIdErr
  /-- Pure relation tying `ist0` to the `get_identity_key_pair` answer. -/
  kpRel : ikit.IdState → Except KpErr IdentityKeyPair → Prop
  /-- Pure relation tying `ist0` to the `get_local_registration_id` answer. -/
  regIdRel : ikit.IdState → Except RegIdErr (BitVec 32) → Prop
  /-- Trace events emitted by a `get_identity_key_pair` poll. -/
  kpEvs : Except KpErr IdentityKeyPair → List TraceEvent
  /-- Trace events emitted by a `get_local_registration_id` poll. -/
  regIdEvs : Except RegIdErr (BitVec 32) → List TraceEvent
  /-- Code/vtable offsets for `get_identity_key_pair` shim, future vtable, poll, and drop. -/
  kpShimOff : BitVec 64
  kpFutVtOff : BitVec 64
  kpPollOff : BitVec 64
  kpFutDropOff : BitVec 64
  /-- Code/vtable offsets for `get_local_registration_id` shim, future vtable, poll, and drop. -/
  regIdShimOff : BitVec 64
  regIdFutVtOff : BitVec 64
  regIdPollOff : BitVec 64
  regIdFutDropOff : BitVec 64
  /-- Heap box sizes in bytes for the two futures (`16` in both CLI and InMem). -/
  kpBoxSize : Nat
  regIdBoxSize : Nat
  /-- Stack budgets in bytes for the two shims and two polls. -/
  kpShimStack : Nat
  kpPollStack : Nat
  regIdShimStack : Nat
  regIdPollStack : Nat
  /-- Future box separation-logic predicates (`state = 0#8` before first poll, `1#8` after). -/
  kpBoxAt : (box self : BitVec 64) → (state : BitVec 8) → SepProp
  regIdBoxAt : (box self : BitVec 64) → (state : BitVec 8) → SepProp
  /-- Any `kpBoxAt` state entails raw `memRegion` of `kpBoxSize` bytes for deallocation. -/
  kpBoxAt_memRegion : ∀ box self st, kpBoxAt box self st ⊢ memRegion box kpBoxSize
  /-- Any `regIdBoxAt` state entails raw `memRegion` of `regIdBoxSize` bytes for deallocation. -/
  regIdBoxAt_memRegion : ∀ box self st, regIdBoxAt box self st ⊢ memRegion box regIdBoxSize
  /-- `kpBoxSize` is non-zero as a 64-bit word (so `cbz` before `__rust_dealloc` does not skip). -/
  kpBoxSize_ne_zero : BitVec.ofNat 64 kpBoxSize ≠ 0#64
  /-- `regIdBoxSize` is non-zero as a 64-bit word. -/
  regIdBoxSize_ne_zero : BitVec.ofNat 64 regIdBoxSize ≠ 0#64
  /-- `kpBoxSize` fits in 64 bits. -/
  kpBoxSize_lt : kpBoxSize < 2 ^ 64
  /-- `regIdBoxSize` fits in 64 bits. -/
  regIdBoxSize_lt : regIdBoxSize < 2 ^ 64
  /-- `b + kpFutDropOff` is non-zero for page-aligned `b`. -/
  kpFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + kpFutDropOff ≠ 0#64
  /-- `b + regIdFutDropOff` is non-zero for page-aligned `b`. -/
  regIdFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + regIdFutDropOff ≠ 0#64

/-! ## Poll Output Layouts (`Poll<Result<IdentityKeyPair, SPE>>` / `Poll<Result<u32, SPE>>`) -/

/-- The 72-byte `Poll::Ready<Result<IdentityKeyPair, SignalProtocolError>>` written to `out` by
`get_identity_key_pair`'s future poll:
* `.ok kp`: byte `0#8` at `out`, 32-byte serialized public key at `out + 1`, 32-byte private key
  at `out + 0x21`, and 7 bytes of trailing padding at `out + 0x41` (matching
  `RecordCodecsBinary.identityKeyPairResultAt A out (.ok kp)`);
* `.error e`: byte `1#8` at `out`, 7 bytes of padding at `out + 1`, the 48-byte
  `speErrAt skit.kpErr (out + 8) e`, and 16 bytes of trailing padding at `out + 0x38`. -/
@[expose] def kpPollOutAt {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (out : BitVec 64) :
    Except skit.KpErr IdentityKeyPair → SepProp
  | .ok kp =>
      (out ↦₈ 0#8) ∗
        ((out + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((out + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        memRegion (out + 0x41#64) 7
  | .error e =>
      (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
        speErrAt skit.kpErr (out + 8#64) e ∗ memRegion (out + 0x38#64) 16

/-- The 48-byte `Poll::Ready<Result<u32, SignalProtocolError>>` written to `out` by
`get_local_registration_id`'s future poll:
* `.ok reg`: word `0xFFFFFFFFFFFFFFFE#64` (`-2`) at `out`, 32-bit registration ID `reg` at
  `out + 8`, and 36 bytes of trailing uninspected payload/padding at `out + 0xc`;
* `.error e`: the 48-byte `SignalProtocolError` `speErrAt skit.regIdErr out e`. -/
@[expose] def regIdPollOutAt {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (out : BitVec 64) :
    Except skit.RegIdErr (BitVec 32) → SepProp
  | .ok reg =>
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
        memRegion (out + 0xc#64) 36
  | .error e => speErrAt skit.regIdErr out e

/-! ## Generic Shim and Poll Contracts -/

/-- Generic `get_identity_key_pair` shim spec parameterized by `skit : IdentitySelfStoreSpec ikit`.
Takes `self` in `x0` and returns `(box, b + skit.kpFutVtOff)` in `(x0, x1)` with `box ≠ 0#64` and
8-aligned. -/
@[expose] def kitKpShimSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Spec (BitVec 64) where
  pre := fun self s =>
    ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp skit.kpShimStack
  post := fun self s0 sf =>
    ⌜sf.readReg64 .x1 = b + skit.kpFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) skit.kpBoxSize 8 ∗
      skit.kpBoxAt (sf.readReg64 .x0) self 0#8 ∗
      A.pool ∗ stackAt s0.sp skit.kpShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_local_registration_id` shim spec parameterized by
`skit : IdentitySelfStoreSpec ikit`. Takes `self` in `x0` and returns
`(box, b + skit.regIdFutVtOff)` in `(x0, x1)` with `box ≠ 0#64` and 8-aligned. -/
@[expose] def kitRegIdShimSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Spec (BitVec 64) where
  pre := fun self s =>
    ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp skit.regIdShimStack
  post := fun self s0 sf =>
    ⌜sf.readReg64 .x1 = b + skit.regIdFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) skit.regIdBoxSize 8 ∗
      skit.regIdBoxAt (sf.readReg64 .x0) self 0#8 ∗
      A.pool ∗ stackAt s0.sp skit.regIdShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_identity_key_pair` poll spec parameterized by `skit : IdentitySelfStoreSpec ikit`.
Ghost state `(fut, out, self, ist0)`: reads `ikit.identityAt self ist0` without modifying `ist0`
and writes `kpPollOutAt skit out ans` (`72` bytes). -/
@[expose] def kitKpPollSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) where
  pre := fun (fut, out, self, ist0) s =>
    ⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = out⌝ ∗
      skit.kpBoxAt fut self 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion out 72 ∗
      A.pool ∗ stackAt s.sp skit.kpPollStack
  post := fun (fut, out, self, ist0) s0 sf =>
    ∃∗ ans : Except skit.KpErr IdentityKeyPair,
      ⌜skit.kpRel ist0 ans ∧ sf.trace = s0.trace ++ skit.kpEvs ans⌝ ∗
      skit.kpBoxAt fut self 1#8 ∗
      ikit.identityAt self ist0 ∗
      kpPollOutAt skit out ans ∗
      A.pool ∗ stackAt s0.sp skit.kpPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_local_registration_id` poll spec parameterized by
`skit : IdentitySelfStoreSpec ikit`. Ghost state `(fut, out, self, ist0)`: reads
`ikit.identityAt self ist0` without modifying `ist0` and writes `regIdPollOutAt skit out ans`
(`48` bytes). -/
@[expose] def kitRegIdPollSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) where
  pre := fun (fut, out, self, ist0) s =>
    ⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = out⌝ ∗
      skit.regIdBoxAt fut self 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion out 48 ∗
      A.pool ∗ stackAt s.sp skit.regIdPollStack
  post := fun (fut, out, self, ist0) s0 sf =>
    ∃∗ ans : Except skit.RegIdErr (BitVec 32),
      ⌜skit.regIdRel ist0 ans ∧ sf.trace = s0.trace ++ skit.regIdEvs ans⌝ ∗
      skit.regIdBoxAt fut self 1#8 ∗
      ikit.identityAt self ist0 ∗
      regIdPollOutAt skit out ans ∗
      A.pool ∗ stackAt s0.sp skit.regIdPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- The `get_identity_key_pair` poll spec with `ikit.envOk` on the entry files. -/
abbrev kitKpPollSpecE {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitKpPollSpec skit) fun s => ikit.envOk s.fs.files

/-- The `get_local_registration_id` poll spec with `ikit.envOk` on the entry files. -/
abbrev kitRegIdPollSpecE {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitRegIdPollSpec skit) fun s => ikit.envOk s.fs.files

/-! ### In-Image Poll Contracts (`logOff img` and `.inImage img`) -/

/-- The self-identity methods' own trace events contain no file-system event (`FsCtx`'s `Q`). -/
@[expose] def IdentitySelfStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Prop :=
  (∀ ans, NoFsEv (skit.kpEvs ans)) ∧
    (∀ ans, NoFsEv (skit.regIdEvs ans))

/-! ## Vtable and Code Bundles -/

/-- Own-identity memory layout (`self + 0x30..0x70` key pair and `self + 0x70` `u32`
registration ID) of `InMemIdentityKeyStore`. -/
@[expose] def inMemSelfIdentityAt (self : BitVec 64) (st : IdentityKeyPair × BitVec 32) : SepProp :=
  ((self + 0x30#64) ↦ₛ st.1.identityKey.publicKey.bytes.toList) ∗
    ((self + 0x50#64) ↦ₛ st.1.privateKey.bytes.toList) ∗
    ((self + 0x70#64) ↦₃₂ st.2)

/-- Local witness `IdentityStoreSpec` owning `InMemIdentityKeyStore`'s self key pair and local
registration ID cells. -/
@[expose] def inMemSelfIdentityStoreSpec (A : RustAlloc) (b : BitVec 64) : IdentityStoreSpec A b :=
  { hookIdentityStoreSpec A b with
    IdState := IdentityKeyPair × BitVec 32
    identityAt := inMemSelfIdentityAt
    trustUpdate := fun st _ _ _ _ => st
    saveUpdate := fun st _ _ _ => st
    trustRel := fun _ _ _ _ _ => True
    saveRel := fun _ _ _ _ => True }

section InMemWitness

open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
open CryptoVerification.E2E.InMem.IdentityKeyStoreImpl
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_sp_inMemSelf (s : Arm64.State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) (m : Memory)
    (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

private theorem memRegion_16_inMemSelf (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₈ b0) ∗ memRegion (p + 9#64) 7) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_inMemSelfShim (sp : BitVec 64) :
    stackAt sp inMemId16ShimStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem sepWPp_pure_mid_inMemSelf {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : Arm64.State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 by ac_rfl]
  exact SepWPp.pure_elim h

private theorem pointsToBytes_len32_words4 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (w0 w1 w2 w3 : BitVec 64), ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  have hw0 : (bs.take 8).length = 8 := by simp [h]
  have hw1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have hw2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have hw3 : (bs.drop 24).length = 8 := by simp [h]
  obtain ⟨w0, hw0_eq⟩ := exists_unpack64_of_length_8 hw0
  obtain ⟨w1, hw1_eq⟩ := exists_unpack64_of_length_8 hw1
  obtain ⟨w2, hw2_eq⟩ := exists_unpack64_of_length_8 hw2
  obtain ⟨w3, hw3_eq⟩ := exists_unpack64_of_length_8 hw3
  have hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 := by
    rw [← hw0_eq, ← hw1_eq, ← hw2_eq, ← hw3_eq]
    simp only [List.append_assoc]
    have s2 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
      have := List.take_append_drop 8 (bs.drop 16)
      rwa [List.drop_drop] at this
    have s1 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
      have := List.take_append_drop 8 (bs.drop 8)
      rwa [List.drop_drop] at this
    rw [s2, s1, List.take_append_drop]
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [hbs]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion72_split_kpPoll (out : BitVec 64) :
    memRegion out 72 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
       ∃∗ b0 : BitVec 8,
        (out ↦₈ b0) ∗
        ((out + 0x01#64) ↦₆₄ u0) ∗ ((out + 0x09#64) ↦₆₄ u1) ∗
        ((out + 0x11#64) ↦₆₄ u2) ∗ ((out + 0x19#64) ↦₆₄ u3) ∗
        ((out + 0x21#64) ↦₆₄ u4) ∗ ((out + 0x29#64) ↦₆₄ u5) ∗
        ((out + 0x31#64) ↦₆₄ u6) ∗ ((out + 0x39#64) ↦₆₄ u7) ∗
        memRegion (out + 0x41#64) 7) := by
  have hc : memRegion (out + 1#64) 64 = cells (out + 1#64) 8 :=
    ProofLib.memRegion_cells (out + 1#64) 8 (by decide)
  rw [show (72 : Nat) = 1 + (64 + 7) from rfl,
      memRegion_split out 1 71 (by decide),
      memRegion_split (out + 1#64) 64 7 (by decide),
      memRegion_one out, hc]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion48_split_regIdPoll (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ u8 : BitVec 32, ∃∗ u0 : BitVec 64,
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₃₂ u8) ∗ memRegion (out + 0xc#64) 36) := by
  rw [show (48 : Nat) = 8 + (4 + 36) from rfl,
      memRegion_split out 8 40 (by decide),
      memRegion_split (out + 8#64) 4 36 (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_four (out + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

end InMemWitness

end CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

namespace CryptoVerification.LibsignalPublicApi.StoreKit

export IdentitySelf
  (kpPollOutAt regIdPollOutAt
   IdentitySelfStoreSpec IdentitySelfStoreSpec.Quiet
   kitKpShimSpec kitRegIdShimSpec
   kitKpPollSpec kitRegIdPollSpec
   kitKpPollSpecE kitRegIdPollSpecE
   inMemSelfIdentityAt inMemSelfIdentityStoreSpec)

end CryptoVerification.LibsignalPublicApi.StoreKit
