/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitStk -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit
import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.KpkMark
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI KyberPreKey `StoreKitOkImgE` Bundle

Extends `KyberMarkFit.CliKpkInv` with `get_kyber_pre_key` preconditions (`CliKpkInvFull`), proves
closure under `kpkMarkOf`, defines `cliKpkStoreSpecFull`, and assembles `KyberPreKeyStoreKitOkImgE`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Full Kyber Store Invariant (`get_kyber_pre_key` + `mark_kyber_pre_key_used`) -/

private theorem keyName_ne_baseKeysName (id : BitVec 32) : keyName id ≠ baseKeysName id := by
  intro h
  have hlen := congrArg List.length h
  have h10 : (utf8 ".base-keys").length = 10 := by decide +kernel
  rw [baseKeysName, List.length_append, h10] at hlen
  omega

/-- Full Kyber store invariant combining `CliKpkInv` (`mark_kyber_pre_key_used` preconditions) with
`kpkGetPollSpec`'s `lastResort` name bound and `< 2^32` file-size bounds on both directories. -/
structure CliKpkInvFull (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (g : KyberGhost) : Prop where
  markInv : CliKpkInv rd F0 pathOk kid ksid kbk g
  lastNameOk : PkNameOk pathOk g.lastResort kid
  oneSizeOk : PkSizeOk rd F0 g.oneTime kid
  lastSizeOk : PkSizeOk rd F0 g.lastResort kid

theorem CliKpkInvFull.mark {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {g : KyberGhost}
    (h : CliKpkInvFull rd F0 pathOk kid ksid kbk g) :
    CliKpkInvFull rd F0 pathOk kid ksid kbk (kpkMarkOf rd F0 g kid ksid kbk).2 := by
  refine ⟨h.markInv.mark, ?_, ?_, ?_⟩
  · unfold kpkMarkOf
    rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
    · exact h.lastNameOk
    · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
      · exact h.lastNameOk
      · dsimp only
        split
        · exact h.lastNameOk
        · split <;> exact h.lastNameOk
    · exact h.lastNameOk
  · unfold kpkMarkOf
    rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
    · exact h.oneSizeOk
    · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
      · exact h.oneSizeOk
      · dsimp only
        split
        · exact h.oneSizeOk
        · split <;> exact h.oneSizeOk
    · intro bs hbs
      rw [DirGhost.get_put_self] at hbs
      cases hbs
      decide
  · unfold kpkMarkOf
    rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
    · exact h.lastSizeOk
    · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
      · exact h.lastSizeOk
      · dsimp only
        split
        · exact h.lastSizeOk
        · split
          · exact h.lastSizeOk
          · intro bs hbs
            rw [DirGhost.get_put_ne rd F0 g.lastResort (keyName_ne_baseKeysName kid)] at hbs
            exact h.lastSizeOk bs hbs
    · exact h.lastSizeOk

@[expose] def cliKpkStoreAtFull (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (self : BitVec 64) (g : KyberGhost) : SepProp :=
  ⌜CliKpkInvFull rd F0 pathOk kid ksid kbk g⌝ ∗ dirAt A self g.oneTime ∗
    dirAt A (self + 0x28#64) g.lastResort

/-- `cliKyberPreKeyStoreSpec` with `storeAt := cliKpkStoreAtFull`, sharing all vtable, box, error,
and relation fields definitionally with `cliKyberPreKeyStoreSpec`. -/
@[expose] def cliKpkStoreSpecFull (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (getShimStk getPollStk markShimStk markPollStk : Nat) : KyberPreKeyStoreSpec A b :=
  { cliKyberPreKeyStoreSpec A b rd F0 pathOk kid ksid kbk
      getShimStk getPollStk markShimStk markPollStk with
    storeAt := cliKpkStoreAtFull A rd F0 pathOk kid ksid kbk }

theorem cliKpkStoreSpecFull_quiet {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat) :
    (cliKpkStoreSpecFull A b rd F0 pathOk kid ksid kbk s1 s2 s3 s4).Quiet :=
  cliKpkStoreSpec_quiet (A := A) (b := b) rd F0 pathOk kid ksid kbk
    (cliKpkGetSide A rd F0 pathOk kid) s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion

theorem cliKpkStoreSpecFull_getRel_error_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat)
    (g : KyberGhost) (id : BitVec 32) :
    (∃ e, (cliKpkStoreSpecFull A b rd F0 pathOk kid ksid kbk s1 s2 s3 s4).getRel g id (.error e)) ↔
      g.get rd F0 id = .error () :=
  cliKpk_getRel_error_iff (A := A) rd F0 pathOk kid g id

theorem cliKpkStoreSpecFull_getRel_ok_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat)
    (g : KyberGhost) (id : BitVec 32) (r : KyberPreKeyRecord) :
    (cliKpkStoreSpecFull A b rd F0 pathOk kid ksid kbk s1 s2 s3 s4).getRel g id (.ok r) ↔
      g.get rd F0 id = .ok r :=
  cliKpk_getRel_ok_iff (A := A) rd F0 pathOk kid g id r

/-! ## 2. Sret Layout Bridge for `mark_kyber_pre_key_used` -/

private theorem cliMarkErr_of_parts' (A : RustAlloc) (out : BitVec 64) (ans : KpkMarkAns)
    (bs : List (BitVec 8)) (w4 w5 : BitVec 64) (tail : SepProp)
    (htail : tail ⊢ match ans with
      | .readErr => ⌜w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (w4 ↦ᵣ utf8 "read")
      | _ => emp)
    (hne : ans ≠ .ok) :
    ((out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1) ∗
      vecU8 A (out + 8#64) bs ∗
      ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5) ∗ tail) ⊢
    ∃∗ r : Except CliKpkMarkErr Unit,
      ⌜(match r with | .ok () => ans = .ok | .error e => ans = e.ans)⌝ ∗
        unitSpePollOutAt (cliKpkMarkErrSpec A) out r := by
  unfold vecU8 vecU8At vecHeader
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr => ?_
  let e : CliKpkMarkErr :=
    { ans := ans, ne_ok := hne, cap := cap, ptr := ptr,
      len := BitVec.ofNat 64 bs.length, w4 := w4, w5 := w5 }
  refine Entails.sepExists_right (.error e) (Entails.pure_right rfl ?_)
  dsimp only [unitSpePollOutAt, speErrAt, speWordsAt, cliKpkMarkErrSpec, e]
  have h10 : out + 8#64 + 8#64 = out + 0x10#64 := by bv_omega
  have h18 : out + 8#64 + 16#64 = out + 0x18#64 := by bv_omega
  rw [h10, h18]
  set bufHeap : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  set w0Term : SepProp := out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1
  have hvec :
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap ⊢
        ∃∗ bs' : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs'.length = BitVec.ofNat 64 bs.length ∧
            bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs') ∗
             memRegion (ptr + BitVec.ofNat 64 bs'.length) (cap.toNat - bs'.length)) := by
    refine Entails.pure_left fun ⟨hlen, hcap, hptr⟩ => ?_
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨rfl, hlen, hcap, hptr⟩ (Entails.refl _)
  refine Entails.trans (Entails.of_eq (show _ =
    ((w0Term ∗ ((out + 0x08#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗
        ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) ∗
      ((⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap) ∗ tail)) by ac_rfl)) ?_
  cases ans <;> exact sepConj_mono_right (sepConj_mono hvec htail)

private theorem cliKpkMarkOut_entails' (A : RustAlloc) (out : BitVec 64) (a : KpkMarkAns) :
    kpkMarkOutAt A out a ⊢
      ∃∗ ans : Except CliKpkMarkErr Unit,
        ⌜(match ans with | .ok () => a = .ok | .error e => a = e.ans)⌝ ∗
          unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := by
  rcases a with _ | _ | _ | _
  · exact Entails.sepExists_right (.ok ()) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only [kpkMarkOutAt, speAt, strRefAt]
    have e1 : out + asm64% spePayloadOff = out + 8#64 := by bv_omega
    have e2 : out + asm64% speInvalidStateFnOff = out + 0x20#64 := by bv_omega
    have e3 : out + 0x20#64 + asm64% boxSliceLenOff = out + 0x28#64 := by bv_omega
    rw [e1, e2, e3, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p => ?_
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts' A out .readErr bs p
        (BitVec.ofNat 64 (utf8 "read").length) (p ↦ᵣ utf8 "read")
        (Entails.pure_right rfl (Entails.refl _)) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts' A out .malformed bs w4 w5 emp (Entails.refl _) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts' A out .reused bs w4 w5 emp (Entails.refl _) (by nofun))

/-! ## 3. `KyberPreKeyStoreKitOkImgE` Assembly -/

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
