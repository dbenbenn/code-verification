/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# CLI `SessionOnlyKitOkSE` Assembly

Assembles `MessageDecrypt.SessionOnlyKitOkSE` for `cliSessionStoreSpec` from the `SessionFiles`
shim, poll, and `futDrop` contracts over an arbitrary allocator, `ReadRule`, initial file table,
`SessionRecord` scope, and external-hook map.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.SessKit

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## Stack bounds -/

abbrev decNeed : Nat := 10 * 0x50 + doReserveStackX
abbrev addrTextNeed : Nat := 0x70 + max (max doReserveStackX extHookStack) decNeed
abbrev growOneDirNeed : Nat := 0x40 + finishGrowStackX
abbrev dirPutNeed : Nat := 0x60 + max growOneDirNeed extHookStack
abbrev loadShimNeed : Nat := 0x20 + extHookStack
abbrev storeShimNeed : Nat := 0x30 + extHookStack
abbrev loadPollNeed (readStk : Nat) : Nat :=
  0x350 + max (max addrTextNeed (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩))
    (max E2E.Record.recDeserializeStack extHookStack)
abbrev storePollNeedX : Nat :=
  0xd0 + max (max addrTextNeed Proofs.libsignal.Hooks2.serializeStackX) (max dirPutNeed extHookStack)

/-! ## Separation-logic rearrangement helpers -/

private theorem poll_pre_entails {p1 p2 p3 q1 q2 : Prop} {box dir rest : SepProp}
    (hq : p1 → p2 → p3 → q1 ∧ q2) :
    ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) ⊢
      ⌜q1⌝ ∗ (⌜q2⌝ ∗ box ∗ dir ∗ rest) := by
  have hperm :
      ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest))) := by
    ac_rfl
  rw [hperm]
  apply Entails.pure_left; intro hp1
  apply Entails.pure_left; intro hp2
  apply Entails.pure_left; intro hp3
  obtain ⟨hq1, hq2⟩ := hq hp1 hp2 hp3
  exact Entails.pure_right hq1 (Entails.pure_right hq2 (Entails.refl _))

private theorem storePoll_pre_entails {fl p1 p2 p3 q : Prop} {box dir rest : SepProp}
    (hq : p1 → p2 → p3 → q) :
    ⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ⊢
      ⌜fl⌝ ∗ (⌜q⌝ ∗ box ∗ dir ∗ rest) := by
  apply Entails.pure_left; intro hfl
  refine Entails.pure_right hfl ?_
  have hperm :
      ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest))) := by
    ac_rfl
  rw [hperm]
  apply Entails.pure_left; intro hp1
  apply Entails.pure_left; intro hp2
  apply Entails.pure_left; intro hp3
  exact Entails.pure_right (hq hp1 hp2 hp3) (Entails.refl _)

private theorem extract_pure3 {p1 p2 p3 : Prop} {box dir rest R : SepProp} {m : Memory}
    (hm : m ⊨ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ∗ R) :
    p1 ∧ p2 ∧ p3 := by
  have hperm :
      (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ∗ R =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest ∗ R))) := by
    ac_rfl
  rw [hperm, satisfies_pure_sepConj] at hm
  obtain ⟨hp1, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  obtain ⟨hp2, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  exact ⟨hp1, hp2, hm.1⟩

private theorem extract_storePoll_pure {fl p1 p2 p3 : Prop} {box dir rest R : SepProp} {m : Memory}
    (hm : m ⊨ (⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest))) ∗ R) :
    p1 ∧ p2 ∧ p3 := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact extract_pure3 hm.2

private theorem loadPoll_post_sat {α β : Type} {p : α → β → Prop} {q : β → Prop}
    {inv : Prop} {out1 out2 : β → SepProp} {box1 dir tail R : SepProp} {m : Memory}
    (hinv : inv)
    (hstep : ∀ g a, p g a → q a ∧ (out1 a ⊢ out2 a))
    (hm : m ⊨ ((∃∗ g : α, ∃∗ a : β, ⌜p g a⌝ ∗ out1 a) ∗ box1 ∗ dir ∗ tail) ∗ R) :
    m ⊨ (∃∗ a : β, ⌜q a⌝ ∗ box1 ∗ (⌜inv⌝ ∗ dir) ∗ out2 a ∗ tail) ∗ R := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  have hperm1 :
      ((⌜p g a⌝ ∗ out1 a) ∗ (box1 ∗ dir ∗ tail)) ∗ R =
        ⌜p g a⌝ ∗ ((box1 ∗ dir ∗ out1 a ∗ tail) ∗ R) := by
    ac_rfl
  rw [hperm1, satisfies_pure_sepConj] at hm
  obtain ⟨hpga, hm⟩ := hm
  obtain ⟨hqa, hout⟩ := hstep g a hpga
  refine Satisfies.sepExists_intro a ?_
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hqa, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  exact sepConj_mono_right
    (sepConj_mono (Entails.pure_right hinv (Entails.refl dir)) (sepConj_mono_left hout))

private theorem storePoll_post_sat {p : Prop} {q : Except Unit Unit → Prop} {inv' : Prop}
    {box1 dir0 outA outB tail R : SepProp}
    {storeAt' outAt' : Except Unit Unit → SepProp} {m : Memory}
    (hq : p → q (.ok ())) (hinv' : inv')
    (hstore : storeAt' (.ok ()) = ⌜inv'⌝ ∗ dir0)
    (hout : outAt' (.ok ()) = outA ∗ outB)
    (hm : m ⊨ (⌜p⌝ ∗ box1 ∗ dir0 ∗ outA ∗ outB ∗ tail) ∗ R) :
    m ⊨ (∃∗ ans : Except Unit Unit,
          ⌜q ans⌝ ∗ box1 ∗ storeAt' ans ∗ outAt' ans ∗ tail) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hp, hm⟩ := hm
  refine Satisfies.sepExists_intro (.ok ()) ?_
  rw [hstore, hout, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hq hp, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  rw [← sepConj_assoc outA outB tail]
  exact sepConj_mono_right (sepConj_mono_left (Entails.pure_right hinv' (Entails.refl dir0)))

/-! ## Kit assembly -/

end CryptoVerification.SignalSession.Cli.KitInst.SessKit
