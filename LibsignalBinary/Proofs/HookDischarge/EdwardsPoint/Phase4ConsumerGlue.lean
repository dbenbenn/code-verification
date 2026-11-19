/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs -- proof-setup: allow-public-import
public import ProofLib.SepLogic.HeapIntro
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.Model

/-!
# Consumer Glue: `dalek*GhostLs` `*RowSpec` Instances and `RwOnlyHeap` Closure
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ConsumerGlue

open Arm64 ProofLib SepProp BitVec
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (dalekHookStack)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality
  (RwOnlyHeap rwOnlyHeap_pure rwOnlyHeap_pointsToBytes rwOnlyHeap_pointsTo64 rwOnlyHeap_memRegion
   rwOnlyHeap_stackAt rwOnlyHeap_sepConj rwOnlyHeap_sepExists)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks
  (dalekCompressGhostLs dalekCompressGhostLs_keepsFs_ok dalekDsmbGhostLs dalekDsmbGhostLs_keepsFs_ok
   dalekMontToEdGhostLs dalekMontToEdGhostLs_keepsFs_ok dalekScalarModGhostLs dalekScalarModGhostLs_keepsFs_ok
   dalekScalarWideGhostLs dalekScalarWideGhostLs_keepsFs_ok dalekTorsionFreeGhostLs dalekTorsionFreeGhostLs_keepsFs_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202
  (dalekMontToEdExtOutAt dalekMontToEdExtSpec dalekTorsionFreeExtSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204
  (dalekCompressExtSpec dalekDsmbExtSpec dalekEdNegExtSpec dalekScalarModExtSpec dalekScalarWideExtSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (DalekLsRowTuple DalekScalarModRowSpec DalekScalarWideRowSpec DalekMontToEdRowSpec
   DalekCompressRowSpec DalekTorsionFreeRowSpec DalekDsmbRowSpec ghostRow
   specSimulates_keepsFs_dalekScalarModExtSpec specSimulates_keepsFs_dalekScalarWideExtSpec
   specSimulates_keepsFs_dalekMontToEdExtSpec_of_ghost specSimulates_keepsFs_dalekCompressExtSpec
   specSimulates_keepsFs_dalekTorsionFreeExtSpec_of_ghost specSimulates_keepsFs_dalekDsmbExtSpec
   dalekScalarModFallback_rowSpec dalekScalarWideFallback_rowSpec dalekMontToEdFallback_rowSpec
   dalekCompressFallback_rowSpec dalekTorsionFreeFallback_rowSpec dalekDsmbFallback_rowSpec)

export LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality (RwOnlyHeap)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (DalekLsRowTuple DalekScalarModRowSpec DalekScalarWideRowSpec DalekMontToEdRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (DalekCompressRowSpec DalekTorsionFreeRowSpec DalekDsmbRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (dalekScalarModFallback_rowSpec dalekScalarWideFallback_rowSpec dalekMontToEdFallback_rowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (dalekCompressFallback_rowSpec dalekTorsionFreeFallback_rowSpec dalekDsmbFallback_rowSpec)

/-! ## 1. Placement-Free `RwOnlyHeap` Closure Across All `dalek*ExtSpec` Contracts -/

private theorem rwStd2 {P : Prop} {A : SepProp} {sp : BitVec 64} {stk : Nat}
    (ha : ∀ {h}, A h → RwOnlyHeap h) {h : Heap} (hh : (⌜P⌝ ∗ A ∗ stackAt sp stk) h) : RwOnlyHeap h :=
  rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) (fun _ => rwOnlyHeap_sepConj (fun _ => ha) (fun _ => rwOnlyHeap_stackAt _ _)) hh
private theorem rwStd {P : Prop} {A B : SepProp} {sp : BitVec 64} {stk : Nat} (ha : ∀ {h}, A h → RwOnlyHeap h)
    (hb : ∀ {h}, B h → RwOnlyHeap h) {h : Heap} (hh : (⌜P⌝ ∗ A ∗ B ∗ stackAt sp stk) h) : RwOnlyHeap h :=
  rwStd2 (fun hp => rwOnlyHeap_sepConj (fun _ => ha) (fun _ => hb) hp) (by simpa [sepConj_assoc] using hh)
private theorem rwStd5 {P : Prop} {A B C D : SepProp} {sp : BitVec 64} {stk : Nat} (ha : ∀ {h}, A h → RwOnlyHeap h)
    (hb : ∀ {h}, B h → RwOnlyHeap h) (hc : ∀ {h}, C h → RwOnlyHeap h) (hd : ∀ {h}, D h → RwOnlyHeap h)
    {h : Heap} (hh : (⌜P⌝ ∗ A ∗ B ∗ C ∗ D ∗ stackAt sp stk) h) : RwOnlyHeap h :=
  rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) (fun _ => rwOnlyHeap_sepConj (fun _ => ha) (fun _ => rwOnlyHeap_sepConj
    (fun _ => hb) (fun _ => rwOnlyHeap_sepConj (fun _ => hc) (fun _ => rwOnlyHeap_sepConj (fun _ => hd) (fun _ => rwOnlyHeap_stackAt _ _))))) hh
private theorem rwOnlyHeap_dalekMontToEdExtOutAt (outPtr : BitVec 64) (u_bs : List (BitVec 8))
    (sign : Nat) {h : Heap} (hh : dalekMontToEdExtOutAt outPtr u_bs sign h) : RwOnlyHeap h := by
  unfold dalekMontToEdExtOutAt at hh; split at hh
  · exact rwOnlyHeap_sepExists (fun _ _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) (fun _ => rwOnlyHeap_pointsToBytes _ _)) hh
  · exact rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pointsTo64 _ _) (fun _ => rwOnlyHeap_memRegion _ _) hh

private theorem rwBytesMem {P : Prop} {a b sp : BitVec 64} {bs : List (BitVec 8)} {n stk : Nat} {h : Heap}
    (hh : (⌜P⌝ ∗ (a ↦ₛ bs) ∗ memRegion b n ∗ stackAt sp stk) h) : RwOnlyHeap h :=
  rwStd (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_memRegion _ _) hh
private theorem rwBytes2 {P : Prop} {a b sp : BitVec 64} {bs₁ bs₂ : List (BitVec 8)} {stk : Nat} {h : Heap}
    (hh : (⌜P⌝ ∗ (a ↦ₛ bs₁) ∗ (b ↦ₛ bs₂) ∗ stackAt sp stk) h) : RwOnlyHeap h :=
  rwStd (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_pointsToBytes _ _) hh

theorem rwOnlyHeap_dalekMontToEdExtSpec_pre (stk) (g) (s) {h} (hh : (dalekMontToEdExtSpec stk).pre g s h) : RwOnlyHeap h := rwBytesMem hh
theorem rwOnlyHeap_dalekMontToEdExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekMontToEdExtSpec stk).post g s0 sf h) : RwOnlyHeap h :=
  rwStd (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_dalekMontToEdExtOutAt _ _ _) hh
theorem rwOnlyHeap_dalekTorsionFreeExtSpec_pre (stk) (g) (s) {h} (hh : (dalekTorsionFreeExtSpec stk).pre g s h) : RwOnlyHeap h :=
  rwStd2 (rwOnlyHeap_pointsToBytes _ _) hh
theorem rwOnlyHeap_dalekTorsionFreeExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekTorsionFreeExtSpec stk).post g s0 sf h) : RwOnlyHeap h :=
  rwStd2 (rwOnlyHeap_pointsToBytes _ _) hh
theorem rwOnlyHeap_dalekCompressExtSpec_pre (stk) (g) (s) {h} (hh : (dalekCompressExtSpec stk).pre g s h) : RwOnlyHeap h := rwBytesMem hh
theorem rwOnlyHeap_dalekCompressExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekCompressExtSpec stk).post g s0 sf h) : RwOnlyHeap h := rwBytes2 hh
theorem rwOnlyHeap_dalekScalarWideExtSpec_pre (stk) (g) (s) {h} (hh : (dalekScalarWideExtSpec stk).pre g s h) : RwOnlyHeap h := rwBytesMem hh
theorem rwOnlyHeap_dalekScalarWideExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekScalarWideExtSpec stk).post g s0 sf h) : RwOnlyHeap h := rwBytes2 hh
theorem rwOnlyHeap_dalekScalarModExtSpec_pre (stk) (g) (s) {h} (hh : (dalekScalarModExtSpec stk).pre g s h) : RwOnlyHeap h := rwBytesMem hh
theorem rwOnlyHeap_dalekScalarModExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekScalarModExtSpec stk).post g s0 sf h) : RwOnlyHeap h := rwBytes2 hh
theorem rwOnlyHeap_dalekDsmbExtSpec_pre (stk) (g) (s) {h} (hh : (dalekDsmbExtSpec stk).pre g s h) : RwOnlyHeap h :=
  rwStd5 (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_memRegion _ _) hh
theorem rwOnlyHeap_dalekDsmbExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekDsmbExtSpec stk).post g s0 sf h) : RwOnlyHeap h :=
  rwStd5 (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_pointsToBytes _ _) (rwOnlyHeap_pointsToBytes _ _)
    (rwOnlyHeap_sepExists (fun _ _ => rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) (fun _ => rwOnlyHeap_pointsToBytes _ _))) hh
theorem rwOnlyHeap_dalekEdNegExtSpec_pre (stk) (g) (s) {h} (hh : (dalekEdNegExtSpec stk).pre g s h) : RwOnlyHeap h := rwBytesMem hh
theorem rwOnlyHeap_dalekEdNegExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (dalekEdNegExtSpec stk).post g s0 sf h) : RwOnlyHeap h := rwBytes2 hh

theorem rwOnlyHeap_withLsRet_pre [LibsignalPlacement] {α : Type} {spec : Spec α} {g : α} {s : State}
    (hp : ∀ h, spec.pre g s h → RwOnlyHeap h) {h : Heap} (hh : (withLsRet spec).pre g s h) : RwOnlyHeap h :=
  rwOnlyHeap_sepConj (fun _ => rwOnlyHeap_pure) hp hh
theorem rwOnlyHeap_withLsRet_post [LibsignalPlacement] {α : Type} {spec : Spec α} {g : α} {s0 sf : State}
    (hp : ∀ h, spec.post g s0 sf h → RwOnlyHeap h) {h : Heap} (hh : (withLsRet spec).post g s0 sf h) : RwOnlyHeap h := hp h hh

section WithPlacement

variable [LibsignalPlacement]

theorem rwOnlyHeap_withLsRet_dalekMontToEdExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekMontToEdExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekMontToEdExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekMontToEdExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekMontToEdExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekMontToEdExtSpec_post stk g s0 sf hh
theorem rwOnlyHeap_withLsRet_dalekTorsionFreeExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekTorsionFreeExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekTorsionFreeExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekTorsionFreeExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekTorsionFreeExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekTorsionFreeExtSpec_post stk g s0 sf hh
theorem rwOnlyHeap_withLsRet_dalekCompressExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekCompressExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekCompressExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekCompressExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekCompressExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekCompressExtSpec_post stk g s0 sf hh
theorem rwOnlyHeap_withLsRet_dalekScalarWideExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekScalarWideExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekScalarWideExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekScalarWideExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekScalarWideExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekScalarWideExtSpec_post stk g s0 sf hh
theorem rwOnlyHeap_withLsRet_dalekScalarModExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekScalarModExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekScalarModExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekScalarModExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekScalarModExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekScalarModExtSpec_post stk g s0 sf hh
theorem rwOnlyHeap_withLsRet_dalekDsmbExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekDsmbExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekDsmbExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekDsmbExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekDsmbExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekDsmbExtSpec_post stk g s0 sf hh
theorem rwOnlyHeap_withLsRet_dalekEdNegExtSpec_pre (stk) (g) (s) {h} (hh : (withLsRet (dalekEdNegExtSpec stk)).pre g s h) : RwOnlyHeap h := rwOnlyHeap_withLsRet_pre (fun _ => rwOnlyHeap_dalekEdNegExtSpec_pre stk g s) hh
theorem rwOnlyHeap_withLsRet_dalekEdNegExtSpec_post (stk) (g) (s0) (sf) {h} (hh : (withLsRet (dalekEdNegExtSpec stk)).post g s0 sf h) : RwOnlyHeap h := rwOnlyHeap_dalekEdNegExtSpec_post stk g s0 sf hh

/-! ## 2. `dalek*GhostLs` Consumer `*RowSpec` Instances -/

theorem dalekScalarModGhostLs_ext_at_stk (m : MultiPlacement) (stk : Nat := dalekHookStack)
    (hlo : 208 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple (dalekScalarModGhostLs m) (dalekScalarModExtSpec stk) :=
  ghostRow (specSimulates_keepsFs_dalekScalarModExtSpec stk) (dalekScalarModGhostLs_keepsFs_ok m stk false hlo hhi)
theorem dalekScalarWideGhostLs_ext_at_stk (m : MultiPlacement) (stk : Nat := dalekHookStack)
    (hlo : 448 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple (dalekScalarWideGhostLs m) (dalekScalarWideExtSpec stk) :=
  ghostRow (specSimulates_keepsFs_dalekScalarWideExtSpec stk) (dalekScalarWideGhostLs_keepsFs_ok m stk false hlo hhi)
theorem dalekMontToEdGhostLs_ext_at_stk (m : MultiPlacement) (stk : Nat := dalekHookStack)
    (hlo : 2576 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple (dalekMontToEdGhostLs m) (dalekMontToEdExtSpec stk) :=
  ghostRow (specSimulates_keepsFs_dalekMontToEdExtSpec_of_ghost stk) (dalekMontToEdGhostLs_keepsFs_ok m stk hlo hhi)
theorem dalekCompressGhostLs_ext_at_stk (m : MultiPlacement) (stk : Nat := dalekHookStack)
    (hlo : 1552 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple (dalekCompressGhostLs m) (dalekCompressExtSpec stk) :=
  ghostRow (specSimulates_keepsFs_dalekCompressExtSpec stk) (dalekCompressGhostLs_keepsFs_ok m stk false (2 ^ 53) hlo hhi (by decide))
theorem dalekTorsionFreeGhostLs_ext_at_stk (m : MultiPlacement) (stk : Nat := dalekHookStack)
    (hlo : 4848 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple (dalekTorsionFreeGhostLs m) (dalekTorsionFreeExtSpec stk) :=
  ghostRow (specSimulates_keepsFs_dalekTorsionFreeExtSpec_of_ghost stk) (dalekTorsionFreeGhostLs_keepsFs_ok m stk (2 ^ 53) hlo hhi (by decide))
theorem dalekDsmbGhostLs_ext_at_stk (m : MultiPlacement) (stk : Nat := dalekHookStack)
    (hlo : 5008 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple (dalekDsmbGhostLs m) (dalekDsmbExtSpec stk) :=
  ghostRow (specSimulates_keepsFs_dalekDsmbExtSpec stk) (dalekDsmbGhostLs_keepsFs_ok m stk hlo hhi)

theorem dalekScalarModGhostLs_rowSpec (dalekMpl : MultiPlacement) : DalekScalarModRowSpec (dalekScalarModGhostLs dalekMpl) := dalekScalarModGhostLs_ext_at_stk dalekMpl
theorem dalekScalarWideGhostLs_rowSpec (dalekMpl : MultiPlacement) : DalekScalarWideRowSpec (dalekScalarWideGhostLs dalekMpl) := dalekScalarWideGhostLs_ext_at_stk dalekMpl
theorem dalekMontToEdGhostLs_rowSpec (dalekMpl : MultiPlacement) : DalekMontToEdRowSpec (dalekMontToEdGhostLs dalekMpl) := dalekMontToEdGhostLs_ext_at_stk dalekMpl
theorem dalekCompressGhostLs_rowSpec (dalekMpl : MultiPlacement) : DalekCompressRowSpec (dalekCompressGhostLs dalekMpl) := dalekCompressGhostLs_ext_at_stk dalekMpl
theorem dalekTorsionFreeGhostLs_rowSpec (dalekMpl : MultiPlacement) : DalekTorsionFreeRowSpec (dalekTorsionFreeGhostLs dalekMpl) := dalekTorsionFreeGhostLs_ext_at_stk dalekMpl
theorem dalekDsmbGhostLs_rowSpec (dalekMpl : MultiPlacement) : DalekDsmbRowSpec (dalekDsmbGhostLs dalekMpl) := dalekDsmbGhostLs_ext_at_stk dalekMpl

end WithPlacement

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ConsumerGlue
