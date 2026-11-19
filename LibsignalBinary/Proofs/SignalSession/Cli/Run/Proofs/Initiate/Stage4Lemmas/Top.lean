/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Frames -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Cells
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSession
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqr
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt

/-!
# Stage 4 Top-Level Composition

Composes `stage4_step_prechain_to_4496` (`+4260 → +4496`) with the `<RootKey>::create_chain`
outcome split: `.error .invalidKeyAgreement` exits via `stage4_err_exit` (`S.initiate = some none`),
and `.ok (rk1, ck1)` steps through `stage4_step_spqr` (`+4576 → +4848`) and `stage4_step_session`
(`+4848 → +5252`) into `AtStage5` + `stage5Mem`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

s4_clean_sp_attrs

theorem bundleEOf_props {b : BundleV} {be : PreKeyBundleFields} (h : bundleEOf? b = some be) :
    b.kpk.length = 1568 ∧
      (⟨be.spkPub⟩ : PublicKey) = b.spk ∧
      (⟨⟨be.idPub⟩⟩ : IdentityKey) = b.idKey := by
  unfold bundleEOf? at h
  split at h <;> try simp at h
  rcases h with ⟨_, hkpk, rfl⟩
  exact ⟨hkpk, by cases b.spk; rfl, by cases b.idKey; cases ‹PublicKey›; rfl⟩

theorem idKey_eq_of_publicKey_eq {ik : IdentityKey} {pk : PublicKey}
    (h : ik.publicKey = pk) :
    (⟨pk⟩ : IdentityKey) = ik := by
  cases ik
  dsimp only at h
  subst h
  rfl

private theorem padCoins_take32_len (coins : List (BitVec 8)) :
    ((padCoins coins).toList.take 32).length = 32 := by simp; decide

private theorem ofU8_toU8_id : ∀ (bs : List (BitVec 8)), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (ofU8_toU8_id rest)

private theorem u8Vec_toU8_vec {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (toU8 v.toList) = v := by
  apply Subtype.ext
  show ((ofU8 (toU8 v.toList) ++ List.replicate n 0#8).take n) = v.toList
  rw [ofU8_toU8_id, List.take_append_of_le_length (by rw [v.toList_length]),
      List.take_of_length_le (by rw [v.toList_length])]

private theorem clamp0_idem (b : BitVec 8) : (b &&& 248#8) &&& 248#8 = b &&& 248#8 := by
  rw [BitVec.and_assoc]; rfl

private theorem bool_clamp31 (x a c : Bool) :
    ((x && a || c) && a || c) = (x && a || c) := by
  cases x <;> cases a <;> cases c <;> rfl

private theorem clamp31_idem (b : BitVec 8) :
    ((b &&& 127#8 ||| 64#8) &&& 127#8) ||| 64#8 = b &&& 127#8 ||| 64#8 := by
  ext k hk
  simp only [BitVec.getElem_or, BitVec.getElem_and]
  exact bool_clamp31 _ _ _

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  rcases v with ⟨_ | ⟨b0, rest⟩, hv⟩
  · simp at hv
  let u : List.Vector (BitVec 8) 32 := ⟨b0 :: rest, hv⟩
  let w : List.Vector (BitVec 8) 32 := Ratchet.clampScalar u
  have hw0 : w.get 0 = b0 &&& 248#8 := rfl
  have hw31 : w.get 31 = u.get 31 &&& 127#8 ||| 64#8 := by simp [w, Ratchet.clampScalar]
  apply Subtype.ext
  show ((w.set 0 (w.get 0 &&& 248#8)).set 31 (w.get 31 &&& 127#8 ||| 64#8)).toList = w.toList
  rw [hw0, hw31, clamp0_idem, clamp31_idem]
  show (b0 &&& 248#8) :: (rest.set 30 (u.get 31 &&& 127#8 ||| 64#8)).set 30
    (u.get 31 &&& 127#8 ||| 64#8) = (b0 &&& 248#8) :: rest.set 30 (u.get 31 &&& 127#8 ||| 64#8)
  rw [List.set_set]

private theorem baseKey_bytes_eq_ekAPk_ext {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {kp : IdentityKeyPair} {be : PreKeyBundleFields} {coins : List (BitVec 8)}
    {ekAPk : List (BitVec 8)} {hdrEkAPk : List UInt8}
    (hekPair : ekAPk = (keyPairOf P.C ⟨(padCoins coins).toList.take 32, padCoins_take32_len coins⟩).publicKey.bytes.toList)
    (hhdr : hdrEkAPk = (modelPrims X P).x25519Base
      (initiateInput P ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk) :
    ekAPk = (PublicKey.mk (u8Vec 32 hdrEkAPk)).bytes.toList := by
  subst hekPair hhdr
  let v : List.Vector (BitVec 8) 32 := ⟨(padCoins coins).toList.take 32, padCoins_take32_len coins⟩
  change (P.C.pubKey (Ratchet.clampScalar v)).toList =
    (u8Vec 32 (toU8 (P.C.pubKey (Ratchet.clampScalar (u8Vec 32 (toU8 v.toList)))).toList)).toList
  rw [u8Vec_toU8_vec v, u8Vec_toU8_vec (P.C.pubKey (Ratchet.clampScalar v))]

private theorem baseKey_bytes_eq_ekAPk {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {kp : IdentityKeyPair} {be : PreKeyBundleFields} {coins : List (BitVec 8)}
    {ekAPk : List (BitVec 8)} {hdrEkAPk : List UInt8}
    (hekPair : ekAPk = (keyPairOf W.C ⟨(padCoins coins).toList.take 32, padCoins_take32_len coins⟩).publicKey.bytes.toList)
    (hhdr : hdrEkAPk = (modelPrims X ⟨W.C, W.Q⟩).x25519Base
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk) :
    ekAPk = (PublicKey.mk (u8Vec 32 hdrEkAPk)).bytes.toList :=
  baseKey_bytes_eq_ekAPk_ext (P := ⟨W.C, W.Q⟩) hekPair hhdr

theorem err_rest5ba_merge (fsp : BitVec 64) :
    (stage4IdleSlots fsp ∗
      memRegion (fsp + 1904#64) 288 ∗
      memRegion (fsp + 2192#64) 24 ∗
      memRegion (fsp + 2224#64) 32 ∗
      memRegion (fsp + 2256#64) 36 ∗
      memRegion (fsp + 2304#64) 32 ∗
      memRegion (fsp + 2336#64) 16 ∗
      memRegion (fsp + 2352#64) 100 ∗
      memRegion (fsp + 2496#64) 32 ∗
      memRegion (fsp + 2528#64) 32 ∗
      memRegion (fsp + 4064#64) 32 ∗
      memRegion (fsp + 4096#64) 312 ∗
      ((fsp + 5632#64) ↦₃₂ 1#32) ∗
      memRegion (fsp + 5636#64) 4 ∗
      memRegion (fsp + 5688#64) 16 ∗
      memRegion (fsp + 5704#64) 272 ∗
      memRegion (fsp + 7232#64) 32 ∗
      memRegion (fsp + 7264#64) 24) ∗
    memRegion (fsp + 5640#64) 48 ⊢
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  have h5632_4 : ((fsp + 5632#64) ↦₃₂ 1#32) ⊢ memRegion (fsp + 5632#64) 4 :=
    pointsTo32_entails_memRegion (fsp + 5632#64) 1#32
  have h100 :
      memRegion (fsp + 2352#64) 100 =
        memRegion (fsp + 2352#64) 20 ∗ memRegion (fsp + 2372#64) 80 :=
    ProofLib.memRegion_split' (b := fsp + 2352#64) (n := 20) (k := 80)
      (b' := fsp + 2372#64) rfl (by bv_omega) (by decide)
  have h36 :
      memRegion (fsp + 2336#64) 36 =
        memRegion (fsp + 2336#64) 16 ∗ memRegion (fsp + 2352#64) 20 :=
    ProofLib.memRegion_split' (b := fsp + 2336#64) (n := 16) (k := 20)
      (b' := fsp + 2352#64) rfl (by bv_omega) (by decide)
  have h4064 :
      memRegion (fsp + 4064#64) 344 =
        memRegion (fsp + 4064#64) 32 ∗ memRegion (fsp + 4096#64) 312 :=
    ProofLib.memRegion_split' (b := fsp + 4064#64) (n := 32) (k := 312)
      (b' := fsp + 4096#64) rfl (by bv_omega) (by decide)
  have h5632_344 :
      memRegion (fsp + 5632#64) 344 =
        memRegion (fsp + 5632#64) 4 ∗ memRegion (fsp + 5636#64) 4 ∗
        memRegion (fsp + 5640#64) 48 ∗ memRegion (fsp + 5688#64) 16 ∗
        memRegion (fsp + 5704#64) 272 := by
    rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 4) (k := 340)
          (b' := fsp + 5636#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5636#64) (n := 4) (k := 336)
          (b' := fsp + 5640#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5640#64) (n := 48) (k := 288)
          (b' := fsp + 5688#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5688#64) (n := 16) (k := 272)
          (b' := fsp + 5704#64) rfl (by bv_omega) (by decide)]
  s4_fold_ent h5632_4
  refine Entails.of_eq ?_
  rw [← stage4Locals_merge_5ba fsp, h36, h100, h4064, h5632_344]
  s4_ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
