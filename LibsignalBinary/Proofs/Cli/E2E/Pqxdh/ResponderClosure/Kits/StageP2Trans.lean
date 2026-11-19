/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb

/-!
# Stage P2 Precondition and Inter-Substage Spatial Transitions

Defines the fresh-session Stage P2 spatial precondition `stageP2PreAt` at `+0x0868` and proves the
inter-substage framing transitions (`p2_entry_to_sub1To4`, `p2_sub4_to_sub5`, `p2_sub5_to_sub6`)
used by `stageP2_v1_kits`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem mkP2AcceptKeysInput_spkBSk (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    bytesToBv8 (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes).spkBSk =
      clampBv8List spkPrivBytes :=
  bytesToBv8_toU8 (clampBv8List spkPrivBytes)

theorem mkP2AcceptKeysInput_pqspkBSk (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    bytesToBv8 (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes).pqspkBSk =
      kyberPrivBytes :=
  bytesToBv8_toU8 kyberPrivBytes

theorem mkP2AcceptKeysInput_ikBSk (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes).ikBSk = ikBSk := rfl

theorem mkP2AcceptKeysInput_hdr (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes).hdr = hdr := rfl

theorem mkP2AcceptKeysInput_opkBSk? (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes).opkBSk? =
      opkOkSkBytes? (hdrOpkIdBv? hdr) opkSkBytes := rfl

theorem p2_sp3b8_40_split (sp : BitVec 64) :
    memRegion (sp + 0x3b8#64) 40 =
      memRegion (sp + 0x3b8#64) 8 ∗ memRegion (sp + 0x3c0#64) 8 ∗
      memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3cf#64) 1 ∗
      memRegion (sp + 0x3d0#64) 8 ∗ memRegion (sp + 0x3d8#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3b8#64) (n := 8) (k := 32)
        (b' := sp + 0x3c0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3c0#64) (n := 8) (k := 24)
        (b' := sp + 0x3c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3c8#64) (n := 7) (k := 17)
        (b' := sp + 0x3cf#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3cf#64) (n := 1) (k := 16)
        (b' := sp + 0x3d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3d0#64) (n := 8) (k := 8)
        (b' := sp + 0x3d8#64) rfl (by bv_omega) (by decide)]

theorem p2_fp80_9_split (fp : BitVec 64) :
    memRegion (fp + 0xffffffffffffff80#64) 9 =
      ∃∗ u_b90 : BitVec 64, ∃∗ b_b98 : BitVec 8,
        ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) := by
  rw [ProofLib.memRegion_split' (b := fp + 0xffffffffffffff80#64) (n := 8) (k := 1)
        (b' := fp + 0xffffffffffffff88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_one]
  rw [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

theorem p2_sp3c8_7_1_eq_exists64 (sp : BitVec 64) :
    memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3cf#64) 1 =
      ∃∗ u : BitVec 64, (sp + 0x3c8#64) ↦₆₄ u := by
  rw [(ProofLib.memRegion_split' (b := sp + 0x3c8#64) (n := 7) (k := 1)
        (b' := sp + 0x3cf#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_eight]

theorem p2_fp80_words_entails_9 (fp u_b90 : BitVec 64) (b_b98 : BitVec 8) :
    ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ⊢
      memRegion (fp + 0xffffffffffffff80#64) 9 := by
  rw [p2_fp80_9_split fp]
  exact Entails.sepExists_right u_b90 (Entails.sepExists_right b_b98 (Entails.refl _))

theorem p2_toU8_bytesToBv8 (bs : SignalPqxdh.Bytes) : toU8 (bytesToBv8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    simpa [bytesToBv8, toU8, UInt8.ofBitVec_toBitVec] using ih

theorem p2_fsAt_step_regId {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {P : Program} {s s' : State} (ans : Except skit.RegIdErr (BitVec 32))
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace ++ skit.regIdEvs ans) :
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s' :=
  hfs.of_steps hst htr (fun hq => hq.2.2.2.2 ans)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
