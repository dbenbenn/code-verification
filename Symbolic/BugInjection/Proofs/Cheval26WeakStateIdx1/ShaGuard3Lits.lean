/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon

/-!
# Concrete Step-3 Intermediate Literals & Transitivity for `Cheval26WeakStateIdx1Cli`

Splits the `ws3` kernel evaluation across `ws3DkLit` (`96` B) and `ws3OutLit` (`~450` B) so
`compP0` and `compP0RealFast` run in separate processes without re-evaluating ML-KEM-1024 inside
`recvWithDkAt`, keeping peak RSS well under `16 GiB`.
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Lits

open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (
  ChainKey IdentityKey KeyPair MessageKeyGenerator PrivateKey PublicKey ReceiverChain SenderChain
  SessionState SignalMessage initializeRecipientSession
)
open CryptoVerification.E2E (PEParams PreKeyMessageFields keyPairOf ofU8 pqxdhSpqrSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (PqParty preKeysNamedBy)
open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon (recvWithDkAt)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  chainKeyEqBool idKeyEqBool keyPairEqBool listEqBool msgKeyGenEqBool optEqBool
  pqxdhSessionParamsFast privKeyEqBool prodEqBool pubKeyEqBool recvChainEqBool senderChainEqBool
  sessionStateEqBool
)

@[expose] public section

set_option autoImplicit false

def ws3DkLit : SignalPqxdh.DRKey where
  rootKey := [116, 233, 175, 26, 88, 9, 112, 5, 181, 119, 148, 190, 81, 120, 114, 52,
              110, 61, 180, 29, 186, 87, 43, 105, 108, 214, 90, 102, 50, 48, 153, 255]
  chainKey := [246, 248, 152, 35, 199, 247, 60, 16, 248, 43, 128, 83, 173, 38, 22, 107,
               10, 163, 240, 252, 48, 142, 52, 232, 123, 52, 84, 60, 230, 47, 178, 5]
  pqrKey := [195, 148, 54, 230, 195, 237, 42, 232, 231, 17, 206, 142, 188, 142, 91, 131,
             184, 161, 222, 74, 231, 187, 27, 163, 228, 212, 233, 55, 27, 83, 155, 87]

def ws3StLit : SessionState HwBytes where
  sessionVersion := 0x00000004#32
  localIdentity := ⟨⟨⟨[247#8, 109#8, 80#8, 243#8, 118#8, 136#8, 44#8, 111#8, 251#8, 173#8, 206#8, 88#8,
                       76#8, 36#8, 40#8, 170#8, 130#8, 232#8, 133#8, 229#8, 21#8, 181#8, 50#8, 192#8,
                       176#8, 72#8, 3#8, 255#8, 139#8, 172#8, 127#8, 98#8], rfl⟩⟩⟩
  remoteIdentity := some ⟨⟨⟨[90#8, 247#8, 121#8, 180#8, 152#8, 213#8, 132#8, 49#8, 81#8, 244#8, 57#8, 203#8,
                             137#8, 239#8, 255#8, 62#8, 189#8, 99#8, 243#8, 76#8, 184#8, 253#8, 158#8, 215#8,
                             86#8, 105#8, 159#8, 101#8, 45#8, 67#8, 1#8, 60#8], rfl⟩⟩⟩
  rootKey := 90265444911378510547528097673378290714564695771321854611860089182120213587632#256
  previousCounter := 0x00000000#32
  senderChain := some
    { ratchetKey :=
        { publicKey := ⟨⟨[69#8, 104#8, 127#8, 247#8, 36#8, 72#8, 81#8, 141#8, 0#8, 214#8, 9#8, 16#8,
                          55#8, 63#8, 33#8, 171#8, 71#8, 21#8, 176#8, 110#8, 239#8, 125#8, 152#8, 142#8,
                          254#8, 124#8, 53#8, 156#8, 235#8, 110#8, 40#8, 114#8], rfl⟩⟩
          privateKey := ⟨⟨[176#8, 248#8, 4#8, 5#8, 227#8, 12#8, 254#8, 210#8, 4#8, 207#8, 221#8, 86#8,
                           244#8, 39#8, 146#8, 198#8, 118#8, 79#8, 111#8, 72#8, 97#8, 217#8, 212#8, 1#8,
                           123#8, 204#8, 87#8, 62#8, 31#8, 96#8, 100#8, 98#8], rfl⟩⟩ }
      chainKey := ⟨54891226312624102466657904800591340997754869280778314752579137433788187066781#256,
                   0x00000000#32⟩ }
  receiverChains :=
    [{ senderRatchetKey := ⟨⟨[39#8, 22#8, 93#8, 235#8, 114#8, 149#8, 99#8, 173#8, 141#8, 145#8, 17#8, 116#8,
                              157#8, 239#8, 24#8, 140#8, 239#8, 44#8, 22#8, 143#8, 245#8, 111#8, 190#8, 138#8,
                              74#8, 205#8, 62#8, 19#8, 240#8, 32#8, 224#8, 74#8], rfl⟩⟩
       chainKey := some ⟨11756124284552480753951225361797232659349181918850522547001757626896981495613#256,
                         0x00000002#32⟩
       messageKeys :=
         [{ seed := [4#8, 203#8, 254#8, 54#8, 73#8, 217#8, 159#8, 193#8, 146#8, 145#8, 252#8, 147#8,
                     156#8, 53#8, 91#8, 79#8, 17#8, 198#8, 25#8, 78#8, 146#8, 110#8, 58#8, 222#8,
                     88#8, 95#8, 50#8, 215#8, 56#8, 70#8, 102#8, 27#8]
            counter := 0x00000000#32 }] }]
  pendingPreKey := false
  pqRatchetState :=
    [18#8, 152#8, 1#8, 8#8, 1#8, 26#8, 112#8, 10#8, 34#8, 18#8, 32#8, 111#8, 88#8, 59#8, 227#8, 187#8,
     92#8, 237#8, 117#8, 26#8, 196#8, 74#8, 69#8, 225#8, 208#8, 182#8, 58#8, 113#8, 86#8, 169#8, 224#8, 136#8,
     18#8, 82#8, 124#8, 100#8, 151#8, 58#8, 138#8, 25#8, 208#8, 198#8, 155#8, 18#8, 74#8, 8#8, 2#8, 18#8,
     32#8, 70#8, 44#8, 222#8, 228#8, 102#8, 190#8, 85#8, 246#8, 11#8, 141#8, 42#8, 1#8, 254#8, 14#8, 11#8,
     53#8, 198#8, 184#8, 146#8, 198#8, 110#8, 81#8, 84#8, 236#8, 184#8, 144#8, 11#8, 44#8, 132#8, 253#8, 68#8,
     182#8, 26#8, 36#8, 0#8, 0#8, 0#8, 1#8, 117#8, 101#8, 207#8, 237#8, 172#8, 88#8, 7#8, 20#8,
     94#8, 126#8, 243#8, 182#8, 84#8, 254#8, 20#8, 66#8, 172#8, 96#8, 97#8, 156#8, 179#8, 198#8, 46#8, 30#8,
     247#8, 246#8, 247#8, 198#8, 68#8, 58#8, 11#8, 138#8, 34#8, 32#8, 19#8, 146#8, 171#8, 6#8, 181#8, 152#8,
     197#8, 112#8, 10#8, 95#8, 227#8, 190#8, 207#8, 197#8, 101#8, 133#8, 149#8, 219#8, 174#8, 112#8, 236#8, 159#8,
     142#8, 72#8, 206#8, 173#8, 182#8, 89#8, 201#8, 123#8, 87#8, 190#8, 50#8, 0#8, 26#8, 179#8, 1#8, 50#8,
     176#8, 1#8, 10#8, 72#8, 8#8, 1#8, 18#8, 68#8, 10#8, 32#8, 141#8, 249#8, 166#8, 198#8, 18#8, 219#8,
     225#8, 73#8, 65#8, 187#8, 13#8, 210#8, 1#8, 106#8, 147#8, 143#8, 206#8, 89#8, 98#8, 65#8, 199#8, 214#8,
     3#8, 120#8, 30#8, 80#8, 204#8, 198#8, 102#8, 93#8, 202#8, 180#8, 18#8, 32#8, 251#8, 59#8, 179#8, 17#8,
     39#8, 49#8, 58#8, 95#8, 59#8, 35#8, 75#8, 78#8, 161#8, 39#8, 55#8, 13#8, 12#8, 149#8, 52#8, 57#8,
     215#8, 71#8, 34#8, 47#8, 188#8, 216#8, 120#8, 204#8, 249#8, 49#8, 149#8, 218#8, 18#8, 100#8, 8#8, 48#8,
     16#8, 16#8, 26#8, 4#8, 0#8, 1#8, 134#8, 2#8, 26#8, 4#8, 0#8, 1#8, 229#8, 196#8, 26#8, 4#8,
     0#8, 1#8, 180#8, 8#8, 26#8, 4#8, 0#8, 1#8, 85#8, 75#8, 26#8, 4#8, 0#8, 1#8, 7#8, 199#8,
     26#8, 4#8, 0#8, 1#8, 211#8, 88#8, 26#8, 4#8, 0#8, 1#8, 251#8, 13#8, 26#8, 4#8, 0#8, 1#8,
     6#8, 34#8, 26#8, 4#8, 0#8, 1#8, 87#8, 141#8, 26#8, 4#8, 0#8, 1#8, 251#8, 149#8, 26#8, 4#8,
     0#8, 1#8, 214#8, 175#8, 26#8, 4#8, 0#8, 1#8, 194#8, 169#8, 26#8, 4#8, 0#8, 1#8, 223#8, 90#8,
     26#8, 4#8, 0#8, 1#8, 172#8, 8#8, 26#8, 4#8, 0#8, 1#8, 55#8, 165#8, 26#8, 4#8, 0#8, 1#8,
     223#8, 197#8]

def ws3OutLit : Option (Option (Option (HwBytes × SessionState HwBytes))) :=
  some (some (some ([115#8, 101#8, 99#8, 111#8, 110#8, 100#8], ws3StLit)))

def recvOutEqBool :=
  optEqBool (optEqBool (optEqBool (prodEqBool (fun (x y : HwBytes) => x == y) sessionStateEqBool)))

private theorem optEqBool_trans {α : Type} {eq : α → α → Bool}
    (htr : ∀ x y z, eq x y = true → eq y z = true → eq x z = true) :
    ∀ a b c : Option α, optEqBool eq a b = true → optEqBool eq b c = true → optEqBool eq a c = true
  | none, none, none, _, _ => rfl
  | some x, some y, some z, h1, h2 => htr x y z h1 h2

private theorem listEqBool_trans {α : Type} {eq : α → α → Bool}
    (htr : ∀ x y z, eq x y = true → eq y z = true → eq x z = true) :
    ∀ a b c : List α, listEqBool eq a b = true → listEqBool eq b c = true → listEqBool eq a c = true
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    obtain ⟨h1a, h1b⟩ := (Bool.and_eq_true _ _).mp h1
    obtain ⟨h2a, h2b⟩ := (Bool.and_eq_true _ _).mp h2
    exact (Bool.and_eq_true _ _).mpr ⟨htr x y z h1a h2a, listEqBool_trans htr xs ys zs h1b h2b⟩

private theorem prodEqBool_trans {α β : Type} {eqA : α → α → Bool} {eqB : β → β → Bool}
    (htrA : ∀ x y z, eqA x y = true → eqA y z = true → eqA x z = true)
    (htrB : ∀ x y z, eqB x y = true → eqB y z = true → eqB x z = true)
    (a b c : α × β) (h1 : prodEqBool eqA eqB a b = true) (h2 : prodEqBool eqA eqB b c = true) :
    prodEqBool eqA eqB a c = true := by
  obtain ⟨h1a, h1b⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨h2a, h2b⟩ := (Bool.and_eq_true _ _).mp h2
  exact (Bool.and_eq_true _ _).mpr ⟨htrA a.1 b.1 c.1 h1a h2a, htrB a.2 b.2 c.2 h1b h2b⟩

private theorem beq_trans {α : Type} [BEq α] [LawfulBEq α] (x y z : α)
    (h1 : (x == y) = true) (h2 : (y == z) = true) : (x == z) = true :=
  beq_iff_eq.mpr ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2))

private theorem senderChainEqBool_trans (a b c : CryptoGames.LibsignalSession.SenderChain)
    (h1 : senderChainEqBool a b = true) (h2 : senderChainEqBool b c = true) :
    senderChainEqBool a c = true := by
  unfold senderChainEqBool keyPairEqBool pubKeyEqBool privKeyEqBool chainKeyEqBool at h1 h2 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

private theorem msgKeyGenEqBool_trans (a b c : CryptoGames.LibsignalSession.MessageKeyGenerator)
    (h1 : msgKeyGenEqBool a b = true) (h2 : msgKeyGenEqBool b c = true) :
    msgKeyGenEqBool a c = true := by
  unfold msgKeyGenEqBool at h1 h2 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

private theorem chainKeyEqBool_trans (a b c : CryptoGames.LibsignalSession.ChainKey)
    (h1 : chainKeyEqBool a b = true) (h2 : chainKeyEqBool b c = true) :
    chainKeyEqBool a c = true := by
  unfold chainKeyEqBool at h1 h2 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

private theorem recvChainEqBool_trans (a b c : CryptoGames.LibsignalSession.ReceiverChain)
    (h1 : recvChainEqBool a b = true) (h2 : recvChainEqBool b c = true) :
    recvChainEqBool a c = true := by
  unfold recvChainEqBool pubKeyEqBool at h1 h2 ⊢
  obtain ⟨⟨h1a, h1b⟩, h1c⟩ := (Bool.and_eq_true _ _).mp h1 |>.imp_left (Bool.and_eq_true _ _).mp
  obtain ⟨⟨h2a, h2b⟩, h2c⟩ := (Bool.and_eq_true _ _).mp h2 |>.imp_left (Bool.and_eq_true _ _).mp
  exact (Bool.and_eq_true _ _).mpr
    ⟨(Bool.and_eq_true _ _).mpr ⟨beq_trans _ _ _ h1a h2a, optEqBool_trans chainKeyEqBool_trans _ _ _ h1b h2b⟩,
     listEqBool_trans msgKeyGenEqBool_trans _ _ _ h1c h2c⟩

private theorem idKeyEqBool_trans (a b c : CryptoGames.LibsignalSession.IdentityKey)
    (h1 : idKeyEqBool a b = true) (h2 : idKeyEqBool b c = true) :
    idKeyEqBool a c = true := by
  unfold idKeyEqBool pubKeyEqBool at h1 h2 ⊢
  exact beq_trans _ _ _ h1 h2

private theorem sessionStateEqBool_trans (a b c : SessionState HwBytes)
    (h1 : sessionStateEqBool a b = true) (h2 : sessionStateEqBool b c = true) :
    sessionStateEqBool a c = true := by
  unfold sessionStateEqBool at h1 h2 ⊢
  simp only [Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨⟨beq_trans _ _ _ h1.1.1.1.1.1.1.1.1 h2.1.1.1.1.1.1.1.1,
                idKeyEqBool_trans _ _ _ h1.1.1.1.1.1.1.1.2 h2.1.1.1.1.1.1.1.2⟩,
               optEqBool_trans idKeyEqBool_trans _ _ _ h1.1.1.1.1.1.1.2 h2.1.1.1.1.1.1.2⟩,
              beq_trans _ _ _ h1.1.1.1.1.1.2 h2.1.1.1.1.1.2⟩,
             beq_trans _ _ _ h1.1.1.1.1.2 h2.1.1.1.1.2⟩,
            optEqBool_trans senderChainEqBool_trans _ _ _ h1.1.1.1.2 h2.1.1.1.2⟩,
           listEqBool_trans recvChainEqBool_trans _ _ _ h1.1.1.2 h2.1.1.2⟩,
          beq_trans _ _ _ h1.1.2 h2.1.2⟩,
         beq_trans _ _ _ h1.2 h2.2⟩

theorem recvOutEqBool_trans {a b c : Option (Option (Option (HwBytes × SessionState HwBytes)))}
    (h1 : recvOutEqBool a b = true) (h2 : recvOutEqBool b c = true) :
    recvOutEqBool a c = true :=
  optEqBool_trans
    (optEqBool_trans
      (optEqBool_trans
        (prodEqBool_trans beq_trans sessionStateEqBool_trans))) a b c h1 h2

def ws3St0Lit : SessionState HwBytes where
  sessionVersion := 0x00000004#32
  localIdentity := ⟨⟨⟨[247#8, 109#8, 80#8, 243#8, 118#8, 136#8, 44#8, 111#8, 251#8, 173#8, 206#8, 88#8,
                       76#8, 36#8, 40#8, 170#8, 130#8, 232#8, 133#8, 229#8, 21#8, 181#8, 50#8, 192#8,
                       176#8, 72#8, 3#8, 255#8, 139#8, 172#8, 127#8, 98#8], rfl⟩⟩⟩
  remoteIdentity := some ⟨⟨⟨[90#8, 247#8, 121#8, 180#8, 152#8, 213#8, 132#8, 49#8, 81#8, 244#8, 57#8, 203#8,
                             137#8, 239#8, 255#8, 62#8, 189#8, 99#8, 243#8, 76#8, 184#8, 253#8, 158#8, 215#8,
                             86#8, 105#8, 159#8, 101#8, 45#8, 67#8, 1#8, 60#8], rfl⟩⟩⟩
  rootKey := 115610436632245223310197454905554266752444389714101361459935695125551216847220#256
  previousCounter := 0x00000000#32
  senderChain := some
    { ratchetKey :=
        { publicKey := ⟨⟨[182#8, 184#8, 136#8, 150#8, 188#8, 230#8, 194#8, 114#8, 5#8, 58#8, 191#8, 28#8,
                          119#8, 23#8, 172#8, 161#8, 81#8, 212#8, 114#8, 114#8, 131#8, 3#8, 255#8, 76#8,
                          234#8, 18#8, 73#8, 108#8, 159#8, 227#8, 20#8, 24#8], rfl⟩⟩
          privateKey := ⟨⟨[128#8, 32#8, 213#8, 75#8, 107#8, 160#8, 240#8, 47#8, 147#8, 197#8, 50#8, 145#8,
                           249#8, 244#8, 42#8, 122#8, 79#8, 211#8, 93#8, 156#8, 209#8, 252#8, 57#8, 144#8,
                           29#8, 9#8, 223#8, 121#8, 37#8, 98#8, 133#8, 99#8], rfl⟩⟩ }
      chainKey := ⟨2576393609666294388050258670144194860297722028128364101156586281059223140598#256,
                   0x00000000#32⟩ }
  receiverChains := []
  pendingPreKey := false
  pqRatchetState :=
    [10#8, 40#8, 10#8, 32#8, 195#8, 148#8, 54#8, 230#8, 195#8, 237#8, 42#8, 232#8, 231#8, 17#8, 206#8, 142#8,
     188#8, 142#8, 91#8, 131#8, 184#8, 161#8, 222#8, 74#8, 231#8, 187#8, 27#8, 163#8, 228#8, 212#8, 233#8, 55#8,
     27#8, 83#8, 155#8, 87#8, 16#8, 1#8, 24#8, 1#8, 34#8, 0#8, 26#8, 114#8, 50#8, 112#8, 10#8, 72#8,
     8#8, 1#8, 18#8, 68#8, 10#8, 32#8, 141#8, 249#8, 166#8, 198#8, 18#8, 219#8, 225#8, 73#8, 65#8, 187#8,
     13#8, 210#8, 1#8, 106#8, 147#8, 143#8, 206#8, 89#8, 98#8, 65#8, 199#8, 214#8, 3#8, 120#8, 30#8, 80#8,
     204#8, 198#8, 102#8, 93#8, 202#8, 180#8, 18#8, 32#8, 251#8, 59#8, 179#8, 17#8, 39#8, 49#8, 58#8, 95#8,
     59#8, 35#8, 75#8, 78#8, 161#8, 39#8, 55#8, 13#8, 12#8, 149#8, 52#8, 57#8, 215#8, 71#8, 34#8, 47#8,
     188#8, 216#8, 120#8, 204#8, 249#8, 49#8, 149#8, 218#8, 18#8, 36#8, 8#8, 48#8, 16#8, 16#8, 26#8, 0#8,
     26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8,
     26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8, 26#8, 0#8]

def recvSt0At (W : PEParams) (st₀ : PqParty) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) : Option (SessionState HwBytes) :=
  (preKeysNamedBy st₀ m).map fun k =>
    initializeRecipientSession (pqxdhSpqrSession W)
      ⟨(keyPairOf W.C st₀.me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
      (bytesToKey32 (ofU8 dk.rootKey)) (bytesToKey32 (ofU8 dk.chainKey))
      (bytesToKey32 (ofU8 dk.pqrKey))

def recvDecWithSt0At (W : PEParams) (st₀ : PqParty) (m : PreKeyMessageFields)
    (rc : BitVec 256) (st0Opt : Option (SessionState HwBytes)) :
    Option (Option (Option (HwBytes × SessionState HwBytes))) :=
  match preKeysNamedBy st₀ m, st0Opt with
  | some k, some st0 =>
    some (match SignalMessage.tryFrom protoSignalCodec m.inner with
      | .error _ => some none
      | .ok inner =>
        if (m.spkId != k.spkId) || (m.kpkId != k.kpkId) then some none
        else
          match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParamsFast W).expectedAddrs st₀.party) inner .preKey rc st0 with
          | (.ok pt, st) => some (some (pt, st)) | (.error .panic, _) => none
          | (.error _, _) => some none)
  | _, _ => none

theorem recvWithDkAt_some_eq_recvDecWithSt0At (W : PEParams) (st₀ : PqParty)
    (m : PreKeyMessageFields) (rc : BitVec 256) (dk : SignalPqxdh.DRKey) :
    recvWithDkAt W st₀ m rc (some dk) =
      recvDecWithSt0At W st₀ m rc (recvSt0At W st₀ m dk) := by
  unfold recvWithDkAt recvDecWithSt0At recvSt0At
  cases preKeysNamedBy st₀ m <;> rfl

private theorem eq_of_listEqBool {α : Type} {eq : α → α → Bool}
    (heq : ∀ x y, eq x y = true → x = y) :
    ∀ xs ys : List α, listEqBool eq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [heq x y h1, eq_of_listEqBool heq xs ys h2]

private theorem eq_of_optEqBool {α : Type} {eq : α → α → Bool}
    (heq : ∀ x y, eq x y = true → x = y) :
    ∀ o1 o2 : Option α, optEqBool eq o1 o2 = true → o1 = o2
  | none, none, _ => rfl
  | some x, some y, h => congrArg some (heq x y h)

private theorem eq_of_pubKeyEqBool (a b : PublicKey) (h : pubKeyEqBool a b = true) : a = b := by
  cases a; cases b; congr; exact List.Vector.eq _ _ (beq_iff_eq.mp h)

private theorem eq_of_privKeyEqBool (a b : PrivateKey) (h : privKeyEqBool a b = true) : a = b := by
  cases a; cases b; congr; exact List.Vector.eq _ _ (beq_iff_eq.mp h)

private theorem eq_of_keyPairEqBool (a b : KeyPair) (h : keyPairEqBool a b = true) : a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [eq_of_pubKeyEqBool _ _ h1, eq_of_privKeyEqBool _ _ h2]

private theorem eq_of_idKeyEqBool (a b : IdentityKey) (h : idKeyEqBool a b = true) : a = b := by
  cases a; cases b; exact congrArg IdentityKey.mk (eq_of_pubKeyEqBool _ _ h)

private theorem eq_of_chainKeyEqBool (a b : ChainKey) (h : chainKeyEqBool a b = true) : a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2]

private theorem eq_of_msgKeyGenEqBool (a b : MessageKeyGenerator) (h : msgKeyGenEqBool a b = true) :
    a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2]

private theorem eq_of_senderChainEqBool (a b : SenderChain) (h : senderChainEqBool a b = true) :
    a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [eq_of_keyPairEqBool _ _ h1, eq_of_chainKeyEqBool _ _ h2]

private theorem eq_of_recvChainEqBool (a b : ReceiverChain) (h : recvChainEqBool a b = true) :
    a = b := by
  cases a; cases b
  obtain ⟨⟨h1, h2⟩, h3⟩ := (Bool.and_eq_true _ _).mp h |>.imp_left (Bool.and_eq_true _ _).mp
  dsimp only at h1 h2 h3
  rw [eq_of_pubKeyEqBool _ _ h1, eq_of_optEqBool eq_of_chainKeyEqBool _ _ h2,
      eq_of_listEqBool eq_of_msgKeyGenEqBool _ _ h3]

private theorem eq_of_sessionStateEqBool (a b : SessionState HwBytes)
    (h : sessionStateEqBool a b = true) : a = b := by
  cases a; cases b; unfold sessionStateEqBool at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [h1, eq_of_idKeyEqBool _ _ h2, eq_of_optEqBool eq_of_idKeyEqBool _ _ h3, h4, h5,
      eq_of_optEqBool eq_of_senderChainEqBool _ _ h6,
      eq_of_listEqBool eq_of_recvChainEqBool _ _ h7, h8, h9]

theorem eq_of_optSessionStateEqBool {o1 o2 : Option (SessionState HwBytes)}
    (h : optEqBool sessionStateEqBool o1 o2 = true) : o1 = o2 :=
  eq_of_optEqBool eq_of_sessionStateEqBool o1 o2 h

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Lits
