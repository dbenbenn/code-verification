/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.SM.RecordInj.Primitives -- proof-setup: allow-public-import

/-!
# Bottom-Up Protobuf Message Injectivity

Proves injectivity of `encChainKey`, `encMessageKey`, `encSenderChain`, `encReceiverChain`,
`encSessionStructureSeed`, and `encodeRecord` on encodings of total byte length `< 2 ^ 64` via
`ChainEq` prefix cancellation.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.SM.RecordInj

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E

theorem chainEq_of_eq_lt {b₁ b₂ : Bytes} (hlen : b₁.length < 2 ^ 64) (heq : b₁ = b₂) :
    ChainEq (b₁ ++ []) (b₂ ++ []) := by
  refine ⟨by rw [heq], ?_⟩
  simpa using hlen

/-! ## Sub-message Injectivity -/

theorem encChainKey_inj (ck₁ ck₂ : ChainKey) (hlen : (encChainKey ck₁).length < 2 ^ 64)
    (h : encChainKey ck₁ = encChainKey ck₂) : ck₁ = ck₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encChainKey, List.append_assoc] at hc0
  obtain ⟨hidx, hc1⟩ := peel_uint32 (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc0
  obtain ⟨hk, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc1
  cases ck₁
  cases ck₂
  cases hidx
  cases keyToBytes32_inj hk
  rfl

theorem encMessageKey_inj (mk₁ mk₂ : MessageKeyGenerator)
    (hlen : (encMessageKey mk₁).length < 2 ^ 64)
    (h : encMessageKey mk₁ = encMessageKey mk₂) : mk₁ = mk₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encMessageKey, List.append_assoc] at hc0
  obtain ⟨hctr, hc1⟩ := peel_uint32 (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc0
  obtain ⟨hseed, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc1
  cases mk₁
  cases mk₂
  cases hctr
  cases hseed
  rfl

theorem encSenderChain_inj (c₁ c₂ : SenderChain) (hlen : (encSenderChain c₁).length < 2 ^ 64)
    (h : encSenderChain c₁ = encSenderChain c₂) : c₁ = c₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encSenderChain, List.append_assoc] at hc0
  obtain ⟨hpub, hc1⟩ := peel_bytes (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))) hc0
  obtain ⟨hpriv, hc2⟩ := peel_bytes (by omega) (by omega)
    (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc1
  change ChainEq (msgField 3 ((some c₁.chainKey).map encChainKey) ++ [])
    (msgField 3 ((some c₂.chainKey).map encChainKey) ++ []) at hc2
  obtain ⟨hck, _⟩ := peel_msg encChainKey (by omega) (by omega) encChainKey_inj
    (tagGe_nil _) (tagGe_nil _) hc2
  obtain ⟨⟨pub₁, priv₁⟩, ck₁⟩ := c₁
  obtain ⟨⟨pub₂, priv₂⟩, ck₂⟩ := c₂
  cases publicKey_serialize_inj hpub
  cases privateKey_toList_inj hpriv
  cases Option.some.inj hck
  rfl

theorem encReceiverChain_inj (c₁ c₂ : ReceiverChain)
    (hlen : (encReceiverChain c₁).length < 2 ^ 64)
    (h : encReceiverChain c₁ = encReceiverChain c₂) : c₁ = c₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encReceiverChain, List.append_assoc] at hc0
  obtain ⟨hsrk, hc1⟩ := peel_bytes (by omega) (by omega)
    (tagGe_msgField _ _ (by omega) (by omega) (by omega)
      (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _)))
    (tagGe_msgField _ _ (by omega) (by omega) (by omega)
      (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _))) hc0
  obtain ⟨hck, hc2⟩ := peel_msg encChainKey (by omega) (by omega) encChainKey_inj
    (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc1
  obtain ⟨hmks, _⟩ := peel_repeated encMessageKey (by omega) (by omega) encMessageKey_inj
    (tagGe_nil _) (tagGe_nil _) hc2
  cases c₁
  cases c₂
  cases publicKey_serialize_inj hsrk
  cases hck
  cases hmks
  rfl

/-! ## `SessionState` and `SessionRecord` Injectivity -/

private theorem remoteIdentity_opt_inj {r₁ r₂ : Option IdentityKey}
    (h : (r₁.map IdentityKey.serialize).getD [] = (r₂.map IdentityKey.serialize).getD []) :
    r₁ = r₂ := by
  cases r₁ with
  | none =>
    cases r₂ with
    | none => rfl
    | some ik₂ => simp [IdentityKey.serialize, PublicKey.serialize] at h
  | some ik₁ =>
    cases r₂ with
    | none => simp [IdentityKey.serialize, PublicKey.serialize] at h
    | some ik₂ =>
      simp only [Option.map_some, Option.getD_some] at h
      exact congrArg some (identityKey_serialize_inj h)

end CryptoVerification.SignalSession.SM.RecordInj
