/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Disproofs.Impl.CkptMacro

/-! Pre-elaborated hooked stub tree (`baseHooks`) for `Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup` (Rule 2: image-free). -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseData

open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree)
open scoped Symbolic.BugInjection.Disproofs.Impl.CkptMacro

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 2000000 in
def baseHooks : BinTree String :=
  ckpt_hooks [
    "BBBBBBH18087;80;_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellmanH18087;57;_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_failH36174;47;_RNvNtCskxtBwYRO61I_4core6option13unwrap_failedBBH18087;52;_RNvNtCs",
    "69KKACWg7bl_5alloc5alloc18handle_alloc_errorH18087;53;_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_innerH36174;74;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2BBH36175;76;_RNvNtNtCskxtBwYRO61I_4core9panicking",
    "11panic_const24panic_const_shl_overflowH36174;41;_RNvNtCskxtBwYRO61I_4core9panicking5panicBH36174;45;_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256BH18087;67;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulateH18086;103;_RNvM",
    "s0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seedBBBH36175;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflowH36174;55;_RNvNtCskxtBwYRO61I_4core9panicking18panic_",
    "bounds_checkBH36174;64;_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decryptBH18087;88;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_keyH18084;48;_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_",
    "fileBBBH18086;50;_RNvCs9Xul1Kjr0QF_16libsignal_cli_io12write_stdoutH18087;80;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumedH36173;57;_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_H72348;35;_RNvNt",
    "CskxtBwYRO61I_4core3fmt5writeBBBH72349;47;_RNvNtCskxtBwYRO61I_4core6result13unwrap_failedBH36174;48;_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_errorH36174;79;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytesBBH",
    "36175;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflowBH18087;45;_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmtH18086;57;_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_BBH18087;45;_RNvNtCsbvWyylYiyxg_",
    "4sha26sha51211compress512H18087;123;_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4fromEBBBH36175;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul",
    "_overflowH36174;56;_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_innerBH36174;64;_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encryptH36174;67;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulateBBH36175;70;_",
    "RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failedBH18087;74;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1H18086;37;_RNvCs65XVORQObL2_12libcrux_hmac4hmacH72348;47;_RNvNtCskxtBwYRO61I_4core6opt",
    "ion13expect_failed"
  ]

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseData
