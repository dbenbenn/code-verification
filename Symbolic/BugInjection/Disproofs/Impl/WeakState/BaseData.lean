/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Disproofs.Impl.CkptMacro

/-! Pre-elaborated hooked stub tree (`baseHooks`) for `Symbolic.BugInjection.Disproofs.Impl.WeakState` (Rule 2: image-free). -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseData

open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree)
open scoped Symbolic.BugInjection.Disproofs.Impl.CkptMacro

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 2000000 in
def baseHooks : BinTree String :=
  ckpt_hooks [
    "BBBBBH36170;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflowBH18084;57;_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_H18084;41;_RNvNtCskxtBwYRO61I_4core9panicking5panicBH36169;45;_RNvNtCsbvWyylYiyxg",
    "_4sha26sha25611compress256H36169;67;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulateBBBH18085;53;_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_innerH18084;52;_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_errorH36169;74",
    ";_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2BH36169;47;_RNvNtCskxtBwYRO61I_4core6option13unwrap_failedH36169;57;_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_failBBBH36170;80;_RNvNtNtCskxtBwYRO61I_4core",
    "9panicking11panic_const28panic_const_async_fn_resumedH36168;37;_RNvCs65XVORQObL2_12libcrux_hmac4hmacH72338;35;_RNvNtCskxtBwYRO61I_4core3fmt5writeBBH36169;64;_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decryptH36169;88;_RNvNtNtC",
    "s1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_keyBH36169;55;_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_checkH36169;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflowBBBBBH180",
    "85;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflowH18083;50;_RNvCs9Xul1Kjr0QF_16libsignal_cli_io12write_stdoutBH18084;57;_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_H18084;45;_RNvNtCskxtBwYRO61I_",
    "4core9panicking9panic_fmtBBH18085;123;_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4fromH18084;45;_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512EBBH36169;48;_RNvNtCs69K",
    "KACWg7bl_5alloc7raw_vec12handle_errorBH18082;48;_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_fileH18084;79;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytesH72338;47;_RNvNtCskxtBwYRO61I_4core6result13unwrap_fail",
    "edBBBH36170;70;_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failedH36169;74;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1BH36169;47;_RNvNtCskxtBwYRO61I_4core6option13expect_failedH36168;80;_RN",
    "vMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellmanBBH36169;64;_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encryptBH18084;103;_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyP",
    "airCompressedBytes9from_seedH18084;67;_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulateBH36169;56;_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_innerH36169;76;_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_",
    "const_mul_overflow"
  ]

end Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseData
