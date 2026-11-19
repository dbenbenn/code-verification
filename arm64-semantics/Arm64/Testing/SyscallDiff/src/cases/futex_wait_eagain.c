// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// futex(2) FUTEX_WAIT_PRIVATE with mismatched expected value returns -EAGAIN on Linux; Lean fails
// closed on non-wake futex operations ([INTENTIONAL_SCOPE]).
#include "sd_rt.h"

#define FUTEX_WAIT_PRIVATE FUTEX_PRIVATE_FLAG

static u32 bss_futex_word = 3;

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("wait_priv_eagain",
            sd_sys(SYS_futex, (u64)&bss_futex_word, FUTEX_WAIT_PRIVATE, 99, 0, 0, 0), -EAGAIN);
  return 0;
}
