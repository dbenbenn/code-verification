// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigprocmask(2): SIG_SETMASK and SIG_BLOCK with SIGKILL|SIGSTOP|SIGUSR1 strip SIGKILL/SIGSTOP and retain SIGUSR1 (0x200).
#include "sd_rt.h"

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 mixed = (1UL << (SIGKILL - 1)) | (1UL << (SIGSTOP - 1)) | (1UL << (SIGUSR1 - 1));
  u64 usr1 = 1UL << (SIGUSR1 - 1);
  u64 zero = 0;
  u64 old = 0xa5a5a5a5a5a5a5a5UL;
  SD_EXPECT("setmask_mixed", spm(SIG_SETMASK, &mixed, &old, 8), 0);
  SD_EXPECT("old0", old, 0);
  SD_EXPECT("query_after_setmask", spm(SIG_BLOCK, 0, &old, 8), 0);
  SD_EXPECT("mask_after_setmask", old, usr1);
  SD_EXPECT("clear", spm(SIG_SETMASK, &zero, 0, 8), 0);
  SD_EXPECT("block_mixed", spm(SIG_BLOCK, &mixed, &old, 8), 0);
  SD_EXPECT("old_cleared", old, 0);
  SD_EXPECT("query_after_block", spm(SIG_BLOCK, 0, &old, 8), 0);
  SD_EXPECT("mask_after_block", old, usr1);
  SD_EXPECT("unblock_mixed", spm(SIG_UNBLOCK, &mixed, &old, 8), 0);
  SD_EXPECT("old_before_unblock", old, usr1);
  SD_EXPECT("query_end", spm(SIG_BLOCK, 0, &old, 8), 0);
  SD_EXPECT("mask_end", old, 0);
  return 0;
}
