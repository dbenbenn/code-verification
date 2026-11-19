// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigprocmask(2): unmapped oldset returns -EFAULT after applying the new mask; aliased set == oldset works.
#include "sd_rt.h"

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 usr1 = 1UL << (SIGUSR1 - 1);
  u64 term = 1UL << (SIGTERM - 1);
  u64 old = 0, x = term, y = 0;
  SD_EXPECT("block_usr1_bad_oldset", spm(SIG_BLOCK, &usr1, (void *)0x10000, 8), -EFAULT);
  SD_EXPECT("query", spm(SIG_BLOCK, 0, &old, 8), 0);
  SD_EXPECT("mask_after_efault", old, usr1);
  SD_EXPECT("alias_setmask", spm(SIG_SETMASK, &x, &x, 8), 0);
  SD_EXPECT("alias_old", x, usr1);
  SD_EXPECT("query2", spm(SIG_BLOCK, 0, &y, 8), 0);
  SD_EXPECT("alias_new", y, term);
  return 0;
}
