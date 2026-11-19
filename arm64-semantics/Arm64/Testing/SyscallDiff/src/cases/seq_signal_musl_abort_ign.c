// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// musl abort() syscall sequence with SIG_IGN installed: raise() returns, then fallback resets SIG_DFL and kills with SIGABRT.
#include "sd_rt.h"

struct ksa { u64 handler, flags, restorer, mask; };

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

static i64 sa(i64 sig, const void *act, void *oact, u64 sz) {
  return sd_sys4(SYS_rt_sigaction, sig, act, oact, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 abrt = 1UL << (SIGABRT - 1), app = 0xfffffffc7fffffffUL, all = ~0UL, old = 0;
  struct ksa ign = {1, 0, 0, 0}, dfl = {0, 0, 0, 0};
  i64 tid = sd_sys0(SYS_gettid);
  SD_EXPECT("ign", sa(SIGABRT, &ign, 0, 8), 0);
  /* musl raise(SIGABRT) */
  SD_EXPECT("block_app", spm(SIG_BLOCK, &app, &old, 8), 0);
  SD_EXPECT("tkill1", sd_sys2(SYS_tkill, tid, SIGABRT), 0);
  SD_EXPECT("restore", spm(SIG_SETMASK, &old, 0, 8), 0);
  sd_puts("survived_raise\n");
  /* musl abort() fallback */
  SD_EXPECT("block_all", spm(SIG_BLOCK, &all, 0, 8), 0);
  SD_EXPECT("dfl", sa(SIGABRT, &dfl, 0, 8), 0);
  SD_EXPECT("tkill2", sd_sys2(SYS_tkill, tid, SIGABRT), 0);
  spm(SIG_UNBLOCK, &abrt, 0, 8);
  sd_puts("post\n");
  return 0;
}
