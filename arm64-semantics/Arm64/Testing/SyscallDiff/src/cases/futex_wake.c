// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// futex(2) single-threaded FUTEX_WAKE / FUTEX_WAKE_PRIVATE: returns 0 on aligned RW word without
// modifying it, -EINVAL on misaligned uaddr, 0 (private) vs -EFAULT (shared) on unmapped user VA.
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)
#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

static u32 bss_futex_word = 3;

static inline i64 sys_futex(u64 uaddr, u64 op, u64 val) {
  return sd_sys(SYS_futex, uaddr, op, val, 0, 0, 0);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;

  SD_EXPECT("wake_priv_bss_1", sys_futex((u64)&bss_futex_word, FUTEX_WAKE_PRIVATE, 1), 0);
  SD_EXPECT("wake_priv_bss_max", sys_futex((u64)&bss_futex_word, FUTEX_WAKE_PRIVATE, 0x7fffffffUL),
            0);
  SD_EXPECT("wake_priv_bss_0", sys_futex((u64)&bss_futex_word, FUTEX_WAKE_PRIVATE, 0), 0);
  SD_EXPECT("wake_shared_bss", sys_futex((u64)&bss_futex_word, FUTEX_WAKE, 1), 0);
  SD_EXPECT("bss_word_unchanged", bss_futex_word, 3);

  SD_EXPECT("wake_priv_unalign1", sys_futex((u64)&bss_futex_word + 1, FUTEX_WAKE_PRIVATE, 1),
            -EINVAL);
  SD_EXPECT("wake_shared_unalign2", sys_futex((u64)&bss_futex_word + 2, FUTEX_WAKE, 1), -EINVAL);

  i64 p = sd_mmap(0, PAGE, MM_RW, MM_PA, -1, 0);
  SD_CHECK("mmap_ok", p > 0 && ((u64)p & (PAGE - 1)) == 0);
  if (p <= 0) return 0;
  *(volatile u32 *)p = 0x12345678U;
  SD_EXPECT("wake_priv_mmap", sys_futex((u64)p, FUTEX_WAKE_PRIVATE, 0x7fffffffUL), 0);
  SD_EXPECT("wake_shared_mmap", sys_futex((u64)p, FUTEX_WAKE, 0x7fffffffUL), 0);
  SD_EXPECT("mmap_word_unchanged", *(volatile u32 *)p, 0x12345678U);

  SD_EXPECT("munmap_ok", sd_munmap((u64)p, PAGE), 0);
  SD_EXPECT("wake_priv_unmapped", sys_futex((u64)p, FUTEX_WAKE_PRIVATE, 1), 0);
  SD_EXPECT("wake_shared_unmapped", sys_futex((u64)p, FUTEX_WAKE, 1), -EFAULT);
  SD_EXPECT("wake_shared_null", sys_futex(0, FUTEX_WAKE, 1), -EFAULT);

  // Above 48-bit user VA limit: alignment check (-EINVAL) still runs before access_ok (-EFAULT),
  // and aligned uaddr >= 2^48 returns -EFAULT for both private and shared wakes.
  SD_EXPECT("wake_priv_va48_efault", sys_futex(1ULL << 48, FUTEX_WAKE_PRIVATE, 1), -EFAULT);
  SD_EXPECT("wake_shared_va48_efault", sys_futex(1ULL << 48, FUTEX_WAKE, 1), -EFAULT);
  SD_EXPECT("wake_priv_hi_efault", sys_futex(0xfffffffffffffffcULL, FUTEX_WAKE_PRIVATE, 1),
            -EFAULT);
  SD_EXPECT("wake_priv_va48_unalign", sys_futex((1ULL << 48) + 2, FUTEX_WAKE_PRIVATE, 1), -EINVAL);
  return 0;
}
