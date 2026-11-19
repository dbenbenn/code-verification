// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// mremap(2) with new_len == 0 returns -EINVAL on Linux 7.3 (for both flags == 0 and
// MREMAP_MAYMOVE) while preserving the existing mapping; qemu-aarch64 returns -ENOMEM (QEMU-DEV-6).
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)
#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 p = sd_mmap(0, PAGE, MM_RW, MM_PA, -1, 0);
  SD_CHECK("mmap_ok", p > 0 && ((u64)p & (PAGE - 1)) == 0);
  if (p <= 0) return 0;
  *(volatile u8 *)p = 0x41;
  SD_EXPECT("flags0_new_len_zero", sd_sys4(SYS_mremap, (u64)p, PAGE, 0, 0), -EINVAL);
  SD_EXPECT("maymove_new_len_zero", sd_sys4(SYS_mremap, (u64)p, PAGE, 0, MREMAP_MAYMOVE), -EINVAL);
  SD_EXPECT("page_kept", *(volatile u8 *)p, 0x41);
  SD_EXPECT("munmap_ok", sd_munmap((u64)p, PAGE), 0);
  return 0;
}
