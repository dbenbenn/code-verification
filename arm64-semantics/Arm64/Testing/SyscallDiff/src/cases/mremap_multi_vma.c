// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// mremap(2) across two adjacent unmerged anonymous RW VMAs: Linux check_prep_vma rejects
// old_len > vma->vm_end - addr with -EFAULT, whereas flat byte-permission Memory has no VMA
// boundaries and succeeds in place ([INTENTIONAL_OVERAPPROX]).
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)
#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

static inline i64 mm_mremap(u64 a, u64 ol, u64 nl, u64 fl) {
  return sd_sys4(SYS_mremap, a, ol, nl, fl);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;

  // 1. Map 2 RW pages at a0, fault page 0 to attach an anon_vma anchored at a0 >> PAGE_SHIFT,
  //    and block [a0 + PAGE, a0 + 2 * PAGE) with PROT_NONE so MAYMOVE must relocate.
  i64 a0 = sd_mmap(0, 2 * PAGE, MM_RW, MM_PA, -1, 0);
  SD_CHECK("a0_ok", a0 > 0 && ((u64)a0 & (PAGE - 1)) == 0);
  if (a0 <= 0) return 0;
  *(volatile u8 *)a0 = 0x41;
  SD_EXPECT("block_a0_tail", sd_sys3(SYS_mprotect, (u64)a0 + PAGE, PAGE, PROT_NONE), 0);

  // 2. Relocate [a0, a0 + PAGE) to a 4-page region [b, b + 4 * PAGE) with vm_pgoff = a0 >> 12,
  //    then shrink in place to [b, b + 2 * PAGE) so [b + 2 * PAGE, b + 4 * PAGE) is unmapped.
  i64 b = mm_mremap((u64)a0, PAGE, 4 * PAGE, MREMAP_MAYMOVE);
  SD_CHECK("b_moved", b > 0 && ((u64)b & (PAGE - 1)) == 0 && b != a0);
  if (b <= 0) return 0;
  SD_CHECK("shrink_b", mm_mremap((u64)b, 4 * PAGE, 2 * PAGE, 0) == b);

  // 3. Map a fresh anonymous RW VMA at [b + 2 * PAGE, b + 3 * PAGE). Because [b, b + 2 * PAGE)
  //    retains anon_vma / vm_pgoff from a0, Linux cannot merge the two adjacent RW VMAs, leaving
  //    [b + 3 * PAGE, b + 4 * PAGE) unmapped immediately above.
  i64 c = sd_mmap((u64)b + 2 * PAGE, PAGE, MM_RW, MM_PA | MAP_FIXED, -1, 0);
  SD_CHECK("c_mapped", c == b + 2 * (i64)PAGE);

  // 4. Attempting to mremap 3 -> 4 pages across the VMA boundary at b + 2 * PAGE with flags == 0
  //    returns -EFAULT on Linux (old_len > vma->vm_end - addr).
  SD_EXPECT("multi_vma_efault", mm_mremap((u64)b, 3 * PAGE, 4 * PAGE, 0), -EFAULT);

  SD_EXPECT("cleanup_a0", sd_munmap((u64)a0 + PAGE, PAGE), 0);
  SD_EXPECT("cleanup_bc", sd_munmap((u64)b, 4 * PAGE), 0);
  return 0;
}
