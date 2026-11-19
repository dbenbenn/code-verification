// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// mremap(2) with flags == 0 (in-place without MREMAP_MAYMOVE): shrink, same-page resize, grow into
// unmapped tail, and -ENOMEM when an adjacent mapping blocks in-place expansion.
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)
#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

static inline int mm_page_aligned(i64 a) { return a > 0 && ((u64)a & (PAGE - 1)) == 0; }

static inline i64 mm_mremap(u64 a, u64 ol, u64 nl, u64 fl) {
  return sd_sys4(SYS_mremap, a, ol, nl, fl);
}

static inline void mm_fill(u64 base, u64 len, u8 v) {
  volatile u8 *p = (volatile u8 *)base;
  for (u64 i = 0; i < len; i += 64) {
    p[i] = v;
    p[i + 63 < len ? i + 63 : len - 1] = v;
  }
}

static inline int mm_all_eq(u64 base, u64 len, u8 v) {
  const volatile u8 *p = (const volatile u8 *)base;
  for (u64 i = 0; i < len; i += 64)
    if (p[i] != v || p[i + 63 < len ? i + 63 : len - 1] != v) return 0;
  return 1;
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;

  // Reserve 4 contiguous pages, populate pages 0..1, and unmap pages 2..3 to leave a free tail.
  i64 p = sd_mmap(0, 4 * PAGE, MM_RW, MM_PA, -1, 0);
  SD_CHECK("mmap_aligned", mm_page_aligned(p));
  if (!mm_page_aligned(p)) return 0;
  mm_fill((u64)p, PAGE, 0x41);
  mm_fill((u64)p + PAGE, PAGE, 0x42);
  SD_EXPECT("munmap_tail", sd_munmap((u64)p + 2 * PAGE, 2 * PAGE), 0);

  // 1. In-place shrink 2 -> 1 page returns p and preserves page 0.
  SD_CHECK("shrink_eq_old", mm_mremap((u64)p, 2 * PAGE, PAGE, 0) == p);
  SD_CHECK("shrink_p0_kept", mm_all_eq((u64)p, PAGE, 0x41));

  // 2. Same-page resize (PAGE -> PAGE / 2) returns p and keeps page 0.
  SD_CHECK("same_page_eq_old", mm_mremap((u64)p, PAGE, PAGE / 2, 0) == p);
  SD_CHECK("same_page_p0_kept", mm_all_eq((u64)p, PAGE, 0x41));

  // 3. In-place grow 1 -> 3 pages using an unaligned new_len (2 * PAGE + 17 -> 3 * PAGE) into the
  //    unmapped hole [p + PAGE, p + 3 * PAGE) returns p, preserves page 0, and maps zero-filled
  //    writable pages 1..2.
  SD_CHECK("grow_eq_old", mm_mremap((u64)p, PAGE, 2 * PAGE + 17, 0) == p);
  SD_CHECK("grow_p0_kept", mm_all_eq((u64)p, PAGE, 0x41));
  SD_CHECK("grow_p1_zero", mm_all_eq((u64)p + PAGE, PAGE, 0));
  SD_CHECK("grow_p2_zero", mm_all_eq((u64)p + 2 * PAGE, PAGE, 0));
  mm_fill((u64)p + 2 * PAGE, PAGE, 0x5a);
  SD_CHECK("grow_p2_writable", mm_all_eq((u64)p + 2 * PAGE, PAGE, 0x5a));

  // 4. Map a blocker at p + 3 * PAGE; growing 3 -> 4 pages with flags == 0 must fail with -ENOMEM.
  i64 blk = sd_mmap((u64)p + 3 * PAGE, PAGE, MM_RW, MM_PA | MAP_FIXED, -1, 0);
  SD_CHECK("blocker_mapped", blk == p + 3 * (i64)PAGE);
  mm_fill((u64)blk, PAGE, 0x33);
  SD_EXPECT("grow_blocked_enomem", mm_mremap((u64)p, 3 * PAGE, 4 * PAGE, 0), -ENOMEM);
  SD_CHECK("blocked_p0_kept", mm_all_eq((u64)p, PAGE, 0x41));
  SD_CHECK("blocked_p2_kept", mm_all_eq((u64)p + 2 * PAGE, PAGE, 0x5a));
  SD_CHECK("blocker_kept", mm_all_eq((u64)blk, PAGE, 0x33));

  // 5. flags == 0 validation errors: new_len == 0, unaligned old_address, overflow new_len,
  //    unmapped old_address, and top-of-VA ranges past 2^48.
  SD_EXPECT("zero_new_einval", mm_mremap((u64)p, PAGE, 0, 0), -EINVAL);
  SD_EXPECT("unaligned_old_einval", mm_mremap((u64)p + 16, PAGE, 2 * PAGE, 0), -EINVAL);
  SD_EXPECT("overflow_new_einval", mm_mremap((u64)p, PAGE, 0xfffffffffffff001ULL, 0), -EINVAL);
  SD_EXPECT("cleanup_munmap", sd_munmap((u64)p, 4 * PAGE), 0);
  SD_EXPECT("unmapped_old_efault", mm_mremap((u64)p, PAGE, 2 * PAGE, 0), -EFAULT);
  SD_EXPECT("top_va_span_efault", mm_mremap((1ULL << 48) - PAGE, 2 * PAGE, 3 * PAGE, 0), -EFAULT);
  SD_EXPECT("above_va48_efault", mm_mremap(1ULL << 48, PAGE, 2 * PAGE, 0), -EFAULT);
  return 0;
}
