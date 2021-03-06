/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#ifndef __Hacl_IntTypes_Intrinsics_H
#define __Hacl_IntTypes_Intrinsics_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

/* SNIPPET_START: Hacl_IntTypes_Intrinsics_add_carry_u64 */

static inline uint64_t
Hacl_IntTypes_Intrinsics_add_carry_u64(uint64_t cin, uint64_t x, uint64_t y, uint64_t *result1)
{
  uint64_t res = x + cin + y;
  uint64_t
  c = (~FStar_UInt64_gte_mask(res, x) | (FStar_UInt64_eq_mask(res, x) & cin)) & (uint64_t)1U;
  result1[0U] = res;
  return c;
}

/* SNIPPET_END: Hacl_IntTypes_Intrinsics_add_carry_u64 */

/* SNIPPET_START: Hacl_IntTypes_Intrinsics_sub_borrow_u64 */

static inline uint64_t
Hacl_IntTypes_Intrinsics_sub_borrow_u64(
  uint64_t cin,
  uint64_t x,
  uint64_t y,
  uint64_t *result1
)
{
  uint64_t res = x - y - cin;
  uint64_t eqlty = FStar_UInt64_eq_mask(res, x);
  uint64_t
  c1 =
    ((FStar_UInt64_gte_mask(res, x) & ~FStar_UInt64_eq_mask(res, x)) | (eqlty & cin))
    & (uint64_t)1U;
  result1[0U] = res;
  return c1;
}

/* SNIPPET_END: Hacl_IntTypes_Intrinsics_sub_borrow_u64 */

#if defined(__cplusplus)
}
#endif

#define __Hacl_IntTypes_Intrinsics_H_DEFINED
#endif
