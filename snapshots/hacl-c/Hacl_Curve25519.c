/* MIT License
 *
 * Copyright (c) 2016-2017 INRIA and Microsoft Corporation
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
#include "Hacl_Curve25519.h"
#include <immintrin.h>
#include <x86intrin.h>

//#define DEBUG(x) {}
#define DEBUG(x) x

inline static void Hacl_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  char c = 0;
  c = _addcarry_u64(c,a[0],b[0],&a[0]);
  c = _addcarry_u64(c,a[1],b[1],&a[1]);
  c = _addcarry_u64(c,a[2],b[2],&a[2]);
  c = _addcarry_u64(c,a[3],b[3],&a[3]);

  DEBUG(if (c > 1) printf("carry greater than 1");)
  uint64_t top = (uint64_t)38 * c;
  c = 0;
  c = _addcarry_u64(c,a[0],top,&a[0]);
  c = _addcarry_u64(c,a[1],0,  &a[1]);
  c = _addcarry_u64(c,a[2],0,  &a[2]);
  c = _addcarry_u64(c,a[3],0,  &a[3]);

  DEBUG(if (c > 0) printf("WARNING: need additional carry in fsum\n"));
}

inline static void Hacl_Bignum_fdifference(uint64_t *a, uint64_t *b)
{
  
  uint64_t tmp[5U] = { 0U };
  char c = 0;
  c = _addcarry_u64(c,b[0],(uint64_t)0xffffffffffffff68,&tmp[0]);
  c = _addcarry_u64(c,b[1],(uint64_t)0xffffffffffffffff,&tmp[1]);
  c = _addcarry_u64(c,b[2],(uint64_t)0xffffffffffffffff,&tmp[2]);
  c = _addcarry_u64(c,b[3],(uint64_t)0xffffffffffffffff,&tmp[3]);
  c = _addcarry_u64(c,3,0,&tmp[4]);

  DEBUG(if (c > 0) printf("WARNING: dropping carry in fdiff\n"));

  c = 0;
  c = _subborrow_u64(c,tmp[0],a[0],&tmp[0]);
  c = _subborrow_u64(c,tmp[1],a[1],&tmp[1]);
  c = _subborrow_u64(c,tmp[2],a[2],&tmp[2]);
  c = _subborrow_u64(c,tmp[3],a[3],&tmp[3]);
  c = _subborrow_u64(c,tmp[4],0,&tmp[4]);
  
  /*
  c = _subborrow_u64(c,a[0],tmp[0],&tmp[0]);
  c = _subborrow_u64(c,a[1],tmp[1],&tmp[1]);
  c = _subborrow_u64(c,a[2],tmp[2],&tmp[2]);
  c = _subborrow_u64(c,a[3],tmp[3],&tmp[3]);
  c = _subborrow_u64(c,0,   tmp[4],&tmp[4]);
  */

  DEBUG(if (c > 0) printf("WARNING: dropping carry in fdiff\n"));
  
  uint64_t top = (uint64_t)38 * tmp[4];
  c = 0;
  c = _addcarry_u64(c,tmp[0],top,&tmp[0]);
  c = _addcarry_u64(c,tmp[1],0,  &tmp[1]);
  c = _addcarry_u64(c,tmp[2],0,  &tmp[2]);
  c = _addcarry_u64(c,tmp[3],0,  &tmp[3]);

  DEBUG(if (c > 1) printf("carry greater than 1");)
  top = (uint64_t)38 * c;
  c = 0;
  c = _addcarry_u64(c,tmp[0],top,&tmp[0]);
  c = _addcarry_u64(c,tmp[1],0,  &tmp[1]);
  c = _addcarry_u64(c,tmp[2],0,  &tmp[2]);
  c = _addcarry_u64(c,tmp[3],0,  &tmp[3]);

  DEBUG(if (c > 0) printf("WARNING: need additional carry in fdifference\n");)

  a[0] = tmp[0];
  a[1] = tmp[1];
  a[2] = tmp[2];
  a[3] = tmp[3];
}

inline static void Hacl_Bignum_fscalar(uint64_t *output, uint64_t *b, uint64_t s)
{
  uint64_t h0,l0,h1,l1,h2,l2,h3,l3,h4,l4;
  l0 = _mulx_u64(b[0],s,&h0);
  l1 = _mulx_u64(b[1],s,&h1);
  l2 = _mulx_u64(b[2],s,&h2);
  l3 = _mulx_u64(b[3],s,&h3);
  char c = 0;
  c = _addcarry_u64(c,l1,h0,&l1);
  c = _addcarry_u64(c,l2,h1,&l2);
  c = _addcarry_u64(c,l3,h2,&l3);
  c = _addcarry_u64(c,0,h3,&l4);

  DEBUG(if (c > 0) printf("WARNING: need carry pass in fscalar\n");)
  
  l4 = _mulx_u64(l4,38,&h4);
  c = 0;
  c = _addcarry_u64(c,l0,l4,&l0);
  c = _addcarry_u64(c,l1,h4,&l1);
  c = _addcarry_u64(c,l2,0,&l2);
  c = _addcarry_u64(c,l3,0,&l3);

  DEBUG(if (c > 0) printf("WARNING: need 2nd carry round in fscalar\n");)

  l4 = (uint64_t)38 * c;
  c = 0;
  c = _addcarry_u64(c,l0,l4,&l0);
  c = _addcarry_u64(c,l1,0,&l1);
  c = _addcarry_u64(c,l2,0,&l2);
  c = _addcarry_u64(c,l3,0,&l3);

  DEBUG(if (c > 0) printf("WARNING: discarding carry in fscalar\n");)

  output[0] = l0;
  output[1] = l1;
  output[2] = l2;
  output[3] = l3;
}


inline static void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input1, uint64_t *input2){
  uint64_t tmp[8] = {0};
  char c = 0;
  char d = 0;
  uint64_t low,h0,h1;
  tmp[0] = _mulx_u64(input1[0],input2[0],&h0);
  for (int j = 1; j < 4; j++) {
    low = _mulx_u64(input1[0],input2[j],&h1);
    c = _addcarry_u64(c,low,h0,&tmp[j]);
    h0 = h1;
  }
  c = _addcarry_u64(c,h0,0,&tmp[4]);
  for (int i = 1; i < 4; i++) {
    DEBUG(if (c > 0) printf("WARNING: dropping carry in fmul\n"));
    c = 0;
    low = _mulx_u64(input1[i],input2[0],&h0);
    d = _addcarry_u64(d,tmp[i],low,&tmp[i]);
    for (int j = 1; j < 4; j++) {
      low = _mulx_u64(input1[i],input2[j],&h1);
      c = _addcarry_u64(c,low,h0,&h0);
      d = _addcarry_u64(d,tmp[i+j],h0,&tmp[i+j]);
      h0 = h1;
    }
    c = _addcarry_u64(c,h0,0,&h0);
    d = _addcarry_u64(d,h0,0,&tmp[i+4]);
  }

  DEBUG(if (c > 0 || d > 0) printf("discarding carry in fmul\n");)
  
  c = 0; d = 0;
  low = _mulx_u64(tmp[4],38,&h0);
  c = _addcarry_u64(c,tmp[0],low,&tmp[0]);
  low = _mulx_u64(tmp[5],38,&h1);
  c = _addcarry_u64(c,tmp[1],low,&tmp[1]);
  d = _addcarry_u64(d,tmp[1],h0,&tmp[1]);
  h0 = h1;
  low = _mulx_u64(tmp[6],38,&h1);
  c = _addcarry_u64(c,tmp[2],low,&tmp[2]);
  d = _addcarry_u64(d,tmp[2],h0,&tmp[2]);
  h0 = h1;
  low = _mulx_u64(tmp[7],38,&h1);
  c = _addcarry_u64(c,tmp[3],low,&tmp[3]);
  d = _addcarry_u64(d,tmp[3],h0,&tmp[3]);

  c = _addcarry_u64(c,h1,0,&h1);
  d = _addcarry_u64(d,h1,0,&h1);

  DEBUG(if (c > 0 || d > 0) printf("discarding carry in fmul (2)\n");)

  h1 = (uint64_t)38 * h1;

  c = 0;
  c = _addcarry_u64(c,tmp[0],h1,&tmp[0]);
  c = _addcarry_u64(c,tmp[1],0,&tmp[1]);
  c = _addcarry_u64(c,tmp[2],0,&tmp[2]);
  c = _addcarry_u64(c,tmp[3],0,&tmp[3]);

  DEBUG(if (c > 1) printf("WARNING: c > 1\n");)

  h1 = (uint64_t)38 * c;

  c = 0;
  c = _addcarry_u64(c,tmp[0],h1,&tmp[0]);
  c = _addcarry_u64(c,tmp[1],0,&tmp[1]);
  c = _addcarry_u64(c,tmp[2],0,&tmp[2]);
  c = _addcarry_u64(c,tmp[3],0,&tmp[3]);

  DEBUG(if (c > 0) printf("WARNING: need 3rd carry round in fmul\n");)

  output[0] = tmp[0];
  output[1] = tmp[1];
  output[2] = tmp[2];
  output[3] = tmp[3];
  
}

  
inline static void
Hacl_Bignum_Fsquare_fsquare(uint64_t *input)
{
  Hacl_Bignum_Fmul_fmul(input,input,input);
}

inline static void
Hacl_Bignum_Fsquare_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count1)
{
  memcpy(output, input, (uint32_t)5U * sizeof input[0U]);
  Hacl_Bignum_Fsquare_fsquare(output);
  for (uint32_t i = (uint32_t)1U; i < count1; i = i + (uint32_t)1U)
    Hacl_Bignum_Fsquare_fsquare(output);
}

inline static void Hacl_Bignum_Fsquare_fsquare_times_inplace(uint64_t *output, uint32_t count1)
{
  Hacl_Bignum_Fsquare_fsquare(output);
  for (uint32_t i = (uint32_t)1U; i < count1; i = i + (uint32_t)1U)
    Hacl_Bignum_Fsquare_fsquare(output);
}

inline static void Hacl_Bignum_Crecip_crecip(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20U] = { 0U };
  uint64_t *a = buf;
  uint64_t *t00 = buf + (uint32_t)5U;
  uint64_t *b0 = buf + (uint32_t)10U;
  Hacl_Bignum_Fsquare_fsquare_times(a, z, (uint32_t)1U);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t)2U);
  Hacl_Bignum_Fmul_fmul(b0, t00, z);
  Hacl_Bignum_Fmul_fmul(a, b0, a);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t)1U);
  Hacl_Bignum_Fmul_fmul(b0, t00, b0);
  Hacl_Bignum_Fsquare_fsquare_times(t00, b0, (uint32_t)5U);
  uint64_t *t01 = buf + (uint32_t)5U;
  uint64_t *b1 = buf + (uint32_t)10U;
  uint64_t *c0 = buf + (uint32_t)15U;
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t)10U);
  Hacl_Bignum_Fmul_fmul(c0, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, c0, (uint32_t)20U);
  Hacl_Bignum_Fmul_fmul(t01, t01, c0);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t01, (uint32_t)10U);
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t)50U);
  uint64_t *a0 = buf;
  uint64_t *t0 = buf + (uint32_t)5U;
  uint64_t *b = buf + (uint32_t)10U;
  uint64_t *c = buf + (uint32_t)15U;
  Hacl_Bignum_Fmul_fmul(c, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times(t0, c, (uint32_t)100U);
  Hacl_Bignum_Fmul_fmul(t0, t0, c);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t)50U);
  Hacl_Bignum_Fmul_fmul(t0, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t)5U);
  Hacl_Bignum_Fmul_fmul(out, t0, a0);
}

void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fmul_fmul(output, a, b);
}

inline static void Hacl_Bignum_crecip(uint64_t *output, uint64_t *input)
{
  Hacl_Bignum_Crecip_crecip(output, input);
}

static void
Hacl_EC_Point_swap_conditional_step(uint64_t *a, uint64_t *b, uint64_t swap1, uint32_t ctr)
{
  uint32_t i = ctr - (uint32_t)1U;
  uint64_t ai = a[i];
  uint64_t bi = b[i];
  uint64_t x = swap1 & (ai ^ bi);
  uint64_t ai1 = ai ^ x;
  uint64_t bi1 = bi ^ x;
  a[i] = ai1;
  b[i] = bi1;
}

static void
Hacl_EC_Point_swap_conditional_(uint64_t *a, uint64_t *b, uint64_t swap1, uint32_t ctr)
{
  if (!(ctr == (uint32_t)0U))
  {
    Hacl_EC_Point_swap_conditional_step(a, b, swap1, ctr);
    uint32_t i = ctr - (uint32_t)1U;
    Hacl_EC_Point_swap_conditional_(a, b, swap1, i);
  }
}

static void Hacl_EC_Point_swap_conditional(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap1 = (uint64_t)0U - iswap;
  Hacl_EC_Point_swap_conditional_(a, b, swap1, (uint32_t)5U);
  Hacl_EC_Point_swap_conditional_(a + (uint32_t)5U, b + (uint32_t)5U, swap1, (uint32_t)5U);
}

static void Hacl_EC_Point_copy(uint64_t *output, uint64_t *input)
{
  memcpy(output, input, (uint32_t)5U * sizeof input[0U]);
  memcpy(output + (uint32_t)5U,
    input + (uint32_t)5U,
    (uint32_t)5U * sizeof (input + (uint32_t)5U)[0U]);
}

static void
Hacl_EC_AddAndDouble_fmonty(
  uint64_t *pp,
  uint64_t *ppq,
  uint64_t *p,
  uint64_t *pq,
  uint64_t *qmqp
)
{
  uint64_t *qx = qmqp;
  uint64_t *x2 = pp;
  uint64_t *z2 = pp + (uint32_t)5U;
  uint64_t *x3 = ppq;
  uint64_t *z3 = ppq + (uint32_t)5U;
  uint64_t *x = p;
  uint64_t *z = p + (uint32_t)5U;
  uint64_t *xprime = pq;
  uint64_t *zprime = pq + (uint32_t)5U;
  uint64_t buf[40U] = { 0U };
  uint64_t *origx = buf;
  uint64_t *origxprime = buf + (uint32_t)5U;
  uint64_t *xxprime0 = buf + (uint32_t)25U;
  uint64_t *zzprime0 = buf + (uint32_t)30U;
  memcpy(origx, x, (uint32_t)5U * sizeof x[0U]);
  Hacl_Bignum_fsum(x, z);
  Hacl_Bignum_fdifference(z, origx);
  memcpy(origxprime, xprime, (uint32_t)5U * sizeof xprime[0U]);
  Hacl_Bignum_fsum(xprime, zprime);
  Hacl_Bignum_fdifference(zprime, origxprime);
  Hacl_Bignum_fmul(xxprime0, xprime, z);
  Hacl_Bignum_fmul(zzprime0, x, zprime);
  uint64_t *origxprime0 = buf + (uint32_t)5U;
  uint64_t *xx0 = buf + (uint32_t)15U;
  uint64_t *zz0 = buf + (uint32_t)20U;
  uint64_t *xxprime = buf + (uint32_t)25U;
  uint64_t *zzprime = buf + (uint32_t)30U;
  uint64_t *zzzprime = buf + (uint32_t)35U;
  memcpy(origxprime0, xxprime, (uint32_t)5U * sizeof xxprime[0U]);
  Hacl_Bignum_fsum(xxprime, zzprime);
  Hacl_Bignum_fdifference(zzprime, origxprime0);
  Hacl_Bignum_Fsquare_fsquare_times(x3, xxprime, (uint32_t)1U);
  Hacl_Bignum_Fsquare_fsquare_times(zzzprime, zzprime, (uint32_t)1U);
  Hacl_Bignum_fmul(z3, zzzprime, qx);
  Hacl_Bignum_Fsquare_fsquare_times(xx0, x, (uint32_t)1U);
  Hacl_Bignum_Fsquare_fsquare_times(zz0, z, (uint32_t)1U);
  uint64_t *zzz = buf + (uint32_t)10U;
  uint64_t *xx = buf + (uint32_t)15U;
  uint64_t *zz = buf + (uint32_t)20U;
  Hacl_Bignum_fmul(x2, xx, zz);
  Hacl_Bignum_fdifference(zz, xx);
  uint64_t scalar = (uint64_t)121665U;
  Hacl_Bignum_fscalar(zzz, zz, scalar);
  Hacl_Bignum_fsum(zzz, xx);
  Hacl_Bignum_fmul(z2, zzz, zz);
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt
)
{
  uint64_t bit = (uint64_t)(byt >> (uint32_t)7U);
  Hacl_EC_Point_swap_conditional(nq, nqpq, bit);
  Hacl_EC_AddAndDouble_fmonty(nq2, nqpq2, nq, nqpq, q);
  uint64_t bit0 = (uint64_t)(byt >> (uint32_t)7U);
  Hacl_EC_Point_swap_conditional(nq2, nqpq2, bit0);
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_double_step(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt
)
{
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(nq, nqpq, nq2, nqpq2, q, byt);
  uint8_t byt1 = byt << (uint32_t)1U;
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(nq2, nqpq2, nq, nqpq, q, byt1);
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  for (int j = 0; j < i; j++) {
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop_double_step(nq, nqpq, nq2, nqpq2, q, byt);
    byt = byt << (uint32_t)2U;
  }
}

static void
Hacl_EC_Ladder_BigLoop_cmult_big_loop(
  uint8_t *n1,
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint32_t i
)
{
  for (int j = i-1; j >= 0; j--) {
    uint8_t byte = n1[j];
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byte, (uint32_t)4U);
  }
}

static void Hacl_EC_Ladder_cmult(uint64_t *result, uint8_t *n1, uint64_t *q)
{
  uint64_t point_buf[40U] = { 0U };
  uint64_t *nq = point_buf;
  uint64_t *nqpq = point_buf + (uint32_t)10U;
  uint64_t *nq2 = point_buf + (uint32_t)20U;
  uint64_t *nqpq2 = point_buf + (uint32_t)30U;
  Hacl_EC_Point_copy(nqpq, q);
  nq[0U] = (uint64_t)1U;
  Hacl_EC_Ladder_BigLoop_cmult_big_loop(n1, nq, nqpq, nq2, nqpq2, q, (uint32_t)32U);
  Hacl_EC_Point_copy(result, nq);
}

void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input)
{
  output[0] = load64_le(input);
  output[1] = load64_le(input+8);
  output[2] = load64_le(input+16);
  output[3] = load64_le(input+24);
}


void Hacl_EC_Format_fcontract(uint8_t *output, uint64_t *input)
{
  uint64_t top = input[3];
  //DEBUG(  if (top >> 63 == 1) printf("fcontract top bit\n");)
  input[3] = top & 0x7fffffffffffffff;
  top = top >> 63;
  top = top * 19;
  char c = 0;
  c = _addcarry_u64(c,input[0],top,&input[0]);
  c = _addcarry_u64(c,input[1],0,  &input[1]);
  c = _addcarry_u64(c,input[2],0,  &input[2]);
  c = _addcarry_u64(c,input[3],0,  &input[3]);

  DEBUG(if (c > 0) printf("discarding carry in fcontract");)
  if (input[0] >= 0xffffffffffffffed &&
      input[1] == 0xffffffffffffffff &&
      input[2] == 0xffffffffffffffff &&
      input[3] == 0x7fffffffffffffff) {
    input[0] = input[0] - 0xffffffffffffffed;
    input[1] = input[1] - 0xffffffffffffffff;
    input[2] = input[2] - 0xffffffffffffffff;
    input[3] = input[3] - 0x7fffffffffffffff;
  }
  
  store64_le(output,input[0]);
  store64_le(output+8,input[1]);
  store64_le(output+16,input[2]);
  store64_le(output+24,input[3]);
  //  DEBUG(printf("fcontract result: ");for (int i = 31; i >= 0; i--) printf("%02X",output[i]);printf("\n");)
}

static void Hacl_EC_Format_scalar_of_point(uint8_t *scalar, uint64_t *point)
{
  uint64_t *x = point;
  uint64_t *z = point + (uint32_t)5U;
  uint64_t buf[10U] = { 0U };
  uint64_t *zmone = buf;
  uint64_t *sc = buf + (uint32_t)5U;
  Hacl_Bignum_crecip(zmone, z);
  Hacl_Bignum_fmul(sc, x, zmone);
  Hacl_EC_Format_fcontract(scalar, sc);
}

void Hacl_EC_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  uint64_t buf0[10U] = { 0U };
  uint64_t *x0 = buf0;
  uint64_t *z = buf0 + (uint32_t)5U;
  Hacl_EC_Format_fexpand(x0, basepoint);
  z[0U] = (uint64_t)1U;
  uint64_t *q = buf0;
  uint8_t e[32U] = { 0U };
  memcpy(e, secret, (uint32_t)32U * sizeof secret[0U]);
  uint8_t e0 = e[0U];
  uint8_t e31 = e[31U];
  uint8_t e01 = e0 & (uint8_t)248U;
  uint8_t e311 = e31 & (uint8_t)127U;
  uint8_t e312 = e311 | (uint8_t)64U;
  e[0U] = e01;
  e[31U] = e312;
  uint8_t *scalar = e;
  uint64_t buf[15U] = { 0U };
  uint64_t *nq = buf;
  uint64_t *x = nq;
  x[0U] = (uint64_t)1U;
  Hacl_EC_Ladder_cmult(nq, scalar, q);
  Hacl_EC_Format_scalar_of_point(mypublic, nq);
  fflush(stdout);

}

void Hacl_Curve25519_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  Hacl_EC_crypto_scalarmult(mypublic, secret, basepoint);
  fflush(stdout);
}

