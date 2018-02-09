#include "testlib.h"
#include "Random.h"
#include "Hacl_Curve25519.h"
#include "Hacl_Impl_Bignum.h"

/*
void Hacl_Impl_Bignum_bn_mul_mod(uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Impl_Bignum_text_to_nat(uint8_t *input, uint64_t *res);

void Hacl_Impl_Bignum_nat_to_text(uint64_t *input, uint8_t *res);

void Hacl_Impl_Bignum_bn_mul_mod_fast(uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b);

void Hacl_EC_Format_fcontract(uint8_t *output, uint64_t *input);

void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input);

void mult_fast(
  uint32_t aLen,
  uint64_t *x,
  uint64_t *y,
  uint64_t *z)

*/

void reverse(uint8_t* a, int i, int j)
{
  while(i > j)
  {
    uint8_t temp = a[i];
    a[i] = a[j];
    a[j] = temp;
    i--;
    j++;
  }
}

int perf_mult() {
  const size_t rLen = 32;
  const size_t rLenNat = 5;
  TestLib_cycles t0,t1,t2,t3,t4,t5;

  uint8_t a1[32];
  random_bytes(a1, rLen);

  printf("\n a1:\n");
  for (int i = 0; i < rLen; i++){
	printf("%02x", a1[i]);
  }

  uint8_t b1[32] = {0};
  random_bytes(b1, rLen);

  printf("\n b1:\n");
  for (int i = 0; i < rLen; i++){
	printf("%02x", b1[i]);
  }
  
/* The textbook multiplication */
  uint64_t a1Nat[4];
  uint64_t b1Nat[4];
  uint64_t res1Nat[4] = {0};
  Hacl_Impl_Bignum_text_to_nat(a1, a1Nat);
  Hacl_Impl_Bignum_text_to_nat(b1, b1Nat);

  t0 = TestLib_cpucycles_begin();
  uint64_t a = 1;
  for (int i = 0; i < 100000000; i++){
    Hacl_Impl_Bignum_bn_mul_mod(a1Nat, b1Nat, res1Nat);
    //Hacl_Impl_Bignum_bn_mul_mod_fast(a1Nat, b1Nat, res1Nat);
    a = a ^ res1Nat[3];
  }
  t1 = TestLib_cpucycles_end();

  uint8_t res1[32] = {0};
  Hacl_Impl_Bignum_nat_to_text(res1Nat, res1);

  printf("\n the usual mult:\n");
  for (int i = 0; i < rLen; i++){
	printf("%02x", res1[i]);
  }
  printf("\n a = %llu \n", a);


/* HACL */
  reverse(a1, 31, 0);
  reverse(b1, 31, 0);

  uint64_t aNat[rLenNat];
  uint64_t bNat[rLenNat];
  uint64_t res2Nat[rLenNat];
  Hacl_EC_Format_fexpand(aNat, a1);
  Hacl_EC_Format_fexpand(bNat, b1);

  t2 = TestLib_cpucycles_begin();
  uint64_t b = 1;
  for (int i = 0; i < 100000000; i++){
    Hacl_Bignum_fmul(res2Nat, aNat, bNat);
    b = b ^ res2Nat[3];
  }
  t3 = TestLib_cpucycles_end();

  uint8_t res2[rLen];
  Hacl_EC_Format_fcontract(res2, res2Nat);

  printf("\n the curve-25519 mult (hacl):\n");
  for (int i = 0; i < rLen; i++){
	printf("%02x ", res2[i]);
  }
  printf("\n b = %llu \n", b);

/* Fast multiplication from the paper */ 
  uint64_t res3Nat[4] = {0};
  uint64_t c = 1;
  t4 = TestLib_cpucycles_begin();
  for (int i = 0; i < 100000000; i++){
    Hacl_Impl_Bignum_bn_mul_mod_fast(a1Nat, b1Nat, res3Nat);
    c = c ^ res3Nat[3];
  }
  t5 = TestLib_cpucycles_end();

  uint8_t res3[32] = {0};
  Hacl_Impl_Bignum_nat_to_text(res3Nat, res3);

  printf("\n the fast mult:\n");
  for (int i = 0; i < rLen; i++){
	printf("%02x", res3[i]);
  }

  printf("\n c = %llu \n", c);


  double ratio = (double) (t1 - t0) / (t3 - t2);
  double ratio1 = (double) (t5 - t4) / (t3 - t2);
  double r1 = (double) (t1 - t0) / 100000000;
  double r2 = (double) (t3 - t2) / 100000000;
  double r3 = (double) (t5 - t4) / 100000000;

  printf("\n (usual / hacl) (fast / hacl) \t  r1 (usual) \t r3 (fast) \t r2 (hacl) \n");
  printf("%lf \t %lf \t %lf \t %lf \t %lf \n", ratio, ratio1, r1, r3, r2);
  return 0;
}

int32_t main(int argc, char *argv[])
{
  perf_mult();
  return 1;
}
