#include "kremlin/testlib.h"
#include "Hacl_Unverified_Random.h"
#include "Hacl_Mult.h"

int perf_mult() {
  const size_t rLen = 32;
  const size_t pow2_i = 32;
  const size_t resLen = 64;
  const size_t tmpLen = 128;
  //uint32_t k = 32;

  uint64_t a[rLen];
  randombytes((uint8_t*) a,rLen*8);

  uint64_t b[rLen];
  randombytes((uint8_t*) b,rLen*8);

  uint64_t tmp[128] = {0};
  uint64_t res1[64] = {0};
  uint64_t res2[64] = {0};

  TestLib_cycles t0,t1,t2,t3;
  printf("k \t ratio \t karatsuba \t mult \t eq \n");
  for (int k = 2; k < rLen; k = k * 2){
    t0 = TestLib_cpucycles_begin();
    for (int i = 0; i < 100000; i++){
      Hacl_Impl_Multiplication_karatsuba_(k, pow2_i, rLen, a, b, tmp, res1);
    }
    t1 = TestLib_cpucycles_end();

    t2 = TestLib_cpucycles_begin();
    for (int i = 0; i < 100000; i++){
      Hacl_Impl_Multiplication_bn_mul(rLen, a, rLen, b, res2);
    }
    t3 = TestLib_cpucycles_end();

    double ratio = (double) (t1 - t0) / (t3 - t2);
    double r1 = (double) (t1 - t0) / 100000;
    double r2 = (double) (t3 - t2) / 100000;
    int eqb = Hacl_Impl_Lib_eq_b(resLen, res1, res2);
    printf("%d \t %lf \t %lf \t %lf \t %d \n", k, ratio, r1, r2, eqb);
  }
  return 0;
}

int32_t main(int argc, char *argv[])
{
  perf_mult();
  return 1;
}
