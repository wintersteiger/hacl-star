#include "testlib.h"
#include "Random.h"
#include "Hacl_Mult.h"

int perf_mult() {
  const size_t rLen = 33;
  const size_t iLen = 31;
  const size_t pow2_i = 64;
  const size_t resLen = 66;
  const size_t tmpLen = 256;
  //uint32_t k = 32;
  
  uint64_t a[rLen];
  random_bytes((uint8_t*) a,32*8);

  for (int i = 0; i < rLen; i++) {
     printf("%llu ", a[i]);
   }
  printf(" \n");
  uint64_t b[rLen];
  random_bytes((uint8_t*) b,32*8);

  uint64_t tmp[256] = {0};
  uint64_t res1[66] = {0};
  uint64_t res2[66] = {0};

  TestLib_cycles t0,t1,t2,t3;
  printf("k \t ratio \t karatsuba \t mult \t eq \n");
  for (int k = 2; k < rLen; k++){
    t0 = TestLib_cpucycles_begin();
    for (int i = 0; i < 100000; i++){
      memset(res1, 0U, resLen * sizeof res1[0U]);    
      Hacl_Impl_Multiplication_karatsuba(k, rLen, pow2_i, iLen, rLen, a, b, tmp, res1);    
    }
    t1 = TestLib_cpucycles_end();

    //TestLib_print_cycles_per_round(t0, t1, 100000);

    t2 = TestLib_cpucycles_begin();
    for (int i = 0; i < 100000; i++){
      memset(res2, 0U, resLen * sizeof res2[0U]);
      Hacl_Impl_Multiplication_bn_mul(rLen, rLen, rLen, a, rLen, b, res2);
    }
    t3 = TestLib_cpucycles_end();

    //TestLib_print_cycles_per_round(t2, t3, 100000);
    //int eqb = Hacl_Impl_Lib_eq_b(resLen, resLen, res1, res2);
    //printf("\n res1 =? res2 %d \n", eqb);
  /* printf("\n Karatsuba's mult: \n"); */
  /* for (int i = 0; i < resLen; i++) { */
  /*   printf("%llu", res1[i]); */
  /* } */
  /* printf(" \n"); */

  /* printf("\nMult: \n"); */
  /* for (int i = 0; i < resLen; i++) { */
  /*   printf("%llu", res2[i]); */
  /* } */
  /* printf(" \n"); */
    //printf("\n Ratio: %lf \n", (double) (t1 - t0) / (t3 - t2));
    double ratio = (double) (t1 - t0) / (t3 - t2);
    double r1 = (double) (t1 - t0) / 100000;
    double r2 = (double) (t3 - t2) / 100000;
    int eqb = Hacl_Impl_Lib_eq_b(resLen, resLen, res1, res2);
    printf("%d \t %lf \t %lf \t %lf \t %d \n", k, ratio, r1, r2, eqb);
  }
  return 0;
}

int32_t main(int argc, char *argv[])
{
  perf_mult();
  return 1;
}
