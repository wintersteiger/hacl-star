#include <immintrin.h>
#include <x86intrin.h>


#define Hacl_Bignum_addcarry_u64(c, a, b, res) (_addcarry_u64(c,a,b,&res))
#define Hacl_Bignum_subborrow_u64(c, a, b, res) (_subborrow_u64(c,a,b,&res))
#define Hacl_Bignum_mulx_u64(a,b,bh) (_mulx_u64(a,b,&bh))
