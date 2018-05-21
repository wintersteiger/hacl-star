#include "kremlin/testlib.h"
#include "Hacl_Unverified_Random.h"
#include "Hacl_RSAPSS.h"
#include "openssl/opensslv.h"
#include "openssl/err.h"
#include "openssl/evp.h"
#include "openssl/rsa.h"

uint8_t n1[256U] =
    {
      (uint8_t)0xa5U, (uint8_t)0xddU, (uint8_t)0x86U, (uint8_t)0x7aU, (uint8_t)0xc4U, (uint8_t)0xcbU,
      (uint8_t)0x02U, (uint8_t)0xf9U, (uint8_t)0x0bU, (uint8_t)0x94U, (uint8_t)0x57U, (uint8_t)0xd4U,
      (uint8_t)0x8cU, (uint8_t)0x14U, (uint8_t)0xa7U, (uint8_t)0x70U, (uint8_t)0xefU, (uint8_t)0x99U,
      (uint8_t)0x1cU, (uint8_t)0x56U, (uint8_t)0xc3U, (uint8_t)0x9cU, (uint8_t)0x0eU, (uint8_t)0xc6U,
      (uint8_t)0x5fU, (uint8_t)0xd1U, (uint8_t)0x1aU, (uint8_t)0xfaU, (uint8_t)0x89U, (uint8_t)0x37U,
      (uint8_t)0xceU, (uint8_t)0xa5U, (uint8_t)0x7bU, (uint8_t)0x9bU, (uint8_t)0xe7U, (uint8_t)0xacU,
      (uint8_t)0x73U, (uint8_t)0xb4U, (uint8_t)0x5cU, (uint8_t)0x00U, (uint8_t)0x17U, (uint8_t)0x61U,
      (uint8_t)0x5bU, (uint8_t)0x82U, (uint8_t)0xd6U, (uint8_t)0x22U, (uint8_t)0xe3U, (uint8_t)0x18U,
      (uint8_t)0x75U, (uint8_t)0x3bU, (uint8_t)0x60U, (uint8_t)0x27U, (uint8_t)0xc0U, (uint8_t)0xfdU,
      (uint8_t)0x15U, (uint8_t)0x7bU, (uint8_t)0xe1U, (uint8_t)0x2fU, (uint8_t)0x80U, (uint8_t)0x90U,
      (uint8_t)0xfeU, (uint8_t)0xe2U, (uint8_t)0xa7U, (uint8_t)0xadU, (uint8_t)0xcdU, (uint8_t)0x0eU,
      (uint8_t)0xefU, (uint8_t)0x75U, (uint8_t)0x9fU, (uint8_t)0x88U, (uint8_t)0xbaU, (uint8_t)0x49U,
      (uint8_t)0x97U, (uint8_t)0xc7U, (uint8_t)0xa4U, (uint8_t)0x2dU, (uint8_t)0x58U, (uint8_t)0xc9U,
      (uint8_t)0xaaU, (uint8_t)0x12U, (uint8_t)0xcbU, (uint8_t)0x99U, (uint8_t)0xaeU, (uint8_t)0x00U,
      (uint8_t)0x1fU, (uint8_t)0xe5U, (uint8_t)0x21U, (uint8_t)0xc1U, (uint8_t)0x3bU, (uint8_t)0xb5U,
      (uint8_t)0x43U, (uint8_t)0x14U, (uint8_t)0x45U, (uint8_t)0xa8U, (uint8_t)0xd5U, (uint8_t)0xaeU,
      (uint8_t)0x4fU, (uint8_t)0x5eU, (uint8_t)0x4cU, (uint8_t)0x7eU, (uint8_t)0x94U, (uint8_t)0x8aU,
      (uint8_t)0xc2U, (uint8_t)0x27U, (uint8_t)0xd3U, (uint8_t)0x60U, (uint8_t)0x40U, (uint8_t)0x71U,
      (uint8_t)0xf2U, (uint8_t)0x0eU, (uint8_t)0x57U, (uint8_t)0x7eU, (uint8_t)0x90U, (uint8_t)0x5fU,
      (uint8_t)0xbeU, (uint8_t)0xb1U, (uint8_t)0x5dU, (uint8_t)0xfaU, (uint8_t)0xf0U, (uint8_t)0x6dU,
      (uint8_t)0x1dU, (uint8_t)0xe5U, (uint8_t)0xaeU, (uint8_t)0x62U, (uint8_t)0x53U, (uint8_t)0xd6U,
      (uint8_t)0x3aU, (uint8_t)0x6aU, (uint8_t)0x21U, (uint8_t)0x20U, (uint8_t)0xb3U, (uint8_t)0x1aU,
      (uint8_t)0x5dU, (uint8_t)0xa5U, (uint8_t)0xdaU, (uint8_t)0xbcU, (uint8_t)0x95U, (uint8_t)0x50U,
      (uint8_t)0x60U, (uint8_t)0x0eU, (uint8_t)0x20U, (uint8_t)0xf2U, (uint8_t)0x7dU, (uint8_t)0x37U,
      (uint8_t)0x39U, (uint8_t)0xe2U, (uint8_t)0x62U, (uint8_t)0x79U, (uint8_t)0x25U, (uint8_t)0xfeU,
      (uint8_t)0xa3U, (uint8_t)0xccU, (uint8_t)0x50U, (uint8_t)0x9fU, (uint8_t)0x21U, (uint8_t)0xdfU,
      (uint8_t)0xf0U, (uint8_t)0x4eU, (uint8_t)0x6eU, (uint8_t)0xeaU, (uint8_t)0x45U, (uint8_t)0x49U,
      (uint8_t)0xc5U, (uint8_t)0x40U, (uint8_t)0xd6U, (uint8_t)0x80U, (uint8_t)0x9fU, (uint8_t)0xf9U,
      (uint8_t)0x30U, (uint8_t)0x7eU, (uint8_t)0xedU, (uint8_t)0xe9U, (uint8_t)0x1fU, (uint8_t)0xffU,
      (uint8_t)0x58U, (uint8_t)0x73U, (uint8_t)0x3dU, (uint8_t)0x83U, (uint8_t)0x85U, (uint8_t)0xa2U,
      (uint8_t)0x37U, (uint8_t)0xd6U, (uint8_t)0xd3U, (uint8_t)0x70U, (uint8_t)0x5aU, (uint8_t)0x33U,
      (uint8_t)0xe3U, (uint8_t)0x91U, (uint8_t)0x90U, (uint8_t)0x09U, (uint8_t)0x92U, (uint8_t)0x07U,
      (uint8_t)0x0dU, (uint8_t)0xf7U, (uint8_t)0xadU, (uint8_t)0xf1U, (uint8_t)0x35U, (uint8_t)0x7cU,
      (uint8_t)0xf7U, (uint8_t)0xe3U, (uint8_t)0x70U, (uint8_t)0x0cU, (uint8_t)0xe3U, (uint8_t)0x66U,
      (uint8_t)0x7dU, (uint8_t)0xe8U, (uint8_t)0x3fU, (uint8_t)0x17U, (uint8_t)0xb8U, (uint8_t)0xdfU,
      (uint8_t)0x17U, (uint8_t)0x78U, (uint8_t)0xdbU, (uint8_t)0x38U, (uint8_t)0x1dU, (uint8_t)0xceU,
      (uint8_t)0x09U, (uint8_t)0xcbU, (uint8_t)0x4aU, (uint8_t)0xd0U, (uint8_t)0x58U, (uint8_t)0xa5U,
      (uint8_t)0x11U, (uint8_t)0x00U, (uint8_t)0x1aU, (uint8_t)0x73U, (uint8_t)0x81U, (uint8_t)0x98U,
      (uint8_t)0xeeU, (uint8_t)0x27U, (uint8_t)0xcfU, (uint8_t)0x55U, (uint8_t)0xa1U, (uint8_t)0x3bU,
      (uint8_t)0x75U, (uint8_t)0x45U, (uint8_t)0x39U, (uint8_t)0x90U, (uint8_t)0x65U, (uint8_t)0x82U,
      (uint8_t)0xecU, (uint8_t)0x8bU, (uint8_t)0x17U, (uint8_t)0x4bU, (uint8_t)0xd5U, (uint8_t)0x8dU,
      (uint8_t)0x5dU, (uint8_t)0x1fU, (uint8_t)0x3dU, (uint8_t)0x76U, (uint8_t)0x7cU, (uint8_t)0x61U,
      (uint8_t)0x37U, (uint8_t)0x21U, (uint8_t)0xaeU, (uint8_t)0x05U
    };

uint8_t e[3U] = { (uint8_t)0x01U, (uint8_t)0x00U, (uint8_t)0x01U };

uint8_t d[256U] =
    {
      (uint8_t)0x2dU, (uint8_t)0x2fU, (uint8_t)0xf5U, (uint8_t)0x67U, (uint8_t)0xb3U, (uint8_t)0xfeU,
      (uint8_t)0x74U, (uint8_t)0xe0U, (uint8_t)0x61U, (uint8_t)0x91U, (uint8_t)0xb7U, (uint8_t)0xfdU,
      (uint8_t)0xedU, (uint8_t)0x6dU, (uint8_t)0xe1U, (uint8_t)0x12U, (uint8_t)0x29U, (uint8_t)0x0cU,
      (uint8_t)0x67U, (uint8_t)0x06U, (uint8_t)0x92U, (uint8_t)0x43U, (uint8_t)0x0dU, (uint8_t)0x59U,
      (uint8_t)0x69U, (uint8_t)0x18U, (uint8_t)0x40U, (uint8_t)0x47U, (uint8_t)0xdaU, (uint8_t)0x23U,
      (uint8_t)0x4cU, (uint8_t)0x96U, (uint8_t)0x93U, (uint8_t)0xdeU, (uint8_t)0xedU, (uint8_t)0x16U,
      (uint8_t)0x73U, (uint8_t)0xedU, (uint8_t)0x42U, (uint8_t)0x95U, (uint8_t)0x39U, (uint8_t)0xc9U,
      (uint8_t)0x69U, (uint8_t)0xd3U, (uint8_t)0x72U, (uint8_t)0xc0U, (uint8_t)0x4dU, (uint8_t)0x6bU,
      (uint8_t)0x47U, (uint8_t)0xe0U, (uint8_t)0xf5U, (uint8_t)0xb8U, (uint8_t)0xceU, (uint8_t)0xe0U,
      (uint8_t)0x84U, (uint8_t)0x3eU, (uint8_t)0x5cU, (uint8_t)0x22U, (uint8_t)0x83U, (uint8_t)0x5dU,
      (uint8_t)0xbdU, (uint8_t)0x3bU, (uint8_t)0x05U, (uint8_t)0xa0U, (uint8_t)0x99U, (uint8_t)0x79U,
      (uint8_t)0x84U, (uint8_t)0xaeU, (uint8_t)0x60U, (uint8_t)0x58U, (uint8_t)0xb1U, (uint8_t)0x1bU,
      (uint8_t)0xc4U, (uint8_t)0x90U, (uint8_t)0x7cU, (uint8_t)0xbfU, (uint8_t)0x67U, (uint8_t)0xedU,
      (uint8_t)0x84U, (uint8_t)0xfaU, (uint8_t)0x9aU, (uint8_t)0xe2U, (uint8_t)0x52U, (uint8_t)0xdfU,
      (uint8_t)0xb0U, (uint8_t)0xd0U, (uint8_t)0xcdU, (uint8_t)0x49U, (uint8_t)0xe6U, (uint8_t)0x18U,
      (uint8_t)0xe3U, (uint8_t)0x5dU, (uint8_t)0xfdU, (uint8_t)0xfeU, (uint8_t)0x59U, (uint8_t)0xbcU,
      (uint8_t)0xa3U, (uint8_t)0xddU, (uint8_t)0xd6U, (uint8_t)0x6cU, (uint8_t)0x33U, (uint8_t)0xceU,
      (uint8_t)0xbbU, (uint8_t)0xc7U, (uint8_t)0x7aU, (uint8_t)0xd4U, (uint8_t)0x41U, (uint8_t)0xaaU,
      (uint8_t)0x69U, (uint8_t)0x5eU, (uint8_t)0x13U, (uint8_t)0xe3U, (uint8_t)0x24U, (uint8_t)0xb5U,
      (uint8_t)0x18U, (uint8_t)0xf0U, (uint8_t)0x1cU, (uint8_t)0x60U, (uint8_t)0xf5U, (uint8_t)0xa8U,
      (uint8_t)0x5cU, (uint8_t)0x99U, (uint8_t)0x4aU, (uint8_t)0xd1U, (uint8_t)0x79U, (uint8_t)0xf2U,
      (uint8_t)0xa6U, (uint8_t)0xb5U, (uint8_t)0xfbU, (uint8_t)0xe9U, (uint8_t)0x34U, (uint8_t)0x02U,
      (uint8_t)0xb1U, (uint8_t)0x17U, (uint8_t)0x67U, (uint8_t)0xbeU, (uint8_t)0x01U, (uint8_t)0xbfU,
      (uint8_t)0x07U, (uint8_t)0x34U, (uint8_t)0x44U, (uint8_t)0xd6U, (uint8_t)0xbaU, (uint8_t)0x1dU,
      (uint8_t)0xd2U, (uint8_t)0xbcU, (uint8_t)0xa5U, (uint8_t)0xbdU, (uint8_t)0x07U, (uint8_t)0x4dU,
      (uint8_t)0x4aU, (uint8_t)0x5fU, (uint8_t)0xaeU, (uint8_t)0x35U, (uint8_t)0x31U, (uint8_t)0xadU,
      (uint8_t)0x13U, (uint8_t)0x03U, (uint8_t)0xd8U, (uint8_t)0x4bU, (uint8_t)0x30U, (uint8_t)0xd8U,
      (uint8_t)0x97U, (uint8_t)0x31U, (uint8_t)0x8cU, (uint8_t)0xbbU, (uint8_t)0xbaU, (uint8_t)0x04U,
      (uint8_t)0xe0U, (uint8_t)0x3cU, (uint8_t)0x2eU, (uint8_t)0x66U, (uint8_t)0xdeU, (uint8_t)0x6dU,
      (uint8_t)0x91U, (uint8_t)0xf8U, (uint8_t)0x2fU, (uint8_t)0x96U, (uint8_t)0xeaU, (uint8_t)0x1dU,
      (uint8_t)0x4bU, (uint8_t)0xb5U, (uint8_t)0x4aU, (uint8_t)0x5aU, (uint8_t)0xaeU, (uint8_t)0x10U,
      (uint8_t)0x2dU, (uint8_t)0x59U, (uint8_t)0x46U, (uint8_t)0x57U, (uint8_t)0xf5U, (uint8_t)0xc9U,
      (uint8_t)0x78U, (uint8_t)0x95U, (uint8_t)0x53U, (uint8_t)0x51U, (uint8_t)0x2bU, (uint8_t)0x29U,
      (uint8_t)0x6dU, (uint8_t)0xeaU, (uint8_t)0x29U, (uint8_t)0xd8U, (uint8_t)0x02U, (uint8_t)0x31U,
      (uint8_t)0x96U, (uint8_t)0x35U, (uint8_t)0x7eU, (uint8_t)0x3eU, (uint8_t)0x3aU, (uint8_t)0x6eU,
      (uint8_t)0x95U, (uint8_t)0x8fU, (uint8_t)0x39U, (uint8_t)0xe3U, (uint8_t)0xc2U, (uint8_t)0x34U,
      (uint8_t)0x40U, (uint8_t)0x38U, (uint8_t)0xeaU, (uint8_t)0x60U, (uint8_t)0x4bU, (uint8_t)0x31U,
      (uint8_t)0xedU, (uint8_t)0xc6U, (uint8_t)0xf0U, (uint8_t)0xf7U, (uint8_t)0xffU, (uint8_t)0x6eU,
      (uint8_t)0x71U, (uint8_t)0x81U, (uint8_t)0xa5U, (uint8_t)0x7cU, (uint8_t)0x92U, (uint8_t)0x82U,
      (uint8_t)0x6aU, (uint8_t)0x26U, (uint8_t)0x8fU, (uint8_t)0x86U, (uint8_t)0x76U, (uint8_t)0x8eU,
      (uint8_t)0x96U, (uint8_t)0xf8U, (uint8_t)0x78U, (uint8_t)0x56U, (uint8_t)0x2fU, (uint8_t)0xc7U,
      (uint8_t)0x1dU, (uint8_t)0x85U, (uint8_t)0xd6U, (uint8_t)0x9eU, (uint8_t)0x44U, (uint8_t)0x86U,
      (uint8_t)0x12U, (uint8_t)0xf7U, (uint8_t)0x04U, (uint8_t)0x8fU
    };

uint8_t p[128U] =
    {
      (uint8_t)0xcfU, (uint8_t)0xd5U, (uint8_t)0x02U, (uint8_t)0x83U, (uint8_t)0xfeU, (uint8_t)0xeeU,
      (uint8_t)0xb9U, (uint8_t)0x7fU, (uint8_t)0x6fU, (uint8_t)0x08U, (uint8_t)0xd7U, (uint8_t)0x3cU,
      (uint8_t)0xbcU, (uint8_t)0x7bU, (uint8_t)0x38U, (uint8_t)0x36U, (uint8_t)0xf8U, (uint8_t)0x2bU,
      (uint8_t)0xbcU, (uint8_t)0xd4U, (uint8_t)0x99U, (uint8_t)0x47U, (uint8_t)0x9fU, (uint8_t)0x5eU,
      (uint8_t)0x6fU, (uint8_t)0x76U, (uint8_t)0xfdU, (uint8_t)0xfcU, (uint8_t)0xb8U, (uint8_t)0xb3U,
      (uint8_t)0x8cU, (uint8_t)0x4fU, (uint8_t)0x71U, (uint8_t)0xdcU, (uint8_t)0x9eU, (uint8_t)0x88U,
      (uint8_t)0xbdU, (uint8_t)0x6aU, (uint8_t)0x6fU, (uint8_t)0x76U, (uint8_t)0x37U, (uint8_t)0x1aU,
      (uint8_t)0xfdU, (uint8_t)0x65U, (uint8_t)0xd2U, (uint8_t)0xafU, (uint8_t)0x18U, (uint8_t)0x62U,
      (uint8_t)0xb3U, (uint8_t)0x2aU, (uint8_t)0xfbU, (uint8_t)0x34U, (uint8_t)0xa9U, (uint8_t)0x5fU,
      (uint8_t)0x71U, (uint8_t)0xb8U, (uint8_t)0xb1U, (uint8_t)0x32U, (uint8_t)0x04U, (uint8_t)0x3fU,
      (uint8_t)0xfeU, (uint8_t)0xbeU, (uint8_t)0x3aU, (uint8_t)0x95U, (uint8_t)0x2bU, (uint8_t)0xafU,
      (uint8_t)0x75U, (uint8_t)0x92U, (uint8_t)0x44U, (uint8_t)0x81U, (uint8_t)0x48U, (uint8_t)0xc0U,
      (uint8_t)0x3fU, (uint8_t)0x9cU, (uint8_t)0x69U, (uint8_t)0xb1U, (uint8_t)0xd6U, (uint8_t)0x8eU,
      (uint8_t)0x4cU, (uint8_t)0xe5U, (uint8_t)0xcfU, (uint8_t)0x32U, (uint8_t)0xc8U, (uint8_t)0x6bU,
      (uint8_t)0xafU, (uint8_t)0x46U, (uint8_t)0xfeU, (uint8_t)0xd3U, (uint8_t)0x01U, (uint8_t)0xcaU,
      (uint8_t)0x1aU, (uint8_t)0xb4U, (uint8_t)0x03U, (uint8_t)0x06U, (uint8_t)0x9bU, (uint8_t)0x32U,
      (uint8_t)0xf4U, (uint8_t)0x56U, (uint8_t)0xb9U, (uint8_t)0x1fU, (uint8_t)0x71U, (uint8_t)0x89U,
      (uint8_t)0x8aU, (uint8_t)0xb0U, (uint8_t)0x81U, (uint8_t)0xcdU, (uint8_t)0x8cU, (uint8_t)0x42U,
      (uint8_t)0x52U, (uint8_t)0xefU, (uint8_t)0x52U, (uint8_t)0x71U, (uint8_t)0x91U, (uint8_t)0x5cU,
      (uint8_t)0x97U, (uint8_t)0x94U, (uint8_t)0xb8U, (uint8_t)0xf2U, (uint8_t)0x95U, (uint8_t)0x85U,
      (uint8_t)0x1dU, (uint8_t)0xa7U, (uint8_t)0x51U, (uint8_t)0x0fU, (uint8_t)0x99U, (uint8_t)0xcbU,
      (uint8_t)0x73U, (uint8_t)0xebU
    };

uint8_t q[128U] =
    {
      (uint8_t)0xccU, (uint8_t)0x4eU, (uint8_t)0x90U, (uint8_t)0xd2U, (uint8_t)0xa1U, (uint8_t)0xb3U,
      (uint8_t)0xa0U, (uint8_t)0x65U, (uint8_t)0xd3U, (uint8_t)0xb2U, (uint8_t)0xd1U, (uint8_t)0xf5U,
      (uint8_t)0xa8U, (uint8_t)0xfcU, (uint8_t)0xe3U, (uint8_t)0x1bU, (uint8_t)0x54U, (uint8_t)0x44U,
      (uint8_t)0x75U, (uint8_t)0x66U, (uint8_t)0x4eU, (uint8_t)0xabU, (uint8_t)0x56U, (uint8_t)0x1dU,
      (uint8_t)0x29U, (uint8_t)0x71U, (uint8_t)0xb9U, (uint8_t)0x9fU, (uint8_t)0xb7U, (uint8_t)0xbeU,
      (uint8_t)0xf8U, (uint8_t)0x44U, (uint8_t)0xe8U, (uint8_t)0xecU, (uint8_t)0x1fU, (uint8_t)0x36U,
      (uint8_t)0x0bU, (uint8_t)0x8cU, (uint8_t)0x2aU, (uint8_t)0xc8U, (uint8_t)0x35U, (uint8_t)0x96U,
      (uint8_t)0x92U, (uint8_t)0x97U, (uint8_t)0x1eU, (uint8_t)0xa6U, (uint8_t)0xa3U, (uint8_t)0x8fU,
      (uint8_t)0x72U, (uint8_t)0x3fU, (uint8_t)0xccU, (uint8_t)0x21U, (uint8_t)0x1fU, (uint8_t)0x5dU,
      (uint8_t)0xbcU, (uint8_t)0xb1U, (uint8_t)0x77U, (uint8_t)0xa0U, (uint8_t)0xfdU, (uint8_t)0xacU,
      (uint8_t)0x51U, (uint8_t)0x64U, (uint8_t)0xa1U, (uint8_t)0xd4U, (uint8_t)0xffU, (uint8_t)0x7fU,
      (uint8_t)0xbbU, (uint8_t)0x4eU, (uint8_t)0x82U, (uint8_t)0x99U, (uint8_t)0x86U, (uint8_t)0x35U,
      (uint8_t)0x3cU, (uint8_t)0xb9U, (uint8_t)0x83U, (uint8_t)0x65U, (uint8_t)0x9aU, (uint8_t)0x14U,
      (uint8_t)0x8cU, (uint8_t)0xddU, (uint8_t)0x42U, (uint8_t)0x0cU, (uint8_t)0x7dU, (uint8_t)0x31U,
      (uint8_t)0xbaU, (uint8_t)0x38U, (uint8_t)0x22U, (uint8_t)0xeaU, (uint8_t)0x90U, (uint8_t)0xa3U,
      (uint8_t)0x2bU, (uint8_t)0xe4U, (uint8_t)0x6cU, (uint8_t)0x03U, (uint8_t)0x0eU, (uint8_t)0x8cU,
      (uint8_t)0x17U, (uint8_t)0xe1U, (uint8_t)0xfaU, (uint8_t)0x0aU, (uint8_t)0xd3U, (uint8_t)0x78U,
      (uint8_t)0x59U, (uint8_t)0xe0U, (uint8_t)0x6bU, (uint8_t)0x0aU, (uint8_t)0xa6U, (uint8_t)0xfaU,
      (uint8_t)0x3bU, (uint8_t)0x21U, (uint8_t)0x6dU, (uint8_t)0x9cU, (uint8_t)0xbeU, (uint8_t)0x6cU,
      (uint8_t)0x0eU, (uint8_t)0x22U, (uint8_t)0x33U, (uint8_t)0x97U, (uint8_t)0x69U, (uint8_t)0xc0U,
      (uint8_t)0xa6U, (uint8_t)0x15U, (uint8_t)0x91U, (uint8_t)0x3eU, (uint8_t)0x5dU, (uint8_t)0xa7U,
      (uint8_t)0x19U, (uint8_t)0xcfU
    };

uint32_t skeyBits = (uint32_t)2048U;
//uint32_t pkeyBits = (uint32_t)24U;
uint32_t pkeyBits = (uint32_t)17U;
uint32_t modBits = (uint32_t)2048U;
uint32_t pTLen = (uint32_t)128U;
uint32_t qTLen = (uint32_t)128U;

uint32_t pow2_i = 32U;
uint64_t rBlind = 8906967415916878848U;

bool
test_rsapss()
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen = (skeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pLen = (pTLen - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t qLen = (qTLen - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t nTLen = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  
  uint32_t pkeyLen = nLen + eLen;
  uint32_t skeyLen = pkeyLen + dLen + pLen + qLen;
  uint64_t skey[skeyLen];
  memset(skey, 0U, skeyLen * sizeof skey[0U]);
  uint64_t *nNat = skey;
  uint64_t *eNat = skey + nLen;
  uint64_t *dNat = skey + nLen + eLen;
  uint64_t *pNat = skey + pkeyLen + dLen;
  uint64_t *qNat = skey + pkeyLen + dLen + pLen;
  Hacl_Impl_Convert_text_to_nat((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Impl_Convert_text_to_nat((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);
  Hacl_Impl_Convert_text_to_nat((skeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, d, dNat);
  Hacl_Impl_Convert_text_to_nat(pTLen, p, pNat);
  Hacl_Impl_Convert_text_to_nat(qTLen, q, qNat);

  uint64_t *pkey = skey;
  uint8_t sgnt[nTLen];
  memset(sgnt, 0U, nTLen * sizeof sgnt[0U]);

  uint32_t msgLen = (uint32_t)128U;
  uint8_t
  msg[128U] =
    {
      (uint8_t)0xddU, (uint8_t)0x67U, (uint8_t)0x0aU, (uint8_t)0x01U, (uint8_t)0x46U, (uint8_t)0x58U,
      (uint8_t)0x68U, (uint8_t)0xadU, (uint8_t)0xc9U, (uint8_t)0x3fU, (uint8_t)0x26U, (uint8_t)0x13U,
      (uint8_t)0x19U, (uint8_t)0x57U, (uint8_t)0xa5U, (uint8_t)0x0cU, (uint8_t)0x52U, (uint8_t)0xfbU,
      (uint8_t)0x77U, (uint8_t)0x7cU, (uint8_t)0xdbU, (uint8_t)0xaaU, (uint8_t)0x30U, (uint8_t)0x89U,
      (uint8_t)0x2cU, (uint8_t)0x9eU, (uint8_t)0x12U, (uint8_t)0x36U, (uint8_t)0x11U, (uint8_t)0x64U,
      (uint8_t)0xecU, (uint8_t)0x13U, (uint8_t)0x97U, (uint8_t)0x9dU, (uint8_t)0x43U, (uint8_t)0x04U,
      (uint8_t)0x81U, (uint8_t)0x18U, (uint8_t)0xe4U, (uint8_t)0x44U, (uint8_t)0x5dU, (uint8_t)0xb8U,
      (uint8_t)0x7bU, (uint8_t)0xeeU, (uint8_t)0x58U, (uint8_t)0xddU, (uint8_t)0x98U, (uint8_t)0x7bU,
      (uint8_t)0x34U, (uint8_t)0x25U, (uint8_t)0xd0U, (uint8_t)0x20U, (uint8_t)0x71U, (uint8_t)0xd8U,
      (uint8_t)0xdbU, (uint8_t)0xaeU, (uint8_t)0x80U, (uint8_t)0x70U, (uint8_t)0x8bU, (uint8_t)0x03U,
      (uint8_t)0x9dU, (uint8_t)0xbbU, (uint8_t)0x64U, (uint8_t)0xdbU, (uint8_t)0xd1U, (uint8_t)0xdeU,
      (uint8_t)0x56U, (uint8_t)0x57U, (uint8_t)0xd9U, (uint8_t)0xfeU, (uint8_t)0xd0U, (uint8_t)0xc1U,
      (uint8_t)0x18U, (uint8_t)0xa5U, (uint8_t)0x41U, (uint8_t)0x43U, (uint8_t)0x74U, (uint8_t)0x2eU,
      (uint8_t)0x0fU, (uint8_t)0xf3U, (uint8_t)0xc8U, (uint8_t)0x7fU, (uint8_t)0x74U, (uint8_t)0xe4U,
      (uint8_t)0x58U, (uint8_t)0x57U, (uint8_t)0x64U, (uint8_t)0x7aU, (uint8_t)0xf3U, (uint8_t)0xf7U,
      (uint8_t)0x9eU, (uint8_t)0xb0U, (uint8_t)0xa1U, (uint8_t)0x4cU, (uint8_t)0x9dU, (uint8_t)0x75U,
      (uint8_t)0xeaU, (uint8_t)0x9aU, (uint8_t)0x1aU, (uint8_t)0x04U, (uint8_t)0xb7U, (uint8_t)0xcfU,
      (uint8_t)0x47U, (uint8_t)0x8aU, (uint8_t)0x89U, (uint8_t)0x7aU, (uint8_t)0x70U, (uint8_t)0x8fU,
      (uint8_t)0xd9U, (uint8_t)0x88U, (uint8_t)0xf4U, (uint8_t)0x8eU, (uint8_t)0x80U, (uint8_t)0x1eU,
      (uint8_t)0xdbU, (uint8_t)0x0bU, (uint8_t)0x70U, (uint8_t)0x39U, (uint8_t)0xdfU, (uint8_t)0x8cU,
      (uint8_t)0x23U, (uint8_t)0xbbU, (uint8_t)0x3cU, (uint8_t)0x56U, (uint8_t)0xf4U, (uint8_t)0xe8U,
      (uint8_t)0x21U, (uint8_t)0xacU
    };
  uint32_t saltLen = (uint32_t)20U;
  uint8_t
  salt[20U] =
    {
      (uint8_t)0x8bU, (uint8_t)0x2bU, (uint8_t)0xddU, (uint8_t)0x4bU, (uint8_t)0x40U, (uint8_t)0xfaU,
      (uint8_t)0xf5U, (uint8_t)0x45U, (uint8_t)0xc7U, (uint8_t)0x78U, (uint8_t)0xddU, (uint8_t)0xf9U,
      (uint8_t)0xbcU, (uint8_t)0x1aU, (uint8_t)0x49U, (uint8_t)0xcbU, (uint8_t)0x57U, (uint8_t)0xf9U,
      (uint8_t)0xb7U, (uint8_t)0x1bU
    };
  uint8_t
  sgnt_expected[256U] =
    {
      (uint8_t)0xa4U, (uint8_t)0x4eU, (uint8_t)0x5cU, (uint8_t)0x83U, (uint8_t)0xc6U, (uint8_t)0xfeU,
      (uint8_t)0xdfU, (uint8_t)0x7fU, (uint8_t)0x44U, (uint8_t)0x33U, (uint8_t)0x78U, (uint8_t)0x82U,
      (uint8_t)0x54U, (uint8_t)0x2aU, (uint8_t)0x96U, (uint8_t)0x10U, (uint8_t)0x72U, (uint8_t)0x4aU,
      (uint8_t)0xa6U, (uint8_t)0xf5U, (uint8_t)0xb8U, (uint8_t)0xf1U, (uint8_t)0x3bU, (uint8_t)0x4fU,
      (uint8_t)0x51U, (uint8_t)0xebU, (uint8_t)0x9eU, (uint8_t)0xf9U, (uint8_t)0x84U, (uint8_t)0xf5U,
      (uint8_t)0x19U, (uint8_t)0xaaU, (uint8_t)0xe9U, (uint8_t)0xe3U, (uint8_t)0x4bU, (uint8_t)0x26U,
      (uint8_t)0x4eU, (uint8_t)0x8dU, (uint8_t)0x06U, (uint8_t)0xb6U, (uint8_t)0x93U, (uint8_t)0x66U,
      (uint8_t)0x4dU, (uint8_t)0xe1U, (uint8_t)0xccU, (uint8_t)0xe1U, (uint8_t)0x36U, (uint8_t)0xd0U,
      (uint8_t)0x6dU, (uint8_t)0x10U, (uint8_t)0x7fU, (uint8_t)0x64U, (uint8_t)0x51U, (uint8_t)0x99U,
      (uint8_t)0x8aU, (uint8_t)0xf9U, (uint8_t)0x01U, (uint8_t)0x21U, (uint8_t)0x3fU, (uint8_t)0xc8U,
      (uint8_t)0x95U, (uint8_t)0x83U, (uint8_t)0xe6U, (uint8_t)0xbeU, (uint8_t)0xfeU, (uint8_t)0x1eU,
      (uint8_t)0xd1U, (uint8_t)0x12U, (uint8_t)0x35U, (uint8_t)0xf5U, (uint8_t)0xb5U, (uint8_t)0xceU,
      (uint8_t)0x8bU, (uint8_t)0xd4U, (uint8_t)0x72U, (uint8_t)0xb3U, (uint8_t)0x84U, (uint8_t)0xefU,
      (uint8_t)0xf0U, (uint8_t)0xcdU, (uint8_t)0x80U, (uint8_t)0xd3U, (uint8_t)0x75U, (uint8_t)0xbdU,
      (uint8_t)0x6aU, (uint8_t)0x88U, (uint8_t)0xaeU, (uint8_t)0x6fU, (uint8_t)0x5bU, (uint8_t)0x76U,
      (uint8_t)0x75U, (uint8_t)0xc2U, (uint8_t)0x50U, (uint8_t)0x8bU, (uint8_t)0xa9U, (uint8_t)0xb9U,
      (uint8_t)0xf0U, (uint8_t)0x17U, (uint8_t)0x1eU, (uint8_t)0x10U, (uint8_t)0xc9U, (uint8_t)0x58U,
      (uint8_t)0xd4U, (uint8_t)0xc0U, (uint8_t)0x4cU, (uint8_t)0x10U, (uint8_t)0x0eU, (uint8_t)0xf9U,
      (uint8_t)0x06U, (uint8_t)0xccU, (uint8_t)0x97U, (uint8_t)0x58U, (uint8_t)0x0dU, (uint8_t)0xe7U,
      (uint8_t)0x73U, (uint8_t)0xadU, (uint8_t)0x9dU, (uint8_t)0xf4U, (uint8_t)0xdaU, (uint8_t)0x13U,
      (uint8_t)0xd5U, (uint8_t)0x95U, (uint8_t)0xbeU, (uint8_t)0xe2U, (uint8_t)0x4aU, (uint8_t)0xf8U,
      (uint8_t)0x12U, (uint8_t)0x88U, (uint8_t)0x4eU, (uint8_t)0xd4U, (uint8_t)0xdcU, (uint8_t)0xe8U,
      (uint8_t)0x09U, (uint8_t)0x51U, (uint8_t)0xecU, (uint8_t)0xd0U, (uint8_t)0x4bU, (uint8_t)0x1bU,
      (uint8_t)0xa6U, (uint8_t)0xd7U, (uint8_t)0x8cU, (uint8_t)0x29U, (uint8_t)0x34U, (uint8_t)0xe6U,
      (uint8_t)0xabU, (uint8_t)0x0aU, (uint8_t)0x77U, (uint8_t)0x36U, (uint8_t)0x83U, (uint8_t)0x91U,
      (uint8_t)0x1fU, (uint8_t)0xccU, (uint8_t)0x68U, (uint8_t)0x91U, (uint8_t)0x35U, (uint8_t)0x37U,
      (uint8_t)0x67U, (uint8_t)0x27U, (uint8_t)0x78U, (uint8_t)0x09U, (uint8_t)0xecU, (uint8_t)0x74U,
      (uint8_t)0x6fU, (uint8_t)0x95U, (uint8_t)0x98U, (uint8_t)0xe4U, (uint8_t)0xf8U, (uint8_t)0xf0U,
      (uint8_t)0xcbU, (uint8_t)0x1dU, (uint8_t)0x3dU, (uint8_t)0x37U, (uint8_t)0x84U, (uint8_t)0x3fU,
      (uint8_t)0xeaU, (uint8_t)0x2aU, (uint8_t)0x8cU, (uint8_t)0xb0U, (uint8_t)0x91U, (uint8_t)0xf2U,
      (uint8_t)0x91U, (uint8_t)0x91U, (uint8_t)0x22U, (uint8_t)0x76U, (uint8_t)0x9eU, (uint8_t)0xe4U,
      (uint8_t)0x17U, (uint8_t)0xdaU, (uint8_t)0x18U, (uint8_t)0xd6U, (uint8_t)0x03U, (uint8_t)0xf7U,
      (uint8_t)0x98U, (uint8_t)0x37U, (uint8_t)0x0cU, (uint8_t)0xadU, (uint8_t)0x7bU, (uint8_t)0x76U,
      (uint8_t)0x0aU, (uint8_t)0x7fU, (uint8_t)0x57U, (uint8_t)0x3aU, (uint8_t)0xeaU, (uint8_t)0xf5U,
      (uint8_t)0x16U, (uint8_t)0xa0U, (uint8_t)0xf9U, (uint8_t)0x0dU, (uint8_t)0x95U, (uint8_t)0x25U,
      (uint8_t)0x65U, (uint8_t)0xb8U, (uint8_t)0xa1U, (uint8_t)0x9aU, (uint8_t)0x8fU, (uint8_t)0xc3U,
      (uint8_t)0xf0U, (uint8_t)0xeeU, (uint8_t)0x7dU, (uint8_t)0x39U, (uint8_t)0x1dU, (uint8_t)0x9bU,
      (uint8_t)0x8bU, (uint8_t)0x3fU, (uint8_t)0x98U, (uint8_t)0xbeU, (uint8_t)0xbbU, (uint8_t)0x0dU,
      (uint8_t)0x5dU, (uint8_t)0x01U, (uint8_t)0x0eU, (uint8_t)0x32U, (uint8_t)0xe0U, (uint8_t)0xb8U,
      (uint8_t)0x00U, (uint8_t)0xe9U, (uint8_t)0x65U, (uint8_t)0x6fU, (uint8_t)0x64U, (uint8_t)0x08U,
      (uint8_t)0x2bU, (uint8_t)0xb1U, (uint8_t)0xacU, (uint8_t)0x95U, (uint8_t)0xa2U, (uint8_t)0x23U,
      (uint8_t)0xf4U, (uint8_t)0x31U, (uint8_t)0xecU, (uint8_t)0x40U, (uint8_t)0x6aU, (uint8_t)0x42U,
      (uint8_t)0x95U, (uint8_t)0x4bU, (uint8_t)0x2dU, (uint8_t)0x57U
    };

  Hacl_RSAPSS_rsa_pss_sign(pow2_i, modBits, pkeyBits, skeyBits, pLen, qLen, skey, rBlind, saltLen, salt, msgLen, msg, sgnt);

  bool check_sgnt = Hacl_Impl_Lib_eq_b(nTLen, sgnt, sgnt_expected);
  bool verify_sgnt = Hacl_RSAPSS_rsa_pss_verify(pow2_i, modBits, pkeyBits, pkey, saltLen, sgnt, msgLen, msg);
  bool res = check_sgnt && verify_sgnt;
  printf("\n Unit-test: %d \n", res);
  return res;
}

bool
hacl_sign(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t skeyBits,
  uint8_t *d,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *salt,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen = (skeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pLen = (pTLen - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t qLen = (qTLen - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;

  uint32_t pkeyLen = nLen + eLen;
  uint32_t skeyLen = pkeyLen + dLen + pLen + qLen;
  uint64_t skey[skeyLen];
  memset(skey, 0U, skeyLen * sizeof skey[0U]);
  uint64_t *nNat = skey;
  uint64_t *eNat = skey + nLen;
  uint64_t *dNat = skey + nLen + eLen;
  uint64_t *pNat = skey + pkeyLen + dLen;
  uint64_t *qNat = skey + pkeyLen + dLen + pLen;
  Hacl_Impl_Convert_text_to_nat((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Impl_Convert_text_to_nat((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);
  Hacl_Impl_Convert_text_to_nat((skeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, d, dNat);
  Hacl_Impl_Convert_text_to_nat(pTLen, p, pNat);
  Hacl_Impl_Convert_text_to_nat(qTLen, q, qNat);

  Hacl_RSAPSS_rsa_pss_sign(pow2_i, modBits, pkeyBits, skeyBits, pLen, qLen, skey, rBlind, saltLen, salt, msgLen, msg, sgnt);
  return 1;
}

bool
hacl_verify(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *salt,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + eLen;
  uint64_t pkey[pkeyLen];
  memset(pkey, 0U, pkeyLen * sizeof pkey[0U]);
  uint64_t *nNat = pkey;
  uint64_t *eNat = pkey + nLen;
  Hacl_Impl_Convert_text_to_nat((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Impl_Convert_text_to_nat((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);

  bool verify_sgnt = Hacl_RSAPSS_rsa_pss_verify (pow2_i, modBits, pkeyBits, pkey, saltLen, sgnt, msgLen, msg);
  return verify_sgnt;
}

int openssl_sign(uint8_t* msg, uint32_t msg_len, uint8_t* kN, const uint32_t kN_len, uint8_t* kE, uint32_t kE_len, uint8_t* kD, uint32_t kD_len, uint8_t* pSignature){
    int status = 0;
    unsigned char pDigest[32];
    unsigned char EM[kN_len];

    RSA* pRsaKey = RSA_new();
    BIGNUM *n = BN_new();
    BIGNUM *e = BN_new();
    BIGNUM *d = BN_new();

    BN_bin2bn(kN, kN_len, n);
    BN_bin2bn(kE, kE_len, e);
    BN_bin2bn(kD, kD_len, d);

    RSA_set0_key(pRsaKey, n, e, d);

    /* hash the message */
    SHA256(msg, msg_len, pDigest);

    /* compute the PSS padded data */
    status = RSA_padding_add_PKCS1_PSS(pRsaKey, EM, pDigest, EVP_sha256(), 0 /* maximum salt length*/);

    /* perform digital signature */
    status = RSA_private_encrypt(kN_len, EM, pSignature, pRsaKey, RSA_NO_PADDING);
    return status;
}

int openssl_verify(uint8_t* msg, uint32_t msg_len, uint8_t* kN, const uint32_t kN_len, uint8_t* kE, uint32_t kE_len, uint8_t* pSignature){
    int status = 0;
    unsigned char pDigest[32];
    unsigned char EM[kN_len];
    unsigned char pDecrypted[kN_len];

    RSA* pRsaKey = RSA_new();
    BIGNUM *n = BN_new();
    BIGNUM *e = BN_new();

    BN_bin2bn(kN, kN_len, n);
    BN_bin2bn(kE, kE_len, e);

    RSA_set0_key(pRsaKey, n, e, NULL);

    /* hash the message */
    SHA256(msg, msg_len, pDigest);

    status = RSA_public_decrypt(kN_len, pSignature, pDecrypted, pRsaKey, RSA_NO_PADDING);
    /* verify the data */
    status = RSA_verify_PKCS1_PSS(pRsaKey, pDigest, EVP_sha256(), pDecrypted, -2 /* salt length recovered from signature*/);
    return status;
}

int perf_rsapss() {
  // Message
  const size_t msg_len = 256;
  uint8_t msg[msg_len];
  randombytes(msg,msg_len);

  // Sgnt
  uint8_t sgnt[256U];
  memset(sgnt, 0U, 256U * sizeof sgnt[0U]);

  uint8_t res = 1;
  printf("\n SIGNATURE: \n");
  TestLib_cycles t0,t1,t2,t3;
  t0 = TestLib_cpucycles_begin();
  for (int i = 0; i < 1000; i++){
    hacl_sign(modBits, n1, pkeyBits, e, skeyBits, d, msg_len, msg, 0, NULL, sgnt);
    res = res ^ sgnt[0];
    }
  t1 = TestLib_cpucycles_end();
  printf("\n sh: %d \n", res);

  TestLib_print_cycles_per_round(t0, t1, 1000);

  uint8_t sgnt1[256U];
  memset(sgnt1, 0U, 256U * sizeof sgnt1[0U]);

  t2 = TestLib_cpucycles_begin();
  for (int i = 0; i < 1000; i++){
    openssl_sign(msg, msg_len, n1, 256U, e, 3U, d, 256U, sgnt1);
    res = res ^ sgnt1[0];
   }
  t3 = TestLib_cpucycles_end();
  printf("\n so: %d \n", res);

  TestLib_print_cycles_per_round(t2, t3, 1000);

  double ratio1 = (double) (t1 - t0) / (t3 - t2);
  printf("\n Ratio =  %lf\n", ratio1);

  printf("\nSignature HACL: \n");
  for (int i = 0; i < 256U; i++) {
    printf("%02X", sgnt[i]);
  }
  printf(" \n");

  printf("\nSignature OpenSSL: \n");
  for (int i = 0; i < 256U; i++) {
    printf("%02X", sgnt1[i]);
  }
  printf(" \n");

  //bool check_sgnt = Hacl_Impl_Lib_eq_b(256, sgnt, sgnt1);
  //printf("hacl* sgnt == openssl sgnt %d", check_sgnt);
  
  printf("\n VERIFICATION: \n");

  t0 = TestLib_cpucycles_begin();
  for (int i = 0; i < 10000; i++){
    int r = hacl_verify(modBits, n1, pkeyBits, e, msg_len, msg, 0, NULL, sgnt);
    res = res ^ r;
  }
  t1 = TestLib_cpucycles_end();
  printf("\n vh: %d \n", res);

  TestLib_print_cycles_per_round(t0, t1, 10000);

  t2 = TestLib_cpucycles_begin();
  for (int i = 0; i < 10000; i++){
    int r = openssl_verify(msg, msg_len, n1, 256U, e, 3U, sgnt1);
    res = res ^ r;
  }
  t3 = TestLib_cpucycles_end();
  printf("\n vo: %d \n", res);

  TestLib_print_cycles_per_round(t2, t3, 10000);

  double ratio2 = (double) (t1 - t0) / (t3 - t2);
  printf("\n Ratio =  %lf \n", ratio2);

  return 1;
}

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    int32_t res = test_rsapss();
    if (res) {
      res = perf_rsapss();
    }
    return res;
    } else if (argc == 2 && strcmp(argv[1], "unit-test") == 0 ) {
    return test_rsapss();
  } else {
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return 0;
  }
}
