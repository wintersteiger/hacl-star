#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h> // memcmp
#include "dut.h"
#include "random.h"
#include "uint128.h"

const size_t chunk_size = 32;
const size_t number_measurements = 1e5; // per test

uint8_t do_one_computation(uint8_t *data) {
  uint64_t* d = (uint64_t*) data;
  uint128_t d0 = {d[0],d[1]};
  uint128_t d1 = {d[2],d[3]};
  uint128_t u = add128(d0,d1);
  uint8_t ret = (uint8_t) (u.lo + u.hi);
  return ret;
}

void init_dut(void) {}

void prepare_inputs(uint8_t *input_data, uint8_t *classes) {
  randombytes(input_data, number_measurements * chunk_size);
  for (size_t i = 0; i < number_measurements; i++) {
    classes[i] = randombit();
    if (classes[i] == 0) {
      memset(input_data + (size_t)i * chunk_size, 0x00, chunk_size);
    } else {
      // leave random
    }
  }
}
