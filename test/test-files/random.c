#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <time.h>
#include <string.h>
#include "Random.h"

void random_bytes(uint8_t *rand, uint32_t n) {
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, rand, n);
  return;
}
