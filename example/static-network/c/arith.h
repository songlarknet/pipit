/** Basic arithmetic helpers */
#pragma once

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

uint32_t sat_add_u32(uint32_t a, uint32_t b) {
  uint32_t r = a + b;
  if (r < a)
    return UINT32_MAX;
  else
    return r;
}

uint32_t sat_inc_u32(uint32_t a) {
  return sat_add_u32(a, 1);
}

#define BIT(n) (1 << ((n)-1))
