#include <stdio.h>

typedef unsigned long uint64_t;
typedef struct { uint64_t v[5]; } fe25519;

void x25519_x86_64_work_cswap(fe25519 *, uint64_t);
void x25519_x86_64_mul(fe25519 *out, const fe25519 *a, const fe25519 *b);
void x25519_x86_64_square(fe25519 *out, const fe25519 *a);
void x25519_x86_64_freeze(fe25519 *);
void x25519_x86_64_ladderstep(fe25519 *work);

fe25519 a = { 0x0007ffffffffffec, 0x0007ffffffffffff,
              0x0007ffffffffffff, 0x0007ffffffffffff,
              0x0007ffffffffffff };

fe25519 b = { 0x0007ffffffffffec, 0x0007ffffffffffff,
              0x0007ffffffffffff, 0x0007ffffffffffff,
              0x0007ffffffffffff };

int main ()
{
  fe25519 r;

  x25519_x86_64_square (&r, &a);
  return 0;
}
