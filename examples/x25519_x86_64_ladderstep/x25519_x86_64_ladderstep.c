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

fe25519 one = { 1, 0, 0, 0, 0 };
fe25519 two = { 2, 0, 0, 0, 0 };

int main ()
{
  fe25519 work[5];

  work[0] = a;
  work[1] = one;
  work[2] = two;
  work[3] = a;
  work[4] = one;
  x25519_x86_64_ladderstep(work);

  printf ("%lx %lx %lx %lx %lx\n",
          work[1].v[0], work[1].v[1], work[1].v[2],
          work[1].v[3], work[1].v[4]);
  printf ("%lx %lx %lx %lx %lx\n",
          work[2].v[0], work[2].v[1], work[2].v[2],
          work[2].v[3], work[2].v[4]);
  return 0;
}
