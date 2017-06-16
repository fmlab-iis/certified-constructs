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

fe25519 one = { 0x0000000000000001, 0x0000000000000000,
                0x0000000000000000, 0x0000000000000000,
                0x0000000000000000 };

fe25519 two = { 0x0000000000000002, 0x0000000000000000,
                0x0000000000000000, 0x0000000000000000,
                0x0000000000000000 };

int main ()
{
  fe25519 r;

  printf ("%lx %lx %lx %lx %lx\n", a.v[0], a.v[1], a.v[2], a.v[3], a.v[4]);
  x25519_x86_64_mul (&r, &two, &a);
  printf ("%lx %lx %lx %lx %lx\n", r.v[0], r.v[1], r.v[2], r.v[3], r.v[4]);
  x25519_x86_64_mul (&r, &a, &a);
  printf ("%lx %lx %lx %lx %lx\n", r.v[0], r.v[1], r.v[2], r.v[3], r.v[4]);
  x25519_x86_64_square (&r, &a);
  printf ("%lx %lx %lx %lx %lx\n", r.v[0], r.v[1], r.v[2], r.v[3], r.v[4]);
  return 0;
}
