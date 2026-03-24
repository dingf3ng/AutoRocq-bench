#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_strcpy_ground-1.c",3,"0");
  return;
}

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false; */
void __VERIFIER_assert(int cond)
{
  if (! cond) {
    ERROR: {
             reach_error();
             abort();
           }
  }
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int src[100000];
  int dst[100000];
  int x;
  int i = 0;
  int j = 0;

  /*@
    loop invariant 0 <= j <= 100000;
    loop assigns j, src[0 .. 99999];
    loop variant 100000 - j;
  */
  while (j < 100000) {
    src[j] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
    j ++;
  }

  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k];
    loop assigns i, dst[0 .. 99999];
    loop variant 100000 - i;
  */
  while (1) {
    if (i < 100000) {
      /*@ assert reachability: i < 100000 ==> (src[i] != 0 || !(src[i] != 0)); */
      if (! (src[i] != 0)) break;
    }
    else break;
    dst[i] = src[i];
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  x = 0;
  /*@
    loop invariant 0 <= x <= i;
    loop invariant \forall integer k; 0 <= k < x ==> dst[k] == src[k];
    loop assigns x;
    loop variant i - x;
  */
  while (x < i) {
    /*@ assert reachability: dst[x] == src[x]; */
    __VERIFIER_assert(dst[x] == src[x]);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}