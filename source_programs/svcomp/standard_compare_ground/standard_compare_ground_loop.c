#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_compare_ground.c",3,"0");
  return;
}

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
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int a[100000];
  int b[100000];
  {
    int j = 0;
    /*@
      loop invariant 0 <= j <= 100000;
      loop assigns j, a[0..99999], b[0..99999];
      loop variant 100000 - j;
    */
    while (j < 100000) {
      a[j] = __VERIFIER_nondet_int();
      b[j] = __VERIFIER_nondet_int();
      /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
      j ++;
    }
  }
  int i = 0;
  int rv = 1;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= rv <= 1;
    loop invariant rv == 1 ==> \forall integer k; 0 <= k < i ==> a[k] == b[k];
    loop assigns i, rv;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i] != b[i]) rv = 0;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  if (rv) {
    int x;
    x = 0;
    /*@
      loop invariant 0 <= x <= 100000;
      loop invariant \forall integer k; 0 <= k < x ==> a[k] == b[k];
      loop assigns x;
      loop variant 100000 - x;
    */
    while (x < 100000) {
      /*@ assert reachability: a[x] == b[x]; */
      __VERIFIER_assert(a[x] == b[x]);
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    }
  }
  __retres = 0;
  return __retres;
}