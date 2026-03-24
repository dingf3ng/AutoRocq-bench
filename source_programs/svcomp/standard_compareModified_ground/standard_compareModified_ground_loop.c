#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_compareModified_ground.c",3,"0");
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
  int c[100000];
  int x;
  int i = 0;
  int rv = 1;
  {
    int j = 0;
    /*@
      loop invariant 0 <= j <= 100000;
      loop assigns j, a[0 .. 99999], b[0 .. 99999];
      loop variant 100000 - j;
    */
    while (j < 100000) {
      a[j] = __VERIFIER_nondet_int();
      b[j] = __VERIFIER_nondet_int();
      /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
      j ++;
    }
  }
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> c[k] == a[k];
    loop invariant rv == 0 || (\forall integer k; 0 <= k < i ==> a[k] == b[k]);
    loop assigns i, rv, c[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i] != b[i]) rv = 0;
    c[i] = a[i];
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  if (rv) {
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
  x = 0;
  /*@
    loop invariant 0 <= x <= 100000;
    loop invariant \forall integer k; 0 <= k < x ==> a[k] == c[k];
    loop assigns x;
    loop variant 100000 - x;
  */
  while (x < 100000) {
    /*@ assert reachability: a[x] == c[x]; */
    __VERIFIER_assert(a[x] == c[x]);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}