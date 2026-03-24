#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_find_ground-1.c",3,"0");
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
  int a[100000];
  int j;
  int x;
  int e = __VERIFIER_nondet_int();
  int i = 0;
  j = 0;

  /*@
    loop invariant 0 <= j <= 100000;
    loop assigns j, a[0 .. 99999];
    loop variant 100000 - j;
  */
  while (j < 100000) {
    a[j] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
    j ++;
  }

  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] != e;
    loop assigns i;
    loop variant 100000 - i;
  */
  while (1) {
    if (i < 100000) {
      /*@ assert reachability: i < 100000 ==> (a[i] != e || !(a[i] != e)); */
      if (! (a[i] != e)) break;
    }
    else break;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  x = 0;

  /*@
    loop invariant 0 <= x <= i;
    loop invariant \forall integer k; 0 <= k < x ==> a[k] != e;
    loop assigns x;
    loop variant i - x;
  */
  while (x < i) {
    /*@ assert reachability: a[x] != e; */
    __VERIFIER_assert(a[x] != e);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}