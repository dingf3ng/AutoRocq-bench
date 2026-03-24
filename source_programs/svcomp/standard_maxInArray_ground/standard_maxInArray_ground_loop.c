#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_maxInArray_ground.c",3,"0");
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
  int x;
  int max = 0;
  {
    int j = 0;
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
  }
  int i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= max <= \max(0, i == 0 ? 0 : \max(0, a[0]));
    loop invariant \forall integer k; 0 <= k < i ==> a[k] <= max;
    loop assigns i, max;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i] > max) max = a[i];
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= 100000;
    loop invariant \forall integer k; 0 <= k < x ==> a[k] <= max;
    loop assigns x;
    loop variant 100000 - x;
  */
  while (x < 100000) {
    /*@ assert reachability: a[x] <= max; */
    __VERIFIER_assert(a[x] <= max);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}