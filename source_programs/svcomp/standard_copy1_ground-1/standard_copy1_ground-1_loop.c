#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_copy1_ground-1.c",3,"0");
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
  int a1[100000];
  int a2[100000];
  int a;
  int i;
  int x;
  a = 0;
  /*@
    loop invariant 0 <= a <= 100000;
    loop assigns a, a1[0 .. 99999];
    loop variant 100000 - a;
  */
  while (a < 100000) {
    a1[a] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: a + 1 <= 2147483647; */
    a ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a2[k] == a1[k];
    loop assigns i, a2[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a2[i] = a1[i];
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= 100000;
    loop invariant \forall integer k; 0 <= k < x ==> a1[k] == a2[k];
    loop assigns x;
    loop variant 100000 - x;
  */
  while (x < 100000) {
    /*@ assert reachability: a1[x] == a2[x]; */
    __VERIFIER_assert(a1[x] == a2[x]);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}