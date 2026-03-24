#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"sanfoundry_27_ground.c",3,"0");
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
  int array[100000];
  int i;
  int x;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i, array[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    array[i] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  int largest = array[0];
  i = 1;
  /*@
    loop invariant 1 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> largest >= array[k];
    loop assigns i, largest;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (largest < array[i]) largest = array[i];
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= 100000;
    loop invariant \forall integer k; 0 <= k < x ==> largest >= array[k];
    loop assigns x;
    loop variant 100000 - x;
  */
  while (x < 100000) {
    /*@ assert reachability: largest >= array[x]; */
    __VERIFIER_assert(largest >= array[x]);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}