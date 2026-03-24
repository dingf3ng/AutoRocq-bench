#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"array_2-2.c",3,"0");
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
  int A[2048];
  int B[2048];
  int i;
  int tmp;
  i = 0;
  /*@
    loop invariant 0 <= i <= 2048;
    loop assigns i, A[0..2047], B[0..2047];
    loop variant 2048 - i;
  */
  while (i < 2048) {
    A[i] = __VERIFIER_nondet_int();
    B[i] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 2048;
    loop invariant \forall integer k; 0 <= k < i ==> B[k] == A[k];
    loop assigns i, B[0..2047];
    loop variant 2048 - i;
  */
  while (i < 2048) {
    tmp = A[i];
    B[i] = tmp;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  /*@ assert reachability: A[2048 / 2] == B[2048 / 2]; */
  __VERIFIER_assert(A[2048 / 2] == B[2048 / 2]);
  __retres = 0;
  return __retres;
}