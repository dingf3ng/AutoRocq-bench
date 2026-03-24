#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"array_3-1.c",3,"0");
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
  int A[1024];
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= 1024;
    loop assigns i, A[0..1023];
    loop variant 1024 - i;
  */
  while (i < 1024) {
    A[i] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 1024;
    loop invariant \forall integer k; 0 <= k < i ==> A[k] != 0;
    loop assigns i;
    loop variant 1024 - i;
  */
  while (A[i] != 0) {
    if (i >= 1024 - 1) break;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  /*@ assert reachability: i <= 1024; */
  __VERIFIER_assert(i <= 1024);
  __retres = 0;
  return __retres;
}