#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_palindrome_ground.c",3,"0");
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
  int A[100000];
  int i;
  int x;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i, A[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    A[i] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 50000;
    loop invariant \forall integer k; 0 <= k < i ==> A[k] == A[(100000 - k) - 1];
    loop assigns i, A[0 .. 49999];
    loop variant 50000 - i;
  */
  while (i < 100000 / 2) {
    /*@ assert rte: signed_overflow: 100000 - i <= 2147483647; */
    /*@ assert rte: signed_overflow: -2147483648 <= (int)(100000 - i) - 1; */
    A[i] = A[(100000 - i) - 1];
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= 50000;
    loop invariant \forall integer k; 0 <= k < x ==> A[k] == A[(100000 - k) - 1];
    loop assigns x;
    loop variant 50000 - x;
  */
  while (x < 100000 / 2) {
    /*@ assert rte: signed_overflow: 100000 - x <= 2147483647; */
    /*@ assert rte: signed_overflow: -2147483648 <= (int)(100000 - x) - 1; */
    /*@ assert reachability: A[x] == A[(100000 - x) - 1]; */
    __VERIFIER_assert(A[x] == A[(100000 - x) - 1]);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}