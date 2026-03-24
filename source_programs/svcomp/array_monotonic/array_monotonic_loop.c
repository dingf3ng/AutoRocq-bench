#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"array_monotonic.c",3,"0");
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
int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  int a[100000];
  int b[100000];
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i, a[0 .. 99999], b[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = __VERIFIER_nondet_int();
    if (a[i] == 10) b[i] = 20;
    /*@ assert rte: signed_overflow: i + 2 <= 2147483647; */
    i += 2;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i && a[k] == 10 ==> b[k] == 20;
    loop assigns i;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i] == 10) {
      /*@ assert reachability: b[i] == 20; */
      __VERIFIER_assert(b[i] == 20);
    }
    /*@ assert rte: signed_overflow: i + 2 <= 2147483647; */
    i += 2;
  }
  __retres = 0;
  return __retres;
}