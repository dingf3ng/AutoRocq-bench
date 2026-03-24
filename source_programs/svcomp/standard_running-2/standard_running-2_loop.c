#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_running-2.c",3,"0");
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
  int i = 0;

  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> (a[k] >= 0 ==> b[k] == 1) && (a[k] < 0 ==> b[k] == 0);
    loop assigns i, b[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i] >= 0) b[i] = 1; else b[i] = 0;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  int f = 1;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= f <= 1;
    loop invariant \forall integer k; 0 <= k < i ==> ((a[k] >= 0 && b[k] == 1) || (a[k] < 0 && b[k] == 0));
    loop assigns i, f;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i] >= 0) 
      if (! b[i]) f = 0;
    if (a[i] < 0) 
      if (b[i]) f = 0;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  /*@ assert reachability: f == 1; */
  __VERIFIER_assert(f);
  __retres = 0;
  return __retres;
}