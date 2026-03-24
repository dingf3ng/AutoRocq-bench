#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark52_polynomial.c",2,"0");
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
  if (! cond) reach_error();
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i = __VERIFIER_nondet_int();
  if (i < 10) {
    if (! (i > -10)) {
      __retres = 0;
      goto return_label;
    }
  }
  else {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant -9 <= i <= 10;
    loop invariant \forall integer j; i <= j <= 9 ==> j * j < 100;
    loop assigns i;
    loop variant 10 - i;
  */
  while (1) {
    /*@ assert rte: signed_overflow: -2147483648 <= i * i; */
    /*@ assert rte: signed_overflow: i * i <= 2147483647; */
    if (! (i * i < 100)) break;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  /*@ assert reachability: i == 10; */
  __VERIFIER_assert(i == 10);
  __retres = 0;
  return_label: return __retres;
}