#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark25_linear.c",2,"0");
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
  int x = __VERIFIER_nondet_int();
  if (! (x < 0)) {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant -2147483648 <= x <= 10;
    loop invariant \forall integer k; x <= k <= 9 ==> k < 10;
    loop assigns x;
    loop variant 10 - x;
  */
  while (x < 10) 
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  /*@ assert reachability: x == 10; */
  __VERIFIER_assert(x == 10);
  __retres = 0;
  return_label: return __retres;
}