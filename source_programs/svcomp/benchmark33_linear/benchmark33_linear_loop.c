#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark33_linear.c",2,"0");
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
  if (! (x >= 0)) {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant inv_x_nonneg: x >= 0;
    loop invariant inv_x_le_100: x <= 100;
    loop assigns x;
    loop variant 100 - x;
  */
  while (1) {
    if (x < 100) {
      if (! (x >= 0)) break;
    }
    else break;
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  /*@ assert reachability: x >= 100; */
  __VERIFIER_assert(x >= 100);
  __retres = 0;
  return_label: return __retres;
}