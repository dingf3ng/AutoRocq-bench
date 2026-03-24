#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark02_linear.c",2,"0");
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
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  i = l;
  if (! (l > 0)) {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant inv_i_bounds: l <= i <= n;
    loop invariant inv_l_pos: l > 0;
    loop assigns i;
    loop variant n - i;
  */
  while (i < n) 
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  /*@ assert reachability: l >= 1; */
  __VERIFIER_assert(l >= 1);
  __retres = 0;
  return_label: return __retres;
}