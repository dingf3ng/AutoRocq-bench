#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark19_conjunctive.c",2,"0");
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
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  if (j == n) 
    if (k == n) {
      if (! (n > 0)) {
        __retres = 0;
        goto return_label;
      }
    }
    else {
      __retres = 0;
      goto return_label;
    }
  else {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant inv_j_bounds: 0 <= j <= n;
    loop invariant inv_k_bounds: 0 <= k <= n;
    loop invariant inv_jk_diff: j - k == 0;
    loop invariant inv_n_pos: n > 0;
    loop assigns j, k;
    loop variant j;
  */
  while (1) {
    if (j > 0) {
      /*@ assert reachability: n > 0; */
      if (! (n > 0)) break;
    }
    else break;
    /*@ assert rte: signed_overflow: -2147483648 <= j - 1; */
    j --;
    /*@ assert rte: signed_overflow: -2147483648 <= k - 1; */
    k --;
  }
  /*@ assert reachability: k == 0; */
  __VERIFIER_assert(k == 0);
  __retres = 0;
  return_label: return __retres;
}