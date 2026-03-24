#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark05_conjunctive.c",2,"0");
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
  int y = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  if (x >= 0) 
    if (x <= y) {
      if (! (y < n)) {
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
    loop invariant inv1: x <= y <= n-1;
    loop invariant inv2: x >= 0;
    loop invariant inv3: y >= 0;
    loop invariant inv4: x <= n;
    loop invariant inv5: y <= n;
    loop invariant inv6: y >= x - 1;
    loop assigns x, y;
    loop variant n - x;
  */
  while (x < n) {
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
    if (x > y) 
      /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
      y ++;
  }
  /*@ assert reachability: y == n; */
  __VERIFIER_assert(y == n);
  __retres = 0;
  return_label: return __retres;
}