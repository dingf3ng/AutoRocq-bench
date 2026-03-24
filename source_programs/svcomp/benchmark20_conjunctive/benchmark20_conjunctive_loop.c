#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark20_conjunctive.c",2,"0");
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
  int n = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  if (i == 0) 
    if (n >= 0) 
      if (n <= 100) {
        if (! (sum == 0)) {
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
  else {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant 0 <= i <= n <= 100;
    loop invariant sum >= 0;
    loop assigns i, sum;
    loop variant n - i;
  */
  while (i < n) {
    /*@ assert rte: signed_overflow: -2147483648 <= sum + i; */
    /*@ assert rte: signed_overflow: sum + i <= 2147483647; */
    sum += i;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  /*@ assert reachability: sum >= 0; */
  __VERIFIER_assert(sum >= 0);
  __retres = 0;
  return_label: return __retres;
}