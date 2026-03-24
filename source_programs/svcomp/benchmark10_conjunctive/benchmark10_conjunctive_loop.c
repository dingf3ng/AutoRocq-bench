#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark10_conjunctive.c",2,"0");
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
  int c = __VERIFIER_nondet_int();
  if (c == 0) {
    if (! (i == 0)) {
      __retres = 0;
      goto return_label;
    }
  }
  else {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant 0 <= i <= 100;
    loop invariant c == 0 || (c >= 0 && i > 0);
    loop assigns i, c;
    loop variant 100 - i;
  */
  while (i < 100) {
    /*@ assert rte: signed_overflow: -2147483648 <= c + i; */
    /*@ assert rte: signed_overflow: c + i <= 2147483647; */
    c += i;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
    if (i <= 0) break;
  }
  /*@ assert reachability: c >= 0; */
  __VERIFIER_assert(c >= 0);
  __retres = 0;
  return_label: return __retres;
}