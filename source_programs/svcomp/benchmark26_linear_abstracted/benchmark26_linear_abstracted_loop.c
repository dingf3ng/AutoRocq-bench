#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark26_linear_abstracted.c",2,"0");
  return;
}

/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

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

  if (!(x < y)) {
    __retres = 0;
    goto return_label;
  }

  if (x < y) {
    x = __VERIFIER_nondet_int();

    if (!(x < y)) abort();

    if (x < y) 
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;

    if (x < y) abort();
  }

  /*@ assert reachability: x == y; */
  __VERIFIER_assert(x == y);
  __retres = 0;
return_label:
  return __retres;
}