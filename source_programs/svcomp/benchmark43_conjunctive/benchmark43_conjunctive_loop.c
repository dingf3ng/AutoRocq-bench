#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark43_conjunctive.c",2,"0");
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
  int tmp_1;
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (x < 100) {
    if (! (y < 100)) {
      __retres = 0;
      goto return_label;
    }
  }
  else {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant 0 <= x <= 100;
    loop invariant 0 <= y <= 100;
    loop invariant x < 100 || y < 100;
    loop assigns x, y;
    loop variant (100 - x) + (100 - y);
  */
  while (1) {
    if (x < 100) {
      if (! (y < 100)) break;
    }
    else break;
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
    /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
    y ++;
  }
  if (x == 100) tmp_1 = 1;
  else 
    if (y == 100) tmp_1 = 1; else tmp_1 = 0;
  /*@ assert reachability: tmp_1 == 1; */
  __VERIFIER_assert(tmp_1);
  __retres = 0;
  return_label: return __retres;
}