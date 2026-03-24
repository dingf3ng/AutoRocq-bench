#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark51_polynomial.c",2,"0");
  return;
}

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern _Bool __VERIFIER_nondet_bool(void);

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
  if (x >= 0) {
    if (! (x <= 50)) {
      __retres = 0;
      goto return_label;
    }
  }
  else {
    __retres = 0;
    goto return_label;
  }
  /*@
    loop invariant 0 <= x <= 51;
    loop assigns x;
    loop variant x;
  */
  while (1) {
    _Bool tmp_0;
    tmp_0 = __VERIFIER_nondet_bool();
    if (! tmp_0) break;
    if (x > 50) 
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    if (x == 0) 
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    else 
      /*@ assert rte: signed_overflow: -2147483648 <= x - 1; */
      x --;
  }
  if (x >= 0) 
    if (x <= 50) tmp_1 = 1; else tmp_1 = 0;
  else tmp_1 = 0;
  /*@ assert reachability: tmp_1 == 1; */
  __VERIFIER_assert(tmp_1);
  __retres = 0;
  return_label: return __retres;
}