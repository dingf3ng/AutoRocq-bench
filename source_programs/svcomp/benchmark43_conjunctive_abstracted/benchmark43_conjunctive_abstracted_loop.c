#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark43_conjunctive_abstracted.c",2,"0");
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
  if ((y < 100) & (x < 100)) {
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    if (! ((y < 100) & (x < 100))) abort();
    if (x < 100) 
      if (y < 100) {
        /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
        x ++;
        /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
        y ++;
      }
    if ((y < 100) & (x < 100)) abort();
  }
  if (x == 100) tmp_1 = 1;
  else 
    if (y == 100) tmp_1 = 1; else tmp_1 = 0;
  /*@ assert reachability: tmp_1 == 1; */
  __VERIFIER_assert(tmp_1);
  __retres = 0;
  return_label: return __retres;
}