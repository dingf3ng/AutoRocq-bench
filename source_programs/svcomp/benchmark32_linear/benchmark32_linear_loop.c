#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark32_linear.c",2,"0");
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
  int x = __VERIFIER_nondet_int();
  if (!(x == 1)) 
    if (!(x == 2)) {
      __retres = 0;
      goto return_label;
    }
  /*@
    loop invariant x == 1 || x == 2;
    loop assigns x;
    loop variant 0;
  */
  while (1) {
    _Bool tmp_0;
    tmp_0 = __VERIFIER_nondet_bool();
    if (! tmp_0) break;
    if (x == 1) x = 2;
    else 
      if (x == 2) x = 1;
  }
  /*@ assert reachability: x <= 8; */
  __VERIFIER_assert(x <= 8);
  __retres = 0;
  return_label: return __retres;
}