#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"benchmark11_linear_abstracted.c",2,"0");
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
  int n = __VERIFIER_nondet_int();
  if (x == 0) {
    /*@ assert reachability: x == 0; */
    if (! (n > 0)) {
      __retres = 0;
      goto return_label;
    }
  }
  else {
    __retres = 0;
    goto return_label;
  }
  if (x < n) {
    /*@ assert reachability: x < n; */
    x = __VERIFIER_nondet_int();
    /*@ assert reachability: x < n; */
    if (! (x < n)) abort();
    if (x < n) 
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    /*@ assert reachability: x >= n || x == n; */
    if (x < n) abort();
  }
  /*@ assert reachability: x == n; */
  __VERIFIER_assert(x == n);
  __retres = 0;
  return_label: return __retres;
}