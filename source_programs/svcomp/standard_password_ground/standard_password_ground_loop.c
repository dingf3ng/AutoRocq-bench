#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_password_ground.c",3,"0");
  return;
}

/*@ terminates \true;
    exits \false; */
void __VERIFIER_assert(int cond)
{
  if (! cond) {
    ERROR: {
             reach_error();
             abort();
           }
  }
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
int main(void)
{
  int __retres;
  int password[100000];
  int guess[100000];
  int i;
  int result = 1;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i, password[0..99999], guess[0..99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    password[i] = __VERIFIER_nondet_int();
    guess[i] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= i ==> (result == 0 || (\forall integer k; 0 <= k < i ==> password[k] == guess[k]));
    loop assigns i, result;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (password[i] != guess[i]) result = 0;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  if (result) {
    int x;
    x = 0;
    /*@
      loop invariant 0 <= x <= 100000;
      loop invariant \forall integer k; 0 <= k < x ==> password[k] == guess[k];
      loop assigns x;
      loop variant 100000 - x;
    */
    while (x < 100000) {
      /*@ assert reachability: password[x] == guess[x]; */
      __VERIFIER_assert(password[x] == guess[x]);
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    }
  }
  __retres = 0;
  return __retres;
}