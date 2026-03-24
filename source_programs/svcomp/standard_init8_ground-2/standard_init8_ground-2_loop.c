#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_init8_ground-2.c",3,"0");
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
    exits \false; */
int main(void)
{
  int __retres;
  int a[100000];
  int x;
  int i = 0;

  /*@ 
    loop invariant 0 <= i <= 100000;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 42;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 43;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 43;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 44;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 44;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 45;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 45;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 46;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 46;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 47;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 47;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 48;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 48;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 0;
  /*@ 
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == 49;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = 49;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  x = 0;
  /*@ 
    loop invariant 0 <= x <= 100000;
    loop invariant \forall integer k; 0 <= k < x ==> a[k] == 49;
    loop assigns x;
    loop variant 100000 - x;
  */
  while (x < 100000) {
    /*@ assert reachability: a[x] == 49; */
    __VERIFIER_assert(a[x] == 49);
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}