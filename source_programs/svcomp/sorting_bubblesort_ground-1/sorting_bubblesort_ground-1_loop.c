#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"sorting_bubblesort_ground-1.c",3,"0");
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
  int a[100000];
  int x;
  int y;
  {
    int j = 0;
    /*@
      loop invariant 0 <= j <= 100000;
      loop assigns j, a[0 .. 99999];
      loop variant 100000 - j;
    */
    while (j < 100000) {
      a[j] = __VERIFIER_nondet_int();
      /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
      j ++;
    }
  }
  int swapped = 1;
  /*@
    loop invariant 0 <= swapped <= 1;
    loop assigns swapped, a[0 .. 99999];
    loop variant 100000;
  */
  while (swapped) {
    swapped = 0;
    int i = 1;
    /*@
      loop invariant 1 <= i <= 100000;
      loop assigns i, a[0 .. 99999], swapped;
      loop variant 100000 - i;
    */
    while (i < 100000) {
      /*@ assert rte: signed_overflow: -2147483648 <= i - 1; */
      if (a[i - 1] > a[i]) {
        int t = a[i];
        /*@ assert rte: signed_overflow: -2147483648 <= i - 1; */
        a[i] = a[i - 1];
        /*@ assert rte: signed_overflow: -2147483648 <= i - 1; */
        a[i - 1] = t;
        swapped = 1;
      }
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= 100000;
    loop assigns x, y;
    loop variant 100000 - x;
  */
  while (x < 100000) {
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    y = x + 1;
    /*@
      loop invariant x + 1 <= y <= 100000;
      loop assigns y;
      loop variant 100000 - y;
    */
    while (y < 100000) {
      /*@ assert reachability: a[x] <= a[y]; */
      __VERIFIER_assert(a[x] <= a[y]);
      /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
      y ++;
    }
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}