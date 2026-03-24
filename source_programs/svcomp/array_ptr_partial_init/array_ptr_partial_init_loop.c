#include "assert.h"
typedef unsigned int size_t;
/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from __size;
 */
extern  __attribute__((__nothrow__)) void *malloc(size_t __size) __attribute__((
__leaf__));

/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"array_ptr_partial_init.c",5,"0");
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

int *a[100000];
int i;
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == (int *)0;
    loop assigns i, a[0..99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    a[i] = (int *)0;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 50000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] != (int *)0;
    loop assigns i, a[0..49999];
    loop variant 50000 - i;
  */
  while (i < 100000 / 2) {
    a[i] = (int *)malloc((size_t)sizeof(int));
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 50000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] != (int *)0;
    loop assigns i;
    loop variant 50000 - i;
  */
  while (i < 100000 / 2) {
    /*@ assert reachability: a[i] != (int *)0; */
    __VERIFIER_assert(a[i] != (int *)0);
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}