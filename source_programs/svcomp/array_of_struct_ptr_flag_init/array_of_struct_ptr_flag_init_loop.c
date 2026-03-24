#include "assert.h"
typedef unsigned int size_t;
struct __anonstruct_S_1 {
   int *n ;
};
typedef struct __anonstruct_S_1 S;
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
  __FC_assert(0 != 0,"array_of_struct_ptr_flag_init.c",5,"0");
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
void init(S *a, int size)
{
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= size;
    loop invariant \forall integer k; 0 <= k < i ==> (a + k)->n != \null;
    loop assigns i, a[0 .. size-1].n;
    loop variant size - i;
  */
  while (i < size) {
    (a + i)->n = (int *)malloc((size_t)sizeof(int));
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  S a[100000];
  int i;
  int flag;
  flag = 0;
  init(a,100000);
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= flag <= 1;
    loop invariant \forall integer k; 0 <= k < i ==> (a[k].n != (int *)0) ==> flag == 1;
    loop assigns i, flag;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (a[i].n != (int *)0) flag = 1;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant 0 <= flag <= 1;
    loop invariant flag == 0 ==> \forall integer k; 0 <= k < 100000 ==> a[k].n == (int *)0;
    loop assigns i;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (flag == 0) {
      /*@ assert reachability: a[i].n == (int *)0; */
      __VERIFIER_assert(a[i].n == (int *)0);
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}