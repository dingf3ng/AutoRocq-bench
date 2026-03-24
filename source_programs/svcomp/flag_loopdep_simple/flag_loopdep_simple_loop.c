#include "assert.h"
struct __anonstruct_S_1 {
   int n ;
};
typedef struct __anonstruct_S_1 S;
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"flag_loopdep_simple.c",3,"0");
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
void init(S *a, int size)
{
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= size;
    loop assigns i, a[0 .. size-1].n;
    loop variant size - i;
  */
  while (i < size) {
    (a + i)->n = __VERIFIER_nondet_int();
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
  S a[1000000];
  int i;
  int flag;
  flag = 0;
  init(a,1000000);
  i = 0;
  /*@
    loop invariant 0 <= i <= 1000000;
    loop invariant 0 <= flag <= 1;
    loop invariant flag == 1 <==> (\exists integer k; 0 <= k < i && a[k].n != 0);
    loop assigns i, flag;
    loop variant 1000000 - i;
  */
  while (i < 1000000) {
    if (a[i].n != 0) flag = 1;
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 1000000;
    loop invariant flag == 1 || (\forall integer k; 0 <= k < i ==> a[k].n == 0);
    loop assigns i;
    loop variant 1000000 - i;
  */
  while (i < 1000000) {
    if (flag == 0) {
      /*@ assert reachability: a[i].n == 0; */
      __VERIFIER_assert(a[i].n == 0);
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}