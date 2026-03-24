#include "assert.h"
struct S {
   int *n ;
};
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"break-1.c",3,"0");
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
    assigns \result \from size;
 */
void *malloc(unsigned int size);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

struct S s[1000000];
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  int c = __VERIFIER_nondet_int();
  i = 0;
  /*@
    loop invariant 0 <= i <= 1000000;
    loop invariant \forall integer k; 0 <= k < i ==> (c > 5 ==> s[k].n != (int *)0);
    loop assigns i, s[0 .. 999999].n;
    loop variant 1000000 - i;
  */
  while (i < 1000000) {
    if (c > 5) break;
    s[i].n = (int *)malloc((unsigned int)sizeof(int));
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 1000000;
    loop invariant \forall integer k; 0 <= k < i ==> (c > 5 ==> s[k].n != (int *)0);
    loop assigns i;
    loop variant 1000000 - i;
  */
  while (i < 1000000) {
    if (c <= 5) {
      /*@ assert reachability: s[i].n != (int *)0; */
      __VERIFIER_assert(s[i].n != (int *)0);
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}