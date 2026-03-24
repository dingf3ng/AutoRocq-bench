#include "assert.h"
typedef unsigned int size_t;
struct S {
   int t ;
   int *p1 ;
};
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
  __FC_assert(0 != 0,"array_of_struct_ptr_monotonic.c",5,"0");
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

struct S *a[100000];
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] != \null;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    {
      struct S *s = malloc((size_t)sizeof(struct S));
      s->t = __VERIFIER_nondet_int();
      if (s->t == 10) s->p1 = (int *)malloc((size_t)sizeof(int));
      a[i] = s;
    }
    /*@ assert rte: signed_overflow: i + 2 <= 2147483647; */
    i += 2;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] != \null;
    loop assigns i;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    {
      struct S *u = a[i];
      /*@ assert reachability: u->t != 10 || u->p1 != (int *)0; */
      if (u->t == 10) __VERIFIER_assert(u->p1 != (int *)0);
    }
    /*@ assert rte: signed_overflow: i + 2 <= 2147483647; */
    i += 2;
  }
  __retres = 0;
  return __retres;
}