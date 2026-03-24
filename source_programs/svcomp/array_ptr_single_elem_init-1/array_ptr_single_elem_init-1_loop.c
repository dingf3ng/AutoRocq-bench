#include "assert.h"
typedef unsigned int size_t;
struct S {
   int *p ;
   int n ;
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
  __FC_assert(0 != 0,"array_ptr_single_elem_init-1.c",5,"0");
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
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == \null || (a[k]->n == 0 ==> a[k]->p != \null);
    loop assigns i, a[0..99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    {
      int q = __VERIFIER_nondet_int();
      struct S *s = (struct S *)0;
      if (q == 0) {
        s = (struct S *)malloc((size_t)sizeof(struct S));
        s->n = q % 2;
      }
      if (s != (struct S *)0) 
        if (s->n == 0) s->p = (int *)malloc((size_t)sizeof(int));
        else s->p = (int *)0;
      a[i] = s;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  a[3] = (struct S *)malloc((size_t)sizeof(struct S));
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    {
      struct S *s1 = a[i];
      if (i != 3) 
        if (s1 != (struct S *)0) 
          if (s1->n == 0) 
            /*@ assert reachability: s1->p != (int *)0; */
            __VERIFIER_assert(s1->p != (int *)0);
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}