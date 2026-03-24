#include "assert.h"
struct S {
   int *p ;
   int n ;
};
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"single_elem_safe.c",3,"0");
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
    exits \false;
    assigns \result;
    assigns \result \from size;
 */
void *malloc(unsigned int size);

struct S *a[1000000];
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= 1000000;
    loop assigns i, a[0 .. 999999];
    loop variant 1000000 - i;
  */
  while (i < 1000000) {
    {
      int q = __VERIFIER_nondet_int();
      struct S *s = (struct S *)0;
      if (q == 0) {
        s = (struct S *)malloc((unsigned int)sizeof(struct S));
        s->n = q % 2;
      }
      if (s != (struct S *)0) 
        if (s->n == 0) s->p = (int *)malloc((unsigned int)sizeof(int));
        else s->p = (int *)0;
      a[i] = s;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  a[3] = (struct S *)malloc((unsigned int)sizeof(struct S));
  i = 0;
  /*@
    loop invariant 0 <= i <= 1000000;
    loop assigns i;
    loop variant 1000000 - i;
  */
  while (i < 1000000) {
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