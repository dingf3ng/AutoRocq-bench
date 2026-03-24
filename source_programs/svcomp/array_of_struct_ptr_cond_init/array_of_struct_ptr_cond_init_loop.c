#include "assert.h"
typedef unsigned int size_t;
struct _S {
   int *p ;
   int n ;
};
typedef struct _S S;
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
  __FC_assert(0 != 0,"array_of_struct_ptr_cond_init.c",5,"0");
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

S *a[100000];
/*@ terminates \true;
    exits \false; */
int user_read(void)
{
  int x = __VERIFIER_nondet_int();
  return x;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i, a[0 .. 99999];
    loop variant 100000 - i;
  */
  while (i < 100000) {
    {
      S *s1 = malloc((size_t)sizeof(S));
      s1->n = user_read();
      if (s1->n == 1) s1->p = (int *)malloc((size_t)sizeof(int));
      else s1->p = (int *)0;
      a[i] = s1;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop assigns i;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    {
      S *s2 = a[i];
      if (s2->n == 1) {
        /*@ assert reachability: s2->p != (int *)0; */
        __VERIFIER_assert(s2->p != (int *)0);
      }
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}