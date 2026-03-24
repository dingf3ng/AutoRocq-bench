#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"bAnd5.c",5,"0");
  return;
}

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

int N;
/*@ terminates \true;
    exits \false; */
int bAnd(int x[N])
{
  int __retres;
  int i;
  long long res;
  res = (long long)*(x + 0);
  i = 1;
  /*@
    loop invariant 1 <= i <= N;
    loop invariant \forall integer k; 1 <= k < i ==> 0 <= k < N;
    loop assigns i, res;
    loop variant N - i;
  */
  while (i < N) {
    res &= (long long)*(x + i);
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = (int)res;
  return __retres;
}

/*@ terminates \true;
    exits \false;
    assigns \nothing;
    frees p; */
 __attribute__((__FC_BUILTIN__)) void __fc_vla_free(void *p);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
    allocates \result;
 */
 __attribute__((__FC_BUILTIN__)) void *__fc_vla_alloc(unsigned long size);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  N = __VERIFIER_nondet_int();
  if (N > 1) {
    unsigned long __lengthof_x;
    int temp;
    int ret;
    int ret2;
    int ret5;
    /*@ assert alloca_bounds: 0 < sizeof(int) * N <= 18446744073709551615; */
    ;
    __lengthof_x = (unsigned long)N;
    int *x = __fc_vla_alloc(sizeof(int) * __lengthof_x);
    {
      int i = 0;
      /*@
        loop invariant 0 <= i <= N;
        loop assigns i, x[0 .. N-1];
        loop variant N - i;
      */
      while (i < N) {
        *(x + i) = __VERIFIER_nondet_int();
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
    }
    ret = bAnd(x);
    temp = *(x + 0);
    *(x + 0) = *(x + 1);
    *(x + 1) = temp;
    ret2 = bAnd(x);
    temp = *(x + 0);
    {
      int i_0 = 0;
      /*@
        loop invariant 0 <= i_0 <= N-1;
        loop assigns i_0, x[0 .. N-2];
        loop variant N-1 - i_0;
      */
      while (1) {
        /*@ assert rte: signed_overflow: -2147483648 <= N - 1; */
        if (! (i_0 < N - 1)) break;
        /*@ assert rte: signed_overflow: i_0 + 1 <= 2147483647; */
        *(x + i_0) = *(x + (i_0 + 1));
        /*@ assert rte: signed_overflow: i_0 + 1 <= 2147483647; */
        i_0 ++;
      }
    }
    /*@ assert rte: signed_overflow: -2147483648 <= N - 1; */
    *(x + (N - 1)) = temp;
    ret5 = bAnd(x);
    /*@ assert reachability: ret == ret2 || ret == ret5; */
    if (ret != ret2) goto _LOR;
    else 
      if (ret != ret5) _LOR: reach_error();
    __fc_vla_free((void *)x);
  }
  __retres = 1;
  return __retres;
}