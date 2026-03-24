#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"standard_strcmp_ground.c",3,"0");
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
int _strcmp(int src[100000], int dst[100000])
{
  int __retres;
  int i = 0;
  /*@
    loop invariant 0 <= i <= 100000;
    loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k];
    loop assigns i;
    loop variant 100000 - i;
  */
  while (i < 100000) {
    if (*(dst + i) != *(src + i)) {
      /*@ assert reachability: \exists integer j; 0 <= j < 100000 && dst[j] != src[j]; */
      __retres = 1;
      goto return_label;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  /*@ assert reachability: \forall integer k; 0 <= k < 100000 ==> dst[k] == src[k]; */
  __retres = 0;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int a[100000];
  int b[100000];
  {
    int i = 0;
    /*@
      loop invariant 0 <= i <= 100000;
      loop assigns i, a[0..99999], b[0..99999];
      loop variant 100000 - i;
    */
    while (i < 100000) {
      a[i] = __VERIFIER_nondet_int();
      b[i] = __VERIFIER_nondet_int();
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
  }
  int c = _strcmp(a,b);
  if (c == 0) {
    /*@ assert reachability: \forall integer k; 0 <= k < 100000 ==> a[k] == b[k]; */
    int x;
    x = 0;
    /*@
      loop invariant 0 <= x <= 100000;
      loop invariant \forall integer k; 0 <= k < x ==> a[k] == b[k];
      loop assigns x;
      loop variant 100000 - x;
    */
    while (x < 100000) {
      /*@ assert reachability: a[x] == b[x]; */
      __VERIFIER_assert(a[x] == b[x]);
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    }
  }
  __retres = 0;
  return __retres;
}