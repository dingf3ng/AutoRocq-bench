#include "assert.h"
/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"bAnd1.c",6,"0");
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
int bAnd(int x[100])
{
  int __retres;
  int i;
  long long res;
  res = (long long)*(x + 0);
  i = 1;
  /*@
    loop invariant 1 <= i <= 100;
    loop invariant \forall integer k; 1 <= k < i ==> -2147483648LL <= (long long)x[k] <= 2147483647LL;
    loop assigns i, res;
    loop variant 100 - i;
  */
  while (i < 100) {
    res &= (long long)*(x + i);
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = (int)res;
  return __retres;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int x[100];
  int temp;
  int ret;
  int ret2;
  int ret5;
  {
    int i = 0;
    /*@
      loop invariant 0 <= i <= 100;
      loop assigns i, x[0..99];
      loop variant 100 - i;
    */
    while (i < 100) {
      x[i] = __VERIFIER_nondet_int();
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
  }
  ret = bAnd(x);
  temp = x[0];
  x[0] = x[1];
  x[1] = temp;
  ret2 = bAnd(x);
  temp = x[0];
  {
    int i_0 = 0;
    /*@
      loop invariant 0 <= i_0 <= 99;
      loop assigns i_0, x[0..98];
      loop variant 99 - i_0;
    */
    while (i_0 < 100 - 1) {
      /*@ assert rte: signed_overflow: i_0 + 1 <= 2147483647; */
      x[i_0] = x[i_0 + 1];
      /*@ assert rte: signed_overflow: i_0 + 1 <= 2147483647; */
      i_0 ++;
    }
  }
  x[100 - 1] = temp;
  ret5 = bAnd(x);
  /*@ assert reachability: ret == ret2 || ret == ret5; */
  if (ret != ret2) goto _LOR;
  else 
    if (ret != ret5) _LOR: reach_error();
  __retres = 1;
  return __retres;
}