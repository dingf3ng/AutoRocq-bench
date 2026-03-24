/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from x_0;
 */
extern int ( /* missing proto */ __VERIFIER_assert)(int x_0);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  int j;
  int k;
  i = 0;
  k = 9;
  j = -100;
  /*@
    loop invariant 0 <= i <= 101;
    loop invariant k == 4 || (i == 0 && k == 9);
    loop assigns i, j, k;
    loop variant 101 - i;
  */
  while (i <= 100) {
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
    /*@
      loop invariant j <= 2147483647;
      loop assigns j;
      loop variant 20 - j;
    */
    while (j < 20) {
      /*@ assert rte: signed_overflow: -2147483648 <= i + j; */
      /*@ assert rte: signed_overflow: i + j <= 2147483647; */
      j = i + j;
    }
    k = 4;
    /*@
      loop invariant k == 4;
      loop assigns k;
      loop variant 4 - k;
    */
    while (k <= 3) {
      /*@ assert rte: signed_overflow: k + 1 <= 2147483647; */
      k ++;
    }
  }
  /*@ assert reachability: k == 4; */
  __VERIFIER_assert(k == 4);
  __retres = 0;
  return __retres;
}