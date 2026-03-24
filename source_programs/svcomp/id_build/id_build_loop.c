/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int ( /* missing proto */ __VERIFIER_nondet_int)(void);

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
  int offset;
  int length;
  int i;
  int j;
  int nlen = __VERIFIER_nondet_int();
  i = 0;
  /*@
    loop invariant outer_bounds: 0 <= i <= nlen;
    loop assigns i, j;
    loop variant nlen - i;
  */
  while (i < nlen) {
    j = 0;
    /*@
      loop invariant inner_bounds: 0 <= j <= 8;
      loop invariant outer_index: 0 <= i < nlen;
      loop assigns j;
      loop variant 8 - j;
    */
    while (j < 8) {
      /*@ assert rte: signed_overflow: -2147483648 <= nlen - 1; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(nlen - 1) - i; */
      /*@ assert rte: signed_overflow: (int)(nlen - 1) - i <= 2147483647; */
      /*@ assert reachability: 0 <= (nlen - 1) - i; */
      __VERIFIER_assert(0 <= (nlen - 1) - i);
      /*@ assert rte: signed_overflow: -2147483648 <= nlen - 1; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(nlen - 1) - i; */
      /*@ assert rte: signed_overflow: (int)(nlen - 1) - i <= 2147483647; */
      /*@ assert reachability: (nlen - 1) - i < nlen; */
      __VERIFIER_assert((nlen - 1) - i < nlen);
      /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
      j ++;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return __retres;
}