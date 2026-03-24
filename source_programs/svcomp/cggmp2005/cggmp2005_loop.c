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
  i = 1;
  j = 10;
  /*@
    loop invariant inv_i_bounds: 1 <= i <= 13;
    loop invariant inv_j_bounds: 6 <= j <= 10;
    loop invariant inv_relation: j + i == 11 || j + i == 13;
    loop assigns i, j;
    loop variant j - i + 1;
  */
  while (j >= i) {
    /*@ assert rte: signed_overflow: i + 2 <= 2147483647; */
    i += 2;
    /*@ assert rte: signed_overflow: -2147483648 <= (int)(-1) + j; */
    j = -1 + j;
  }
  /*@ assert reachability: j == 6; */
  __VERIFIER_assert(j == 6);
  __retres = 0;
  return __retres;
}