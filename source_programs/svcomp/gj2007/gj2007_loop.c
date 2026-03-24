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
  int x = 0;
  int y = 50;
  /*@
    loop invariant 0 <= x <= 100;
    loop invariant 50 <= y <= x + 50;
    loop invariant x < 50 ==> y == 50;
    loop invariant x >= 50 ==> y == x;
    loop assigns x, y;
    loop variant 100 - x;
  */
  while (x < 100) 
    if (x < 50) 
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    else {
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
      /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
      y ++;
    }
  /*@ assert reachability: y == 100; */
  __VERIFIER_assert(y == 100);
  __retres = 0;
  return __retres;
}