/*@ terminates \false;
    exits \false;
    assigns \nothing; */
extern  __attribute__((__noreturn__, __nothrow__)) void __assert_fail
(char const *, char const *, unsigned int, char const *) __attribute__((__leaf__));

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __assert_fail("0","nested_2.c",(unsigned int)13,"reach_error");
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int a = 6;
  int b = 6;
  a = 0;
  /*@
    loop invariant 0 <= a <= 6;
    loop assigns a, b;
    loop variant 6 - a;
  */
  while (a < 6) {
    b = 0;
    /*@
      loop invariant 0 <= b <= 6;
      loop assigns b;
      loop variant 6 - b;
    */
    while (b < 6) 
      /*@ assert rte: signed_overflow: b + 1 <= 2147483647; */
      b ++;
    /*@ assert rte: signed_overflow: a + 1 <= 2147483647; */
    a ++;
  }
  if (a == 6) {
    /*@ assert reachability: b == 6; */
    if (! (b == 6)) goto _LAND;
  }
  else _LAND: reach_error();
  __retres = 1;
  return __retres;
}