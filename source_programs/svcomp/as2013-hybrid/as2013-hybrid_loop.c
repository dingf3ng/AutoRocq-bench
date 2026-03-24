/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);


/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  abort();
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
    exits \false; */
int main(void)
{
  int __retres;
  int i = 0;
  /*@
    loop invariant 0 <= i <= 10;
    loop assigns i;
    loop variant 0;
  */
  while (1) {
    {
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
      int j = 0;
      /*@
        loop invariant 0 <= j <= 10;
        loop invariant 1 <= i <= 10;
        loop assigns j;
        loop variant 10 - j;
      */
      while (j < 10) {
        /*@ assert reachability: 0 <= i; */
        __VERIFIER_assert(0 <= i);
        /*@ assert reachability: i <= 10; */
        __VERIFIER_assert(i <= 10);
        /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
        j ++;
      }
      if (i > 9) i = 0;
    }
  }
  __retres = 0;
  return __retres;
}