/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);


/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  assert(0);
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
extern _Bool __VERIFIER_nondet_bool(void);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int n = 0;
  /*@
    loop invariant 0 <= n <= 60;
    loop assigns n;
    loop variant 61 - n;
  */
  while (1) {
    {
      _Bool tmp;
      /*@ assert reachability: n <= 60; */
      __VERIFIER_assert(n <= 60);
      tmp = __VERIFIER_nondet_bool();
      if (tmp) 
        if (n < 60) 
          /*@ assert rte: signed_overflow: n + 1 <= 2147483647; */
          n ++;
        else {
          /*@ assert reachability: n == 60; */
          __VERIFIER_assert(n == 60);
          n = 0;
        }
    }
  }
  __retres = 0;
  return __retres;
}