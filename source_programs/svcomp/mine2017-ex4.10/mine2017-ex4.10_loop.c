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
  int v = 1;
  /*@
    loop invariant 1 <= v <= 53;
    loop invariant (v - 1) % 2 == 0;
    loop assigns v;
    loop variant 52 - v;
  */
  while (v <= 50) {
    /*@ assert reachability: 1 <= v; */
    __VERIFIER_assert(1 <= v);
    /*@ assert rte: signed_overflow: v + 2 <= 2147483647; */
    v += 2;
    /*@ assert reachability: v <= 52; */
    __VERIFIER_assert(v <= 52);
  }
  /*@ assert reachability: 51 <= v; */
  __VERIFIER_assert(51 <= v);
  /*@ assert reachability: v <= 52; */
  __VERIFIER_assert(v <= 52);
  __retres = 0;
  return __retres;
}