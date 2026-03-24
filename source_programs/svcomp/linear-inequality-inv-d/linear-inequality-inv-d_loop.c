/*@ terminates \false;
    exits \false;
    assigns \nothing; */
extern  __attribute__((__noreturn__, __nothrow__)) void __assert_fail
(char const *, char const *, unsigned int, char const *) __attribute__((
__leaf__));

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __assert_fail("0","linear-inequality-inv-a.c",(unsigned int)2,
                "reach_error");
  return;
}

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern unsigned int __VERIFIER_nondet_uint(void);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  unsigned int n = __VERIFIER_nondet_uint();
  if (n == (unsigned int)0) {
    __retres = 0;
    goto return_label;
  }
  unsigned int v = (unsigned int)0;
  unsigned long s = (unsigned long)0;
  unsigned long i = (unsigned long)0;

  /*@
    loop invariant 0 <= i <= n;
    loop invariant s <= 4294967295UL * i;
    loop assigns i, s, v;
    loop variant n - i;
  */
  while (i < (unsigned long)n) {
    v = __VERIFIER_nondet_uint();
    /*@ assert rte:signed_overflow: s + (unsigned long)v <= 18446744073709551615UL; */
    s += (unsigned long)v;
    i ++;
  }

  /*@ assert reachability: !(s < (unsigned long)v); */
  if (s < (unsigned long)v) {
    reach_error();
    __retres = 1;
    goto return_label;
  }
  /*@ assert reachability: !((unsigned long long)s > 18446744065119617025ULL); */
  if ((unsigned long long)s > 18446744065119617025ULL) {
    reach_error();
    __retres = 1;
    goto return_label;
  }
  __retres = 0;
  return_label: return __retres;
}