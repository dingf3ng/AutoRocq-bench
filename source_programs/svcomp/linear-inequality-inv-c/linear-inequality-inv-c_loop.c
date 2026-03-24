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
extern unsigned short __VERIFIER_nondet_ushort(void);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  unsigned short n = __VERIFIER_nondet_ushort();
  if ((int)n == 0) {
    __retres = 0;
    goto return_label;
  }
  unsigned short v = (unsigned short)0;
  unsigned int s = (unsigned int)0;
  unsigned int i = (unsigned int)0;

  /*@
    loop invariant 0 <= i <= n;
    loop invariant s <= 65535 * i;
    loop assigns i, s, v;
    loop variant n - i;
  */
  while (i < (unsigned int)n) {
    v = __VERIFIER_nondet_ushort();
    /*@ assert rte:signed_overflow: s + (unsigned int)v <= 4294967295; */
    s += (unsigned int)v;
    /*@ assert rte:signed_overflow: i + 1 <= 4294967295; */
    i ++;
  }

  /*@ assert reachability: !(s < (unsigned int)v); */
  if (s < (unsigned int)v) {
    reach_error();
    __retres = 1;
    goto return_label;
  }
  /*@ assert reachability: !((long)s > 4294836225); */
  if ((long)s > 4294836225) {
    reach_error();
    __retres = 1;
    goto return_label;
  }
  __retres = 0;
  return_label: return __retres;
}