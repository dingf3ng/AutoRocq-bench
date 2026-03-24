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
extern unsigned char __VERIFIER_nondet_uchar(void);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  unsigned char n = __VERIFIER_nondet_uchar();
  if ((int)n == 0) {
    __retres = 0;
    goto return_label;
  }
  unsigned char v = (unsigned char)0;
  unsigned int s = (unsigned int)0;
  unsigned int i = (unsigned int)0;

  /*@
    loop invariant 0 <= i <= n;
    loop invariant s <= 255 * i;
    loop assigns i, s, v;
    loop variant n - i;
  */
  while (i < (unsigned int)n) {
    v = __VERIFIER_nondet_uchar();
    /*@ assert rte:signed_overflow: 0 <= s + (unsigned int)v <= 4294967295; */
    s += (unsigned int)v;
    i ++;
  }

  /*@ assert reachability: s >= (unsigned int)v; */
  if (s < (unsigned int)v) {
    reach_error();
    __retres = 1;
    goto return_label;
  }
  /*@ assert reachability: s <= (unsigned int)65025; */
  if (s > (unsigned int)65025) {
    reach_error();
    __retres = 1;
    goto return_label;
  }
  __retres = 0;
  return_label: return __retres;
}