/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

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
  __assert_fail("0","odd.c",(unsigned int)3,"reach_error");
  return;
}

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

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
  unsigned int x = (unsigned int)1;

  /*@
    loop invariant odd_x: x % 2 == 1;
    loop invariant x_ge_1: x >= 1;
    loop assigns x;
    loop variant 0; // infinite loop, but breaks on nondet
  */
  while (1) {
    int tmp;
    tmp = __VERIFIER_nondet_int();
    /*@ assert reachability: tmp != 0 ==> x % 2 == 1; */
    if (! tmp) break;
    /*@ assert rte: signed_overflow: x + 2 <= 4294967295; */
    x += (unsigned int)2;
  }

  /*@ assert reachability: x % 2 == 1; */
  __VERIFIER_assert((int)(x % (unsigned int)2));
  __retres = 0;
  return __retres;
}