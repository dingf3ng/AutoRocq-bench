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
  __assert_fail("0","inv_square_int.c",(unsigned int)3,"reach_error");
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
void assume_abort_if_not(int cond)
{
  if (! cond) abort();
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
  int x;
  float y;
  float z;
  int tmp;
  x = __VERIFIER_nondet_int();
  if (x >= -10) 
    if (x <= 10) tmp = 1; else tmp = 0;
  else tmp = 0;
  assume_abort_if_not(tmp);

  /*@ assert rte: signed_overflow: -2147483648 <= x * x; */
  /*@ assert rte: signed_overflow: x * x <= 2147483647; */
  /*@ assert
      rte: is_nan_or_infinite:
        \is_finite(\sub_float((float)((int)(x * x)), 2.f));
  */

  y = (float)(x * x) - 2.f;

  /*@ assert reachability: y != 0.f; */
  __VERIFIER_assert(y != 0.f);

  /*@ assert rte: is_nan_or_infinite: \is_finite(\div_float(1.f, y)); */
  z = 1.f / y;
  __retres = 0;
  return __retres;
}