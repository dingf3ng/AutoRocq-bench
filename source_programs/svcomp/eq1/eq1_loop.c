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
  __assert_fail("0","eq1.c",(unsigned int)3,"reach_error");
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
  int tmp_3;
  unsigned int w = __VERIFIER_nondet_uint();
  unsigned int x = w;
  unsigned int y = __VERIFIER_nondet_uint();
  unsigned int z = y;

  /*@
    loop invariant inv_wx: w - x == 0;
    loop invariant inv_yz: y - z == 0;
    loop invariant inv_bounds: 0 <= w && 0 <= x && 0 <= y && 0 <= z;
    loop assigns w, x, y, z;
  */
  while (1) {
    unsigned int tmp_2;
    tmp_2 = __VERIFIER_nondet_uint();
    if (! tmp_2) break;
    {
      unsigned int tmp_1;
      tmp_1 = __VERIFIER_nondet_uint();
      if (tmp_1) {
        /*@ assert rte:signed_overflow: w + 1 <= 4294967295; */
        w ++;
        /*@ assert rte:signed_overflow: x + 1 <= 4294967295; */
        x ++;
      }
      else {
        /*@ assert rte:signed_overflow: y >= 1; */
        y --;
        /*@ assert rte:signed_overflow: z >= 1; */
        z --;
      }
    }
  }

  /*@ assert reachability: (w == x) ==> (y == z) ==> tmp_3 == 1; */
  if (w == x) 
    if (y == z) tmp_3 = 1; else tmp_3 = 0;
  else tmp_3 = 0;

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: tmp_3 == 1 ==> (w == x && y == z); */
  /*@ assert reachability: tmp_3 == 0 ==> (w != x || y != z); */
  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: tmp_3 == 1 ==> (w == x && y == z); */
  /*@ assert reachability: tmp_3 == 0 ==> (w != x || y != z); */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  /*@ assert reachability: tmp_3 == 1 || tmp_3 == 0; */
  /*@ assert reachability: (w == x && y == z) ==> tmp_3 == 1; */
  /*@ assert reachability: (w != x || y != z) ==> tmp_3 == 0; */
  /*@ assert reachability: (tmp_3 == 1) ==> (w == x && y == z); */
  /*@ assert reachability: (tmp_3 == 0) ==> (w != x || y != z); */

  __VERIFIER_assert(tmp_3);
  __retres = 0;
  return __retres;
}