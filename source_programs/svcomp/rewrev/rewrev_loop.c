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
  __assert_fail("0","rewrev.c",(unsigned int)3,"reach_error");
  return;
}

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
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from size;
 */
void *malloc(unsigned int size);

int const MAX = 100000;
int SIZE;
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) 
    if (SIZE < MAX) {
      int i;
      int *a = malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      int val2 = 3;
      int val1 = 7;
      int low = 2;
      /*@ assert rte: signed_overflow: -2147483648 <= SIZE - 2; */

      i = SIZE - 2;

      /*@
        loop invariant inv_i_bounds: -1 <= i <= SIZE-2;
        loop invariant inv_a_val2: \forall integer k; i+1 <= k < SIZE ==> a[k] == val2;
        loop invariant inv_a_val1: \forall integer k; i+1 <= k <= SIZE-2 ==> a[k] == val2 || a[k] == val1;
        loop assigns i, a[0 .. SIZE-1];
        loop variant i+2;
      */
      while (i >= -1) {
        if (i >= 0) {
          a[i] = val1;
        }
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        a[i + 1] = val2;
        /*@ assert rte: signed_overflow: -2147483648 <= i - 1; */
        i --;
      }

      i = 0;
      /*@
        loop invariant inv_scan_bounds: 0 <= i <= SIZE;
        loop invariant inv_a_geq_low: \forall integer k; 0 <= k < i ==> a[k] >= low;
        loop assigns i;
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        /*@ assert reachability: a[i] >= low; */
        __VERIFIER_assert(a[i] >= low);
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
    }
  __retres = 1;
  return __retres;
}