/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from size;
 */
extern  __attribute__((__nothrow__)) void *malloc(unsigned int size) __attribute__((
__leaf__));

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from x_0;
 */
extern int ( /* missing proto */ __VERIFIER_assert)(int x_0);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int n = __VERIFIER_nondet_int();
  if (0 <= n) {
    if (! (n <= 1000)) {
      __retres = 0;
      goto return_label;
    }
  }
  else {
    __retres = 0;
    goto return_label;
  }
  int *x = malloc((unsigned int)((unsigned long)n * sizeof(int)));
  {
    int i = 0;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> x[k] == 0;
      loop assigns i, x[0..n-1];
      loop variant n - i;
    */
    while (i < n) {
      *(x + i) = 0;
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
  }
  {
    int i_0 = 0;
    /*@
      loop invariant 0 <= i_0 <= n;
      loop invariant \forall integer k; 0 <= k < n ==> x[k] == 0;
      loop assigns i_0;
      loop variant n - i_0;
    */
    while (i_0 < n) {
      /*@ assert reachability: *(x + i_0) == 0; */
      __VERIFIER_assert(*(x + i_0) == 0);
      /*@ assert rte: signed_overflow: i_0 + 1 <= 2147483647; */
      i_0 ++;
    }
  }
  __retres = 0;
  return_label: return __retres;
}