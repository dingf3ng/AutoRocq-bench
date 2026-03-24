/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from nmemb, size;
 */
extern void *calloc(unsigned int nmemb, unsigned int size);

/*@ terminates \true;
    exits \false;
    assigns *((char *)__x0 + (0 ..));
    assigns *((char *)__x0 + (0 ..)) \from *((char *)__x0 + (0 ..));
 */
extern void free(void *);

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
  __assert_fail("0","elimination_max.c",(unsigned int)5,"reach_error");
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
    reach_error();
    abort();
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
    exits \false; */
int main(void)
{
  int tmp_0;
  int i;
  int tmp_2;
  int n = __VERIFIER_nondet_int();
  if (n >= 0) 
    if (n < 1 << 30) tmp_0 = 1; else tmp_0 = 0;
  else tmp_0 = 0;
  assume_abort_if_not(tmp_0);
  int *a = calloc((unsigned int)n,(unsigned int)sizeof(int));
  int x = 0;
  /*@ assert rte: signed_overflow: -2147483648 <= n - 1; */
  int y = n - 1;

  /*@
    loop invariant 0 <= x <= y + 1 <= n;
    loop invariant 0 <= y + 1 <= n;
    loop invariant 0 <= y < n || x == n;
    loop invariant \forall integer k; 0 <= k < x ==> *(a + k) <= *(a + y);
    loop invariant \forall integer k; y < k < n ==> *(a + y) < *(a + k);
    loop assigns x, y;
    loop variant y - x + 1;
  */
  while (x < y) 
    if (*(a + x) <= *(a + y)) 
      /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
      x ++;
    else 
      /*@ assert rte: signed_overflow: -2147483648 <= y - 1; */
      y --;

  i = __VERIFIER_nondet_int();
  if (0 <= i) 
    if (i < n) tmp_2 = 1; else tmp_2 = 0;
  else tmp_2 = 0;
  assume_abort_if_not(tmp_2);

  /*@ assert reachability: *(a + i) <= *(a + x); */
  __VERIFIER_assert(*(a + i) <= *(a + x));

  i = 0;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer k; 0 <= k < i ==> *(a + k) <= *(a + x);
    loop assigns i;
    loop variant n - i;
  */
  while (i < n) {
    /*@ assert reachability: *(a + i) <= *(a + x); */
    __VERIFIER_assert(*(a + i) <= *(a + x));
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  free((void *)a);
  return x;
}