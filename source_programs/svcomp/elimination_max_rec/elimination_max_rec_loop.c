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
  __assert_fail("0","elimination_max_rec.c",(unsigned int)5,"reach_error");
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
int check(int x, int y, int *a, int n)
{
  int __retres;
  int tmp;
  int tmp_2;
  if (x >= y) {
    __retres = x;
    goto return_label;
  }
  if (0 <= x) 
    if (y < n) tmp = 1; else tmp = 0;
  else tmp = 0;
  /*@ assert reachability: tmp == 1; */
  __VERIFIER_assert(tmp);
  int x0 = x;
  int y0 = y;
  if (*(a + x) <= *(a + y)) 
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  else 
    /*@ assert rte: signed_overflow: -2147483648 <= y - 1; */
    y --;
  int x1 = check(x,y,a,n);
  int i = __VERIFIER_nondet_int();
  if (x0 <= i) 
    if (i <= y0) tmp_2 = 1; else tmp_2 = 0;
  else tmp_2 = 0;
  assume_abort_if_not(tmp_2);
  int ai = *(a + i);
  int ax = *(a + x1);
  /*@ assert reachability: ai <= ax; */
  __VERIFIER_assert(ai <= ax);
  __retres = x1;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int tmp_0;
  int n = __VERIFIER_nondet_int();
  if (n >= 0) 
    if (n < 1 << 30) tmp_0 = 1; else tmp_0 = 0;
  else tmp_0 = 0;
  assume_abort_if_not(tmp_0);
  int *a = calloc((unsigned int)n,(unsigned int)sizeof(int));
  /*@ assert rte: signed_overflow: -2147483648 <= n - 1; */
  int x = check(0,n - 1,a,n);
  free((void *)a);
  return x;
}