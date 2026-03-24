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
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void assume_abort_if_not(int cond)
{
  if (! cond) abort();
  return;
}

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
  __assert_fail("0","lcp.c",(unsigned int)11,"reach_error");
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
    exits \false; */
int lcp(int *a, int n, int x, int y)
{
  int l = 0;
  /*@
    loop invariant 0 <= l <= n;
    loop invariant \forall integer k; 0 <= k < l ==> x + k < n && y + k < n && *(a + (x + k)) == *(a + (y + k));
    loop assigns l;
    loop variant n - l;
  */
  while (1) {
    /*@ assert rte: signed_overflow: -2147483648 <= x + l; */
    /*@ assert rte: signed_overflow: x + l <= 2147483647; */
    if (x + l < n) 
      /*@ assert rte: signed_overflow: -2147483648 <= y + l; */
      /*@ assert rte: signed_overflow: y + l <= 2147483647; */
      if (y + l < n) {
        /*@ assert rte: signed_overflow: -2147483648 <= x + l; */
        /*@ assert rte: signed_overflow: x + l <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= y + l; */
        /*@ assert rte: signed_overflow: y + l <= 2147483647; */
        if (! (*(a + (x + l)) == *(a + (y + l)))) break;
      }
      else break;
    else break;
    /*@ assert rte: signed_overflow: l + 1 <= 2147483647; */
    l ++;
  }
  return l;
}

/*@ terminates \true;
    exits \false; */
void check(int *a, int n, int x, int y, int l)
{
  int tmp_0;
  int i = __VERIFIER_nondet_int();
  if (0 <= i) 
    if (i < l) tmp_0 = 1; else tmp_0 = 0;
  else tmp_0 = 0;
  assume_abort_if_not(tmp_0);
  /*@ assert rte: signed_overflow: -2147483648 <= x + i; */
  /*@ assert rte: signed_overflow: x + i <= 2147483647; */
  /*@ assert rte: signed_overflow: -2147483648 <= y + i; */
  /*@ assert rte: signed_overflow: y + i <= 2147483647; */
  /*@ assert reachability: *(a + (x + i)) == *(a + (y + i)); */
  __VERIFIER_assert(*(a + (x + i)) == *(a + (y + i)));
  /*@ assert rte: signed_overflow: -2147483648 <= x + l; */
  /*@ assert rte: signed_overflow: x + l <= 2147483647; */
  if (x + l < n) 
    /*@ assert rte: signed_overflow: -2147483648 <= y + l; */
    /*@ assert rte: signed_overflow: y + l <= 2147483647; */
    if (y + l < n) 
      /*@ assert rte: signed_overflow: -2147483648 <= x + l; */
      /*@ assert rte: signed_overflow: x + l <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= y + l; */
      /*@ assert rte: signed_overflow: y + l <= 2147483647; */
      /*@ assert reachability: *(a + (x + l)) != *(a + (y + l)); */
      __VERIFIER_assert(*(a + (x + l)) != *(a + (y + l)));
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int tmp_0;
  int tmp_4;
  int n = __VERIFIER_nondet_int();
  if (n >= 0) 
    if (n < 1 << 30) tmp_0 = 1; else tmp_0 = 0;
  else tmp_0 = 0;
  assume_abort_if_not(tmp_0);
  int *a = calloc((unsigned int)n,(unsigned int)sizeof(int));
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (x >= 0) 
    if (y >= 0) tmp_4 = 1; else tmp_4 = 0;
  else tmp_4 = 0;
  assume_abort_if_not(tmp_4);
  int l = lcp(a,n,x,y);
  check(a,n,x,y,l);
  free((void *)a);
  __retres = 0;
  return __retres;
}