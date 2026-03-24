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
  __assert_fail("0","array_init_nondet_vars.c",(unsigned int)3,"reach_error");
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
    assigns \nothing;
    frees p; */
 __attribute__((__FC_BUILTIN__)) void __fc_vla_free(void *p);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
    allocates \result;
 */
 __attribute__((__FC_BUILTIN__)) void *__fc_vla_alloc(unsigned long size);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int i;
  unsigned long __lengthof_a;
  int tmp_1;
  int j = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  assume_abort_if_not(n < 100000);
  /*@ assert alloca_bounds: 0 < sizeof(int) * n <= 18446744073709551615; */
  ;
  __lengthof_a = (unsigned long)n;
  int *a = __fc_vla_alloc(sizeof(int) * __lengthof_a);
  if (j > 0) 
    if (j < 10000) tmp_1 = 1; else tmp_1 = 0;
  else tmp_1 = 0;
  assume_abort_if_not(tmp_1);
  i = 1;

  /*@
    loop invariant 1 <= i <= n;
    loop assigns i, a[1 .. n-1];
    loop variant n - i;
  */
  while (i < n) {
    {
      int tmp_3;
      int k = __VERIFIER_nondet_int();
      if (k > 0) 
        if (k < 10000) tmp_3 = 1; else tmp_3 = 0;
      else tmp_3 = 0;
      assume_abort_if_not(tmp_3);
      /*@ assert rte: signed_overflow: -2147483648 <= i + j; */
      /*@ assert rte: signed_overflow: i + j <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i + j) + k; */
      /*@ assert rte: signed_overflow: (int)(i + j) + k <= 2147483647; */
      *(a + i) = (i + j) + k;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }

  i = 1;

  /*@
    loop invariant 1 <= i <= n;
    loop invariant \forall integer m; 1 <= m < i ==> a[m] >= m + 2;
    loop assigns i;
    loop variant n - i;
  */
  while (i < n) {
    /*@ assert rte: signed_overflow: i + 2 <= 2147483647; */
    /*@ assert reachability: *(a + i) >= i + 2; */
    __VERIFIER_assert(*(a + i) >= i + 2);
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  __fc_vla_free((void *)a);
  return __retres;
}