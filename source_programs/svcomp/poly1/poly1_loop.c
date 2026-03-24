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
  __assert_fail("0","poly1.c",(unsigned int)3,"reach_error");
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

int SIZE;
int const MAX = 100000;
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) 
    if (SIZE < MAX) {
      long long i;
      long long *a =
        malloc((unsigned int)(sizeof(long long) * (unsigned long)SIZE));
      i = (long long)0;
      /*@
        loop invariant 0 <= i <= (long long)SIZE;
        loop invariant \forall long long k; 0 <= k < i ==> a[k] == k * k;
        loop assigns i, a[0 .. SIZE-1];
        loop variant (long long)SIZE - i;
      */
      while (i < (long long)SIZE) {
        /*@ assert rte: signed_overflow: -9223372036854775808 <= i * i; */
        /*@ assert rte: signed_overflow: i * i <= 9223372036854775807; */
        *(a + i) = i * i;
        /*@ assert rte: signed_overflow: i + 1 <= 9223372036854775807; */
        i ++;
      }
      i = (long long)0;
      /*@
        loop invariant 0 <= i <= (long long)SIZE;
        loop invariant \forall long long k; 0 <= k < i ==> a[k] == k * k;
        loop assigns i;
        loop variant (long long)SIZE - i;
      */
      while (i < (long long)SIZE) {
        /*@ assert rte: signed_overflow: -9223372036854775808 <= i * i; */
        /*@ assert rte: signed_overflow: i * i <= 9223372036854775807; */
        /*@ assert reachability: *(a + i) == i * i; */
        __VERIFIER_assert(*(a + i) == i * i);
        /*@ assert rte: signed_overflow: i + 1 <= 9223372036854775807; */
        i ++;
      }
    }
  __retres = 1;
  return __retres;
}