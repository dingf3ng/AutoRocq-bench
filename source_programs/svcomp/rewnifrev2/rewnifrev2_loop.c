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
  __assert_fail("0","rewnifrev2.c",(unsigned int)3,"reach_error");
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
  int i;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) 
    if (SIZE < MAX) {
      int *a = malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      /*@ assert rte: signed_overflow: -2147483648 <= SIZE - 2; */
      i = SIZE - 2;
      /*@
        loop invariant 0 <= i + 1 <= SIZE;
        loop invariant -1 <= i <= SIZE - 2;
        loop assigns i, a[0 .. SIZE-1];
        loop variant i + 1;
      */
      while (i >= 0) {
        *(a + i) = i;
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        *(a + (i + 1)) = i + 1;
        /*@ assert rte: signed_overflow: -2147483648 <= i - 1; */
        i --;
      }
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop invariant \forall integer k; 0 <= k < i ==> *(a + k) >= k;
        loop assigns i;
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        /*@ assert reachability: *(a + i) >= i; */
        __VERIFIER_assert(*(a + i) >= i);
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
    }
  __retres = 1;
  return __retres;
}