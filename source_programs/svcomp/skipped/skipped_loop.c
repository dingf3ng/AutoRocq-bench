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
  __assert_fail("0","skipped.c",(unsigned int)3,"reach_error");
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
      int i;
      int *a = malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop assigns i, a[0 .. SIZE-1];
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        *(a + i) = __VERIFIER_nondet_int();
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      if (SIZE % 2 != 0) {
        __retres = 1;
        goto return_label;
      }
      assume_abort_if_not(SIZE % 2 == 0);
      i = 1;
      /*@
        loop invariant 1 <= i <= SIZE/2 + 1;
        loop invariant \forall integer k; 0 <= k < 2*(i-1) && k < SIZE ==> *(a + k) <= k;
        loop assigns i, a[0 .. SIZE-1];
        loop variant (SIZE/2) - (i-1);
      */
      while (i <= SIZE / 2) {
        /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
        /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 2; */
        /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
        /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 2; */
        if (*(a + (2 * i - 2)) > 2 * i - 2) 
          /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
          /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 2;
          */
          /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
          /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 2;
          */
          *(a + (2 * i - 2)) = 2 * i - 2;
        /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
        /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 1; */
        /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
        /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 1; */
        if (*(a + (2 * i - 1)) > 2 * i - 1) 
          /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
          /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 1;
          */
          /*@ assert rte: signed_overflow: -2147483648 <= 2 * i; */
          /*@ assert rte: signed_overflow: 2 * i <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(2 * i) - 1;
          */
          *(a + (2 * i - 1)) = 2 * i - 1;
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop invariant \forall integer k; 0 <= k < i ==> *(a + k) <= k;
        loop assigns i;
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        /*@ assert reachability: *(a + i) <= i; */
        __VERIFIER_assert(*(a + i) <= i);
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
    }
  __retres = 1;
  return_label: return __retres;
}