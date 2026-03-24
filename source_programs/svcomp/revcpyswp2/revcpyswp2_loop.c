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
  __assert_fail("0","revcpyswp2.c",(unsigned int)4,"reach_error");
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
      int tmp;
      int *a = malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      int *b = malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      int *a_copy =
        malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      int *b_copy =
        malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop assigns i, a_copy[0..SIZE-1], b_copy[0..SIZE-1];
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        *(a_copy + i) = __VERIFIER_nondet_int();
        *(b_copy + i) = __VERIFIER_nondet_int();
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop assigns i, a[0..SIZE-1], b[0..SIZE-1];
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        /*@ assert rte: signed_overflow: -2147483648 <= SIZE - i; */
        /*@ assert rte: signed_overflow: SIZE - i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(SIZE - i) - 1; */
        *(a + i) = *(a_copy + ((SIZE - i) - 1));
        /*@ assert rte: signed_overflow: -2147483648 <= SIZE - i; */
        /*@ assert rte: signed_overflow: SIZE - i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(SIZE - i) - 1; */
        *(b + i) = *(b_copy + ((SIZE - i) - 1));
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop assigns i, a[0..SIZE-1], b[0..SIZE-1];
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        tmp = *(a + i);
        *(a + i) = *(b + i);
        *(b + i) = tmp;
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop assigns i, a[0..SIZE-1], b[0..SIZE-1];
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        tmp = *(a + i);
        *(a + i) = *(b + i);
        *(b + i) = tmp;
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      i = 0;
      /*@
        loop invariant 0 <= i <= SIZE;
        loop assigns i;
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        /*@ assert rte: signed_overflow: -2147483648 <= SIZE - i; */
        /*@ assert rte: signed_overflow: SIZE - i <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(SIZE - i) - 1; */
        /*@ assert reachability: *(a + i) == *(a_copy + ((SIZE - i) - 1)); */
        __VERIFIER_assert(*(a + i) == *(a_copy + ((SIZE - i) - 1)));
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
    }
  __retres = 1;
  return __retres;
}