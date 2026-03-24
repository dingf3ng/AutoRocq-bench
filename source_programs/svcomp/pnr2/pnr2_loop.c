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
  __assert_fail("0","pnr2.c",(unsigned int)3,"reach_error");
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

/*@ terminates \true;
    exits \false; */
int ReadFromPort(void)
{
  int x = __VERIFIER_nondet_int();
  return x;
}

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
      int value;
      int *a = malloc((unsigned int)(sizeof(int) * (unsigned long)SIZE));
      int DEFAULTVAL = 0;
      int FIXEDVAL = 10;
      if (SIZE % 2 != 0) {
        __retres = 1;
        goto return_label;
      }
      assume_abort_if_not(SIZE % 2 == 0);
      i = 1;
      /*@
        loop invariant inv_i_bounds: 1 <= i <= (SIZE/2) + 1;
        loop invariant inv_even_filled:
          \forall integer q; 0 <= q < i-1 ==> 0 <= 2*q < SIZE && a[2*q] != DEFAULTVAL;
        loop invariant inv_odd_filled:
          \forall integer q; 0 <= q < i-1 && 2*q+1 < SIZE ==> a[2*q+1] != DEFAULTVAL;
        loop invariant inv_two_i_nonneg: 0 <= 2*i;
        loop invariant inv_two_i_upper: 2*i <= SIZE + 2;
        loop assigns i, value, a[0 .. SIZE-1];
        loop variant (SIZE/2) - (i-1);
      */
      while (i <= SIZE / 2) {
        value = ReadFromPort();
        if (value != DEFAULTVAL) 
          /*@ assert rte: signed_overflow: -2147483648 <= i * 2; */
          /*@ assert rte: signed_overflow: i * 2 <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 2) - 2; */
          *(a + (i * 2 - 2)) = value;
        else 
          /*@ assert rte: signed_overflow: -2147483648 <= i * 2; */
          /*@ assert rte: signed_overflow: i * 2 <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 2) - 2; */
          *(a + (i * 2 - 2)) = FIXEDVAL;
        value = ReadFromPort();
        if (value != DEFAULTVAL) 
          /*@ assert rte: signed_overflow: -2147483648 <= i * 2; */
          /*@ assert rte: signed_overflow: i * 2 <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 2) - 1; */
          *(a + (i * 2 - 1)) = value;
        else 
          /*@ assert rte: signed_overflow: -2147483648 <= i * 2; */
          /*@ assert rte: signed_overflow: i * 2 <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 2) - 1; */
          *(a + (i * 2 - 1)) = FIXEDVAL;
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
      i = 0;
      /*@
        loop invariant inv_scan_bounds: 0 <= i <= SIZE;
        loop invariant inv_scan_prefix_ok:
          \forall integer k; 0 <= k < i ==> a[k] != DEFAULTVAL;
        loop assigns i;
        loop variant SIZE - i;
      */
      while (i < SIZE) {
        /*@ assert reachability: *(a + i) != DEFAULTVAL; */
        __VERIFIER_assert(*(a + i) != DEFAULTVAL);
        /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
        i ++;
      }
    }
  __retres = 1;
  return_label: return __retres;
}