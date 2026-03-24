/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \false;
    exits \false;
    assigns \nothing; */
extern  __attribute__((__noreturn__, __nothrow__)) void __assert_fail
(char const *, char const *, unsigned int, char const *) __attribute__((__leaf__));

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __assert_fail("0","pr4.c",(unsigned int)3,"reach_error");
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

int CELLCOUNT;
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
  CELLCOUNT = __VERIFIER_nondet_int();
  if (CELLCOUNT > 1) {
    int MINVAL;
    int i;
    unsigned long __lengthof_volArray;
    /*@
    assert
    alloca_bounds: 0 < sizeof(int) * CELLCOUNT <= 18446744073709551615; */
    ;
    __lengthof_volArray = (unsigned long)CELLCOUNT;
    int *volArray = __fc_vla_alloc(sizeof(int) * __lengthof_volArray);
    int CCCELVOL4 = 5;
    int CCCELVOL3 = 7;
    int CCCELVOL2 = 3;
    int CCCELVOL1 = 1;
    if (CELLCOUNT % 4 != 0) {
      __retres = 1;
      __fc_vla_free((void *)volArray);
      goto return_label;
    }
    assume_abort_if_not(CELLCOUNT % 4 == 0);
    i = 1;
    /*@
      loop invariant inv_i_bounds: 1 <= i <= (CELLCOUNT/4) + 1;
      loop invariant inv_even_filled:
        \forall integer q; 0 <= q < i-1 ==> 0 <= 4*q < CELLCOUNT && 
          ((CCCELVOL4 >= MINVAL ? volArray[4*q] == CCCELVOL4 : volArray[4*q] == 0)) &&
          ((CCCELVOL3 >= MINVAL ? volArray[4*q+1] == CCCELVOL3 : volArray[4*q+1] == 0)) &&
          ((CCCELVOL2 >= MINVAL ? volArray[4*q+2] == CCCELVOL2 : volArray[4*q+2] == 0)) &&
          ((CCCELVOL1 >= MINVAL ? volArray[4*q+3] == CCCELVOL1 : volArray[4*q+3] == 0));
      loop invariant inv_index_bounds: 0 <= 4*(i-1) < CELLCOUNT + 4;
      loop assigns i, volArray[0 .. CELLCOUNT-1];
      loop variant (CELLCOUNT/4) - (i-1);
    */
    while (i <= CELLCOUNT / 4) {
      if (CCCELVOL4 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 4; */
        *(volArray + (i * 4 - 4)) = CCCELVOL4;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 4; */
        *(volArray + (i * 4 - 4)) = 0;
      if (CCCELVOL3 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 3; */
        *(volArray + (i * 4 - 3)) = CCCELVOL3;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 3; */
        *(volArray + (i * 4 - 3)) = 0;
      if (CCCELVOL2 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 2; */
        *(volArray + (i * 4 - 2)) = CCCELVOL2;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 2; */
        *(volArray + (i * 4 - 2)) = 0;
      if (CCCELVOL1 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 1; */
        *(volArray + (i * 4 - 1)) = CCCELVOL1;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 4; */
        /*@ assert rte: signed_overflow: i * 4 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 4) - 1; */
        *(volArray + (i * 4 - 1)) = 0;
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
    i = 0;
    /*@
      loop invariant inv_scan_bounds: 0 <= i <= CELLCOUNT;
      loop invariant inv_scan_prefix_ok:
        \forall integer k; 0 <= k < i ==> volArray[k] == 0 || volArray[k] >= MINVAL;
      loop assigns i;
      loop variant CELLCOUNT - i;
    */
    while (i < CELLCOUNT) {
      {
        int tmp;
        if (*(volArray + i) >= MINVAL) tmp = 1;
        else 
          if (*(volArray + i) == 0) tmp = 1; else tmp = 0;
        /*@ assert reachability: tmp == 1; */
        __VERIFIER_assert(tmp);
      }
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
    ;
    __fc_vla_free((void *)volArray);
  }
  __retres = 1;
  return_label: return __retres;
}