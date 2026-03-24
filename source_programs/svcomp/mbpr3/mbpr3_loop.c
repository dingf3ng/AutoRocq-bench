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
  __assert_fail("0","mbpr3.c",(unsigned int)3,"reach_error");
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
    int i;
    unsigned long __lengthof_volArray;
    int MINVAL = 2;
    /*@
    assert
    alloca_bounds: 0 < sizeof(int) * CELLCOUNT <= 18446744073709551615; */
    ;
    /*@ assert rte: signed_overflow: 0 < CELLCOUNT; */
    /*@ assert rte: signed_overflow: CELLCOUNT <= 715827882; */ /* 715827882*3 < 2^31 */
    __lengthof_volArray = (unsigned long)CELLCOUNT;
    int *volArray = __fc_vla_alloc(sizeof(int) * __lengthof_volArray);
    int CCCELVOL3 = 7;
    int CCCELVOL2 = 3;
    int CCCELVOL1 = 1;
    if (CELLCOUNT % 3 != 0) {
      __retres = 1;
      __fc_vla_free((void *)volArray);
      goto return_label;
    }
    assume_abort_if_not(CELLCOUNT % 3 == 0);
    i = 1;
    /*@
      loop invariant outer1_bounds: 1 <= i <= (CELLCOUNT/3)+1;
      loop invariant outer1_range: 0 <= (i-1)*3 <= CELLCOUNT;
      loop assigns i, volArray[0 .. CELLCOUNT-1];
      loop variant (CELLCOUNT/3) - (i-1);
    */
    while (i <= CELLCOUNT / 3) {
      if (CCCELVOL3 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
        /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 3; */
        *(volArray + (i * 3 - 3)) = CCCELVOL3;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
        /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 3; */
        *(volArray + (i * 3 - 3)) = 0;
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 2; */
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 2; */
      *(volArray + (i * 3 - 2)) = *(volArray + (i * 3 - 2));
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 1; */
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 1; */
      *(volArray + (i * 3 - 1)) = *(volArray + (i * 3 - 1));
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
    i = 1;
    /*@
      loop invariant outer2_bounds: 1 <= i <= (CELLCOUNT/3)+1;
      loop invariant outer2_range: 0 <= (i-1)*3 <= CELLCOUNT;
      loop assigns i, volArray[0 .. CELLCOUNT-1];
      loop variant (CELLCOUNT/3) - (i-1);
    */
    while (i <= CELLCOUNT / 3) {
      if (CCCELVOL2 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
        /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 2; */
        *(volArray + (i * 3 - 2)) = CCCELVOL2;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
        /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 2; */
        *(volArray + (i * 3 - 2)) = 0;
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 3; */
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 3; */
      *(volArray + (i * 3 - 3)) = *(volArray + (i * 3 - 3));
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 1; */
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 1; */
      *(volArray + (i * 3 - 1)) = *(volArray + (i * 3 - 1));
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
    i = 1;
    /*@
      loop invariant outer3_bounds: 1 <= i <= (CELLCOUNT/3)+1;
      loop invariant outer3_range: 0 <= (i-1)*3 <= CELLCOUNT;
      loop assigns i, volArray[0 .. CELLCOUNT-1];
      loop variant (CELLCOUNT/3) - (i-1);
    */
    while (i <= CELLCOUNT / 3) {
      if (CCCELVOL1 >= MINVAL) 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
        /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 1; */
        *(volArray + (i * 3 - 1)) = CCCELVOL1;
      else 
        /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
        /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
        /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 1; */
        *(volArray + (i * 3 - 1)) = 0;
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 2; */
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 2; */
      *(volArray + (i * 3 - 2)) = *(volArray + (i * 3 - 2));
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 3; */
      /*@ assert rte: signed_overflow: -2147483648 <= i * 3; */
      /*@ assert rte: signed_overflow: i * 3 <= 2147483647; */
      /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 3) - 3; */
      *(volArray + (i * 3 - 3)) = *(volArray + (i * 3 - 3));
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
    i = 0;
    /*@
      loop invariant scan_bounds: 0 <= i <= CELLCOUNT;
      loop invariant scan_prefix_ok:
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