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
  __assert_fail("0","nr5.c",(unsigned int)3,"reach_error");
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
    int j;
    unsigned long __lengthof_volArray;
    int DEFAULTVALUE = 1;
    int MINVAL = 2;
    /*@
    assert
    alloca_bounds: 0 < sizeof(int) * CELLCOUNT <= 18446744073709551615; */
    ;
    /*@ assert alloca_bounds: CELLCOUNT > 1; */
    /*@ assert alloca_bounds: CELLCOUNT <= 2147483646; */
    assume_abort_if_not(CELLCOUNT <= 2147483646);
    __lengthof_volArray = (unsigned long)CELLCOUNT;
    int *volArray = __fc_vla_alloc(sizeof(int) * __lengthof_volArray);
    if (CELLCOUNT % 5 != 0) {
      __retres = 1;
      __fc_vla_free((void *)volArray);
      goto return_label;
    }
    assume_abort_if_not(CELLCOUNT % 5 == 0);
    i = 1;
    /*@
      loop invariant outer_i_bounds: 1 <= i && i <= (CELLCOUNT/5) + 1;
      loop invariant outer_even_filled:
        \forall integer q; 0 <= q < i-1 ==> 0 <= 5*q < CELLCOUNT && volArray[5*q] == 5;
      loop invariant outer_fill_4:
        \forall integer q; 0 <= q < i-1 && 5*q+1 < CELLCOUNT ==> volArray[5*q+1] == 4;
      loop invariant outer_fill_3:
        \forall integer q; 0 <= q < i-1 && 5*q+2 < CELLCOUNT ==> volArray[5*q+2] == 3;
      loop invariant outer_fill_2:
        \forall integer q; 0 <= q < i-1 && 5*q+3 < CELLCOUNT ==> volArray[5*q+3] == 2;
      loop invariant outer_fill_1:
        \forall integer q; 0 <= q < i-1 && 5*q+4 < CELLCOUNT ==> volArray[5*q+4] == 0;
      loop invariant outer_5i_nonneg: 0 <= 5*i;
      loop invariant outer_5i_upper: 5*i <= CELLCOUNT + 5;
      loop assigns i, j, volArray[0 .. CELLCOUNT-1];
      loop variant (CELLCOUNT/5) - (i-1);
    */
    while (i <= CELLCOUNT / 5) {
      j = 5;
      /*@
        loop invariant inner_j_bounds: 1 <= j && j <= 5;
        loop invariant inner_index_bounds: 0 <= (5*i - j) < CELLCOUNT;
        loop assigns j, volArray[0 .. CELLCOUNT-1];
        loop variant j;
      */
      while (j >= 1) {
        if (j >= MINVAL) 
          /*@ assert rte: signed_overflow: -2147483648 <= i * 5; */
          /*@ assert rte: signed_overflow: i * 5 <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 5) - j; */
          /*@ assert rte: signed_overflow: (int)(i * 5) - j <= 2147483647; */
          *(volArray + (i * 5 - j)) = j;
        else 
          /*@ assert rte: signed_overflow: -2147483648 <= i * 5; */
          /*@ assert rte: signed_overflow: i * 5 <= 2147483647; */
          /*@ assert rte: signed_overflow: -2147483648 <= (int)(i * 5) - j; */
          /*@ assert rte: signed_overflow: (int)(i * 5) - j <= 2147483647; */
          *(volArray + (i * 5 - j)) = 0;
        /*@ assert rte: signed_overflow: -2147483648 <= j - 1; */
        j --;
      }
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
    /*@ assert fill_all_5:
          \forall integer q; 0 <= q < CELLCOUNT/5 ==> volArray[5*q] == 5; */
    /*@ assert fill_all_4:
          \forall integer q; 0 <= q && 5*q+1 < CELLCOUNT ==> volArray[5*q+1] == 4; */
    /*@ assert fill_all_3:
          \forall integer q; 0 <= q && 5*q+2 < CELLCOUNT ==> volArray[5*q+2] == 3; */
    /*@ assert fill_all_2:
          \forall integer q; 0 <= q && 5*q+3 < CELLCOUNT ==> volArray[5*q+3] == 2; */
    /*@ assert fill_all_1:
          \forall integer q; 0 <= q && 5*q+4 < CELLCOUNT ==> volArray[5*q+4] == 0; */
    i = 0;
    /*@
      loop invariant scan_i_bounds: 0 <= i && i <= CELLCOUNT;
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