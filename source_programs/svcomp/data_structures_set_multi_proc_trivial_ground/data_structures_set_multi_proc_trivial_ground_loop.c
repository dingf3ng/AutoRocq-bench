#include "assert.h"
/*@ terminates \true;
    exits \false;
    assigns \nothing; */
extern void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"data_structures_set_multi_proc_trivial_ground.c",3,"0");
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
    exits \false; */
int insert(int *set, int size, int value)
{
  int __retres;
  *(set + size) = value;
  /*@ assert rte: signed_overflow: size + 1 <= 2147483647; */
  __retres = size + 1;
  return __retres;
}

/*@ terminates \true;
    exits \false; */
int elem_exists(int *set, int size, int value)
{
  int __retres;
  int i;
  i = 0;
  /*@
    loop invariant 0 <= i <= size;
    loop assigns i;
    loop variant size - i;
  */
  while (i < size) {
    if (*(set + i) == value) {
      __retres = 1;
      goto return_label;
    }
    /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
    i ++;
  }
  __retres = 0;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int set[100000];
  int x;
  int y;
  int values[100000];
  int v;
  int n = 0;
  x = 0;
  /*@
    loop invariant 0 <= x <= 100000;
    loop assigns x, set[0..99999];
    loop variant 100000 - x;
  */
  while (x < 100000) {
    set[x] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= n <= 100000;
    loop assigns x, y;
    loop variant n - x;
  */
  while (x < n) {
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    y = x + 1;
    /*@
      loop invariant x + 1 <= y <= n;
      loop assigns y;
      loop variant n - y;
    */
    while (y < n) {
      /*@ assert reachability: set[x] != set[y]; */
      __VERIFIER_assert(set[x] != set[y]);
      /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
      y ++;
    }
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  v = 0;
  /*@
    loop invariant 0 <= v <= 100000;
    loop assigns v, values[0..99999];
    loop variant 100000 - v;
  */
  while (v < 100000) {
    values[v] = __VERIFIER_nondet_int();
    /*@ assert rte: signed_overflow: v + 1 <= 2147483647; */
    v ++;
  }
  v = 0;
  /*@
    loop invariant 0 <= v <= 100000;
    loop assigns v, n, x, y, set[0..99999];
    loop variant 100000 - v;
  */
  while (v < 100000) {
    {
      int tmp;
      tmp = elem_exists(set,n,values[v]);
      if (tmp) n = insert(set,n,values[v]);
      x = 0;
      /*@
        loop invariant 0 <= x <= n <= 100000;
        loop assigns x, y;
        loop variant n - x;
      */
      while (x < n) {
        /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
        y = x + 1;
        /*@
          loop invariant x + 1 <= y <= n;
          loop assigns y;
          loop variant n - y;
        */
        while (y < n) {
          /*@ assert reachability: set[x] != set[y]; */
          __VERIFIER_assert(set[x] != set[y]);
          /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
          y ++;
        }
        /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
        x ++;
      }
    }
    /*@ assert rte: signed_overflow: v + 1 <= 2147483647; */
    v ++;
  }
  x = 0;
  /*@
    loop invariant 0 <= x <= n <= 100000;
    loop assigns x, y;
    loop variant n - x;
  */
  while (x < n) {
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    y = x + 1;
    /*@
      loop invariant x + 1 <= y <= n;
      loop assigns y;
      loop variant n - y;
    */
    while (y < n) {
      /*@ assert reachability: set[x] != set[y]; */
      __VERIFIER_assert(set[x] != set[y]);
      /*@ assert rte: signed_overflow: y + 1 <= 2147483647; */
      y ++;
    }
    /*@ assert rte: signed_overflow: x + 1 <= 2147483647; */
    x ++;
  }
  __retres = 0;
  return __retres;
}