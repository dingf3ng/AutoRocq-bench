// Common logic constants needed by Frama-C standard library specs
/*@ logic integer F_OK = 0; */
/*@ logic integer R_OK = 4; */
/*@ logic integer W_OK = 2; */
/*@ logic integer X_OK = 1; */
/*@ logic integer __FC_MAX_OPEN_FILES = 1024; */
/*@ logic integer HOST_NAME_MAX = 64; */
/*@ logic integer SEEK_SET = 0; */
/*@ logic integer SEEK_CUR = 1; */
/*@ logic integer SEEK_END = 2; */
/*@ logic integer SSIZE_MAX = 9223372036854775807; */
/*@ logic integer __FC_FOPEN_MAX = 16; */
/*@ logic integer L_tmpnam = 20; */
/*@ logic integer EOF = -1; */
/*@ logic integer __FC_UCHAR_MAX = 255; */

// Errno constants
/*@ logic integer EAGAIN = 11; */
/*@ logic integer EWOULDBLOCK = 11; */
/*@ logic integer EINTR = 4; */
/*@ logic integer EBADF = 9; */
/*@ logic integer EINVAL = 22; */
/*@ logic integer EIO = 5; */
/*@ logic integer ENOSPC = 28; */
/*@ logic integer EPIPE = 32; */
/*@ logic integer ERANGE = 34; */
/*@ logic integer EDOM = 33; */
/*@ logic integer ENOMEM = 12; */
/*@ logic integer EACCES = 13; */
/*@ logic integer EEXIST = 17; */
/*@ logic integer ENOENT = 2; */
/*@ logic integer ENOTDIR = 20; */
/*@ logic integer EISDIR = 21; */
/*@ logic integer EMFILE = 24; */
/*@ logic integer ENFILE = 23; */
/*@ logic integer EFBIG = 27; */
/*@ logic integer EOVERFLOW = 75; */
/*@ logic integer ESPIPE = 29; */
/*@ logic integer ENXIO = 6; */
/*@ logic integer ELOOP = 40; */
/*@ logic integer ENAMETOOLONG = 36; */

// errno variable (global error indicator)
/*@ logic integer errno = 0; */

// Size limits
/*@ logic integer SIZE_MAX = 18446744073709551615; */
/*@ logic integer __FC_SIZE_MAX = 18446744073709551615; */
/*@ logic integer PATH_MAX = 4096; */
/*@ logic integer NAME_MAX = 255; */
/*@ logic integer FILENAME_MAX = 4096; */
/*@ logic integer BUFSIZ = 8192; */
/*@ logic integer TMP_MAX = 238328; */

// Exit status constants
/*@ logic integer EXIT_SUCCESS = 0; */
/*@ logic integer EXIT_FAILURE = 1; */

// Signal constants
/*@ logic integer SIGINT = 2; */
/*@ logic integer SIGTERM = 15; */
/*@ logic integer SIGKILL = 9; */
/*@ logic integer SIGPIPE = 13; */

// Timer constants
/*@ logic integer ITIMER_REAL = 0; */
/*@ logic integer ITIMER_VIRTUAL = 1; */
/*@ logic integer ITIMER_PROF = 2; */

// Timer predicates
/*@ predicate __VALID_ITIMERVAL(struct itimerval *val) = \true; */

// utmp field size constants
/*@ logic integer UT_NAMESIZE = 32; */
/*@ logic integer UT_HOSTSIZE = 256; */
/*@ logic integer UT_LINESIZE = 32; */
/*@ logic integer ut_name = 32; */
/*@ logic integer ut_host = 256; */
/*@ logic integer ut_line = 32; */

// Standard file descriptors
/*@ logic integer STDIN_FILENO = 0; */
/*@ logic integer STDOUT_FILENO = 1; */
/*@ logic integer STDERR_FILENO = 2; */

// Character limits
/*@ logic integer CHAR_BIT = 8; */
/*@ logic integer CHAR_MAX = 127; */
/*@ logic integer CHAR_MIN = -128; */
/*@ logic integer UCHAR_MAX = 255; */
/*@ logic integer SHRT_MAX = 32767; */
/*@ logic integer SHRT_MIN = -32768; */
/*@ logic integer USHRT_MAX = 65535; */
/*@ logic integer INT_MAX = 2147483647; */
/*@ logic integer INT_MIN = -2147483648; */
/*@ logic integer UINT_MAX = 4294967295; */
/*@ logic integer LONG_MAX = 9223372036854775807; */
/*@ logic integer LONG_MIN = -9223372036854775808; */
/*@ logic integer ULONG_MAX = 18446744073709551615; */
/*@ logic integer LLONG_MAX = 9223372036854775807; */
/*@ logic integer LLONG_MIN = -9223372036854775808; */
/*@ logic integer ULLONG_MAX = 18446744073709551615; */


#include "assert.h"
#include "errno.h"
#include "stdlib.h"
struct node {
   int hash ;
   struct node *next ;
};
/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \false;
    exits status: \exit_status ≢ 0;
    ensures never_terminates: \false;
    
    assigns \exit_status \from \nothing;
 */
extern  __attribute__((__noreturn__)) void abort(void);

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"hash_fun.c",4,"0");
  return;
}

/*@ terminates \true;
    exits \false; */
int hash_fun(void)
{
  int tmp;
  tmp = __VERIFIER_nondet_int();
  return tmp;
}

/*@ terminates \true;
    exits \false; */
void append_to_list(struct node **list, int hash)
{
  struct node *tmp_0;
  struct node *node = malloc(sizeof(*tmp_0));
  node->next = *list;
  node->hash = hash;
  *list = node;
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  struct node *list = (struct node *)0;
  int base = __VERIFIER_nondet_int();

  /*@
    loop invariant \true;
    loop assigns list, base;
  */
  while (1) {
    int tmp_1;
    tmp_1 = __VERIFIER_nondet_int();
    if (! tmp_1) break;
    if (base >= 0) 
      if (base <= 1000000) {
        base += 0;
        int hash = hash_fun();
        if (hash > base) 
          /*@ assert rte: signed_overflow: base + 100 <= 2147483647; */
          if (hash < base + 100) append_to_list(& list,hash);
      }
  }

  /*@
    loop invariant \valid(list) || list == \null;
    loop assigns list;
  */
  while (list) {
    if (list->hash >= base) {
      /*@ assert rte: signed_overflow: base + 100 <= 2147483647; */
      /*@ assert reachability: list->hash < base + 100; */
      if (! (list->hash < base + 100)) goto _LAND;
    }
    else _LAND: reach_error();
    list = list->next;
  }
  __retres = 0;
  return __retres;
}
