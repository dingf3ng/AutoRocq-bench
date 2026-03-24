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
#include "getopt.h"
#include "stdarg.h"
#include "stdint.h"
#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "strings.h"
#include "sys/select.h"
#include "sys/time.h"
// #include "unistd.h"
// Declare only the functions we need instead of including unistd.h
extern long write(int fd, void const *buf, unsigned long count);
// #include "utmp.h"
// Declare utmp struct to avoid include issues
struct utmp { int dummy; };
/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern long __VERIFIER_nondet_long(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern unsigned long __VERIFIER_nondet_ulong(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int __VERIFIER_nondet_int(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern char __VERIFIER_nondet_char(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern short __VERIFIER_nondet_short(void);

/*@ terminates \false;
    exits status: \exit_status ≢ 0;
    ensures never_terminates: \false;
    
    assigns \exit_status \from \nothing;
 */
extern  __attribute__((__noreturn__)) void abort(void);

/*@ terminates \true;
    exits \false; */
void assume_abort_if_not(int cond)
{
  if (! cond) abort();
  return;
}

/*@ terminates \true;
    exits \false; */
void reach_error(void)
{
  __FC_assert(0 != 0,"busybox_sv_comp.h",14,"0");
  return;
}

static char *bb_get_last_path_component_nostrip(char const *path);

static char *bb_get_last_path_component_strip(char *path);

static void bb_show_usage(void);

static long full_write(int fd, void const *buf, unsigned long len);

static char *last_char_is(char const *s, int c);

static long safe_write(int fd, void const *buf, unsigned long count);

static char const *applet_name;
static int bb_errno_location;
static int * const bb_errno = & bb_errno_location;
/*@ terminates \true;
    exits \false; */
void syslog(int priority, char const *format, void * const *__va_params)
{
  return;
}

/*@ terminates \true;
    exits \false; */
int __main(int argc, char **argv)
{
  int __retres;
  unsigned long m;
  unsigned long n;
  char *s;
  int tmp_statement_expression_1;
  _Bool tmp_if_expr_2;
  int tmp_if_expr_5;
  int tmp_statement_expression_3;
  int return_value___builtin_strcmp_4;
  int tmp_statement_expression_6;
  long return_value_full_write_9;
  if (! (*(argv + 1l) == (char *)0)) {
    unsigned long basename_main__s1_len;
    unsigned long __s2_len;
    if ((_Bool)1) {
      int tmp;
      if (! ((unsigned long)("--" + 1l) + - ((unsigned long)"--") == 1ul)) 
        goto __CPROVER_DUMP_L3;
      __s2_len = strlen("--");
      if (__s2_len < (unsigned long)4) tmp = 1 != 0; else tmp = 0 != 0;
      tmp_if_expr_2 = (_Bool)(tmp != 0);
    }
    else {
      __CPROVER_DUMP_L3: ;
      tmp_if_expr_2 = (_Bool)(0 != 0);
    }
    if (! ((int)tmp_if_expr_2 == (int)((_Bool)0))) {
      char const *__s2;
      int __result;
      __s2 = (char const *)*(argv + (long)1);
      /*@ assert
          rte: signed_overflow:
            -2147483648 <= (int)*("--" + 0) - (int)*(__s2 + 0);
      */
      /*@ assert
          rte: signed_overflow:
            (int)*("--" + 0) - (int)*(__s2 + 0) <= 2147483647;
      */
      __result = (int)*("--" + (long)0) - (int)*(__s2 + (long)0);
      if (__s2_len > 0ul) 
        if (__result == 0) {
          /*@ assert
              rte: signed_overflow:
                -2147483648 <= (int)*("--" + 1) - (int)*(__s2 + 1);
          */
          /*@ assert
              rte: signed_overflow:
                (int)*("--" + 1) - (int)*(__s2 + 1) <= 2147483647;
          */
          __result = (int)*("--" + (long)1) - (int)*(__s2 + (long)1);
          if (__s2_len > 1ul) 
            if (__result == 0) {
              /*@ assert
                  rte: signed_overflow:
                    -2147483648 <= (int)*("--" + 2) - (int)*(__s2 + 2);
              */
              /*@ assert
                  rte: signed_overflow:
                    (int)*("--" + 2) - (int)*(__s2 + 2) <= 2147483647;
              */
              __result = (int)*("--" + (long)2) - (int)*(__s2 + (long)2);
              if (__s2_len > 2ul) 
                /*@ assert reachability: !(__result == 0); */
                if (__result == 0) reach_error();
            }
        }
      tmp_statement_expression_3 = __result;
      /*@ assert
          rte: signed_overflow: -2147483647 <= tmp_statement_expression_3;
      */
      tmp_if_expr_5 = - tmp_statement_expression_3;
    }
    else {
      return_value___builtin_strcmp_4 = strcmp((char const *)*(argv + (long)1),
                                               "--");
      tmp_if_expr_5 = return_value___builtin_strcmp_4;
    }
    tmp_statement_expression_1 = tmp_if_expr_5;
    if (tmp_statement_expression_1 == 0) {
      argv ++;
      /*@ assert rte: signed_overflow: -2147483648 <= argc - 1; */
      argc --;
    }
  }
  if (4294967294u + (unsigned int)argc >= 2u) {
    __retres = 1;
    goto return_label;
  }
  argv ++;
  s = bb_get_last_path_component_strip(*argv);
  m = strlen((char const *)s);
  argv ++;
  if (! (*argv == (char *)0)) {
    n = strlen((char const *)*argv);
    if (! (n >= m)) {
      unsigned long __s1_len;
      unsigned long basename_main__s2_len;
      int return_value___builtin_strcmp_7;
      return_value___builtin_strcmp_7 = strcmp((char const *)((s + (long)m) - (long)n),
                                               (char const *)*argv);
      tmp_statement_expression_6 = return_value___builtin_strcmp_7;
      if (tmp_statement_expression_6 == 0) m -= n;
    }
  }
  unsigned long tmp_post_8 = m;
  m ++;
  *(s + (long)tmp_post_8) = (char)10;
  return_value_full_write_9 = full_write(1,(void const *)s,m);
  __retres = return_value_full_write_9 != (long)m;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
static char *bb_get_last_path_component_nostrip(char const *path)
{
  char *__retres;
  char *slash;
  _Bool tmp_if_expr_2;
  _Bool tmp_if_expr_1;
  slash = strrchr(path,47);
  if (slash == (char *)0) tmp_if_expr_2 = (_Bool)(1 != 0);
  else {
    int tmp_0;
    if ((void *)slash == (void *)path) {
      int tmp;
      if (! ((int)*(slash + (long)1) != 0)) tmp = 1 != 0; else tmp = 0 != 0;
      tmp_if_expr_1 = (_Bool)(tmp != 0);
    }
    else tmp_if_expr_1 = (_Bool)(0 != 0);
    if ((int)tmp_if_expr_1 != (int)((_Bool)0)) tmp_0 = 1 != 0;
    else tmp_0 = 0 != 0;
    tmp_if_expr_2 = (_Bool)(tmp_0 != 0);
  }
  if (! ((int)tmp_if_expr_2 == (int)((_Bool)0))) {
    __retres = (char *)path;
    goto return_label;
  }
  __retres = slash + (long)1;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
static char *bb_get_last_path_component_strip(char *path)
{
  char *slash;
  char *tmp_post_1;
  char *return_value_bb_get_last_path_component_nostrip_2;
  slash = last_char_is((char const *)path,47);
  if (! (slash == (char *)0)) 
    /*@
      loop invariant 0 <= (slash - path) <= 10000;
      loop assigns slash, *slash;
      loop variant (slash - path);
    */
    while ((int)*slash == 47) {
      if (slash == path) break;
      tmp_post_1 = slash;
      slash --;
      *tmp_post_1 = (char)0;
    }
  return_value_bb_get_last_path_component_nostrip_2 = bb_get_last_path_component_nostrip
  ((char const *)path);
  return return_value_bb_get_last_path_component_nostrip_2;
}

/*@ terminates \true;
    exits \false; */
static void bb_show_usage(void)
{
  return;
}

/*@ terminates \true;
    exits \false; */
static long full_write(int fd, void const *buf, unsigned long len)
{
  long __retres;
  long cc;
  long total = (long)0;
  /*@
    loop invariant 0 <= total <= 9223372036854775807;
    loop assigns total, buf, len, cc;
    loop variant len;
  */
  while (! (len == 0ul)) {
    cc = safe_write(fd,buf,len);
    if (cc < 0l) {
      if (! (total == 0l)) {
        __retres = total;
        goto return_label;
      }
      __retres = cc;
      goto return_label;
    }
    /*@ assert rte: signed_overflow: -9223372036854775808 <= total + cc; */
    /*@ assert rte: signed_overflow: total + cc <= 9223372036854775807; */
    total += cc;
    buf = (void const *)((char const *)buf + cc);
    len -= (unsigned long)cc;
  }
  __retres = total;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
static char *last_char_is(char const *s, int c)
{
  char *__retres;
  if (! (s == (char const *)0)) 
    if (! ((int)*s == 0)) {
      unsigned long sz;
      unsigned long return_value_strlen_1;
      return_value_strlen_1 = strlen(s);
      sz = return_value_strlen_1 - (unsigned long)1;
      s += (long)sz;
      if ((int)*s == c) {
        __retres = (char *)s;
        goto return_label;
      }
    }
  __retres = (char *)0;
  return_label: return __retres;
}

/*@ terminates \true;
    exits \false; */
static long safe_write(int fd, void const *buf, unsigned long count)
{
  long n;
  _Bool tmp_if_expr_1;
  /*@
    loop assigns n;
    loop variant 1;
  */
  while (1) {
    n = write(fd,buf,count);
    if (n < 0l) {
      int tmp;
      if (*bb_errno == 4) tmp = 1 != 0; else tmp = 0 != 0;
      tmp_if_expr_1 = (_Bool)(tmp != 0);
    }
    else tmp_if_expr_1 = (_Bool)(0 != 0);
    if (! ((int)tmp_if_expr_1 != (int)((_Bool)0))) break;
  }
  return n;
}

static struct utmp dummy_utmp;
/*@ terminates \true;
    exits \false; */
int main(void)
{
  int tmp_1;
  char *a = malloc((size_t)11);
  *(a + 10) = (char)0;
  {
    int i = 0;
    /*@
      loop invariant 0 <= i <= 10;
      loop assigns i, a[0..9];
      loop variant 10 - i;
    */
    while (i < 10) {
      *(a + i) = __VERIFIER_nondet_char();
      /*@ assert rte: signed_overflow: i + 1 <= 2147483647; */
      i ++;
    }
  }
  applet_name = (char const *)a;
  bb_errno_location = __VERIFIER_nondet_int();
  optind = 1;
  int argc = __VERIFIER_nondet_int();
  if (argc >= 1) 
    if (argc <= 10000) tmp_1 = 1; else tmp_1 = 0;
  else tmp_1 = 0;
  assume_abort_if_not(tmp_1);
  /*@ assert rte: signed_overflow: argc + 1 <= 2147483647; */
  char **argv = malloc((unsigned long)(argc + 1) * sizeof(char *));
  /*@ assert rte: signed_overflow: argc + 1 <= 2147483647; */
  char **mem_track = malloc((unsigned long)(argc + 1) * sizeof(char *));
  *(argv + argc) = (char *)0;
  {
    int i_0 = 0;
    /*@
      loop invariant 0 <= i_0 <= argc;
      loop assigns i_0, argv[0..argc-1], mem_track[0..argc-1];
      loop variant argc - i_0;
    */
    while (i_0 < argc) {
      *(argv + i_0) = (char *)malloc((size_t)11);
      *(mem_track + i_0) = *(argv + i_0);
      *(*(argv + i_0) + 10) = (char)0;
      {
        int j = 0;
        /*@
          loop invariant 0 <= j <= 10;
          loop assigns j, (*(argv + i_0))[0..9];
          loop variant 10 - j;
        */
        while (j < 10) {
          *(*(argv + i_0) + j) = __VERIFIER_nondet_char();
          /*@ assert rte: signed_overflow: j + 1 <= 2147483647; */
          j ++;
        }
      }
      /*@ assert rte: signed_overflow: i_0 + 1 <= 2147483647; */
      i_0 ++;
    }
  }
  int res = __main(argc,argv);
  {
    int i_1 = 0;
    /*@
      loop invariant 0 <= i_1 <= argc;
      loop assigns i_1;
      loop variant argc - i_1;
    */
    while (i_1 < argc) {
      free((void *)*(mem_track + i_1));
      /*@ assert rte: signed_overflow: i_1 + 1 <= 2147483647; */
      i_1 ++;
    }
  }
  free((void *)mem_track);
  free((void *)argv);
  free((void *)a);
  return res;
}
