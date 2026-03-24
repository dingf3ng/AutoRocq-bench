/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from \nothing;
 */
extern int ( /* missing proto */ __VERIFIER_nondet_int)(void);

/*@ terminates \true;
    exits \false;
    assigns \result;
    assigns \result \from x_0;
 */
extern int ( /* missing proto */ __VERIFIER_assert)(int x_0);

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int in;
  int buf;
  int buflim;
  int inlen = __VERIFIER_nondet_int();
  int bufferlen = __VERIFIER_nondet_int();
  if (! (bufferlen > 1)) goto END;
  if (! (inlen > 0)) goto END;
  if (! (bufferlen < inlen)) goto END;
  buf = 0;
  in = 0;
  /*@ assert rte: signed_overflow: -2147483648 <= bufferlen - 2; */
  buflim = bufferlen - 2;
  /*@
    loop invariant 0 <= buf <= bufferlen;
    loop invariant 0 <= in <= inlen;
    loop invariant buflim == bufferlen - 2;
    loop invariant bufferlen > 1;
    loop invariant inlen > 0;
    loop invariant bufferlen < inlen;
    loop assigns buf, in;
    loop variant inlen - in;
  */
  while (1) {
    int tmp_1;
    tmp_1 = __VERIFIER_nondet_int();
    /*@ assert reachability: (buf < bufferlen) && (in < inlen); */
    if (! tmp_1) break;
    if (buf == buflim) break;
    /*@ assert reachability: 0 <= buf; */
    __VERIFIER_assert(0 <= buf);
    /*@ assert reachability: buf < bufferlen; */
    __VERIFIER_assert(buf < bufferlen);
    /*@ assert rte: signed_overflow: buf + 1 <= 2147483647; */
    buf ++;
    out: /*@ assert rte: signed_overflow: in + 1 <= 2147483647; */
    in ++;
    /*@ assert reachability: 0 <= in; */
    __VERIFIER_assert(0 <= in);
    /*@ assert reachability: in < inlen; */
    __VERIFIER_assert(in < inlen);
  }
  /*@ assert reachability: 0 <= buf; */
  __VERIFIER_assert(0 <= buf);
  /*@ assert reachability: buf < bufferlen; */
  __VERIFIER_assert(buf < bufferlen);
  /*@ assert rte: signed_overflow: buf + 1 <= 2147483647; */
  buf ++;
  /*@ assert reachability: 0 <= buf; */
  __VERIFIER_assert(0 <= buf);
  /*@ assert reachability: buf < bufferlen; */
  __VERIFIER_assert(buf < bufferlen);
  /*@ assert rte: signed_overflow: buf + 1 <= 2147483647; */
  buf ++;
  END: __retres = 0;
  return __retres;
}