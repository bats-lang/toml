#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use result as R
#use str as S
#use toml as T

(* bats-lang/toml#46: parse_whole says when a document does not fit
   (limits); parse, kept for one version, still cuts (parse-old). *)

fn _put {l:agz}{n:pos}{i:nat | i < n}
  (buf: !$A.arr(byte, l, n), i: int i, c: int): void =
  $A.set<byte>(buf, i, $A.int2byte(c))

(* Every byte of buf[i, n) is c. *)
fun _fill {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (buf: !$A.arr(byte, l, n), n: int n, i: int i, c: int): void =
  if i >= n then ()
  else let val () = _put(buf, i, c) in _fill(buf, n, i + 1, c) end

(* Lines "a=1\n", j of them from the line j. *)
fun _lines {l:agz}{n:pos}{m:nat | 4 * m <= n}{j:nat | j <= m} .<m - j>.
  (buf: !$A.arr(byte, l, n), j: int j, m: int m): void =
  if j >= m then ()
  else let
    val () = _put(buf, 4 * j, 97)
    val () = _put(buf, 4 * j + 1, 61)
    val () = _put(buf, 4 * j + 2, 49)
    val () = _put(buf, 4 * j + 3, 10)
  in _lines(buf, j + 1, m) end

fn _try {l:agz}{n:pos}{len:nat | len <= n}
  (name: string, buf: $A.arr(byte, l, n), len: int len): void = let
  val @(fz, bw) = $A.freeze<byte>(buf)
  val whole = $T.parse_whole(bw, len)
  val () = print! (name, " whole: ")
  val () = (case+ whole of
    | ~$T.Whole(d) => let val () = println! ("Whole") in $T.toml_free(d) end
    | ~$T.Too_many_bytes() => println! ("Too_many_bytes")
    | ~$T.Too_many_entries() => println! ("Too_many_entries")): void
  val old = $T.parse(bw, len)
  val () = print! (name, " old: ")
  val () = (case+ old of
    | ~$R.ok(d) => let val () = println! ("ok") in $T.toml_free(d) end
    | ~$R.err(_) => println! ("err")): void
  val () = $A.drop<byte>(fz, bw)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in end

implement main0 () = let
  (* 65536 bytes of comment fit; 65537 do not *)
  val b0 = $A.alloc<byte>(65537)
  val () = _fill(b0, 65537, 0, 35)
  val () = _try("bytes-65536", b0, 65536)
  val b1 = $A.alloc<byte>(65537)
  val () = _fill(b1, 65537, 0, 35)
  val () = _try("bytes-65537", b1, 65537)
  (* 256 entries fit; the 257th does not *)
  val b2 = $A.alloc<byte>(1028)
  val () = _lines(b2, 0, 256)
  val () = _try("entries-256", b2, 1024)
  val b3 = $A.alloc<byte>(1028)
  val () = _lines(b3, 0, 257)
  val () = _try("entries-257", b3, 1028)
  (* 256 entries and a comment after them: nothing is left out *)
  val b4 = $A.alloc<byte>(1026)
  val () = _lines(b4, 0, 256)
  val () = _put(b4, 1024, 35)
  val () = _put(b4, 1025, 10)
  val () = _try("entries-256-comment", b4, 1026)
in end
