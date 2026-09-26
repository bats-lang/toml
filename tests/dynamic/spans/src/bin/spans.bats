#include "share/atspre_staload.hats"
#use array as A
#use result as R
#use str as S
#use toml as T

(* The spans of a header, a literal string and a bare value with a
   comment after it, and what get and keys give for them. *)

(* Prints bytes [0, n) of buf *)
fun _pr {l:agz}{m:pos}{i:nat | i <= m} .<m - i>.
  (buf: !$A.arr(byte, l, m), m: int m, i: int i, n: int): void =
  if i >= m then ()
  else if i >= n then ()
  else let
    val () = print! (int2char0(byte2int0($A.get<byte>(buf, i))))
  in _pr(buf, m, i + 1, n) end

fn _sec {ks:pos | ks <= 1048576} (d: !$T.toml_doc, sc: &(@[char][ks]), ks: int ks): void = let
  val @(fs, bs) = $A.freeze<byte>($S.from_char_array(sc, ks))
  val @(s, e) = $T.section_at(d, bs, ks)
  val () = println! ("section ", s, " ", e)
  val () = $A.drop<byte>(fs, bs)
in $A.free<byte>($A.thaw<byte>(fs)) end

fn _val {ks:pos | ks <= 1048576}{kk:pos | kk <= 1048576}
  (d: !$T.toml_doc, sc: &(@[char][ks]), ks: int ks, kc: &(@[char][kk]), kk: int kk): void = let
  val @(fs, bs) = $A.freeze<byte>($S.from_char_array(sc, ks))
  val @(fk, bk) = $A.freeze<byte>($S.from_char_array(kc, kk))
  val @(s, e, q) = $T.value_at(d, bs, ks, bk, kk)
  val buf = $A.alloc<byte>(64)
  val n = (case+ $T.get(d, bs, ks, bk, kk, buf, 64) of | ~$R.some(n) => n | ~$R.none() => 0): int
  val () = print! ("value ", s, " ", e, (if q then " string [" else " bare ["): string)
  val () = _pr(buf, 64, 0, n)
  val () = println! ("]")
  val () = $A.free<byte>(buf)
  val () = $A.drop<byte>(fs, bs)
  val () = $A.free<byte>($A.thaw<byte>(fs))
  val () = $A.drop<byte>(fk, bk)
in $A.free<byte>($A.thaw<byte>(fk)) end

implement main0 () = let
  var input = @[char][72]('x', ' ', '=', ' ', '1', '\n', '\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', ' ', '#', ' ', 'h', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\047', 'l', 'i', 't', '\047', '\n', 'u', 'n', 's', 'a', 'f', 'e', ' ', '=', ' ', 't', 'r', 'u', 'e', ' ', '#', ' ', 'c', '\n', 'k', 'i', 'n', 'd', ' ', '=', ' ', '\042', 'b', 'i', 'n', '\042', '\n', '\133', 'e', 'm', 'p', 't', 'y', ']', '\n')
  val @(fi, bi) = $A.freeze<byte>($S.from_char_array(input, 72))
  val pr = $T.parse(bi, 72)
  val () = $A.drop<byte>(fi, bi)
  val () = $A.free<byte>($A.thaw<byte>(fi))
in
  case+ pr of
  | ~$R.err(_) => println! ("parse error")
  | ~$R.ok(d) => let
      var s0 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
      val () = _sec(d, s0, 7)
      var s1 = @[char][5]('e', 'm', 'p', 't', 'y')
      val () = _sec(d, s1, 5)
      var s2 = @[char][6]('n', 'o', 's', 'u', 'c', 'h')
      val () = _sec(d, s2, 6)
      var s3 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
      var k3 = @[char][4]('n', 'a', 'm', 'e')
      val () = _val(d, s3, 7, k3, 4)
      var s4 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
      var k4 = @[char][6]('u', 'n', 's', 'a', 'f', 'e')
      val () = _val(d, s4, 7, k4, 6)
      var s5 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
      var k5 = @[char][4]('k', 'i', 'n', 'd')
      val () = _val(d, s5, 7, k5, 4)
      var s6 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
      var k6 = @[char][7]('m', 'i', 's', 's', 'i', 'n', 'g')
      val () = _val(d, s6, 7, k6, 7)
      val () = println! ("root keys ", (if $T.has_root_keys(d) then "yes" else "no"): string)
      val () = println! ("bytes ", $T.byte_at(d, 6), " ", $T.byte_at(d, 72), " ", $T.byte_at(d, ~1))
    in $T.toml_free(d) end
end
