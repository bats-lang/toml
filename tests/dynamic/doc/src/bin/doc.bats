#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use result as R
#use str as S
#use toml as T

(* Prints bytes [0, n) of buf; a 0 byte prints as '|'. *)
fun _print {l:agz}{m:pos}{i:nat | i <= m} .<m - i>.
  (buf: !$A.arr(byte, l, m), m: int m, i: int i, n: int): void =
  if i >= m then ()
  else if i >= n then ()
  else let
    val b = byte2int0($A.get<byte>(buf, i))
    val () = (if b = 0 then print! ("|") else print! (int2char0(b))): void
  in _print(buf, m, i + 1, n) end

fn _get {ks:pos | ks <= 1048576}{kk:pos | kk <= 1048576}{m:pos | m <= 1048576}
  (d: !$T.toml_doc, sc: &(@[char][ks]), ks: int ks, kc: &(@[char][kk]), kk: int kk, m: int m): void = let
  val @(fs, bs) = $A.freeze<byte>($S.from_char_array(sc, ks))
  val @(fk, bk) = $A.freeze<byte>($S.from_char_array(kc, kk))
  val buf = $A.alloc<byte>(m)
  val r = $T.get(d, bs, ks, bk, kk, buf, m)
  val n = (case+ r of | ~$R.some(n) => n | ~$R.none() => ~1): int
  val () = (if n < 0 then print! ("get none") else print! ("get ", n, " [")): void
  val () = _print(buf, m, 0, n)
  val () = (if n < 0 then println! () else println! ("]")): void
  val () = $A.free<byte>(buf)
  val () = $A.drop<byte>(fs, bs)
  val () = $A.free<byte>($A.thaw<byte>(fs))
  val () = $A.drop<byte>(fk, bk)
  val () = $A.free<byte>($A.thaw<byte>(fk))
in end

fn _keys {ks:pos | ks <= 1048576}{m:pos | m <= 1048576}
  (d: !$T.toml_doc, sc: &(@[char][ks]), ks: int ks, m: int m): void = let
  val @(fs, bs) = $A.freeze<byte>($S.from_char_array(sc, ks))
  val buf = $A.alloc<byte>(m)
  val r = $T.keys(d, bs, ks, buf, m)
  val n = (case+ r of | ~$R.some(n) => n | ~$R.none() => ~1): int
  val () = (if n < 0 then print! ("keys none") else print! ("keys ", n, " [")): void
  val () = _print(buf, m, 0, n)
  val () = (if n < 0 then println! () else println! ("]")): void
  val () = $A.free<byte>(buf)
  val () = $A.drop<byte>(fs, bs)
  val () = $A.free<byte>($A.thaw<byte>(fs))
in end

implement main0 () = let
  var input = @[char][149]('#', ' ', 'c', 'o', 'm', 'm', 'e', 'n', 't', '\n', '\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'h', 'e', 'l', 'l', 'o', '\042', '\n', 'k', 'i', 'n', 'd', '=', '\042', 'l', 'i', 'b', '\042', ' ', ' ', '\n', '\t', 'u', 'n', 's', 'a', 'f', 'e', ' ', '=', ' ', 'f', 'a', 'l', 's', 'e', '\r', '\n', '\133', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'i', 'e', 's', ']', '\n', '\042', 'a', 'r', 'i', 't', 'h', '\042', ' ', '=', ' ', '\042', '\042', '\n', 's', 't', 'r', ' ', '=', ' ', '\042', 'a', ' ', 'b', '\042', '\n', '\133', 'e', 'm', 'p', 't', 'y', ']', '\n', 'x', ' ', '=', ' ', '\n', 'n', 'o', 'e', 'q', ' ', 'l', 'i', 'n', 'e', '\n', '\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'v', 'e', 'r', 's', 'i', 'o', 'n', ' ', '=', ' ', '3')
  val @(fi, bi) = $A.freeze<byte>($S.from_char_array(input, 149))
  val pr = $T.parse(bi, 149)
  val () = $A.drop<byte>(fi, bi)
  val () = $A.free<byte>($A.thaw<byte>(fi))
in
  case+ pr of
  | ~$R.err(_) => println! ("parse error")
  | ~$R.ok(d) => let
  var s0 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  var k0 = @[char][4]('n', 'a', 'm', 'e')
  val () = _get(d, s0, 7, k0, 4, 64)
  var s1 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  var k1 = @[char][4]('k', 'i', 'n', 'd')
  val () = _get(d, s1, 7, k1, 4, 64)
  var s2 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  var k2 = @[char][6]('u', 'n', 's', 'a', 'f', 'e')
  val () = _get(d, s2, 7, k2, 6, 64)
  var s3 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  var k3 = @[char][7]('v', 'e', 'r', 's', 'i', 'o', 'n')
  val () = _get(d, s3, 7, k3, 7, 64)
  var s4 = @[char][12]('d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'i', 'e', 's')
  var k4 = @[char][5]('a', 'r', 'i', 't', 'h')
  val () = _get(d, s4, 12, k4, 5, 64)
  var s5 = @[char][12]('d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'i', 'e', 's')
  var k5 = @[char][3]('s', 't', 'r')
  val () = _get(d, s5, 12, k5, 3, 64)
  var s6 = @[char][5]('e', 'm', 'p', 't', 'y')
  var k6 = @[char][1]('x')
  val () = _get(d, s6, 5, k6, 1, 64)
  var s7 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  var k7 = @[char][7]('m', 'i', 's', 's', 'i', 'n', 'g')
  val () = _get(d, s7, 7, k7, 7, 64)
  var s8 = @[char][6]('n', 'o', 's', 'u', 'c', 'h')
  var k8 = @[char][4]('n', 'a', 'm', 'e')
  val () = _get(d, s8, 6, k8, 4, 64)
  var s9 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  var k9 = @[char][4]('n', 'a', 'm', 'e')
  val () = _get(d, s9, 7, k9, 4, 3)
  var s10 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  val () = _keys(d, s10, 7, 256)
  var s11 = @[char][12]('d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'i', 'e', 's')
  val () = _keys(d, s11, 12, 256)
  var s12 = @[char][5]('e', 'm', 'p', 't', 'y')
  val () = _keys(d, s12, 5, 256)
  var s13 = @[char][7]('p', 'a', 'c', 'k', 'a', 'g', 'e')
  val () = _keys(d, s13, 7, 6)
    in $T.toml_free(d) end
end
