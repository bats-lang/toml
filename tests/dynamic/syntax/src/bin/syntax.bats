#include "share/atspre_staload.hats"
#use array as A
#use result as R
#use str as S
#use toml as T

(* syntax_error's offset and message for each case; a newline in the
   message prints as |. The expected output is what the toml crate
   reports (checked through the bats compiler against the Rust bats). *)

fun _pr {l:agz}{m:pos}{i:nat | i <= m} .<m - i>.
  (buf: !$A.arr(byte, l, m), m: int m, i: int i, n: int): void =
  if i >= m then ()
  else if i >= n then ()
  else let
    val b = byte2int0($A.get<byte>(buf, i))
    val () = (if b = 10 then print! ("|") else print! (int2char0(b))): void
  in _pr(buf, m, i + 1, n) end

fn _case {n:pos | n <= 1048576} (cs: &(@[char][n]), n: int n): void = let
  val @(fi, bi) = $A.freeze<byte>($S.from_char_array(cs, n))
  val pr = $T.parse(bi, n)
  val () = $A.drop<byte>(fi, bi)
  val () = $A.free<byte>($A.thaw<byte>(fi))
in
  case+ pr of
  | ~$R.err(_) => println! ("parse error")
  | ~$R.ok(d) => let
      val mb = $A.alloc<byte>(256)
      val @(off, k) = $T.syntax_error(d, mb, 256)
      val () = print! (off, " ")
      val () = _pr(mb, 256, 0, k)
      val () = println! ()
      val () = $A.free<byte>(mb)
    in $T.toml_free(d) end
end

implement main0 () = let
  var c0 = @[char][20]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'x', '\042', '\n')
  val () = _case(c0, 20)
  var c1 = @[char][20]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'x', '\n')
  val () = _case(c1, 20)
  var c2 = @[char][19]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', 'x', '\n')
  val () = _case(c2, 19)
  var c3 = @[char][32]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'x', '\042', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'y', '\042', '\n')
  val () = _case(c3, 32)
  var c4 = @[char][19]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '\042', 'x', '\042', '\n')
  val () = _case(c4, 19)
  var c5 = @[char][11]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', ']', '\n')
  val () = _case(c5, 11)
  var c6 = @[char][27]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'a', '\042', ' ', 'e', 'x', 't', 'r', 'a', '\n')
  val () = _case(c6, 27)
  var c7 = @[char][31]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'a', '\042', '\n', '\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n')
  val () = _case(c7, 31)
  var c8 = @[char][5]('n', 'a', 'm', 'e', '\n')
  val () = _case(c8, 5)
  var c9 = @[char][16]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', '=', ' ', '\042', 'a', '\042', '\n')
  val () = _case(c9, 16)
  var c10 = @[char][18]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\n')
  val () = _case(c10, 18)
  var c11 = @[char][3]('\133', ']', '\n')
  val () = _case(c11, 3)
  var c12 = @[char][23]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'a', '\134', 'q', '\042', '\n')
  val () = _case(c12, 23)
  var c13 = @[char][11]('\133', 'p', 'a', 'c', 'k', ' ', 'a', 'g', 'e', ']', '\n')
  val () = _case(c13, 11)
  var c14 = @[char][60]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'a', '\042', '\n', 'v', ' ', '=', ' ', '\133', '1', ',', ' ', '2', ']', '\n', 't', ' ', '=', ' ', '\173', ' ', 'a', ' ', '=', ' ', '1', ' ', '}', '\n', 'm', ' ', '=', ' ', '\042', '\042', '\042', 'x', '\n', 'y', '\042', '\042', '\042', '\n')
  val () = _case(c14, 60)
  var c15 = @[char][12]('x', ' ', '=', ' ', '1', '\n', 'x', ' ', '=', ' ', '2', '\n')
  val () = _case(c15, 12)
  var c16 = @[char][40]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'a', '\042', '\n', '\133', '\133', 'b', 'i', 'n', ']', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'x', '\042', '\n')
  val () = _case(c16, 40)
  var c17 = @[char][26]('\133', 'p', 'a', 'c', 'k', 'a', 'g', 'e', ']', '\n', 'n', 'a', 'm', 'e', ' ', '=', ' ', '\042', 'a', '\042', ' ', '#', ' ', 'o', 'k', '\n')
  val () = _case(c17, 26)
in end
