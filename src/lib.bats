(* toml -- minimal TOML parser *)
(* Handles [section], key = "value", key = true/false, # comments. *)
(* Pure computation. No $UNSAFE, no assume. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use str as S
#use result as R

(* ============================================================
   Constants
   ============================================================ *)

#pub stadef TOML_MAX_BUF = 65536
#pub stadef TOML_ENTRY_INTS = 1536

#define MAX_ENTRIES 256
#define QUOTE 34
#define HASH 35
#define EQUALS 61
#define LBRACKET 91
#define RBRACKET 93
#define NEWLINE 10
#define SPACE 32
#define TAB 9
#define CR 13

(* ============================================================
   toml_doc: owns the parsed data
   ============================================================ *)

#pub datavtype toml_doc =
  | {lb:agz}{le:agz}
    toml_doc_mk of (
      $A.arr(byte, lb, TOML_MAX_BUF),
      int,
      $A.arr(int, le, TOML_ENTRY_INTS),
      int
    )

(* ============================================================
   API
   ============================================================ *)

#pub fun parse
  {lb:agz}{n:pos}
  (input: !$A.borrow(byte, lb, n), len: int n): $R.result(toml_doc, int)

#pub fun get
  {lb:agz}{nb:pos}{lk:agz}{nk:pos}{lo:agz}{mo:pos}
  (doc: !toml_doc,
   section: !$A.borrow(byte, lb, nb), slen: int nb,
   key: !$A.borrow(byte, lk, nk), klen: int nk,
   buf: !$A.arr(byte, lo, mo), max: int mo): $R.option(int)

#pub fun keys
  {lb:agz}{nb:pos}{lo:agz}{mo:pos}
  (doc: !toml_doc,
   section: !$A.borrow(byte, lb, nb), slen: int nb,
   buf: !$A.arr(byte, lo, mo), max: int mo): $R.option(int)

#pub fun toml_free
  (doc: toml_doc): void

(* ============================================================
   Safe read/write helpers using g1ofg0 + bounds branching
   ============================================================ *)

fn _to_nat(x: int): [n:nat] int(n) = let
  val v = g1ofg0(x)
in
  if v >= 0 then v else 0
end

fn _to_byte(x: int): [v:nat | v < 256] int(v) = let
  val v = g1ofg0(x)
in
  if v >= 0 then if v < 256 then v else 0 else 0
end

fn _rd_bw {l:agz}
  (buf: !$A.borrow(byte, l, TOML_MAX_BUF), pos: int): int = let
  val i = g1ofg0(pos)
in
  if i >= 0 then if i < 65536 then byte2int0($A.read<byte>(buf, i)) else 0 else 0
end

fn _rd_arr {l:agz}
  (arr: !$A.arr(byte, l, TOML_MAX_BUF), pos: int): int = let
  val i = g1ofg0(pos)
in
  if i >= 0 then if i < 65536 then byte2int0($A.get<byte>(arr, i)) else 0 else 0
end

fn _wr_arr {l:agz}
  (arr: !$A.arr(byte, l, TOML_MAX_BUF), pos: int, b: byte): void = let
  val i = g1ofg0(pos)
in
  if i >= 0 then if i < 65536 then $A.set<byte>(arr, i, b) else () else ()
end

fn _rd_int {l:agz}{n:pos}
  (arr: !$A.arr(int, l, n), pos: int, sz: int n): int = let
  val i = g1ofg0(pos)
in
  if i >= 0 then if $AR.lt_g1(i, sz) then $A.get<int>(arr, i) else 0 else 0
end

fn _wr_int {l:agz}{n:pos}
  (arr: !$A.arr(int, l, n), pos: int, v: int, sz: int n): void = let
  val i = g1ofg0(pos)
in
  if i >= 0 then if $AR.lt_g1(i, sz) then $A.set<int>(arr, i, v) else () else ()
end

(* ============================================================
   Internal helpers
   ============================================================ *)

fn _is_ws(c: int): bool =
  if $AR.eq_int_int(c, SPACE) then true
  else if $AR.eq_int_int(c, TAB) then true
  else if $AR.eq_int_int(c, CR) then true
  else false

fun _skip_ws
  {lb:agz}{fuel:nat} .<fuel>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF),
   pos: int, fuel: int fuel): int =
  if fuel <= 0 then pos
  else let
    val c = _rd_bw(buf, pos)
  in if _is_ws(c) then _skip_ws(buf, pos + 1, fuel - 1) else pos end

fun _find_char
  {lb:agz}{fuel:nat} .<fuel>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF),
   pos: int, target: int, fuel: int fuel): int =
  if fuel <= 0 then pos
  else let
    val c = _rd_bw(buf, pos)
  in
    if $AR.eq_int_int(c, target) then pos
    else if $AR.eq_int_int(c, NEWLINE) then pos
    else _find_char(buf, pos + 1, target, fuel - 1)
  end

fun _find_eol
  {lb:agz}{fuel:nat} .<fuel>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF),
   pos: int, input_len: int, fuel: int fuel): int =
  if fuel <= 0 then pos
  else if $AR.gte_int_int(pos, input_len) then input_len
  else let
    val c = _rd_bw(buf, pos)
  in if $AR.eq_int_int(c, NEWLINE) then pos else _find_eol(buf, pos + 1, input_len, fuel - 1) end

fun _trim_right_pos
  {lb:agz}{fuel:nat} .<fuel>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF),
   start: int, endp: int, fuel: int fuel): int =
  if fuel <= 0 then endp
  else if $AR.lte_int_int(endp, start) then start
  else let
    val c = _rd_bw(buf, endp - 1)
  in if _is_ws(c) then _trim_right_pos(buf, start, endp - 1, fuel - 1) else endp end

(* Store a single entry. *)
fn _store_entry
  {le:agz}
  (entries: !$A.arr(int, le, TOML_ENTRY_INTS),
   nentries: int,
   sec_off: int, sec_len: int,
   key_off: int, key_len: int,
   val_off: int, val_len: int): int = let
  val base = nentries * 6
  val last = base + 5
in
  if last >= 0 then
    if last < 1536 then let
      val () = _wr_int(entries, base, sec_off, 1536)
      val () = _wr_int(entries, base + 1, sec_len, 1536)
      val () = _wr_int(entries, base + 2, key_off, 1536)
      val () = _wr_int(entries, base + 3, key_len, 1536)
      val () = _wr_int(entries, base + 4, val_off, 1536)
      val () = _wr_int(entries, last, val_len, 1536)
    in nentries + 1 end
    else nentries
  else nentries
end

(* ============================================================
   parse implementation
   ============================================================ *)

implement parse {lb}{n} (input, len) = let
  val doc_buf = $A.alloc<byte>(65536)
  val entries = $A.alloc<int>(1536)

  val actual_len = (if $AR.gt_int_int(len, 65536) then 65536 else g0ofg1(len)): int

  fun copy_input {ld:agz}{lb:agz}{n:pos}{fuel:nat} .<fuel>.
    (dst: !$A.arr(byte, ld, TOML_MAX_BUF),
     src: !$A.borrow(byte, lb, n),
     i: int, actual: int, src_len: int n, fuel: int fuel): void =
    if fuel <= 0 then ()
    else if $AR.gte_int_int(i, actual) then ()
    else let
      val ig = g1ofg0(i)
    in
      if ig >= 0 then
        if $AR.lt_g1(ig, src_len) then let
          val b = $A.read<byte>(src, ig)
          val () = _wr_arr(dst, i, b)
        in copy_input(dst, src, i + 1, actual, src_len, fuel - 1) end
        else ()
      else ()
    end

  val () = copy_input(doc_buf, input, 0, actual_len, len, len)

  val @(fz_buf, bw_buf) = $A.freeze<byte>(doc_buf)

  fun parse_loop
    {lbw:agz}{le:agz}{fuel:nat} .<fuel>.
    (bw: !$A.borrow(byte, lbw, TOML_MAX_BUF),
     entries: !$A.arr(int, le, TOML_ENTRY_INTS),
     pos: int, nentries: int,
     sec_off: int, sec_len: int,
     input_len: int,
     fuel: int fuel): int =
    if fuel <= 0 then nentries
    else if $AR.gte_int_int(pos, input_len) then nentries
    else if $AR.gte_int_int(nentries, MAX_ENTRIES) then nentries
    else let
      val p = _skip_ws(bw, pos, 65536)
    in
      if $AR.gte_int_int(p, input_len) then nentries
      else let
        val c = _rd_bw(bw, p)
      in
        if $AR.eq_int_int(c, NEWLINE) then
          parse_loop(bw, entries, p + 1, nentries, sec_off, sec_len, input_len, fuel - 1)
        else if $AR.eq_int_int(c, HASH) then let
          val eol = _find_eol(bw, p + 1, input_len, 65536)
        in parse_loop(bw, entries, eol + 1, nentries, sec_off, sec_len, input_len, fuel - 1) end
        else if $AR.eq_int_int(c, LBRACKET) then let
          val sec_start = p + 1
          val sec_end = _find_char(bw, sec_start, RBRACKET, 65536)
          val new_sec_len = $AR.sub_int_int(sec_end, sec_start)
          val eol = _find_eol(bw, sec_end + 1, input_len, 65536)
        in parse_loop(bw, entries, eol + 1, nentries, sec_start, new_sec_len, input_len, fuel - 1) end
        else let
          val key_start = p
          val eq_pos = _find_char(bw, p, EQUALS, 65536)
        in
          if $AR.gte_int_int(eq_pos, input_len) then let
            val eol = _find_eol(bw, p, input_len, 65536)
          in parse_loop(bw, entries, eol + 1, nentries, sec_off, sec_len, input_len, fuel - 1) end
          else let
            val key_end = _trim_right_pos(bw, key_start, eq_pos, 65536)
            val key_len = $AR.sub_int_int(key_end, key_start)
            val val_start0 = _skip_ws(bw, eq_pos + 1, 65536)
            val eol = _find_eol(bw, val_start0, input_len, 65536)
          in
            if $AR.gte_int_int(val_start0, input_len) then
              parse_loop(bw, entries, eol + 1, nentries, sec_off, sec_len, input_len, fuel - 1)
            else let
              val vc = _rd_bw(bw, val_start0)
            in
              if $AR.eq_int_int(vc, QUOTE) then let
                val str_start = val_start0 + 1
                val str_end = _find_char(bw, str_start, QUOTE, 65536)
                val str_len = $AR.sub_int_int(str_end, str_start)
                val new_n = _store_entry(entries, nentries, sec_off, sec_len, key_start, key_len, str_start, str_len)
              in parse_loop(bw, entries, eol + 1, new_n, sec_off, sec_len, input_len, fuel - 1) end
              else let
                val val_end = _trim_right_pos(bw, val_start0, eol, 65536)
                val val_len = $AR.sub_int_int(val_end, val_start0)
                val new_n = _store_entry(entries, nentries, sec_off, sec_len, key_start, key_len, val_start0, val_len)
              in parse_loop(bw, entries, eol + 1, new_n, sec_off, sec_len, input_len, fuel - 1) end
            end
          end
        end
      end
    end

  val nentries = parse_loop(bw_buf, entries, 0, 0, 0, 0, actual_len, 65536)

  val () = $A.drop<byte>(fz_buf, bw_buf)
  val doc_buf2 = $A.thaw<byte>(fz_buf)

in $R.ok(toml_doc_mk(doc_buf2, actual_len, entries, nentries)) end

(* ============================================================
   get implementation
   ============================================================ *)

implement get {lb}{nb}{lk}{nk}{lo}{mo}
  (doc, section, slen, key, klen, buf, max) = let
  val+ @toml_doc_mk(doc_buf, doc_len, entries, nentries) = doc

  fun cmp_arr_borrow
    {la:agz}{lb2:agz}{nb2:pos}{fuel:nat} .<fuel>.
    (arr: !$A.arr(byte, la, TOML_MAX_BUF),
     arr_off: int,
     borrow: !$A.borrow(byte, lb2, nb2), blen: int nb2,
     count: int, i: int, fuel: int fuel): bool =
    if fuel <= 0 then true
    else if $AR.gte_int_int(i, count) then true
    else let
      val ca = _rd_arr(arr, arr_off + i)
      val ig = g1ofg0(i)
    in
      if ig >= 0 then
        if $AR.lt_g1(ig, blen) then let
          val cb = byte2int0($A.read<byte>(borrow, ig))
        in
          if $AR.neq_int_int(ca, cb) then false
          else cmp_arr_borrow(arr, arr_off, borrow, blen, count, i + 1, fuel - 1)
        end
        else false
      else false
    end

  fun search
    {la:agz}{le:agz}{lb2:agz}{nb2:pos}{lb3:agz}{nb3:pos}{fuel:nat} .<fuel>.
    (doc_buf: !$A.arr(byte, la, TOML_MAX_BUF),
     entries: !$A.arr(int, le, TOML_ENTRY_INTS),
     section: !$A.borrow(byte, lb2, nb2), slen: int nb2,
     key: !$A.borrow(byte, lb3, nb3), klen: int nb3,
     nentries: int, i: int, fuel: int fuel): $R.option(@(int, int)) =
    if fuel <= 0 then $R.none()
    else if $AR.gte_int_int(i, nentries) then $R.none()
    else let
      val base = i * 6
      val last = base + 5
    in
      if last < 0 then $R.none()
      else if last >= 1536 then $R.none()
      else let
        val e_sec_off = _rd_int(entries, base, 1536)
        val e_sec_len = _rd_int(entries, base + 1, 1536)
        val e_key_off = _rd_int(entries, base + 2, 1536)
        val e_key_len = _rd_int(entries, base + 3, 1536)
        val e_val_off = _rd_int(entries, base + 4, 1536)
        val e_val_len = _rd_int(entries, last, 1536)

        val sec_match =
          if $AR.neq_int_int(e_sec_len, slen) then false
          else if $AR.eq_int_int(e_sec_len, 0) then true
          else cmp_arr_borrow(doc_buf, e_sec_off, section, slen, e_sec_len, 0, 65536)

        val key_match =
          if $AR.neq_int_int(e_key_len, klen) then false
          else cmp_arr_borrow(doc_buf, e_key_off, key, klen, e_key_len, 0, 65536)
      in
        if sec_match then
          if key_match then $R.some(@(e_val_off, e_val_len))
          else search(doc_buf, entries, section, slen, key, klen, nentries, i + 1, fuel - 1)
        else search(doc_buf, entries, section, slen, key, klen, nentries, i + 1, fuel - 1)
      end
    end

  val found = search(doc_buf, entries, section, slen, key, klen, nentries, 0, _to_nat(nentries))

  prval () = fold@(doc)
in
  case+ found of
  | ~$R.some(@(voff, vlen)) =>
    if $AR.gt_int_int(vlen, max) then $R.none()
    else let
      val+ @toml_doc_mk(doc_buf2, _, _, _) = doc
      fun copy_val
        {ld:agz}{md:pos}{la:agz}{fuel:nat} .<fuel>.
        (dst: !$A.arr(byte, ld, md), max_d: int md,
         src: !$A.arr(byte, la, TOML_MAX_BUF),
         src_off: int, count: int, i: int, fuel: int fuel): void =
        if fuel <= 0 then ()
        else if $AR.gte_int_int(i, count) then ()
        else let
          val b_src = _rd_arr(src, src_off + i)
          val ig = g1ofg0(i)
        in
          if ig >= 0 then
            if $AR.lt_g1(ig, max_d) then let
              val () = $A.set<byte>(dst, ig, $A.int2byte(_to_byte(b_src)))
            in copy_val(dst, max_d, src, src_off, count, i + 1, fuel - 1) end
            else ()
          else ()
        end
      val vl = _to_nat(vlen)
      val () = copy_val(buf, max, doc_buf2, voff, vlen, 0, vl)
      prval () = fold@(doc)
    in $R.some(vlen) end
  | ~$R.none() => $R.none()
end

(* ============================================================
   keys implementation: list all key names in a section
   ============================================================ *)

implement keys {lb}{nb}{lo}{mo}
  (doc, section, slen, buf, max) = let
  val+ @toml_doc_mk(doc_buf, doc_len, entries, nentries) = doc

  fun cmp_sec
    {la:agz}{lb2:agz}{nb2:pos}{fuel:nat} .<fuel>.
    (arr: !$A.arr(byte, la, TOML_MAX_BUF),
     off: int, len: int,
     borrow: !$A.borrow(byte, lb2, nb2), blen: int nb2,
     i: int, fuel: int fuel): bool =
    if fuel <= 0 then true
    else if i >= len then true
    else let
      val ca = _rd_arr(arr, off + i)
      val ig = g1ofg0(i)
    in
      if ig >= 0 then
        if $AR.lt_g1(ig, blen) then let
          val cb = byte2int0($A.read<byte>(borrow, ig))
        in
          if $AR.neq_int_int(ca, cb) then false
          else cmp_sec(arr, off, len, borrow, blen, i + 1, fuel - 1)
        end
        else false
      else false
    end

  fun collect
    {la:agz}{le:agz}{lb2:agz}{nb2:pos}{lo2:agz}{mo2:pos}{fuel:nat} .<fuel>.
    (doc_buf: !$A.arr(byte, la, TOML_MAX_BUF),
     entries: !$A.arr(int, le, TOML_ENTRY_INTS),
     section: !$A.borrow(byte, lb2, nb2), slen: int nb2,
     buf: !$A.arr(byte, lo2, mo2), max: int mo2,
     nentries: int, idx: int, opos: int, fuel: int fuel): int =
    if fuel <= 0 then opos
    else if idx >= nentries then opos
    else let
      val base = idx * 6
      val last = base + 5
    in
      if last < 0 then collect(doc_buf, entries, section, slen, buf, max, nentries, idx + 1, opos, fuel - 1)
      else if last >= 1536 then collect(doc_buf, entries, section, slen, buf, max, nentries, idx + 1, opos, fuel - 1)
      else let
        val e_sec_off = _rd_int(entries, base, 1536)
        val e_sec_len = _rd_int(entries, base + 1, 1536)
        val e_key_off = _rd_int(entries, base + 2, 1536)
        val e_key_len = _rd_int(entries, base + 3, 1536)
        val fuel2 = _to_nat(e_sec_len + 1)
        val sec_match =
          if $AR.neq_int_int(e_sec_len, slen) then false
          else if $AR.eq_int_int(e_sec_len, 0) then true
          else cmp_sec(doc_buf, e_sec_off, e_sec_len, section, slen, 0, fuel2)
      in
        if sec_match then let
          fun copy_key {fuel2:nat} .<fuel2>.
            (arr: !$A.arr(byte, la, TOML_MAX_BUF),
             off: int, len: int,
             out: !$A.arr(byte, lo2, mo2), opos: int, max2: int mo2,
             fuel2: int fuel2): int =
            if fuel2 <= 0 then opos
            else let
              val opg = g1ofg0(opos)
            in
              if opg >= 0 then
                if $AR.lt_g1(opg, max2) then
                  if len <= 0 then let
                    val () = $A.set<byte>(out, opg, $A.int2byte(0))
                  in opos + 1 end
                  else let
                    val b = _rd_arr(arr, off)
                    val () = $A.set<byte>(out, opg, $A.int2byte(_to_byte(b)))
                  in copy_key(arr, off + 1, len - 1, out, opos + 1, max2, fuel2 - 1) end
                else opos
              else opos
            end
          val fuel3 = _to_nat(e_key_len + 2)
          val new_opos = copy_key(doc_buf, e_key_off, e_key_len, buf, opos, max, fuel3)
        in collect(doc_buf, entries, section, slen, buf, max, nentries, idx + 1, new_opos, fuel - 1) end
        else collect(doc_buf, entries, section, slen, buf, max, nentries, idx + 1, opos, fuel - 1)
      end
    end

  val fuel = _to_nat(nentries + 1)
  val result = collect(doc_buf, entries, section, slen, buf, max, nentries, 0, 0, fuel)
  prval () = fold@(doc)
in
  if result > 0 then $R.some(result) else $R.none()
end

(* ============================================================
   free implementation
   ============================================================ *)

implement toml_free(doc) = let
  val+ ~toml_doc_mk(doc_buf, _, entries, _) = doc
in
  $A.free<byte>(doc_buf);
  $A.free<int>(entries)
end

(* ============================================================
   Static tests
   ============================================================ *)

fn _safe_byte(x: int): byte = let
  val v = g1ofg0(x)
in
  if v >= 0 then if v < 256 then $A.int2byte(v) else $A.int2byte(0) else $A.int2byte(0)
end

fn _test_parse_free(): void = let
  (* "[pkg]\nname = \"hello\"" *)
  val input = $A.alloc<byte>(20)
  val () = $A.set<byte>(input, 0, _safe_byte(91))
  val () = $A.set<byte>(input, 1, _safe_byte(112))
  val () = $A.set<byte>(input, 2, _safe_byte(107))
  val () = $A.set<byte>(input, 3, _safe_byte(103))
  val () = $A.set<byte>(input, 4, _safe_byte(93))
  val () = $A.set<byte>(input, 5, _safe_byte(10))
  val () = $A.set<byte>(input, 6, _safe_byte(110))
  val () = $A.set<byte>(input, 7, _safe_byte(97))
  val () = $A.set<byte>(input, 8, _safe_byte(109))
  val () = $A.set<byte>(input, 9, _safe_byte(101))
  val () = $A.set<byte>(input, 10, _safe_byte(32))
  val () = $A.set<byte>(input, 11, _safe_byte(61))
  val () = $A.set<byte>(input, 12, _safe_byte(32))
  val () = $A.set<byte>(input, 13, _safe_byte(34))
  val () = $A.set<byte>(input, 14, _safe_byte(104))
  val () = $A.set<byte>(input, 15, _safe_byte(101))
  val () = $A.set<byte>(input, 16, _safe_byte(108))
  val () = $A.set<byte>(input, 17, _safe_byte(108))
  val () = $A.set<byte>(input, 18, _safe_byte(111))
  val () = $A.set<byte>(input, 19, _safe_byte(34))
  val @(fz, bw) = $A.freeze<byte>(input)
  val r = parse(bw, 20)
  val () = $A.drop<byte>(fz, bw)
  val input2 = $A.thaw<byte>(fz)
  val () = $A.free<byte>(input2)
in
  case+ r of
  | ~$R.ok(doc) => toml_free(doc)
  | ~$R.err(_) => ()
end

fn _test_parse_bare(): void = let
  (* "k = true\n" *)
  val input = $A.alloc<byte>(9)
  val () = $A.set<byte>(input, 0, _safe_byte(107))
  val () = $A.set<byte>(input, 1, _safe_byte(32))
  val () = $A.set<byte>(input, 2, _safe_byte(61))
  val () = $A.set<byte>(input, 3, _safe_byte(32))
  val () = $A.set<byte>(input, 4, _safe_byte(116))
  val () = $A.set<byte>(input, 5, _safe_byte(114))
  val () = $A.set<byte>(input, 6, _safe_byte(117))
  val () = $A.set<byte>(input, 7, _safe_byte(101))
  val () = $A.set<byte>(input, 8, _safe_byte(10))
  val @(fz, bw) = $A.freeze<byte>(input)
  val r = parse(bw, 9)
  val () = $A.drop<byte>(fz, bw)
  val input2 = $A.thaw<byte>(fz)
  val () = $A.free<byte>(input2)
in
  case+ r of
  | ~$R.ok(doc) => toml_free(doc)
  | ~$R.err(_) => ()
end
