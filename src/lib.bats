(* toml -- minimal TOML parser *)
(* Handles [section], key = "value" or 'value', key = true/false (any
   bare value up to a # comment), # comments. *)
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
#pub stadef TOML_MAX_ENTRIES = 256
(* Six 16-bit fields per entry, two bytes each. *)
#pub stadef TOML_ENTRY_BYTES = 3072

#define QUOTE 34
#define APOS 39
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
  | {lb:agz}{le:agz}{m:nat | m <= TOML_MAX_BUF}{k:nat | k <= TOML_MAX_ENTRIES}
    toml_doc_mk of (
      $A.arr(byte, lb, TOML_MAX_BUF),
      int m,
      $A.arr(byte, le, TOML_ENTRY_BYTES),
      int k
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
   buf: !$A.arr(byte, lo, mo), max: int mo): $R.option([k:nat | k <= mo] int k)

#pub fun keys
  {lb:agz}{nb:pos}{lo:agz}{mo:pos}
  (doc: !toml_doc,
   section: !$A.borrow(byte, lb, nb), slen: int nb,
   buf: !$A.arr(byte, lo, mo), max: int mo): $R.option(int)

#pub fun toml_free
  (doc: toml_doc): void

(* Where things are in the parsed text, for error messages that point
   at them (as the toml crate's spans do). *)

(* The span [s, e) of section's [header] line, from its '[' to the end
   of the line; (~1, ~1) when the document has no such header. *)
#pub fun section_at
  {lb:agz}{nb:pos}
  (doc: !toml_doc, section: !$A.borrow(byte, lb, nb), slen: int nb): @(int, int)

(* The span [s, e) of key's value in section, quotes included, and
   whether the value is a string; s = ~1 when there is no such key. *)
#pub fun value_at
  {lb:agz}{nb:pos}{lk:agz}{nk:pos}
  (doc: !toml_doc,
   section: !$A.borrow(byte, lb, nb), slen: int nb,
   key: !$A.borrow(byte, lk, nk), klen: int nk): @(int, int, bool)

(* Whether a key comes before the first [header]. *)
#pub fun has_root_keys (doc: !toml_doc): bool

(* The byte at i of the parsed text; ~1 outside it. *)
#pub fun byte_at {i:int} (doc: !toml_doc, i: int i): int

(* ============================================================
   Scanning. Positions are indexed and never pass the input length m,
   so every read is proven in bounds.
   ============================================================ *)

fn _is_ws(c: int): bool =
  if c = SPACE then true
  else if c = TAB then true
  else if c = CR then true
  else false

fn _rd {lb:agz}{p:nat | p < TOML_MAX_BUF}
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF), p: int p): int =
  byte2int0($A.read<byte>(buf, p))

(* First position at or after p that is not a space, tab or CR. *)
fun _skip_ws
  {lb:agz}{m:nat | m <= TOML_MAX_BUF}{p:nat | p <= m} .<m - p>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF), p: int p, m: int m)
  : [r:int | p <= r; r <= m] int r =
  if p >= m then p
  else if _is_ws(_rd(buf, p)) then _skip_ws(buf, p + 1, m)
  else p

(* First position at or after p holding target or a newline; m if none. *)
fun _find_char
  {lb:agz}{m:nat | m <= TOML_MAX_BUF}{p:nat | p <= m} .<m - p>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF), p: int p, target: int, m: int m)
  : [r:int | p <= r; r <= m] int r =
  if p >= m then p
  else let
    val c = _rd(buf, p)
  in
    if c = target then p
    else if c = NEWLINE then p
    else _find_char(buf, p + 1, target, m)
  end

(* First newline at or after p; m if none. *)
fun _find_eol
  {lb:agz}{m:nat | m <= TOML_MAX_BUF}{p:nat | p <= m} .<m - p>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF), p: int p, m: int m)
  : [r:int | p <= r; r <= m] int r =
  if p >= m then m
  else if _rd(buf, p) = NEWLINE then p
  else _find_eol(buf, p + 1, m)

(* End of [s, e) with trailing whitespace removed. *)
fun _trim_right
  {lb:agz}{s,e:nat | s <= e; e <= TOML_MAX_BUF} .<e - s>.
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF), s: int s, e: int e)
  : [r:int | s <= r; r <= e] int r =
  if e <= s then s
  else if _is_ws(_rd(buf, e - 1)) then _trim_right(buf, s, e - 1)
  else e

(* ============================================================
   Entry table: entry j holds six 16-bit fields at bytes 12j .. 12j+11:
   section offset, section length, key offset, key length, value
   offset, value length. Reading a field back gives a value proven
   below 65536. Parsed offsets and lengths are at most 65536, and only
   an offset can reach 65536: a string value that starts at the very
   end of a full buffer, whose length is then 0.
   ============================================================ *)

fn _put16 {le:agz}{i:nat | i + 2 <= TOML_ENTRY_BYTES}
  (e: !$A.arr(byte, le, TOML_ENTRY_BYTES), i: int i, v: int): void = let
  val () = $A.set<byte>(e, i, $A.int2byte($AR.low_byte(v)))
in $A.set<byte>(e, i + 1, $A.int2byte($AR.low_byte(v / 256))) end

fn _get16 {le:agz}{i:nat | i + 2 <= TOML_ENTRY_BYTES}
  (e: !$A.arr(byte, le, TOML_ENTRY_BYTES), i: int i): [v:nat | v < 65536] int v =
  $AR.low_byte(byte2int0($A.get<byte>(e, i)))
  + 256 * $AR.low_byte(byte2int0($A.get<byte>(e, i + 1)))

fn _store_entry
  {le:agz}{k:nat | k < TOML_MAX_ENTRIES}
  (e: !$A.arr(byte, le, TOML_ENTRY_BYTES), k: int k,
   sec_off: int, sec_len: int,
   key_off: int, key_len: int,
   val_off: int, val_len: int): int (k + 1) = let
  val b = 12 * k
  val () = _put16(e, b, sec_off)
  val () = _put16(e, b + 2, sec_len)
  val () = _put16(e, b + 4, key_off)
  val () = _put16(e, b + 6, key_len)
  val () = _put16(e, b + 8, val_off)
  val () = _put16(e, b + 10, val_len)
in k + 1 end

(* Whether buf[s, e) is a quoted key "k". TOML names such a key by the
   text between the quotes, so it is stored without them. *)
fn _is_quoted
  {lb:agz}{s,e:nat | s <= e; e <= TOML_MAX_BUF}
  (buf: !$A.borrow(byte, lb, TOML_MAX_BUF), s: int s, e: int e): bool =
  if e - s < 2 then false
  else if _rd(buf, s) != QUOTE then false
  else _rd(buf, e - 1) = QUOTE

(* doc[off + j] = b[j] for every j < nb. *)
fn _region_eq
  {la:agz}{lb:agz}{nb:pos}{o:nat | o + nb <= TOML_MAX_BUF}
  (doc: !$A.arr(byte, la, TOML_MAX_BUF), off: int o,
   b: !$A.borrow(byte, lb, nb), nb: int nb): bool = let
  fun loop {j:nat | j <= nb} .<nb - j>.
    (doc: !$A.arr(byte, la, TOML_MAX_BUF), b: !$A.borrow(byte, lb, nb), j: int j): bool =
    if j >= nb then true
    else if byte2int0($A.get<byte>(doc, off + j)) = byte2int0($A.read<byte>(b, j)) then loop(doc, b, j + 1)
    else false
in loop(doc, b, 0) end

(* Whether the stored field (off, len) spells b. *)
fn _field_eq
  {la:agz}{lb:agz}{nb:pos}{o,n:nat}
  (doc: !$A.arr(byte, la, TOML_MAX_BUF), off: int o, len: int n,
   b: !$A.borrow(byte, lb, nb), nb: int nb): bool =
  if len != nb then false
  else if off + nb > 65536 then false
  else _region_eq(doc, off, b, nb)

(* ============================================================
   parse implementation
   ============================================================ *)

implement parse {lb}{n} (input, len) = let
  val doc_buf = $A.alloc<byte>(65536)
  val entries = $A.alloc<byte>(3072)
  val m = min(len, 65536)

  fun copy_input {ld:agz}{m:nat | m <= n; m <= TOML_MAX_BUF}{i:nat | i <= m} .<m - i>.
    (dst: !$A.arr(byte, ld, TOML_MAX_BUF), src: !$A.borrow(byte, lb, n),
     i: int i, m: int m): void =
    if i >= m then ()
    else let
      val () = $A.set<byte>(dst, i, $A.read<byte>(src, i))
    in copy_input(dst, src, i + 1, m) end

  val () = copy_input(doc_buf, input, 0, m)

  val @(fz_buf, bw_buf) = $A.freeze<byte>(doc_buf)

  (* One line per step; every step moves pos forward. *)
  fun parse_loop
    {lbw:agz}{le:agz}{m:nat | m <= TOML_MAX_BUF}{p:nat | p <= m + 1}{k:nat | k <= TOML_MAX_ENTRIES}
    .<m + 1 - p>.
    (bw: !$A.borrow(byte, lbw, TOML_MAX_BUF),
     entries: !$A.arr(byte, le, TOML_ENTRY_BYTES),
     pos: int p, k: int k, sec_off: int, sec_len: int, m: int m)
    : [r:nat | r <= TOML_MAX_ENTRIES] int r =
    if pos >= m then k
    else if k >= 256 then k
    else let
      val p = _skip_ws(bw, pos, m)
    in
      if p >= m then k
      else let
        val c = _rd(bw, p)
      in
        if c = NEWLINE then
          parse_loop(bw, entries, p + 1, k, sec_off, sec_len, m)
        else if c = HASH then let
          val eol = _find_eol(bw, p + 1, m)
        in parse_loop(bw, entries, eol + 1, k, sec_off, sec_len, m) end
        else if c = LBRACKET then let
          val sec_start = p + 1
          val sec_end = _find_char(bw, sec_start, RBRACKET, m)
          val eol = _find_eol(bw, min(sec_end + 1, m), m)
          (* The header itself, as an entry with an empty key (which
             get and keys never match): its line is [p, eol) *)
          val k2 = _store_entry(entries, k, sec_start, sec_end - sec_start, p, 0, eol, 0)
        in parse_loop(bw, entries, eol + 1, k2, sec_start, sec_end - sec_start, m) end
        else let
          val eq_pos = _find_char(bw, p, EQUALS, m)
        in
          (* No '=' on this line (the scan stopped at a newline or the
             end): skip the line. *)
          if eq_pos >= m then let
            val eol = _find_eol(bw, p, m)
          in parse_loop(bw, entries, eol + 1, k, sec_off, sec_len, m) end
          else if _rd(bw, eq_pos) != EQUALS then
            parse_loop(bw, entries, eq_pos + 1, k, sec_off, sec_len, m)
          else let
            val key_end = _trim_right(bw, p, eq_pos)
            val q = (if _is_quoted(bw, p, key_end) then 1 else 0): int
            val v0 = _skip_ws(bw, eq_pos + 1, m)
            val eol = _find_eol(bw, v0, m)
          in
            if v0 >= m then
              parse_loop(bw, entries, eol + 1, k, sec_off, sec_len, m)
            else if _rd(bw, v0) = QUOTE then let
              val s0 = v0 + 1
              val s1 = _find_char(bw, s0, QUOTE, m)
              val k2 = _store_entry(entries, k, sec_off, sec_len, p + q, key_end - p - 2 * q, s0, s1 - s0)
            in parse_loop(bw, entries, eol + 1, k2, sec_off, sec_len, m) end
            else if _rd(bw, v0) = APOS then let
              (* A literal string 'v' *)
              val s0 = v0 + 1
              val s1 = _find_char(bw, s0, APOS, m)
              val k2 = _store_entry(entries, k, sec_off, sec_len, p + q, key_end - p - 2 * q, s0, s1 - s0)
            in parse_loop(bw, entries, eol + 1, k2, sec_off, sec_len, m) end
            else let
              (* A bare value ends at a # comment *)
              val v1 = _trim_right(bw, v0, _find_char(bw, v0, HASH, m))
              val k2 = _store_entry(entries, k, sec_off, sec_len, p + q, key_end - p - 2 * q, v0, v1 - v0)
            in parse_loop(bw, entries, eol + 1, k2, sec_off, sec_len, m) end
          end
        end
      end
    end

  val nentries = parse_loop(bw_buf, entries, 0, 0, 0, 0, m)

  val () = $A.drop<byte>(fz_buf, bw_buf)
  val doc_buf2 = $A.thaw<byte>(fz_buf)

in $R.ok(toml_doc_mk(doc_buf2, m, entries, nentries)) end

(* ============================================================
   get implementation
   ============================================================ *)

(* Index of the first entry in section with the given key; ~1 if none. *)
fn _search
  {la:agz}{le:agz}{lb:agz}{nb:pos}{lk:agz}{nk:pos}{k:nat | k <= TOML_MAX_ENTRIES}
  (doc: !$A.arr(byte, la, TOML_MAX_BUF), e: !$A.arr(byte, le, TOML_ENTRY_BYTES),
   section: !$A.borrow(byte, lb, nb), slen: int nb,
   key: !$A.borrow(byte, lk, nk), klen: int nk, k: int k)
  : [r:int | ~1 <= r; r < k] int r = let
  fun loop {i:nat | i <= k} .<k - i>.
    (doc: !$A.arr(byte, la, TOML_MAX_BUF), e: !$A.arr(byte, le, TOML_ENTRY_BYTES),
     section: !$A.borrow(byte, lb, nb), key: !$A.borrow(byte, lk, nk), i: int i)
    : [r:int | ~1 <= r; r < k] int r =
    if i >= k then ~1
    else let
      val b = 12 * i
    in
      if _field_eq(doc, _get16(e, b), _get16(e, b + 2), section, slen) then
        if _field_eq(doc, _get16(e, b + 4), _get16(e, b + 6), key, klen) then i
        else loop(doc, e, section, key, i + 1)
      else loop(doc, e, section, key, i + 1)
    end
in loop(doc, e, section, key, 0) end

implement get {lb}{nb}{lk}{nk}{lo}{mo}
  (doc, section, slen, key, klen, buf, max) = let
  val+ @toml_doc_mk(doc_buf, _, entries, nentries) = doc
  val i = _search(doc_buf, entries, section, slen, key, klen, nentries)
  val res =
    (if i < 0 then $R.none()
     else let
       val voff = _get16(entries, 12 * i + 8)
       val vlen = _get16(entries, 12 * i + 10)
     in
       if vlen > max then $R.none()
       else if voff + vlen > 65536 then $R.none()
       else let
         fun copy_val {ld:agz}{la:agz}{vlen0:nat | vlen0 <= mo}{v0:nat | v0 + vlen0 <= TOML_MAX_BUF}{j:nat | j <= vlen0}
           .<vlen0 - j>.
           (dst: !$A.arr(byte, ld, mo), src: !$A.arr(byte, la, TOML_MAX_BUF),
            voff: int v0, vlen: int vlen0, j: int j): void =
           if j >= vlen then ()
           else let
             val () = $A.set<byte>(dst, j, $A.get<byte>(src, voff + j))
           in copy_val(dst, src, voff, vlen, j + 1) end
         val () = copy_val(buf, doc_buf, voff, vlen, 0)
       in $R.some(vlen) end
     end): $R.option([k:nat | k <= mo] int k)
  prval () = fold@(doc)
in res end

(* ============================================================
   keys implementation: list all key names in a section
   ============================================================ *)

(* Copies len bytes of doc from off into out at opos, then a 0 byte;
   stops early when out is full. Returns the next output position. *)
fun _copy_key
  {la:agz}{lo:agz}{mo:pos}{kl:nat}{q:nat | q + kl <= TOML_MAX_BUF}{o:nat | o <= mo} .<kl>.
  (doc: !$A.arr(byte, la, TOML_MAX_BUF), off: int q, len: int kl,
   out: !$A.arr(byte, lo, mo), opos: int o, max: int mo)
  : [r:nat | r <= mo] int r =
  if opos >= max then opos
  else if len <= 0 then let
    val () = $A.set<byte>(out, opos, $A.int2byte(0))
  in opos + 1 end
  else let
    val () = $A.set<byte>(out, opos, $A.get<byte>(doc, off))
  in _copy_key(doc, off + 1, len - 1, out, opos + 1, max) end

implement keys {lb}{nb}{lo}{mo}
  (doc, section, slen, buf, max) = let
  val+ @toml_doc_mk(doc_buf, _, entries, nentries) = doc

  fun collect
    {la:agz}{le:agz}{k:nat | k <= TOML_MAX_ENTRIES}{i:nat | i <= k}{o:nat | o <= mo} .<k - i>.
    (doc: !$A.arr(byte, la, TOML_MAX_BUF), e: !$A.arr(byte, le, TOML_ENTRY_BYTES),
     section: !$A.borrow(byte, lb, nb), out: !$A.arr(byte, lo, mo),
     k: int k, i: int i, opos: int o)
    : [r:nat | r <= mo] int r =
    if i >= k then opos
    else let
      val b = 12 * i
      val koff = _get16(e, b + 4)
      val klen = _get16(e, b + 6)
    in
      if klen = 0 then collect(doc, e, section, out, k, i + 1, opos)
      else if _field_eq(doc, _get16(e, b), _get16(e, b + 2), section, slen) then
        if koff + klen <= 65536 then
          collect(doc, e, section, out, k, i + 1, _copy_key(doc, koff, klen, out, opos, max))
        else collect(doc, e, section, out, k, i + 1, opos)
      else collect(doc, e, section, out, k, i + 1, opos)
    end

  val result = collect(doc_buf, entries, section, buf, nentries, 0, 0)
  prval () = fold@(doc)
in
  if result > 0 then $R.some(g0ofg1(result)) else $R.none()
end

(* ============================================================
   Spans
   ============================================================ *)

implement section_at {lb}{nb} (doc, section, slen) = let
  val+ @toml_doc_mk(doc_buf, _, entries, nentries) = doc
  fun loop {la:agz}{le:agz}{k:nat | k <= TOML_MAX_ENTRIES}{i:nat | i <= k} .<k - i>.
    (d: !$A.arr(byte, la, TOML_MAX_BUF), e: !$A.arr(byte, le, TOML_ENTRY_BYTES),
     section: !$A.borrow(byte, lb, nb), k: int k, i: int i): @(int, int) =
    if i >= k then @(~1, ~1)
    else let val b = 12 * i in
      if _get16(e, b + 6) != 0 then loop(d, e, section, k, i + 1)
      else if _field_eq(d, _get16(e, b), _get16(e, b + 2), section, slen) then
        @(_get16(e, b + 4), _get16(e, b + 8))
      else loop(d, e, section, k, i + 1)
    end
  val r = loop(doc_buf, entries, section, nentries, 0)
  prval () = fold@(doc)
in r end

implement value_at {lb}{nb}{lk}{nk} (doc, section, slen, key, klen) = let
  val+ @toml_doc_mk(doc_buf, m, entries, nentries) = doc
  val i = _search(doc_buf, entries, section, slen, key, klen, nentries)
  val r = (if i < 0 then @(~1, ~1, false)
    else let
      val voff = _get16(entries, 12 * i + 8)
      val vlen = _get16(entries, 12 * i + 10)
      val before = (if voff > 0 then (if voff - 1 < m then byte2int0($A.get<byte>(doc_buf, voff - 1)) else 0) else 0): int
      val quoted = (if before = QUOTE then true else before = APOS): bool
    in
      if quoted then @(voff - 1, voff + vlen + 1, true)
      else @(voff, voff + vlen, false)
    end): @(int, int, bool)
  prval () = fold@(doc)
in r end

implement has_root_keys (doc) = let
  val+ @toml_doc_mk(_, _, entries, nentries) = doc
  fun loop {le:agz}{k:nat | k <= TOML_MAX_ENTRIES}{i:nat | i <= k} .<k - i>.
    (e: !$A.arr(byte, le, TOML_ENTRY_BYTES), k: int k, i: int i): bool =
    if i >= k then false
    else let val b = 12 * i in
      if _get16(e, b + 2) = 0 then (if _get16(e, b + 6) > 0 then true else loop(e, k, i + 1))
      else loop(e, k, i + 1)
    end
  val r = loop(entries, nentries, 0)
  prval () = fold@(doc)
in r end

implement byte_at {i} (doc, i) = let
  val+ @toml_doc_mk(doc_buf, m, _, _) = doc
  val r = (if i < 0 then ~1 else if i >= m then ~1
           else byte2int0($A.get<byte>(doc_buf, i))): int
  prval () = fold@(doc)
in r end

(* ============================================================
   free implementation
   ============================================================ *)

implement toml_free(doc) = let
  val+ ~toml_doc_mk(doc_buf, _, entries, _) = doc
in
  $A.free<byte>(doc_buf);
  $A.free<byte>(entries)
end

(* ============================================================
   Static tests
   ============================================================ *)

fn _test_parse_free(): void = let
  (* "[pkg]\nname = \"hello\"" *)
  val input = $A.alloc<byte>(20)
  val () = $A.set<byte>(input, 0, $A.int2byte(91))
  val () = $A.set<byte>(input, 1, $A.int2byte(112))
  val () = $A.set<byte>(input, 2, $A.int2byte(107))
  val () = $A.set<byte>(input, 3, $A.int2byte(103))
  val () = $A.set<byte>(input, 4, $A.int2byte(93))
  val () = $A.set<byte>(input, 5, $A.int2byte(10))
  val () = $A.set<byte>(input, 6, $A.int2byte(110))
  val () = $A.set<byte>(input, 7, $A.int2byte(97))
  val () = $A.set<byte>(input, 8, $A.int2byte(109))
  val () = $A.set<byte>(input, 9, $A.int2byte(101))
  val () = $A.set<byte>(input, 10, $A.int2byte(32))
  val () = $A.set<byte>(input, 11, $A.int2byte(61))
  val () = $A.set<byte>(input, 12, $A.int2byte(32))
  val () = $A.set<byte>(input, 13, $A.int2byte(34))
  val () = $A.set<byte>(input, 14, $A.int2byte(104))
  val () = $A.set<byte>(input, 15, $A.int2byte(101))
  val () = $A.set<byte>(input, 16, $A.int2byte(108))
  val () = $A.set<byte>(input, 17, $A.int2byte(108))
  val () = $A.set<byte>(input, 18, $A.int2byte(111))
  val () = $A.set<byte>(input, 19, $A.int2byte(34))
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
  val () = $A.set<byte>(input, 0, $A.int2byte(107))
  val () = $A.set<byte>(input, 1, $A.int2byte(32))
  val () = $A.set<byte>(input, 2, $A.int2byte(61))
  val () = $A.set<byte>(input, 3, $A.int2byte(32))
  val () = $A.set<byte>(input, 4, $A.int2byte(116))
  val () = $A.set<byte>(input, 5, $A.int2byte(114))
  val () = $A.set<byte>(input, 6, $A.int2byte(117))
  val () = $A.set<byte>(input, 7, $A.int2byte(101))
  val () = $A.set<byte>(input, 8, $A.int2byte(10))
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

(* Static test: the length get returns indexes the caller's buffer *)
fn _test_get_len_indexes_buf {lb:agz}{nb:pos}{lk:agz}{nk:pos}{lo:agz}{mo:pos}
  (doc: !toml_doc,
   section: !$A.borrow(byte, lb, nb), slen: int nb,
   key: !$A.borrow(byte, lk, nk), klen: int nk,
   buf: !$A.arr(byte, lo, mo), max: int mo): void =
  case+ get(doc, section, slen, key, klen, buf, max) of
  | ~$R.some(k) => if k > 0 then let
      val _ = $A.get<byte>(buf, k - 1)
    in () end else ()
  | ~$R.none() => ()
