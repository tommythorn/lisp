/*
 *  Tiny McCarthy style Lisp, but with CDR coding
 *
 *  Copyright (C) 2018  Tommy Thorn <tommy-github2@thorn.ws>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *
 * In 1985 I tried writing my own Lisp, but the project detailed for
 * non-technical reasons.  This felt like a good Sunday project so
 * here's a cute little kernel of it closely as possible to the
 * original definition in John McCarty's book, page 13 of
 * http://www.softwarepreservation.org/projects/LISP/book/LISP%201.5%20Programmers%20Manual.pdf
 * an additional tweak by Paul Graham.
 *
 * Since I had it working I went ahead an added CDR-coding (an
 * underappreciate marvel).
 *
 * Note, to make this useful risk harming the readability of this and
 * it's small size, but it certainly needs:
 * - Pervasive checking, stack overflow, etc
 * - Support for integers and strings
 * - Better support for adding symbols
 * - garbage collection, which probably requires ..
 * - ... coding the interpreter as a state machine to we can get the
 *   roots.
 * - Incremental/Real-time GC (Baker-style)
 * - Static scoping
 *
 * PS: Yes, the coding style here is unusual, even for me.  Whatever.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define SYMBOLS 50
#define HEAPSIZE 1000

typedef unsigned long val;
val heap[HEAPSIZE];
val *hp = heap + HEAPSIZE;

// We chose F to be zero to make the C code simpler
#undef NULL
enum { F = 0, T = 4, NIL = 8, CAR = 12, CDR = 16, CONS = 20, ATOM = 24,
       EQ = 28, LAMBDA = 32, LABEL = 36, QUOTE = 40, NULL = 44, COND = 48, };
val next_symbol = COND/4 + 1;

char *symbol_name[SYMBOLS] = {
    "f", "t", "nil", "car", "cdr", "cons", "atom", "eq", "lambda", "label", "quote", "null", "cond",
    0 };

enum { TAG_NORMAL, TAG_NEXT, TAG_NIL, TAG_EXTENDED };

static inline val atom(val x) { return 0 <= x/4 && x/4 < SYMBOLS; }
static inline val car(val x) {
    assert(!atom(x) && x - (unsigned long)heap < HEAPSIZE*sizeof(val));
    val *p = (val *)x;
    switch (p[0] & 3) {
    default:
    case TAG_NORMAL:
    case TAG_NEXT:
    case TAG_NIL:      return p[0] &~ 3;
    case TAG_EXTENDED: return ((val *)(*p &~ 3))[0];}}

static inline val cdr(val x) {
    assert(!atom(x) && x - (unsigned long)heap < HEAPSIZE*sizeof(val));

    val *p = (val *)x;
    switch (p[0] & 3) {
    default:
    case TAG_NORMAL:   return p[1] &~ 3;
    case TAG_NEXT:     return (val) &p[1];
    case TAG_NIL:      return NIL;
    case TAG_EXTENDED: return ((val *)(*p &~ 3))[1];}}

static int nil_saved, next_saved;

static inline val cons(val a, val d) { assert(hp - 2 >= heap);
    assert((a & 3) == 0);
    assert((d & 3) == 0);
    if (d == NIL)     {
        *--hp = a + TAG_NIL;  ++nil_saved; return (val) hp; }
    if (d == (val)hp) {
        *--hp = a + TAG_NEXT; ++next_saved; return (val) hp; }
    *--hp = d;
    *--hp = a;
    return (val) hp;}

#define cddr(x) cdr(cdr(x)) // "drop 2"
#define cdddr(x) cdr(cddr(x)) // "drop 3"
#define cddddr(x) cdr(cdddr(x)) // "drop 4"

#define cadr(x) car(cdr(x)) // "2nd"
#define caddr(x) car(cddr(x)) // "3rd"
#define cadddr(x) car(cdddr(x)) // "4th"
#define caddddr(x) car(cddddr(x)) // "5th"

#define caar(x) car(car(x))
#define cadr(x) car(cdr(x))
#define cdar(x) cdr(car(x))
#define cadar(x) car(cdr(car(x)))

#define eq(x,y) ((x) == (y) ? T : F)
#define null(x) eq(x,NIL)

val printNL(val a);
val trace(const char *func, int lineno, const char *msg, val a) {
    printf("%s:%d:%s: ", func, lineno, msg); printNL(a); return a; }

val eval(val x, val a);

val equal(val x, val y) {
    if (atom(x)) { if (atom(y)) return eq(x,y); if (T) return F; }
    if (equal(car(x),car(y)))                          return (equal(cdr(x),cdr(y)));
    if (T)                                             return F; }

val pairlis(val x, val y, val a) {
    if (null(x)) return a;
    if (T)       return cons(cons(car(x),car(y)),
                             pairlis(cdr(x),cdr(y),a)); }

val assoc(val x, val a) { if (equal(caar(a),x)) return car(a); if (T) return assoc(x,cdr(a)); }
val evcon(val c, val a) { if (eval(caar(c),a))  return eval(cadar(c),a);
                          if (T)                return evcon(cdr(c),a); }
val evlis(val m, val a) { if (null(m))          return NIL;
                          if (T)                return cons(eval(car(m),a),evlis(cdr(m),a)); }

val apply(val fn, val x, val a) {
    if (atom(fn)) {
        if (eq(fn, CAR))     return caar(x);
        if (eq(fn, CDR))     return cdar(x);
        if (eq(fn, CONS))    return cons(car(x), cadr(x));
        if (eq(fn, ATOM))    return atom(car(x));
        if (eq(fn, EQ))      return eq(car(x), cadr(x));
        if (eq(fn, NULL))    return null(car(x)); // Added for reverse example below
        if (T)               return apply(eval(fn,a),x,a); }
    if (eq(car(fn), LAMBDA)) return eval(caddr(fn),pairlis(cadr(fn),x,a));
    if (eq(car(fn), LABEL))  return apply(caddr(fn),x,cons(cons(cadr(fn),caddr(fn)),a));
    if (T)                   assert(0); return F; }

val eval(val e, val a) {
    if (atom(e))              return cdr(assoc(e,a));
    if (atom(car(e))) {
        if (eq(car(e),QUOTE)) return cadr(e);
        if (eq(car(e),COND))  return evcon(cdr(e),a);
        if (T)                return apply(car(e),evlis(cdr(e),a),a); }
    if (T)                    return apply(car(e),evlis(cdr(e),a),a); }

/* Test it -- this code isn't from McCarthy */

val reader_tail(void), reader_(void);

static const char *reader_source, *reader_p;

void skipsp() { while (*reader_p == ' ') ++reader_p;
    if (!*reader_p) printf("ERROR: reached EOF on %s\n", reader_source);
    assert(*reader_p); }
val reader(const char *source) {reader_p = reader_source = source; return reader_();}
void expect(char c) { skipsp(); if (c == *reader_p) {reader_p++; return; }
    printf("\n%s\n", reader_source);
    for (int i = 0; reader_source + i != reader_p; ++i)
        putchar(' ');
    printf("^ expected %c\n", c);
    exit(1); }
val match(char c) { skipsp(); if (c == *reader_p) { ++reader_p; return T; }
    return F; }

val reader_(void) {
    static char buf[99];
    char *sym = buf;

    if (match('(')) return reader_tail();
    if (match('\'')) return cons(QUOTE, cons(reader_(), NIL));
    while (*reader_p && *reader_p != '(' && *reader_p != ')' && *reader_p != ' ' && sym < buf + 98)
        *sym++ = *reader_p++;
    *sym = 0;
    for (int i = 0; i < next_symbol; ++i)
        if (strcmp(buf, symbol_name[i]) == 0) return i*4;
    assert(next_symbol < SYMBOLS);
    symbol_name[next_symbol++] = strdup(buf);
    return 4*(next_symbol - 1);
}

val reader_tail() {
    skipsp();
    if (match(')')) return NIL;
    val a = reader_();
    if (match('.')) { val d = reader_(); expect(')'); return cons(a, d); }
    return cons(a,reader_tail()); }

void print(val a) {
    if (null(a)) { printf("()"); return; }
    if (atom(a)) { printf("%s", symbol_name[a/4]); return; }
    if (eq(car(a),QUOTE) && null(cddr(a))) { printf("'"); print(cadr(a)); return; }
    printf("(");
    for (;;) {
        print(car(a));
        if (null(cdr(a))) { printf(")"); return; };
        if (atom(cdr(a))) { printf(" . "); print(cdr(a)); printf(")"); return; }
        a = cdr(a);
        printf(" ");}}

val env0;

void repl(char *txt) {
    val e = reader(txt);
    print(eval(e, env0));
    printf("\n");}

val printNL(val a) { print(a); putchar('\n'); return a; }

// Test reader and printer
void test(const char *e_s, const char *want_s) {
    val e = reader(e_s);
    val want = reader(want_s);
    val got = eval(e,env0);

    if (!equal(want,got)) {
        printf("Failed test:\n  ");
        print(e);
        printf("\nexpected:\n  ");
        print(want);
        printf("\ngot:\n  ");
        print(got);
        printf("\n");}}

int main(int argc, char *argv[]) {

    env0 = cons(cons(T, T), NIL);

    test("(null '())", "t");
    test("(null '(1))", "f");
    test("(cond ((null '()) 'good) (t t)) ", "good");
    test("(cond ((null '(b)) 'bad) (t 'also-good)) ", "also-good");
    test("((lambda (x y) (cons (car x) y)) '(a b) '(c d))", "(a c d)");
    test("((label reverse"
         "      (lambda (ls new)"
         "        (cond ((null ls) new)"
         "              (t         (reverse (cdr ls) (cons (car ls) new))))))"
         "    '(a b c d e 1 2 3) '())",
         "(3 2 1 e d c b a)");

    for (int i = 1; i < argc; ++i)
        repl(argv[i]);

    printf("\n%ld heap cells used\n", HEAPSIZE - (hp - heap));
    printf("%d NILs saved\n", nil_saved);
    printf("%d nexts saved\n", next_saved);

    return 0;
}
