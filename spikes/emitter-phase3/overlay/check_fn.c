/* Spike 9: spike 8's checker, rebound to Shen/JIT 0.4. 0.4 adds two kept registers (KEPT_REG(k) = SLJIT_S(4 + k),
   x20 and x21 on RV64) that hold slots across instructions and labels, like CACHE. With SPIKE_NO_KEPT defined the
   checker treats them as unknown, as spike 8 did, to measure what they cost.

   Spike 8: a function-level checker of emitted RV64 against bytecode, written with no input from the
   emitter's analysis. It symbolically runs the machine code of each bytecode instruction from a canonical
   state, and compares the result with what the bytecode requires. The emitter supplies only `cuts`, the
   byte offset of each instruction, and these are hints: a wrong one makes a check fail.

   Not part of the proved bytes yet. coq/CheckFn.v holds the same algorithm, and the soundness theorem is
   about that function. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;

enum { OP_MOVE_ = 0, OP_CONST_ = 1, OP_PRIM_ = 4, OP_LABEL_ = 5, OP_JUMP_ = 6, OP_JIF_ = 7, OP_RETURN_ = 14 };
#define CONST_FLAG 0x80000000u
#define NONE32 UINT32_MAX

/* Abstract values: base + k, or a tag test. */
enum base { B_UNK, B_CONST, B_SLOT, B_FP, B_VM, B_HP, B_HLIM, B_RET, B_HD, B_TL, B_CELL, B_STATUS, B_COUNT, B_TAG };
typedef struct { enum base b; u32 a; i64 k; } AV;
static const AV UNK = {B_UNK, 0, 0};
static AV lin(enum base b, u32 a, i64 k) { AV v = {b, a, k}; return v; }
static int same(AV x, AV y) { return x.b != B_UNK && x.b == y.b && x.a == y.a && x.k == y.k; }

/* Decoded instructions, as the model's decoder gives them. */
enum ik { I_BAD, I_ADDI, I_ANDI, I_ADD, I_XOR, I_SLLI, I_LUI, I_AUIPC, I_LD, I_SD, I_BEQ, I_BNE, I_BLTU, I_BGEU, I_JAL, I_JALR, I_FENCE };
typedef struct { enum ik k; int rd, r1, r2; i64 imm; int len; } Ins;

static i64 sx(u64 v, int bits) { return (i64)(v << (64 - bits)) >> (64 - bits); }
static u32 bit(u32 w, int hi, int lo) { return (w >> lo) & ((1u << (hi - lo + 1)) - 1); }

static Ins dec16(u32 w)
{
    Ins i = {I_BAD, 0, 0, 0, 0, 2};
    u32 op = w & 3, f3 = bit(w, 15, 13), rd = bit(w, 11, 7), rs2 = bit(w, 6, 2), rdp = bit(w, 4, 2) + 8, rs1p = bit(w, 9, 7) + 8;
    if (op == 0) {
        i64 d = (bit(w, 12, 10) << 3) | (bit(w, 6, 5) << 6);
        if (f3 == 0 && w) { /* c.addi4spn */
            i64 n = (bit(w, 12, 11) << 4) | (bit(w, 10, 7) << 6) | (bit(w, 6, 6) << 2) | (bit(w, 5, 5) << 3);
            if (n) { i.k = I_ADDI; i.rd = rdp; i.r1 = 2; i.imm = n; }
        } else if (f3 == 3) { i.k = I_LD; i.rd = rdp; i.r1 = rs1p; i.imm = d; }
        else if (f3 == 7) { i.k = I_SD; i.r2 = rdp; i.r1 = rs1p; i.imm = d; }
    } else if (op == 1) {
        i64 imm = sx((bit(w, 12, 12) << 5) | bit(w, 6, 2), 6);
        if (f3 == 0) { i.k = I_ADDI; i.rd = i.r1 = rd; i.imm = imm; }
        else if (f3 == 2) { i.k = I_ADDI; i.rd = rd; i.r1 = 0; i.imm = imm; }
        else if (f3 == 3 && rd != 2 && rd != 0 && imm) { i.k = I_LUI; i.rd = rd; i.imm = imm << 12; }
        else if (f3 == 4 && bit(w, 11, 10) == 2) { i.k = I_ANDI; i.rd = i.r1 = rs1p; i.imm = imm; }
        else if (f3 == 5) {
            u32 o = (bit(w, 12, 12) << 11) | (bit(w, 11, 11) << 4) | (bit(w, 10, 9) << 8) | (bit(w, 8, 8) << 10) |
                    (bit(w, 7, 7) << 6) | (bit(w, 6, 6) << 7) | (bit(w, 5, 3) << 1) | (bit(w, 2, 2) << 5);
            i.k = I_JAL; i.rd = 0; i.imm = sx(o, 12);
        } else if (f3 == 6 || f3 == 7) {
            u32 o = (bit(w, 12, 12) << 8) | (bit(w, 11, 10) << 3) | (bit(w, 6, 5) << 6) | (bit(w, 4, 3) << 1) | (bit(w, 2, 2) << 5);
            i.k = f3 == 6 ? I_BEQ : I_BNE; i.r1 = rs1p; i.r2 = 0; i.imm = sx(o, 9);
        }
    } else if (op == 2) {
        if (f3 == 0 && !bit(w, 12, 12)) { i.k = I_SLLI; i.rd = i.r1 = rd; i.imm = bit(w, 6, 2); }
        else if (f3 == 0) { i.k = I_SLLI; i.rd = i.r1 = rd; i.imm = 32 + bit(w, 6, 2); }
        else if (f3 == 4 && !bit(w, 12, 12) && rs2) { i.k = I_ADD; i.rd = rd; i.r1 = 0; i.r2 = rs2; }
        else if (f3 == 4 && !bit(w, 12, 12) && rd) { i.k = I_JALR; i.rd = 0; i.r1 = rd; i.imm = 0; }
        else if (f3 == 4 && bit(w, 12, 12) && rs2) { i.k = I_ADD; i.rd = i.r1 = rd; i.r2 = rs2; }
        else if (f3 == 4 && bit(w, 12, 12) && rd) { i.k = I_JALR; i.rd = 1; i.r1 = rd; i.imm = 0; }
    }
    return i;
}

static Ins dec32(u32 w)
{
    Ins i = {I_BAD, 0, 0, 0, 0, 4};
    u32 op = w & 0x7f, f3 = bit(w, 14, 12), f7 = bit(w, 31, 25);
    i.rd = bit(w, 11, 7); i.r1 = bit(w, 19, 15); i.r2 = bit(w, 24, 20);
    i64 immi = sx(bit(w, 31, 20), 12);
    switch (op) {
    case 0x13:
        if (f3 == 0) { i.k = I_ADDI; i.imm = immi; }
        else if (f3 == 7) { i.k = I_ANDI; i.imm = immi; }
        else if (f3 == 1 && bit(w, 31, 26) == 0) { i.k = I_SLLI; i.imm = bit(w, 25, 20); }
        break;
    case 0x33:
        if (f3 == 0 && f7 == 0) i.k = I_ADD;
        else if (f3 == 4 && f7 == 0) i.k = I_XOR;
        break;
    case 0x37: i.k = I_LUI; i.imm = sx(w & 0xfffff000u, 32); break;
    case 0x17: i.k = I_AUIPC; i.imm = sx(w & 0xfffff000u, 32); break;
    case 0x03: if (f3 == 3) { i.k = I_LD; i.imm = immi; } break;
    case 0x23: if (f3 == 3) { i.k = I_SD; i.imm = sx((bit(w, 31, 25) << 5) | bit(w, 11, 7), 12); } break;
    case 0x63: {
        i64 o = sx((bit(w, 31, 31) << 12) | (bit(w, 7, 7) << 11) | (bit(w, 30, 25) << 5) | (bit(w, 11, 8) << 1), 13);
        i.imm = o;
        if (f3 == 0) i.k = I_BEQ; else if (f3 == 1) i.k = I_BNE; else if (f3 == 6) i.k = I_BLTU; else if (f3 == 7) i.k = I_BGEU;
        break;
    }
    case 0x6f:
        i.k = I_JAL;
        i.imm = sx((bit(w, 31, 31) << 20) | (bit(w, 19, 12) << 12) | (bit(w, 20, 20) << 11) | (bit(w, 30, 21) << 1), 21);
        break;
    case 0x67: if (f3 == 0) { i.k = I_JALR; i.imm = immi; } break;
    default: break;
    }
    return i;
}

static Ins decode(const uint8_t *p)
{
    u32 lo = p[0] | (u32)p[1] << 8;
    if ((lo & 3) != 3)
        return dec16(lo);
    return dec32(lo | (u32)p[2] << 16 | (u32)p[3] << 24);
}

#define NKEPT 2
#define KEPT_X(k) (20 + (k)) /* x20, x21: SLJIT_S4, SLJIT_S5 in sljitNativeRISCV_common.c's reg_map */
typedef struct { u64 C_set; u32 C; u64 M, P; u32 R; u32 K[NKEPT]; } S; /* C: slot in CACHE, or NONE; M: slots current in the frame; P: known pairs; R: reserved words; K: slot in each kept register, or NONE */
typedef struct {
    const uint8_t *code; size_t len; u64 base;
    const uint32_t *words; size_t nwords; const size_t *cuts; /* by word offset, SIZE_MAX if none; cuts[nwords] is the end */
    u32 frame, arity, nconst; const u64 *const *cells;
    u64 arity_stub, unwind, h_alloc, vtrue, vfalse;
    u32 hp_off, hlimit_off, fp_off, top_off;
    S *lab; uint8_t *lab_seen; size_t *lab_off; u32 nlabels;
    struct { size_t target; size_t cut; u32 words; S st; } *slow; size_t nslow;
    const char *why;
} Ctx;

typedef struct { AV r[32]; struct { AV a, v; } w[16]; int nw; } Sym;

static void sym_init(Sym *y, const S *s)
{
    for (int i = 0; i < 32; i++) y->r[i] = UNK;
    y->r[0] = lin(B_CONST, 0, 0);
    y->r[8] = lin(B_FP, 0, 0);
    y->r[9] = lin(B_VM, 0, 0);
    y->r[18] = s->C == NONE32 ? UNK : lin(B_SLOT, s->C, 0);
    y->r[19] = lin(B_HP, 0, 0);
#ifndef SPIKE_NO_KEPT
    for (int k = 0; k < NKEPT; k++)
        y->r[KEPT_X(k)] = s->K[k] == NONE32 ? UNK : lin(B_SLOT, s->K[k], 0);
#endif
    y->nw = 0;
}

static void setr(Sym *y, int rd, AV v) { if (rd) y->r[rd] = v; }

static AV add_k(AV a, i64 k) { if (a.b == B_UNK || a.b == B_TAG) return UNK; a.k += k; return a; }

static AV load(Ctx *x, const S *s, Sym *y, AV a)
{
    for (int i = y->nw - 1; i >= 0; i--)
        if (same(y->w[i].a, a))
            return y->w[i].v;
    if (a.b == B_FP && a.k >= 0 && a.k % 8 == 0) {
        i64 n = a.k / 8;
        if (n == 0) return lin(B_RET, 0, 0);
        if (n < 64 && ((s->M >> n) & 1)) return lin(B_SLOT, (u32)n, 0);
        return UNK;
    }
    if (a.b == B_VM && a.k == x->hlimit_off) return lin(B_HLIM, 0, 0);
    if (a.b == B_VM && a.k == x->hp_off) return lin(B_HP, 0, 0);
    if (a.b == B_SLOT && a.k == -3 && a.a < 64 && ((s->P >> a.a) & 1)) return lin(B_HD, a.a, 0);
    if (a.b == B_SLOT && a.k == 5 && a.a < 64 && ((s->P >> a.a) & 1)) return lin(B_TL, a.a, 0);
    if (a.b == B_CONST)
        for (u32 i = 0; i < x->nconst; i++)
            if ((u64)(uintptr_t)x->cells[i] == (u64)a.k)
                return lin(B_CELL, i, 0);
    return UNK;
}

typedef struct { int kind; AV a, b; size_t target; Sym at; } Br; /* kind: I_BEQ, I_BNE, I_BLTU */
typedef struct { int nb; Br b[4]; int end; /* 0 reached stop; 1 jump; 2 return; 3 call */ size_t target; AV ret; u64 callee; size_t next; } Run;

static int fail(Ctx *x, const char *why) { if (!x->why) x->why = why; return 0; }

/* Symbolically runs [from, stop), or to an unconditional transfer. */
static int run_block(Ctx *x, const S *s, Sym *y, size_t from, size_t stop, Run *out)
{
    size_t o = from;
    out->nb = 0; out->end = 0;
    for (int fuel = 64; fuel; fuel--) {
        if (o == stop) { out->end = 0; return 1; }
        if (o + 4 > x->len || o > stop) return fail(x, "out of block");
        Ins i = decode(x->code + o);
        AV a = y->r[i.r1], b = y->r[i.r2], v = UNK;
        switch (i.k) {
        case I_ADDI: setr(y, i.rd, add_k(a, i.imm)); break;
        case I_ANDI:
            if (a.b == B_SLOT && a.k == -3 && i.imm == 7) v = lin(B_TAG, a.a, 0);
            else if (a.b == B_CONST) v = lin(B_CONST, 0, a.k & i.imm);
            setr(y, i.rd, v);
            break;
        case I_ADD:
            if (a.b == B_CONST && a.k == 0) v = b;
            else if (b.b == B_CONST) v = add_k(a, b.k);
            else if (a.b == B_CONST) v = add_k(b, a.k);
            setr(y, i.rd, v);
            break;
        case I_XOR: setr(y, i.rd, a.b == B_CONST && b.b == B_CONST ? lin(B_CONST, 0, a.k ^ b.k) : UNK); break;
        case I_SLLI: setr(y, i.rd, a.b == B_CONST ? lin(B_CONST, 0, (i64)((u64)a.k << i.imm)) : UNK); break;
        case I_LUI: setr(y, i.rd, lin(B_CONST, 0, i.imm)); break;
        case I_AUIPC: setr(y, i.rd, lin(B_CONST, 0, (i64)(x->base + o + (u64)i.imm))); break;
        case I_LD: setr(y, i.rd, load(x, s, y, add_k(a, i.imm))); break;
        case I_SD:
            if (y->nw == 16) return fail(x, "too many stores");
            y->w[y->nw].a = add_k(a, i.imm); y->w[y->nw++].v = b;
            break;
        case I_BEQ: case I_BNE: case I_BLTU: case I_BGEU: {
            if (out->nb == 4) return fail(x, "too many branches");
            Br *r = &out->b[out->nb++];
            /* SLJIT's long form: the inverse test skips a jump to the far target. */
            if (i.imm == i.len + 4 && o + (size_t)i.len + 4 <= x->len && decode(x->code + o + i.len).k == I_JAL &&
                decode(x->code + o + i.len).rd == 0 && decode(x->code + o + i.len).len == 4) {
                Ins j = decode(x->code + o + i.len);
                r->kind = i.k == I_BEQ ? I_BNE : i.k == I_BNE ? I_BEQ : i.k == I_BLTU ? I_BGEU : I_BLTU;
                r->a = a; r->b = b; r->target = o + (size_t)i.len + (size_t)j.imm; r->at = *y;
                o += (size_t)i.len + 4;
                continue;
            }
            if (i.k == I_BGEU) return fail(x, "bgeu");
            r->kind = i.k; r->a = a; r->b = b; r->target = o + (size_t)i.imm; r->at = *y;
            break;
        }
        case I_JAL:
            if (i.rd == 1) { out->end = 3; out->callee = x->base + o + (u64)i.imm; out->next = o + (size_t)i.len; return 1; }
            if (i.rd) return fail(x, "jal with a link");
            out->end = 1; out->target = o + (size_t)i.imm;
            return 1;
        case I_JALR:
            if (i.rd == 0 && a.b == B_RET && a.k == 0 && i.imm == 0) { out->end = 2; out->ret = y->r[10]; return 1; }
            if (i.rd == 1 && a.b == B_CONST) { out->end = 3; out->callee = (u64)a.k + (u64)i.imm; out->next = o + (size_t)i.len; return 1; }
            return fail(x, "indirect jump");
        default: return fail(x, "instruction not in the domain");
        }
        o += (size_t)i.len;
    }
    return fail(x, "block too long");
}

/* value.h: is_ptr. */
static int is_pointer_tag(u64 v)
{
    unsigned t = v & 7;
    return t == SPIKE_TAG_OBJECT || t == SPIKE_TAG_PAIR || t == SPIKE_TAG_PROC || t == SPIKE_TAG_SYMBOL;
}

/* What the bytecode requires of an operand. */
static AV opnd(Ctx *x, u32 w)
{
    if (w & CONST_FLAG) {
        u32 i = w & ~CONST_FLAG;
        if (i >= x->nconst) return UNK;
        u64 v = *x->cells[i];
        /* Pointers are read through their cell, since a collection can move them. */
        return is_pointer_tag(v) ? lin(B_CELL, i, 0) : lin(B_CONST, 0, (i64)v);
    }
    return lin(B_SLOT, w, 0);
}

/* The canonical state after a block, with slot d (or NONE) given value v and HP moved by delta. */
static int canon(Ctx *x, const S *s, const Sym *y, u32 d, AV v, i64 delta, S *out, int heap_ok)
{
    if (!same(y->r[8], lin(B_FP, 0, 0)) || !same(y->r[9], lin(B_VM, 0, 0))) return fail(x, "FP or VM changed");
    if (!same(y->r[19], lin(B_HP, 0, delta))) return fail(x, "HP wrong");
    *out = *s;
    if (d != NONE32) {
        if (d >= 64) return fail(x, "slot above 63");
        out->M &= ~(1ull << d);
        out->P &= ~(1ull << d);
    }
    for (int i = 0; i < y->nw; i++) {
        AV a = y->w[i].a, w = y->w[i].v;
        if (a.b == B_FP && a.k > 0 && a.k % 8 == 0 && a.k / 8 < 64) {
            u32 n = (u32)(a.k / 8);
            if (n == d && same(w, v)) out->M |= 1ull << n;
            else if (n != d && same(w, lin(B_SLOT, n, 0))) out->M |= 1ull << n;
            else return fail(x, "store to the wrong slot");
        } else if (a.b == B_HP && heap_ok) {
            continue; /* checked by the caller */
        } else
            return fail(x, "store outside the frame and the new object");
    }
    AV c = y->r[18];
    if (d != NONE32 && same(c, v)) out->C = d;
    else if (c.b == B_SLOT && c.k == 0 && c.a != d) out->C = c.a;
    else out->C = NONE32;
    for (int k = 0; k < NKEPT; k++) {
#ifdef SPIKE_NO_KEPT
        out->K[k] = NONE32;
#else
        AV q = y->r[KEPT_X(k)];
        if (d != NONE32 && same(q, v)) out->K[k] = d;
        else if (q.b == B_SLOT && q.k == 0 && q.a != d) out->K[k] = q.a;
        else out->K[k] = NONE32;
#endif
    }
    return 1;
}

static int to_label(Ctx *x, u32 l, size_t target, const S *st)
{
    if (l >= x->nlabels) return fail(x, "label out of range");
    if (x->lab_off[l] != target) return fail(x, "branch goes elsewhere than the label");
    if (st->R) return fail(x, "reserved room at a label");
    if (!x->lab_seen[l]) { x->lab[l] = *st; x->lab_seen[l] = 1; return 1; }
    S *j = &x->lab[l];
    if (j->C != st->C) j->C = NONE32;
    for (int k = 0; k < NKEPT; k++)
        if (j->K[k] != st->K[k]) j->K[k] = NONE32;
    j->M &= st->M;
    j->P &= st->P;
    return 1;
}

static size_t insn_len(const uint32_t *p)
{
    switch (p[0]) {
    case OP_MOVE_: case OP_CONST_: return 3;
    case OP_PRIM_: return (size_t)4 + p[3];
    case OP_LABEL_: case OP_JUMP_: case OP_RETURN_: return 2;
    case OP_JIF_: return 3;
    default: return 0;
    }
}

static int check_fused(Ctx *x, const S *s, const uint32_t *p, const uint32_t *j, size_t from, size_t stop, int is_consp, S *out)
{
    Sym y; Run r;
    sym_init(&y, s);
    if (!run_block(x, s, &y, from, stop, &r)) return 0;
    if (r.end != 0) return fail(x, "test does not fall through");
    if (r.nb != 1) return fail(x, "test with other than one branch");
    Br *b = &r.b[0];
    u32 t = p[1];
    if (b->kind != I_BNE) return fail(x, "test branch kind");
    AV A = opnd(x, p[4]);
    if (is_consp) {
        if (!(p[4] < 64 && b->a.b == B_TAG && b->a.a == p[4] && same(b->b, lin(B_CONST, 0, 0)))) return fail(x, "cons? test wrong");
    } else {
        AV B = opnd(x, p[5]);
        if (!((same(b->a, A) && same(b->b, B)) || (same(b->a, B) && same(b->b, A)))) return fail(x, "= test wrong");
        if (!((p[4] & CONST_FLAG) || (p[5] & CONST_FLAG))) return fail(x, "= with no constant");
    }
    S taken;
    if (!canon(x, s, &b->at, t, UNK, 0, &taken, 0)) return 0;
    if (!to_label(x, j[2], b->target, &taken)) return 0;
    if (!canon(x, s, &y, t, UNK, 0, out, 0)) return 0;
    if (is_consp && p[4] != t) out->P |= 1ull << p[4];
    return 1;
}

static int check_slow(Ctx *x, size_t i)
{
    size_t target = x->slow[i].target;
    S st = x->slow[i].st;
    Sym y; Run r;
    sym_init(&y, &st);
    if (!run_block(x, &st, &y, target, SIZE_MAX, &r)) return 0;
    if (r.end != 3 || r.callee != x->h_alloc) return fail(x, "slow path does not call h_alloc");
    if (r.nb) return fail(x, "branch before h_alloc");
    int seen = 0;
    for (int k = 0; k < y.nw; k++) {
        AV a = y.w[k].a, v = y.w[k].v;
        if (a.b != B_VM) return fail(x, "slow path stores outside the VM");
        if (a.k == x->fp_off && same(v, lin(B_FP, 0, 0))) seen |= 1;
        else if (a.k == x->top_off && same(v, lin(B_FP, 0, (i64)x->frame * 8))) seen |= 2;
        else if (a.k == x->hp_off && same(v, lin(B_HP, 0, 0))) seen |= 4;
        else return fail(x, "slow path stored the wrong thing");
    }
    if (seen != 7) return fail(x, "slow path did not publish");
    if (!same(y.r[10], lin(B_VM, 0, 0)) || !same(y.r[11], lin(B_CONST, 0, x->slow[i].words))) return fail(x, "h_alloc arguments");
    /* After the call: FP and VM are callee-saved, and everything else is new. */
    S after = st;
    after.C = NONE32;
    for (int k = 0; k < NKEPT; k++) after.K[k] = NONE32; /* callee-saved, but a collection may have moved what they held */
    Sym z;
    sym_init(&z, &after);
    z.r[10] = lin(B_STATUS, 0, 0);
    z.r[19] = UNK;
    if (!run_block(x, &after, &z, r.next, SIZE_MAX, &r)) return 0;
    if (r.end != 1) return fail(x, "slow path does not jump back");
    if (r.nb != 1) return fail(x, "slow path raise check");
    Br *b = &r.b[0];
    if (b->kind != I_BEQ || !same(b->a, lin(B_STATUS, 0, 0)) || !same(b->b, lin(B_CONST, 0, 26)) ||
        (u64)x->base + b->target != x->unwind)
        return fail(x, "raise check wrong");
    if (r.target != x->slow[i].cut) return fail(x, "slow path goes back elsewhere");
    if (!same(z.r[19], lin(B_HP, 0, 0))) return fail(x, "HP not reloaded");
    if (st.C != NONE32 && !same(z.r[18], lin(B_SLOT, st.C, 0))) return fail(x, "CACHE not restored");
    for (int k = 0; k < NKEPT; k++)
        if (st.K[k] != NONE32 && !same(z.r[KEPT_X(k)], lin(B_SLOT, st.K[k], 0))) return fail(x, "kept register not restored");
    if (!same(z.r[8], lin(B_FP, 0, 0)) || !same(z.r[9], lin(B_VM, 0, 0))) return fail(x, "FP or VM changed");
    if (z.nw) return fail(x, "stores after h_alloc");
    return 1;
}

static int check_cons1(Ctx *x, const S *s, const uint32_t *p, size_t cut, size_t from, size_t stop, S *out, int eager);

/* A slow path that doesn't reload CACHE means nothing after relies on it: try again with CACHE dropped. */
static int check_cons(Ctx *x, S *s, const uint32_t *p, size_t cut, size_t from, size_t stop, S *out)
{
    size_t nslow = x->nslow;
    if (check_cons1(x, s, p, cut, from, stop, out, 1))
        return 1;
    if (!x->why) return 0;
    if (s->C != NONE32 && !strcmp(x->why, "CACHE not restored")) {
        x->why = NULL; x->nslow = nslow; s->C = NONE32;
        if (check_cons1(x, s, p, cut, from, stop, out, 1)) return 1;
        if (!x->why) return 0;
    }
    if ((s->K[0] != NONE32 || s->K[1] != NONE32) && !strcmp(x->why, "kept register not restored")) {
        x->why = NULL; x->nslow = nslow; s->K[0] = s->K[1] = NONE32;
        return check_cons1(x, s, p, cut, from, stop, out, 1);
    }
    return 0;
}

static int check_cons1(Ctx *x, const S *s, const uint32_t *p, size_t cut, size_t from, size_t stop, S *out, int eager)
{
    Sym y; Run r;
    sym_init(&y, s);
    if (!run_block(x, s, &y, from, stop, &r)) return 0;
    if (r.end != 0) return fail(x, "cons does not fall through");
    u32 R = s->R;
    if (R < 2) {
        if (r.nb != 1) return fail(x, "cons without its room check");
        Br *b = &r.b[0];
        if (b->kind != I_BLTU || !same(b->a, lin(B_HLIM, 0, 0)) || b->b.b != B_HP || b->b.k < 16 || b->b.k % 8 || b->b.k > 4096)
            return fail(x, "room check wrong");
        R = (u32)(b->b.k / 8);
        if (s->R) return fail(x, "room check with room reserved");
        x->slow[x->nslow].target = b->target; x->slow[x->nslow].cut = cut;
        x->slow[x->nslow].words = R; x->slow[x->nslow].st = *s; x->nslow++;
        if (eager && !check_slow(x, x->nslow - 1)) return 0;
    } else if (r.nb) return fail(x, "branch in a reserved cons");
    AV A = opnd(x, p[4]), B = opnd(x, p[5]);
    int seen = 0;
    for (int i = 0; i < y.nw; i++) {
        AV a = y.w[i].a;
        if (a.b != B_HP) continue;
        if (a.k == 0 && same(y.w[i].v, A)) seen |= 1;
        else if (a.k == 8 && same(y.w[i].v, B)) seen |= 2;
        else return fail(x, "cons wrote the wrong thing");
    }
    if (seen != 3) return fail(x, "cons left a field unwritten");
    /* Slot values do not change, and the new pair is HP + 3 before the move. */
    AV v = lin(B_HP, 0, 3);
    if (!canon(x, s, &y, p[1], v, 16, out, 1)) return 0;
    out->R = R - 2;
    if (p[1] < 64 && out->C == p[1]) out->P |= 1ull << p[1]; /* not needed; a pair by construction */
    return 1;
}

/* A prim the domain handles, and whether the next instruction must be its branch. */
int spike_in_domain(const uint32_t *w, size_t n, u32 p_consp, u32 p_eq, u32 p_cons, u32 p_hd, u32 p_tl)
{
    for (size_t i = 0; i < n;) {
        const uint32_t *p = w + i;
        size_t l = insn_len(p);
        if (!l) return 0;
        if (p[0] == OP_PRIM_) {
            if (p[2] == p_consp || p[2] == p_eq) {
                const uint32_t *j = p + l;
                if (i + l >= n || j[0] != OP_JIF_ || j[1] != p[1]) return 0;
                i += l + 3;
                continue;
            }
            if (p[2] != p_cons && p[2] != p_hd && p[2] != p_tl) return 0;
        } else if (p[0] == OP_JIF_) return 0;
        i += l;
    }
    return 1;
}

typedef struct {
    const uint8_t *code; size_t len; u64 base;
    const uint32_t *words; size_t nwords; const size_t *cuts; size_t first_cut;
    u32 frame, arity, nconst; const u64 *const *cells;
    u64 arity_stub, unwind, h_alloc;
    u32 hp_off, hlimit_off, fp_off, top_off;
    u32 p_consp, p_eq, p_cons, p_hd, p_tl;
    const char *name;
} SpikeFn;

const char *spike_check_fn(const SpikeFn *f)
{
    Ctx x; memset(&x, 0, sizeof x);
    S *seen = calloc(f->nwords + 1, sizeof *seen);
    uint8_t *has = calloc(f->nwords + 1, 1);
    x.code = f->code; x.len = f->len; x.base = f->base; x.words = f->words; x.nwords = f->nwords; x.cuts = f->cuts;
    x.frame = f->frame; x.arity = f->arity; x.nconst = f->nconst; x.cells = f->cells;
    x.arity_stub = f->arity_stub; x.unwind = f->unwind; x.h_alloc = f->h_alloc;
    x.hp_off = f->hp_off; x.hlimit_off = f->hlimit_off; x.fp_off = f->fp_off; x.top_off = f->top_off;
    u32 nl = 0;
    for (size_t i = 0; i < f->nwords; i += insn_len(f->words + i))
        if (f->words[i] == OP_LABEL_ && f->words[i + 1] + 1 > nl) nl = f->words[i + 1] + 1;
    x.nlabels = nl;
    x.lab = calloc(nl + 1, sizeof *x.lab); x.lab_seen = calloc(nl + 1, 1); x.lab_off = calloc(nl + 1, sizeof *x.lab_off);
    x.slow = calloc(f->nwords + 1, sizeof *x.slow);
    const char *ret = NULL;
    if (!x.lab || !x.lab_seen || !x.lab_off || !x.slow) { ret = "out of memory"; goto done; }
    for (size_t i = 0; i < f->nwords; i += insn_len(f->words + i))
        if (f->words[i] == OP_LABEL_) x.lab_off[f->words[i + 1]] = f->cuts[i];
    /* Entry: slots 0 to arity + 1 are in the frame, and the first argument is in CACHE too. */
    S s = {0, f->arity ? 2 : NONE32, 0, 0, 0, {NONE32, NONE32}};
    if (f->arity + 2 > 64) { ret = "too many arguments"; goto done; }
    s.M = ((1ull << (f->arity + 2)) - 1) & ~1ull;
    {
        Sym y; Run r;
        sym_init(&y, &s);
        y.r[12] = lin(B_COUNT, 0, 0);
        if (!run_block(&x, &s, &y, 0, f->first_cut, &r)) goto why;
        if (r.end != 0 || r.nb != 1) { if (getenv("SPIKE_DEBUG")) fprintf(stderr, "entry end=%d nb=%d first=%zu frame=%u arity=%u\n", r.end, r.nb, f->first_cut, f->frame, f->arity); fail(&x, "entry shape"); goto why; }
        Br *b = &r.b[0];
        if (b->kind != I_BNE || !same(b->a, lin(B_COUNT, 0, 0)) || !same(b->b, lin(B_CONST, 0, f->arity)) ||
            f->base + b->target != f->arity_stub) { fail(&x, "arity check wrong"); goto why; }
        if (s.C != NONE32 && !same(y.r[18], lin(B_SLOT, s.C, 0))) { fail(&x, "entry changed CACHE"); goto why; }
    }
    int falls = 1;
    for (size_t i = 0; i < f->nwords;) {
        const uint32_t *p = f->words + i;
        size_t l = insn_len(p), n = i + l, cut = f->cuts[i];
        S next;
        if (!falls && p[0] != OP_LABEL_) { /* unreachable code: nothing to check */ i = n; continue; }
        if (seen && falls) { seen[i] = s; has[i] = 1; }
        if (seen && p[0] == OP_LABEL_ && !falls && x.lab_seen[p[1]]) { seen[i] = x.lab[p[1]]; has[i] = 1; }
        switch (p[0]) {
        case OP_LABEL_: {
            u32 lb = p[1];
            if (falls) { if (!to_label(&x, lb, cut, &s)) goto why; }
            if (!x.lab_seen[lb]) { falls = 0; i = n; continue; }
            s = x.lab[lb];
            falls = 1; i = n;
            continue;
        }
        case OP_JUMP_: {
            Sym y; Run r;
            sym_init(&y, &s);
            if (!run_block(&x, &s, &y, cut, f->cuts[n], &r)) goto why;
            /* A jump to the next label may be elided. */
            size_t target = r.end == 1 ? r.target : f->cuts[n];
            if (r.nb) { fail(&x, "branch in a jump"); goto why; }
            S t;
            if (!canon(&x, &s, &y, NONE32, UNK, 0, &t, 0)) goto why;
            if (!to_label(&x, p[1], target, &t)) goto why;
            falls = 0; i = n;
            continue;
        }
        case OP_RETURN_: {
            Sym y; Run r;
            sym_init(&y, &s);
            if (!run_block(&x, &s, &y, cut, f->cuts[n], &r)) goto why;
            if (r.end != 2 || r.nb) { fail(&x, "return shape"); goto why; }
            if (!same(r.ret, opnd(&x, p[1]))) { fail(&x, "return value wrong"); goto why; }
            if (!same(y.r[8], lin(B_FP, 0, 0))) { fail(&x, "FP changed"); goto why; }
            if (!same(y.r[19], lin(B_HP, 0, 0))) { fail(&x, "HP changed"); goto why; }
            falls = 0; i = n;
            continue;
        }
        case OP_MOVE_: case OP_CONST_: {
            Sym y; Run r;
            sym_init(&y, &s);
            if (!run_block(&x, &s, &y, cut, f->cuts[n], &r)) goto why;
            if (r.end != 0 || r.nb) { fail(&x, "move shape"); goto why; }
            AV v = opnd(&x, p[0] == OP_MOVE_ ? p[2] : (p[2] | CONST_FLAG));
            if (!canon(&x, &s, &y, p[1], v, 0, &next, 0)) goto why;
            if (next.R != s.R) { fail(&x, "reservation"); goto why; }
            s = next; i = n;
            continue;
        }
        case OP_PRIM_:
            if (p[2] == f->p_consp || p[2] == f->p_eq) {
                const uint32_t *j = p + l;
                size_t m = n + 3;
                if (!check_fused(&x, &s, p, j, cut, f->cuts[m], p[2] == f->p_consp, &next)) goto why;
                s = next; i = m;
                continue;
            }
            if (p[2] == f->p_cons) {
                if (!check_cons(&x, &s, p, cut, cut, f->cuts[n], &next)) goto why;
                if (seen) seen[i] = s; /* CACHE may have been dropped */
                s = next; i = n;
                continue;
            }
            if (p[2] == f->p_hd || p[2] == f->p_tl) {
                if (p[4] >= 64 || !((s.P >> p[4]) & 1)) { fail(&x, "hd or tl of what is not known to be a pair"); goto why; }
                Sym y; Run r;
                sym_init(&y, &s);
                if (!run_block(&x, &s, &y, cut, f->cuts[n], &r)) goto why;
                if (r.end != 0 || r.nb) { fail(&x, "hd shape"); goto why; }
                AV v = lin(p[2] == f->p_hd ? B_HD : B_TL, p[4], 0);
                if (!canon(&x, &s, &y, p[1], v, 0, &next, 0)) goto why;
                s = next; i = n;
                continue;
            }
            fail(&x, "prim"); goto why;
        default:
            fail(&x, "opcode"); goto why;
        }
    }
    if (falls) { fail(&x, "falls off the end"); goto why; }
    for (size_t k = 0; k < x.nslow; k++)
        if (!check_slow(&x, k)) goto why;
    if (getenv("SPIKE_DUMP") && f->name && !strcmp(getenv("SPIKE_DUMP"), f->name)) {
        FILE *o = fopen(getenv("SPIKE_DUMP_OUT") ? getenv("SPIKE_DUMP_OUT") : "/tmp/spike-dump.txt", "w");
        fprintf(o, "base %llu\nlen %zu\nframe %u\narity %u\nh_alloc %llu\nunwind %llu\narity_stub %llu\nfirst_cut %zu\n",
                (unsigned long long)f->base, f->len, f->frame, f->arity, (unsigned long long)f->h_alloc,
                (unsigned long long)f->unwind, (unsigned long long)f->arity_stub, f->first_cut);
        fprintf(o, "bytes");
        for (size_t k = 0; k < f->len; k++) fprintf(o, " %u", f->code[k]);
        fprintf(o, "\nwords");
        for (size_t k = 0; k < f->nwords; k++) fprintf(o, " %u", f->words[k]);
        fprintf(o, "\ncuts");
        for (size_t k = 0; k <= f->nwords; k++) fprintf(o, " %lld", f->cuts[k] == SIZE_MAX ? -1LL : (long long)f->cuts[k]);
        fprintf(o, "\nconsts");
        for (u32 k = 0; k < f->nconst; k++) fprintf(o, " %llu:%llu", (unsigned long long)*f->cells[k], (unsigned long long)(uintptr_t)f->cells[k]);
        fprintf(o, "\nstates");
        for (size_t k = 0; k < f->nwords; k++)
            if (has[k]) fprintf(o, " %zu:%lld:%llu:%llu:%u:%lld:%lld", k, seen[k].C == NONE32 ? -1LL : (long long)seen[k].C,
                                (unsigned long long)seen[k].M, (unsigned long long)seen[k].P, seen[k].R,
                                seen[k].K[0] == NONE32 ? -1LL : (long long)seen[k].K[0], seen[k].K[1] == NONE32 ? -1LL : (long long)seen[k].K[1]);
        fprintf(o, "\nops consp=%u eq=%u cons=%u hd=%u tl=%u\n", f->p_consp, f->p_eq, f->p_cons, f->p_hd, f->p_tl);
        fclose(o);
    }
    goto done;
why:
    ret = x.why ? x.why : "rejected";
done:
    free(seen); free(has);
    free(x.lab); free(x.lab_seen); free(x.lab_off); free(x.slow);
    return ret;
}

/* Counters, printed at exit. SPIKE_STRICT=1 stops the process on a rejection. */
static size_t total, indom, accepted, rejected;
static struct { const char *why; size_t n; const char *eg; } reasons[64];
static int nreasons, registered;
static void report(void)
{
    if (!getenv("SPIKE_STATS")) return;
    fprintf(stderr, "spike-check: functions=%zu in_domain=%zu accepted=%zu rejected=%zu\n", total, indom, accepted, rejected);
    for (int i = 0; i < nreasons; i++)
        fprintf(stderr, "spike-check: reason %zu %s (e.g. %s)\n", reasons[i].n, reasons[i].why, reasons[i].eg ? reasons[i].eg : "?");
}
void spike_note(const char *name, const char *why, int in_domain)
{
    if (!registered) { registered = 1; atexit(report); }
    total++;
    if (!in_domain) return;
    indom++;
    if (!why) { accepted++; if (getenv("SPIKE_NAMES")) fprintf(stderr, "spike-accept %s\n", name ? name : "?"); return; }
    rejected++;
    int i;
    for (i = 0; i < nreasons; i++) if (!strcmp(reasons[i].why, why)) break;
    if (i < 64) {
        if (i == nreasons) { reasons[i].why = why; reasons[i].eg = name ? strdup(name) : NULL; nreasons++; }
        reasons[i].n++;
    }
    if (getenv("SPIKE_STRICT")) { fprintf(stderr, "spike-check: %s rejected: %s\n", name ? name : "?", why); abort(); }
}
