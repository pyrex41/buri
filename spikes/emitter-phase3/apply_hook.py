#!/usr/bin/env python3
"""Adds spike 8's function checker to compile_code in Shen/JIT 0.3's jit.c. Usage: apply_hook.py jit.c"""
import sys
p=sys.argv[1]; s=open(p).read()
def rep(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
rep('''#define HP SLJIT_S3, 0
''','''#define HP SLJIT_S3, 0
typedef struct {
    const uint8_t *code; size_t len; uint64_t base;
    const uint32_t *words; size_t nwords; const size_t *cuts; size_t first_cut;
    uint32_t frame, arity, nconst; const uint64_t *const *cells;
    uint64_t arity_stub, unwind, h_alloc;
    uint32_t hp_off, hlimit_off, fp_off, top_off;
    uint32_t p_consp, p_eq, p_cons, p_hd, p_tl;
    const char *name;
} SpikeFn;
const char *spike_check_fn(const SpikeFn *f);
int spike_in_domain(const uint32_t *w, size_t n, uint32_t p_consp, uint32_t p_eq, uint32_t p_cons, uint32_t p_hd, uint32_t p_tl);
void spike_note(const char *name, const char *why, int in_domain);
''')
rep('''    bool falls = true;
    size_t mark = 0;
    for (size_t i = 0; i < nwords; i += insn_length(words + i)) {
        const uint32_t *p = words + i;
''','''    bool falls = true;
    size_t mark = 0;
    /* Spike 8: mark each instruction's first byte, for the checker. */
    struct sljit_label **spike_cuts = calloc(nwords + 1, sizeof *spike_cuts);
    struct sljit_label *spike_first = sljit_emit_label(c);
    for (size_t i = 0; i < nwords; i += insn_length(words + i)) {
        const uint32_t *p = words + i;
        if (spike_cuts)
            spike_cuts[i] = sljit_emit_label(c);
''')
rep('''    e.cached = NONE; /* slow paths read operands from their slots */
''','''    if (spike_cuts)
        spike_cuts[nwords] = sljit_emit_label(c);
    e.cached = NONE; /* slow paths read operands from their slots */
''')
rep('''        native = (void *)sljit_get_label_addr(entry);
''','''        native = (void *)sljit_get_label_addr(entry);
        {
            int dom = spike_in_domain(words, nwords, P_CONSP, P_EQ, P_CONS, P_HD, P_TL) && !e.homes && !e.loops &&
                      !all && !e.nmemory && e.frame < 64;
            const char *why = NULL;
            if (dom && spike_cuts) {
                size_t *cuts = malloc((nwords + 1) * sizeof *cuts);
                const uint64_t **cells = malloc((e.nconst + 1) * sizeof *cells);
                for (uint32_t k = 0; k < e.nconst; k++)
                    cells[k] = (const uint64_t *)ra_at(&vm->consts, e.cbase + k);
                uintptr_t b = (uintptr_t)native;
                for (size_t k = 0; k <= nwords; k++)
                    cuts[k] = spike_cuts[k] ? (size_t)(sljit_get_label_addr(spike_cuts[k]) - b) : SIZE_MAX;
                SpikeFn f = {.code = (const uint8_t *)native, .len = ((const size_t *)native)[-2] - 2 * sizeof(size_t), /* the arena block (spikes-overlay/arena.c) */
                             .base = b, .words = words, .nwords = nwords, .cuts = cuts,
                             .first_cut = (size_t)(sljit_get_label_addr(spike_first) - b),
                             .frame = (uint32_t)e.frame, .arity = e.arity, .nconst = (uint32_t)e.nconst, .cells = cells,
                             .arity_stub = (uint64_t)(uintptr_t)vm->jit->arity, .unwind = (uint64_t)(uintptr_t)vm->jit->unwind,
                             .h_alloc = (uint64_t)(uintptr_t)h_alloc,
                             .hp_off = offsetof(VM, hp), .hlimit_off = offsetof(VM, hlimit), .fp_off = offsetof(VM, fp),
                             .top_off = offsetof(VM, top), .p_consp = P_CONSP, .p_eq = P_EQ, .p_cons = P_CONS,
                             .p_hd = P_HD, .p_tl = P_TL, .name = symbol_cstr_spike(vm, co[CODE_NAME])};
                why = spike_check_fn(&f);
                free(cuts);
                free(cells);
            }
            spike_note(symbol_cstr_spike(vm, co[CODE_NAME]), why, dom);
            /* Spike 9: SPIKE_RAW=NAME writes the words, cuts and constants of NAME whether or not it is in the domain. */
            const char *raw = getenv("SPIKE_RAW"), *nm = symbol_cstr_spike(vm, co[CODE_NAME]);
            if (raw && nm && !strcmp(raw, nm) && spike_cuts) {
                FILE *o = fopen(getenv("SPIKE_RAW_OUT") ? getenv("SPIKE_RAW_OUT") : "/tmp/spike-raw.txt", "w");
                uintptr_t b = (uintptr_t)native;
                fprintf(o, "base %llu\\nframe %u\\narity %u\\nunwind %llu\\nh_alloc %llu\\narity_stub %llu\\nfirst_cut %lld\\nwords",
                        (unsigned long long)b, (unsigned)e.frame, (unsigned)e.arity, (unsigned long long)(uintptr_t)vm->jit->unwind,
                        (unsigned long long)(uintptr_t)h_alloc, (unsigned long long)(uintptr_t)vm->jit->arity,
                        (long long)(sljit_get_label_addr(spike_first) - b));
                for (size_t k = 0; k < nwords; k++) fprintf(o, " %u", words[k]);
                fprintf(o, "\\ncuts");
                for (size_t k = 0; k <= nwords; k++)
                    fprintf(o, " %lld", spike_cuts[k] ? (long long)(sljit_get_label_addr(spike_cuts[k]) - b) : -1LL);
                fprintf(o, "\\nconsts");
                for (uint32_t k = 0; k < e.nconst; k++) {
                    V *cl = ra_at(&vm->consts, e.cbase + k);
                    fprintf(o, " %llu:%llu", (unsigned long long)*cl, (unsigned long long)(uintptr_t)cl);
                }
                fprintf(o, "\\n");
                fclose(o);
            }
        }
''')
open(p,'w').write(s)
