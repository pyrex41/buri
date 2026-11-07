#!/usr/bin/env python3
"""Adds counters for 0.4's kept registers to compile_code in Shen/JIT 0.4's jit.c. Usage: stats_hook.py jit.c
They only count: no emitted code changes. Printed at exit when SPIKE_STATS is set, as `spike-kept: ...`."""
import sys
p = sys.argv[1]; s = open(p).read()
def rep(a, b):
    global s
    assert s.count(a) == 1, a
    s = s.replace(a, b)

rep('''static void *compile_code(VM *vm, V code)
{''', '''/* Spike 9: counters for the kept registers. */
extern unsigned long spike_k_slow_reload;
static struct {
    unsigned long fns, fns_keeps, fns_used, insns, insns_keeps, insns_pre, insns_read, labels, labels_keeps, labels_carry,
        slow_reload;
} spike_k;
static int spike_k_reg;
static void spike_k_report(void)
{
    if (!getenv("SPIKE_STATS")) return;
    fprintf(stderr, "spike-kept: functions=%lu keeps=%lu using=%lu instructions=%lu in_keeps=%lu "
                    "kept_live_before=%lu reading_kept=%lu labels=%lu labels_in_keeps=%lu labels_carrying=%lu slow_reloads=%lu\\n",
            spike_k.fns, spike_k.fns_keeps, spike_k.fns_used, spike_k.insns, spike_k.insns_keeps, spike_k.insns_pre,
            spike_k.insns_read, spike_k.labels, spike_k.labels_keeps, spike_k.labels_carry, spike_k_slow_reload);
}

static void *compile_code(VM *vm, V code)
{
    if (!spike_k_reg) { spike_k_reg = 1; atexit(spike_k_report); }
    int spike_used = 0;''')
rep('''    e.keeps = !e.homes && !e.reals && !e.word_regs && !e.nmemory && !e.raw_saved && SAVED_HOMES >= KEPT;
''', '''    e.keeps = !e.homes && !e.reals && !e.word_regs && !e.nmemory && !e.raw_saved && SAVED_HOMES >= KEPT;
    spike_k.fns++;
    if (e.keeps) spike_k.fns_keeps++;
''')
rep('''        const uint32_t kept_pre[KEPT] = {e.kept[0], e.kept[1]};
''', '''        const uint32_t kept_pre[KEPT] = {e.kept[0], e.kept[1]};
        spike_k.insns++;
        if (e.keeps) spike_k.insns_keeps++;
        if (kept_pre[0] != NONE || kept_pre[1] != NONE) {
            spike_k.insns_pre++;
            spike_used = 1;
            if ((kept_pre[0] != NONE && reads_slot(p, kept_pre[0])) || (kept_pre[1] != NONE && reads_slot(p, kept_pre[1])))
                spike_k.insns_read++;
        }
''')
rep('''            for (int k = 0; k < KEPT; k++)
                e.kept_post[k] = e.at_label[p[1]].seen ? e.at_label[p[1]].kept[k] : NONE;
            break;''', '''            for (int k = 0; k < KEPT; k++)
                e.kept_post[k] = e.at_label[p[1]].seen ? e.at_label[p[1]].kept[k] : NONE;
            spike_k.labels++;
            if (e.keeps) spike_k.labels_keeps++;
            if (e.kept_post[0] != NONE || e.kept_post[1] != NONE) spike_k.labels_carry++;
            break;''')
rep('''    for (int k = 0; k < KEPT; k++)
        if (s->kept[k] != NONE)
            sljit_emit_op1(e->c, SLJIT_MOV, KEPT_REG(k), 0, SLOT(s->kept[k]));
    sljit_set_label''', '''    for (int k = 0; k < KEPT; k++)
        if (s->kept[k] != NONE) {
            spike_k_slow_reload++;
            sljit_emit_op1(e->c, SLJIT_MOV, KEPT_REG(k), 0, SLOT(s->kept[k]));
        }
    sljit_set_label''')
rep('''    e.cached = NONE; /* slow paths read operands from their slots */
''', '''    if (spike_used) spike_k.fns_used++;
    e.cached = NONE; /* slow paths read operands from their slots */
''')
# The reload counter is defined before go_back, which comes before compile_code.
rep('''static void go_back(Emit *e, const Slow *s)
{''', '''unsigned long spike_k_slow_reload;
static void go_back(Emit *e, const Slow *s)
{''')
open(p, 'w').write(s)
