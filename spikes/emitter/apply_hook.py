import sys
p=sys.argv[1]; s=open(p).read()
a='''        case OP_MOVE:
            if (to_home(&e, p[1])) {
                sljit_emit_op1(c, SLJIT_MOV, HOME(&e, p[1]), OPND(&e, p[2]));
                break;
            }
            sljit_emit_op1(c, SLJIT_MOV, R0, OPND(&e, p[2]));
            store_result(&e, p[1]);
            break;
'''
b='''        case OP_MOVE: {
            /* Spike 7: mark the bytes of each move, for the checker after code generation. */
            struct sljit_label *spike_l0 = sljit_emit_label(c);
            if (to_home(&e, p[1])) {
                sljit_emit_op1(c, SLJIT_MOV, HOME(&e, p[1]), OPND(&e, p[2]));
            } else {
                sljit_emit_op1(c, SLJIT_MOV, R0, OPND(&e, p[2]));
                store_result(&e, p[1]);
            }
            if (spike_moves && spike_nmoves < ninsns) {
                spike_moves[spike_nmoves].dst = p[1];
                spike_moves[spike_nmoves].src = p[2];
                spike_moves[spike_nmoves].cached = pre;
                spike_moves[spike_nmoves].homes = e.homes;
                spike_moves[spike_nmoves].keep = e.post == p[1];
                spike_moves[spike_nmoves].from = spike_l0;
                spike_moves[spike_nmoves].to = sljit_emit_label(c);
                spike_nmoves++;
            }
            break;
        }
'''
assert s.count(a)==1; s=s.replace(a,b)
a='''    struct sljit_compiler *c = e.c;
    void *native = NULL, *generated = NULL;
'''
b='''    struct sljit_compiler *c = e.c;
    void *native = NULL, *generated = NULL;
    struct spike_move { uint32_t dst, src, cached, homes, keep; struct sljit_label *from, *to; } *spike_moves =
        calloc(ninsns + 1, sizeof *spike_moves);
    size_t spike_nmoves = 0;
'''
assert s.count(a)==1; s=s.replace(a,b)
a='''        native = (void *)sljit_get_label_addr(entry);
        vm->jit->ncompiled++;
'''
b='''        native = (void *)sljit_get_label_addr(entry);
        vm->jit->ncompiled++;
        for (size_t k = 0; k < spike_nmoves; k++) {
            struct spike_move *m = &spike_moves[k];
            spike_check_move_gate((const uint8_t *)sljit_get_label_addr(m->from),
                                  (const uint8_t *)sljit_get_label_addr(m->to), m->dst, m->src, m->homes,
                                  m->cached, m->keep);
        }
'''
assert s.count(a)==1; s=s.replace(a,b)
a='''#define HP SLJIT_S3, 0
'''
b='''#define HP SLJIT_S3, 0
void spike_check_move_gate(const uint8_t *at, const uint8_t *end, uint32_t dst, uint32_t src, uint32_t homes,
                           uint32_t cached, uint32_t keep);
'''
assert s.count(a)==1; s=s.replace(a,b)
open(p,'w').write(s)
