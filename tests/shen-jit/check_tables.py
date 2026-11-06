#!/usr/bin/env python3
"""Compare JitBytecode.v's primitive table with prims.c and its instructions with ops.h.
Orchestration only: it catches drift between the model and the pinned source."""
import re, sys
root, src = sys.argv[1], sys.argv[2]
model = open(root + '/rocq/JitBytecode.v', encoding='utf-8').read()
prims = open(src + '/src/runtime/prims.c', encoding='utf-8').read()
ops = open(src + '/src/runtime/ops.h', encoding='utf-8').read()
table = prims[prims.index('primitive_table[] = {'):prims.index('const size_t primitive_count')]
c = re.findall(r'\{"([^"]+)", (\d+), NULL\}', table)
body = model[model.index('Definition prim_table'):model.index('Inductive operand')]
m = re.findall(r'\("([^"]+)",\s*P\w+,\s*(\d+)\)', body)
bad = 0
if m[:-1] != c:
    print('PRIM_TABLE_DRIFT', sorted(set(m[:-1]) ^ set(c))[:10] or 'order'); bad = 1
if m[-1] != ('raise-cond', '0'):
    print('PRIM_TABLE_DRIFT raise-cond'); bad = 1
cops = re.findall(r'X\(OP_\w+, "([^"]+)", \d+\)', ops)
for op in cops:
    if not re.search(r'S_' + re.sub(r'[^a-z0-9]', '_', op) + r'\b', model):
        print('OPCODE_DRIFT', op); bad = 1
print('tables: %d primitives, %d opcodes, %s' % (len(c), len(cops), 'DRIFT' if bad else 'match'))
sys.exit(bad)
