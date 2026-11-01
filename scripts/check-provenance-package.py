"""Independent literal byte comparison, without semantic acceptance."""
from pathlib import Path
import re
import sys
kind, source, target = sys.argv[1:]
if kind not in ('bootstrap', 'observer', 'compiler_pass', 'checked_io', 'order_call', 'observer_forms', 'io_read', 'equality_core', 'equality_seal', 'kernel_list', 'eq1_base', 'eq1_equations', 'eq1_theory', 'eq1_kernel', 'e2e07_klambda'):
    raise SystemExit('Unknown packaging profile')
module = Path(target).read_bytes()
if kind.startswith('eq1_') or kind == 'e2e07_klambda':
    # Chunked literal: numbered pieces, consecutive from 0, joined in order.
    found = re.findall(rb'Definition ' + kind.encode() + rb'_text_([0-9]+) : string := "([01]+)"\.', module)
    joined = re.findall(rb'Definition ' + kind.encode() + rb'_text : string := \(([^)]*)\)%string\.', module)
    order = [kind.encode() + b'_text_' + str(i).encode() for i in range(len(found))]
    if (not found or [int(i) for i, _ in found] != list(range(len(found))) or
            joined != [b' ++ '.join(order)] or
            b''.join(p for _, p in found) != Path(source).read_bytes()):
        raise SystemExit('Provenance capture literal does not match source bytes')
else:
    pattern = rb'Definition ' + kind.encode() + rb'_text : string := "([01]+)"\.'
    if re.findall(pattern, module) != [Path(source).read_bytes()]:
        raise SystemExit('Provenance capture literal does not match source bytes')
