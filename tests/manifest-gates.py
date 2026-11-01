"""Regression checks for the build-manifest comparer (identity evidence, not proof)."""
import copy
import json
import pathlib
import subprocess
import sys
import tempfile

root = pathlib.Path(__file__).resolve().parent.parent
tool = root / 'scripts/build-manifest.py'
base = {
    'schema': 'buri-build-manifest-1', 'kind': 'identity-evidence-not-proof',
    'sources': {'rocq/A.v': '00'},
    'tools': {'coq': {'payload_tree_sha256': '11'}, '_launch': {'route': 'host-bootstrap'}},
    'environment': {'variables': {'TZ': None}, '_informational': {'PATH': '/a'}},
    'outputs': {'proof_objects': {'rocq/A.vo': '22'}, 'logs_normalized': {'a.log': '33'},
                '_volatile': {'coq_aux': {'rocq/.A.aux': '44'}}},
}


def outcome(a, b):
    with tempfile.TemporaryDirectory(prefix='buri-manifest-gate-') as directory:
        left, right = pathlib.Path(directory, 'a.json'), pathlib.Path(directory, 'b.json')
        left.write_text(json.dumps(a))
        right.write_text(json.dumps(b))
        result = subprocess.run([sys.executable, str(tool), 'compare', str(left), str(right)],
                                capture_output=True, text=True)
        return result.returncode, result.stdout


count = 0
code, out = outcome(base, base)
assert code == 0 and 'BURI_MANIFEST_IDENTICAL' in out
count += 1

routed = copy.deepcopy(base)
routed['tools']['_launch']['route'] = 'nix'
routed['environment']['_informational']['PATH'] = '/b'
routed['outputs']['_volatile']['coq_aux']['rocq/.A.aux'] = '55'
code, out = outcome(base, routed)
assert code == 0 and out.count('EXPLAINED-DIFF') == 3 and 'IDENTITY-DIFF' not in out
count += 1

for path in [('sources', 'rocq/A.v'), ('outputs', 'proof_objects', 'rocq/A.vo'),
             ('outputs', 'logs_normalized', 'a.log'), ('tools', 'coq', 'payload_tree_sha256')]:
    changed = copy.deepcopy(base)
    node = changed
    for key in path[:-1]:
        node = node[key]
    node[path[-1]] = 'ff'
    code, out = outcome(base, changed)
    assert code == 1 and 'IDENTITY-DIFF ' + '/'.join(path) in out, path
    count += 1

extra = copy.deepcopy(base)
extra['outputs']['proof_objects']['rocq/B.vo'] = '66'
code, out = outcome(base, extra)
assert code == 1 and '<absent>' in out
count += 1

env = copy.deepcopy(base)
env['environment']['variables']['TZ'] = 'UTC'
code, out = outcome(base, env)
assert code == 3 and 'ENVIRONMENT-DIFF environment/variables/TZ' in out
count += 1

wrong = copy.deepcopy(base)
wrong['schema'] = 'other'
code, out = outcome(base, wrong)
assert code == 2
count += 1

print('BURI_MANIFEST_GATE_TESTS_OK %d' % count)
