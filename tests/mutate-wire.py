"""Adversarial fixture construction only; never used for acceptance."""
from pathlib import Path

bits = Path('ports/native-capture.bits').read_text()
index = 0

def read():
    global index
    bit = bits[index]
    index += 1
    if bit == '1':
        return ('cons', read(), read())
    kind = bits[index]
    index += 1
    if kind == '0':
        return ('nil',)
    tag = bits[index]
    index += 1
    payload = bytearray()
    while bits[index] == '1':
        index += 1
        payload.append(sum(int(bits[index + i]) << i for i in range(8)))
        index += 8
    index += 1
    return ('atom', tag, bytes(payload))

def encode(d):
    if d[0] == 'nil':
        return '00'
    if d[0] == 'cons':
        return '1' + encode(d[1]) + encode(d[2])
    return '01' + d[1] + ''.join('1' + ''.join(str((c >> i) & 1) for i in range(8))
                                for c in d[2]) + '0'

def unpack(d):
    result = []
    while d[0] == 'cons':
        result.append(d[1])
        d = d[2]
    assert d == ('nil',)
    return result

def pack(xs):
    result = ('nil',)
    for x in reversed(xs):
        result = ('cons', x, result)
    return result

root = read()
assert index == len(bits) and encode(root) == bits
profile, records_d = unpack(root)
records = unpack(records_d)
assert len(records) == 12
first = unpack(records[0])
target = unpack(first[3])
assert target[0] == ('atom', '0', b'+')
target[0] = ('atom', '0', b'*')
first[3] = pack(target)
corrupt = pack([profile, pack([pack(first)] + records[1:])])
mutations = {
    'CorruptCapture': encode(corrupt),
    'TruncatedCapture': bits[:-1],
    'TrailingCapture': bits + '0',
    'OmittedCaptureRecord': encode(pack([profile, pack(records[:-1])])),
    'WrongCaptureProfile': encode(pack([('atom', '0', b'buri-native-2'), records_d])),
}
for name, content in mutations.items():
    Path('_build/mutations', name + '.bits').write_text(content)
