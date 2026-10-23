"""Check byte identity across packaging; Rocq decides semantic validity."""
from pathlib import Path
import re
import sys
raw, module = map(Path, sys.argv[1:])
bits = raw.read_bytes()
source = module.read_bytes()
assert bits and all(b in b'01' for b in bits), 'Malformed transport bytes'
strings = re.findall(rb'Definition native_capture_text : string := "([01]+)"\.', source)
assert strings == [bits], 'Rocq input does not contain the exact captured bytes'
