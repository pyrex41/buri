"""Independent comparison of captured bytes and the literal proof input."""
from pathlib import Path
import re
import sys

raw = Path(sys.argv[1]).read_bytes()
module = Path(sys.argv[2]).read_text()
match = re.search(r'Definition encoder_kl_text : string := "([01]+)"\.', module)
assert match and match[1].encode('ascii') == raw, 'Proof input differs from exact KLambda capture bytes'
