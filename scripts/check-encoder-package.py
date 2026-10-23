"""Independent byte identity gate; Rocq checks the source-to-program equation."""
from pathlib import Path
import re
import sys

raw = Path(sys.argv[1]).read_bytes()
module = Path(sys.argv[2]).read_text()
match = re.search(r'Definition encoder_source_text : string := "((?:""|[^"])*)"\.', module)
assert match and match[1].replace('""', '"').encode('ascii') == raw, 'Proof input differs from exact loaded encoder source bytes'
