"""Independent byte-for-byte check of literal packaging, not semantics."""
from pathlib import Path
import re
import sys

source, packaged = map(Path, sys.argv[1:])
matches = re.findall(rb'Definition sealed_text : string := "([01]+)"\.', packaged.read_bytes())
if matches != [source.read_bytes()]:
    raise SystemExit('Sealed capture literal does not match source bytes')
