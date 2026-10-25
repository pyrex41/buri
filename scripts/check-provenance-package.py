"""Independent literal byte comparison, without semantic acceptance."""
from pathlib import Path
import re
import sys
kind, source, target = sys.argv[1:]
if kind not in ('bootstrap', 'observer', 'compiler_pass', 'checked_io'):
    raise SystemExit('Unknown packaging profile')
pattern = rb'Definition ' + kind.encode() + rb'_text : string := "([01]+)"\.'
if re.findall(pattern, Path(target).read_bytes()) != [Path(source).read_bytes()]:
    raise SystemExit('Provenance capture literal does not match source bytes')
