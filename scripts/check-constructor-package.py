"""Independent literal-byte consistency check, never a semantic checker."""
from pathlib import Path
import re
import sys

capture, packaged = map(Path, sys.argv[1:])
matches = re.findall(rb'Definition constructor_text : string := "([01]+)"\.', packaged.read_bytes())
if matches != [capture.read_bytes()]:
    raise SystemExit('Constructor capture literal does not match source bytes')
