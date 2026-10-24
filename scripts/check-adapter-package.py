"""Independent literal-byte check; no semantic acceptance decisions."""
from pathlib import Path
import re
import sys
source, target = map(Path, sys.argv[1:])
if re.findall(rb'Definition adapter_text : string := "([01]+)"\.', target.read_bytes()) != [source.read_bytes()]:
    raise SystemExit('Adapter capture literal does not match source bytes')
