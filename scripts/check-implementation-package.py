"""Independent literal correspondence check, not semantic acceptance."""
from pathlib import Path
import re
import sys
kind, source, target = sys.argv[1:]
if kind != 'stock_division':
    raise SystemExit('Unknown source profile')
texts = re.findall(r'Definition stock_division_source : string := "(.*)"\.\n', Path(target).read_text(), re.S)
if len(texts) != 1 or texts[0].replace('""','"').encode('ascii') != Path(source).read_bytes():
    raise SystemExit('Implementation source literal does not match source bytes')
