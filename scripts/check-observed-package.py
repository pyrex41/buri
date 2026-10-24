"""Independent exact-byte comparison; no syntax decoding or proof decisions."""
from pathlib import Path
import re
import sys
raw, module = map(Path, sys.argv[1:])
matches = re.findall(rb'Definition observed_encoder_text : string := "([01]+)"\.', module.read_bytes())
if len(matches) != 1 or matches[0] != raw.read_bytes():
    raise SystemExit('Proof input does not contain exact observed compilation bytes')
