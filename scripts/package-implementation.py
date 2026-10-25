"""Package literal implementation source bytes, never theorem acceptance."""
from pathlib import Path
import sys
kind, source, destination = sys.argv[1:]
assert kind in ('stock_division',)
raw = Path(source).read_bytes()
assert all(b < 128 for b in raw)
text = raw.decode().replace('"', '""')
Path(destination).write_text('From Coq Require Import String.\nOpen Scope string_scope.\nDefinition '+kind+'_source : string := "'+text+'".\n')
