#!/usr/bin/env python3
"""The proof image: the check build's `runtime` ELF with only p_memsz of its one LOAD set to p_filesz,
which drops the 64 MiB NOBITS arena and .bss. Instruction and rodata bytes stay identical.
Usage: mkimage.py RUNTIME OUT [ADDR:HEX]  (the byte patch is for mutation testing only)."""
import struct,sys
src,out=sys.argv[1:3]
b=bytearray(open(src,'rb').read())
phoff=struct.unpack_from('<Q',b,32)[0]; phent,phnum=struct.unpack_from('<HH',b,54)
loads=[phoff+i*phent for i in range(phnum) if struct.unpack_from('<I',b,phoff+i*phent)[0]==1]
assert len(loads)==1
o=loads[0]; filesz,memsz=struct.unpack_from('<QQ',b,o+32)
orig=bytes(b); struct.pack_into('<Q',b,o+40,filesz)
assert all(o+40<=i<o+48 for i in range(len(b)) if b[i]!=orig[i])
if len(sys.argv)>3:
    va,h=sys.argv[3].split(':'); hb=bytes.fromhex(h); b[int(va,16)-0x10000:int(va,16)-0x10000+len(hb)]=hb
open(out,'wb').write(b)
