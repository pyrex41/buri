#!/usr/bin/env python3
"""Makes the image for the proofs: spike 2's `runtime` ELF with only p_memsz of its one
LOAD changed to p_filesz, so the snapshot holds the file's bytes without the 64 MiB
NOBITS code arena and .bss. Every instruction and rodata byte stays identical; the gate
below checks that exactly that one field differs. (shen-jit = runtime + image appended.)
Usage: mkimage.py RUNTIME OUT"""
import hashlib,struct,sys
src,out=sys.argv[1:3]
b=bytearray(open(src,'rb').read())
assert hashlib.sha256(b).hexdigest()=="de349ea06fc770e1dcf735f416a1713c93715aa7371528001918bdd635dcbd38"
phoff=struct.unpack_from('<Q',b,32)[0]; phent,phnum=struct.unpack_from('<HH',b,54)
loads=[phoff+i*phent for i in range(phnum) if struct.unpack_from('<I',b,phoff+i*phent)[0]==1]
assert len(loads)==1
o=loads[0]; filesz,memsz=struct.unpack_from('<QQ',b,o+32)
orig=bytes(b)
struct.pack_into('<Q',b,o+40,filesz)
diff=[i for i in range(len(b)) if b[i]!=orig[i]]
assert all(o+40<=i<o+48 for i in diff),diff
# Mutation testing only (mutate.sh): overwrite bytes at a virtual address.
if len(sys.argv)>3:
    va,hexb=sys.argv[3].split(':')
    b[int(va,16)-0x10000:int(va,16)-0x10000+len(bytes.fromhex(hexb))]=bytes.fromhex(hexb)
open(out,'wb').write(b)
print(f"memsz {memsz:#x} -> {filesz:#x}; {len(diff)} bytes differ, all in p_memsz; sha256 {hashlib.sha256(b).hexdigest()}")
