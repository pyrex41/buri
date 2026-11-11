# Census only (not proof): distinct procedures in the image function cells (docs/SHEN-JIT-IMAGE.md).
import struct, sys
b = open(sys.argv[1],'rb').read(); n = struct.unpack('<Q', b[-16:-8])[0]; W = struct.unpack('<%dQ' % (n//8), b[-n:])
hw, ce = W[6], W[7]; C = W[13+hw:13+hw+ce]
fs = [C[2*i+1] for i in range(ce//2)]
procs = [v for v in fs if v & 7 == 5]
print('function cells holding a procedure', len(procs), 'distinct', len(set(procs)))
