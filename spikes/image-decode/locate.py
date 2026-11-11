# Census only (not proof): the measuring scripts of docs/SHEN-JIT-IMAGE.md.
import struct, sys
b = open(sys.argv[1],'rb').read(); n = struct.unpack('<Q', b[-16:-8])[0]; W = struct.unpack('<%dQ' % (n//8), b[-n:])
hw, ce = W[6], W[7]; H = W[13:13+hw]; C = W[13+hw:13+hw+ce]
i = 0
def sb(o): s = H[o]>>8; return b''.join(struct.pack('<Q', H[o+1+j]) for j in range((s+7)//8))[:s]
while i < hw:
    w = H[i]
    if w & 7 == 7:
        t = (w>>3)&31
        if t == 3 and sb(H[i+1]>>3) == b'print':
            cell = H[i+3] & ((1<<56)-1); clo = C[2*cell+1] >> 3; code = H[clo+2] >> 3; bc = H[code+8] >> 3
            print('code abs word', 13+code, 'arity word', 13+code+2, H[code+2], 'bytecode first word abs', 13+bc+1, hex(H[bc+1]))
        sz = H[i]>>8
        i += {1:max(2,1+(sz+7)//8),2:max(2,1+(sz+7)//8),3:4,4:2,5:max(2,1+sz),6:3+sz,7:5,8:10,9:3,10:3,11:5}[t]
    else: i += 2
