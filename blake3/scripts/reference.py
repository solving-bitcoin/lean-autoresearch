"""Independent word-level specialization of official BLAKE3 to 64 bytes."""
import struct

IV = (0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
      0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19)
PERM = (2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8)
MASK = (1 << 32)-1


def hash64(message: bytes) -> bytes:
    if not isinstance(message, bytes) or len(message) != 64:
        raise ValueError('expected exactly 64 bytes')
    m = list(struct.unpack('<16I', message))
    v = list(IV + IV[:4] + (0,0,64,11))
    def ror(x,n):
        return ((x >> n) | (x << (32-n))) & MASK
    def g(a,b,c,d,x,y):
        v[a] = (v[a]+v[b]+x) & MASK
        v[d] = ror(v[d]^v[a],16)
        v[c] = (v[c]+v[d]) & MASK
        v[b] = ror(v[b]^v[c],12)
        v[a] = (v[a]+v[b]+y) & MASK
        v[d] = ror(v[d]^v[a],8)
        v[c] = (v[c]+v[d]) & MASK
        v[b] = ror(v[b]^v[c],7)
    for _ in range(7):
        for a,b,c,d,x,y in ((0,4,8,12,0,1),(1,5,9,13,2,3),(2,6,10,14,4,5),(3,7,11,15,6,7),
                              (0,5,10,15,8,9),(1,6,11,12,10,11),(2,7,8,13,12,13),(3,4,9,14,14,15)):
            g(a,b,c,d,m[x],m[y])
        m = [m[i] for i in PERM]
    return struct.pack('<8I', *(v[i]^v[i+8] for i in range(8)))
