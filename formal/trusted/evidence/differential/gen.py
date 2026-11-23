# Inputs of the differential check (run.sh). Writes enc.txt, dec.txt, utf8.txt, cps.txt (hex lines)
# into the directory given as argument; deterministic: seed random.Random(20261123) for the
# original inputs, and a second stream random.Random(20261124) for the long inputs added in fix
# round 3 (so the original inputs are unchanged).
import random, sys
import base64 as B
out = sys.argv[1]
rng = random.Random(20261123)
rng2 = random.Random(20261124)
def w(name, lines):
    with open(f"{out}/{name}", "w") as f:
        for l in lines: f.write(l + "\n")
hx = lambda b: b.hex() if b else "-"
# encode: 10000 random byte strings len 0..200
enc = [bytes(rng.randrange(256) for _ in range(rng.randrange(201))) for _ in range(10000)]
# long inputs (fix round 3): the encoder works in 768-byte chunks (ChunkedEncoder, 1024 symbols)
# and its fast loop handles 24 input bytes (32 symbols) per step, so lengths around one and two
# chunk boundaries, around 32-symbol steps, and about 3000 bytes (several chunks) are covered.
LONG = list(range(760, 777)) + list(range(1530, 1545)) + list(range(2300, 2310)) \
    + list(range(2990, 3011)) + [24 * k + d for k in range(1, 12) for d in (-1, 0, 1)]
for n in LONG:
    for _ in range(4):
        enc.append(bytes(rng2.randrange(256) for _ in range(n)))
    enc.append(bytes([0xff]) * n)
    enc.append(bytes(n))
w("enc.txt", [hx(b) for b in enc])
# decode
dec = []
A = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
# 50000 random ASCII strings (any byte 0..127), length 0..40
for _ in range(50000):
    dec.append(bytes(rng.randrange(128) for _ in range(rng.randrange(41))))
# 20000 random strings mostly-valid alphabet with sparse corruption
EXTRA = b"=+/ \t\n\r\x00\x80\xff.~"
for _ in range(20000):
    n = rng.randrange(0, 60)
    s = bytearray(rng.choice(A) for _ in range(n))
    k = rng.choice([0,0,1,1,2])
    for _ in range(k):
        if s: s[rng.randrange(len(s))] = rng.choice(EXTRA)
    dec.append(bytes(s))
# encodings of random bytes (valid), with every possible single-symbol mutation of the last symbol
for _ in range(2000):
    b = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 40)))
    e = B.urlsafe_b64encode(b).rstrip(b"=")
    dec.append(e)
    dec.append(e + b"=")  # padding at end
    dec.append(B.urlsafe_b64encode(b))  # canonical padding
    for c in A:  # non-canonical trailing bits etc.
        if rng.random() < 0.25: dec.append(e[:-1] + bytes([c]))
    i = rng.randrange(len(e)+1)
    dec.append(e[:i] + b"=" + e[i:])
    dec.append(e[:i] + b" " + e[i:])
    dec.append(e[:i] + b"\n" + e[i:])
    dec.append(e.replace(b"-", b"+").replace(b"_", b"/"))
    dec.append(e + b"A")  # length change
    dec.append(e[:-1] if len(e) > 1 else e)
# exhaustive length 0..2 over all bytes
dec.append(b"")
for a in range(256): dec.append(bytes([a]))
for a in range(256):
    for b in range(256): dec.append(bytes([a, b]))
# exhaustive length 3 and 4 over a reduced alphabet
R = b"AQgwBf-_=+/ \x80z09"
for a in R:
    for b in R:
        for c in R:
            dec.append(bytes([a,b,c]))
            for d in R: dec.append(bytes([a,b,c,d]))
# padding everywhere in 8-char strings
for s in [b"QUJDREVG", b"QUJDRA", b"QUI", b"QQ"]:
    for i in range(len(s)+1):
        for p in [b"=", b"==", b"==="]:
            dec.append(s[:i] + p + s[i:])
# length 1 mod 4
for n in [1,5,9,13,101]:
    dec.append(b"A"*n)
# long decode inputs (fix round 3): encodings of 1..300 bytes (2..400 symbols), so the 32-symbol
# steps of the decoder's fast loop and the final partial quads are passed before an error, with a
# corruption late in the input (in the last 40 symbols, often in the last quad).
BAD = b"=+/ \n\x00\x80\xff.~"
for n in range(1, 301):
    for _ in range(3):
        b = bytes(rng2.randrange(256) for _ in range(n))
        e = B.urlsafe_b64encode(b).rstrip(b"=")
        dec.append(e)
        dec.append(e + b"=")
        dec.append(e + b"A")
        dec.append(e[:-1])
        i = len(e) - 1 - rng2.randrange(min(40, len(e)))
        dec.append(e[:i] + bytes([rng2.choice(BAD)]) + e[i + 1:])
        dec.append(e[:i] + bytes([rng2.choice(BAD)]) + e[i:])
        dec.append(e[:-1] + bytes([rng2.choice(A)]))  # trailing bits of the last symbol
w("dec.txt", [hx(b) for b in dec])
# utf8 random/adversarial byte strings
u = []
def enc_cp(cp):  # raw encoding, allowing surrogates/overlong
    return cp
for _ in range(30000):
    u.append(bytes(rng.randrange(256) for _ in range(rng.randrange(1, 12))))
# random valid strings with mutations
for _ in range(20000):
    cps = []
    for _ in range(rng.randrange(1, 8)):
        r = rng.random()
        if r < 0.3: cp = rng.randrange(0x80)
        elif r < 0.5: cp = rng.randrange(0x80, 0x800)
        elif r < 0.8: cp = rng.choice([rng.randrange(0x800, 0xD800), rng.randrange(0xE000, 0x10000)])
        else: cp = rng.randrange(0x10000, 0x110000)
        cps.append(chr(cp))
    b = bytearray("".join(cps).encode())
    u.append(bytes(b))
    m = bytearray(b); m[rng.randrange(len(m))] = rng.randrange(256); u.append(bytes(m))
    u.append(bytes(b[:rng.randrange(len(b))]))
# overlong encodings
for cp in [0, 0x2F, 0x7F, 0x80, 0x7FF, 0x800, 0xFFFF]:
    # 2-byte overlong of cp<0x80
    u.append(bytes([0xC0 | (cp >> 6) & 0x1F, 0x80 | cp & 0x3F]))
    u.append(bytes([0xE0 | (cp >> 12) & 0x0F, 0x80 | (cp >> 6) & 0x3F, 0x80 | cp & 0x3F]))
    u.append(bytes([0xF0 | (cp >> 18) & 0x07, 0x80 | (cp >> 12) & 0x3F, 0x80 | (cp >> 6) & 0x3F, 0x80 | cp & 0x3F]))
# surrogates encoded as 3 bytes; and > U+10FFFF 4-byte
for cp in list(range(0xD7F0, 0xE010)):
    u.append(bytes([0xE0 | (cp >> 12), 0x80 | (cp >> 6) & 0x3F, 0x80 | cp & 0x3F]))
for cp in list(range(0x10FFF0, 0x110010)) + [0x13FFFF, 0x140000, 0x1FFFFF]:
    u.append(bytes([0xF0 | (cp >> 18) & 0x07, 0x80 | (cp >> 12) & 0x3F, 0x80 | (cp >> 6) & 0x3F, 0x80 | cp & 0x3F]))
# 5/6-byte forms and F8-FF leads
for lead in range(0xF5, 0x100):
    u.append(bytes([lead, 0x80, 0x80, 0x80]))
    u.append(bytes([lead, 0x80, 0x80, 0x80, 0x80, 0x80]))
# truncated sequences
for s in ["é", "€", "𝄞", "a€b", "𐍈x"]:
    b = s.encode()
    for i in range(len(b)+1): u.append(b[:i]); u.append(b[i:])
# exhaustive 4-byte with lead F0..F4 and edge continuation bytes
edge = [0x7F, 0x80, 0x8F, 0x90, 0xBF, 0xC0]
for l in range(0xF0, 0xF5):
    for a in edge:
        for b in edge:
            for c in edge: u.append(bytes([l, a, b, c]))
w("utf8.txt", [hx(b) for b in u])
# code point lists for utf8 (Lean String -> bytes)
cl = []
for _ in range(20000):
    cps = []
    for _ in range(rng.randrange(0, 10)):
        while True:
            cp = rng.choice([rng.randrange(0x80), rng.randrange(0x800), rng.randrange(0x10000), rng.randrange(0x110000)])
            if not (0xD800 <= cp <= 0xDFFF): break
        cps.append(cp)
    cl.append(",".join("%x" % c for c in cps) or "-")
for cp in [0, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF, 0x10000, 0x10FFFF]:
    cl.append("%x" % cp)
w("cps.txt", cl)
print(len(enc), len(dec), len(u), len(cl))
