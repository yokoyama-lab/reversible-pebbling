"""episodes_mine.py の E の数え方（フラグ方式）と，定義の直書き（状態列を走査）を無作為の合法な歩きで突き合わせる．
あわせて定義の変異 D1（幽霊もペブル扱い）・D2（直前の状態だけで判定）が値で区別されるかを見る．"""
import random, sys

def legal_moves(st, n, cap):
    np_ = sum(1 for x in st if x == 1)
    mv = []
    for v in range(n):
        ready = 2*v+1 >= n or (st[2*v+1] == 1 and st[2*v+2] == 1)
        if st[v] == 0 and ready and np_ < cap: mv.append(('pebble', v))
        elif st[v] == 1:
            if ready: mv.append(('unpebble', v))
            mv.append(('ghost', v))
        elif st[v] == 2 and ready and np_ < cap: mv.append(('unghost', v))
    return mv

def apply(st, op, v):
    st[v] = {'pebble': 1, 'unghost': 1, 'unpebble': 0, 'ghost': 2}[op]

def flag_E(mv, n):  # episodes_mine.py の方式をそのまま
    anc = []
    for v in range(n):
        a, x = [], v
        while True:
            a.append(x)
            if x == 0: break
            x = (x-1)//2
        anc.append(a)
    st = [0]*n; cnt = [0]*n; emptied = [True]*n; E = [0]*n
    for op, v in mv:
        new = 1 if op in ('pebble', 'unghost') else (2 if op == 'ghost' else 0)
        old = st[v]
        if new == 1:
            if emptied[v]: E[v] += 1
            emptied[v] = False
        st[v] = new
        d = (new == 1) - (old == 1)
        for a in anc[v]:
            cnt[a] += d
            if cnt[a] == 0: emptied[a] = True
    return E

def sub(v, n):
    out, q = [], [v]
    while q:
        x = q.pop(); out.append(x)
        if 2*x+1 < n: q += [2*x+1, 2*x+2]
    return out

def direct_E(mv, n, variant=None):
    # states[t] = 手 t（1 始まり）の直後，states[0] = 初期
    st = [0]*n; states = [tuple(st)]
    for op, v in mv:
        apply(st, op, v); states.append(tuple(st))
    E = [0]*n
    last = {}
    for t, (op, v) in enumerate(mv, start=1):
        if op not in ('pebble', 'unghost'): continue
        T = sub(v, n)
        prev = last.get(v, 0)   # 直前の置く手の時刻（無ければ初期状態 0 も含める）
        occ = (lambda s, x: s[x] != 0) if variant == 'D1' else (lambda s, x: s[x] == 1)
        rng_ = [t-1] if variant == 'D2' else range(prev if v in last else 0, t)
        if any(all(not occ(states[g], x) for x in T) for g in rng_):
            E[v] += 1
        last[v] = t
    return E

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
tot = diff = dD1 = dD2 = 0
for h in (3, 4, 5):
    n = 2**h - 1
    for cap in range(h+1, n+1):
        for _ in range(10):
            st = [0]*n; mv = []
            for _ in range(600):
                op, v = rng.choice(legal_moves(st, n, cap)); apply(st, op, v); mv.append((op, v))
            a = flag_E(mv, n); b = direct_E(mv, n)
            tot += 1; diff += a != b
            dD1 += direct_E(mv, n, 'D1') != b; dD2 += direct_E(mv, n, 'D2') != b
print(f"歩き {tot} 本（各 600 手）: フラグ方式と直書きの不一致 {diff}，D1 が値で区別される {dD1}，D2 が区別される {dD2}")
