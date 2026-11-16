"""森の補題の候補を pair_cmp で調べる。
   sort:     2 本 (a,b) → 1 本（φ_sort）．pair_cmp の自己検査．
   transfer: 2 本 (a,b) の A の一番下の区間（長さ s）を B の一番下へ移す → (a-s, b+s)（A が空になるなら 1 本 (a+b)）．
   transfer_sorted: 同じだが，移す前に A と B がそれぞれ短い順に整列している X に限る。
   tinsert: A と B が整列済みの X で，A の一番下の区間を B の整列した位置へ差し込む．
   isort2: 2 本のまま各鎖の中を短い順に並べる．
   sel2: 2 本のまま，片方の鎖で選択整列の 1 段（補題 Sel を森の中で）．
   topgraft: A が区間 1 つ（A0 だけに石）のとき，A を B の上に載せた 1 本 (a+b)．
   使い方: python3 transfer_check.py <pair_cmp の実行ファイル> <mode> <Lmax>"""
import subprocess
import sys
BIN, MODE, LMAX = sys.argv[1], sys.argv[2], int(sys.argv[3])
def segs(pebbles, n):
    return [q - p for p, q in zip(pebbles, pebbles[1:] + [n])]
def chain_bits(sg, off):
    y = p = 0
    for s in sg:
        y |= 1 << (off + p)
        p += s
    return y
def run(P, Q, pairs):
    if not pairs:
        return None
    inp = ''.join(f'{x} {y}\n' for x, y in pairs)
    out = subprocess.run([BIN, ','.join(map(str, P)), ','.join(map(str, Q))], input=inp, capture_output=True, text=True).stdout
    return out.splitlines()[0]
tot_v = 0
for L in range(2, LMAX + 1):
    for a in range(1, L):
        b = L - a
        groups = {}
        for x in range(1 << L):
            if not (x & 1 and x >> a & 1):
                continue
            A = segs([i for i in range(a) if x >> i & 1], a)
            B = segs([i - a for i in range(a, L) if x >> i & 1], b)
            if MODE == 'sort':
                Q = (L,)
                y = chain_bits(sorted(A + B), 0)
            elif MODE.startswith('transfer'):
                if MODE == 'transfer_sorted' and (A != sorted(A) or B != sorted(B)):
                    continue
                s = A[-1]
                if len(A) == 1:
                    Q = (L,)
                    y = chain_bits(B + [s], 0)
                else:
                    Q = (a - s, b + s)
                    y = chain_bits(A[:-1], 0) | chain_bits(B + [s], a - s)
            elif MODE in ('tinsert', 'tinsert_min'):
                # A と B が整列済みの X で，A の一番下（tinsert）または A の区間のうち B に移すもの…を B の整列位置へ差し込む
                if A != sorted(A) or B != sorted(B):
                    continue
                s = A[-1]
                if len(A) == 1:
                    Q = (L,)
                    y = chain_bits(sorted(B + [s]), 0)
                else:
                    Q = (a - s, b + s)
                    y = chain_bits(A[:-1], 0) | chain_bits(sorted(B + [s]), a - s)
            elif MODE == 'isort2':
                Q = (a, b)
                y = chain_bits(sorted(A), 0) | chain_bits(sorted(B), a)
            elif MODE == 'topgraft':
                if len(A) != 1:
                    continue
                Q = (L,)
                y = chain_bits(A + B, 0)
            if MODE == 'sel2':
                # 森の中の鎖 A または B で選択整列の 1 段（上の j 個が最小の j 個を整列したもの → 残りの最小を j+1 番目へ）
                for c, (G, off) in enumerate(((A, 0), (B, a))):
                    for j in range(len(G) - 1):
                        if G[:j] != sorted(G)[:j]:
                            continue
                        rest = G[j:]
                        i = min(range(len(rest)), key=lambda t: (rest[t], t))
                        H = G[:j] + [rest[i]] + rest[:i] + rest[i + 1:]
                        if H == G:
                            continue
                        y = (chain_bits(H, 0) | chain_bits(B, a)) if c == 0 else (chain_bits(A, 0) | chain_bits(H, a))
                        groups.setdefault(((a, b), c, j), []).append((x, y))
                continue
            groups.setdefault(Q, []).append((x, y))
        for Q, pairs in groups.items():
            r = run((a, b), Q[0] if MODE == 'sel2' else Q, pairs)
            v = int(r.split('viol=')[1].split()[0])
            tot_v += v
            if v or 'CAP' in r:
                print(r)
print(MODE, 'Lmax', LMAX, 'total viol', tot_v)
