"""後片づけの下界の再帰 F(k, m, a, b)．
F = 根にペブルがあり木全体のペブル数 <= m の状態から空にする手数の下界．上限は根を最後に外すまで a，その後 b．
根を最後に外す時刻 f に子は両方ペブル（補題 3）．子の射影は f 以降それぞれ後片づけ（補題 1）．
先に根を外し終える子 X は，その間もう一方の子 Y の根が乗っているので上限 b-1（その後は b に緩める）．Y は b に緩める．
f での子のペブル数 mX+mY <= a-1．f までに増やしたペブルは置く手が要る（開始時の配分 sX+sY <= m-1）．"""
from functools import lru_cache
INF = 10**9
@lru_cache(None)
def F(k, m, a, b):
    if m < 1: return INF
    if k == 1: return 1
    if a < 3: return INF
    best = INF
    for mX in range(1, a - 1):
        for mY in range(1, a - mX):
            fx = F(k - 1, mX, b - 1, b); fy = F(k - 1, mY, b, b)
            if fx >= INF or fy >= INF: continue
            # 開始時の配分は置く手を最小にするように取る
            need = min(max(0, mX - sX) + max(0, mY - (m - 1 - sX)) for sX in range(0, m))
            best = min(best, 1 + need + fx + fy)
    return best
def T_lb(h):
    n = 2**h - 1; best = INF
    for mX in range(1, h):
        for mY in range(1, h + 1 - mX):
            fx = F(h - 1, mX, h - 1, h); fy = F(h - 1, mY, h, h)
            if fx >= INF or fy >= INF: continue
            best = min(best, 2 * (n - 1) - (mX + mY) + 1 + fx + fy)
    return best
exactC = {(2,3):[5,4,3],(3,4):[21,16,11,10],(3,5):[17,12,11,10,9],(4,5):[55,42,37,30,29],(4,6):[49,36,31,28,25,24]}
for (k,c),vals in exactC.items():
    lb=[F(k,m,c,c) for m in range(1,c+1)]
    print(f"C({k},{c}) 厳密 {vals} / 再帰の下界 {lb}", "健全" if all(l<=v for l,v in zip(lb,vals)) else "⚠ 下界が厳密値を超える")
for h in range(2, 21):
    n=2**h-1; t=T_lb(h); print(h, n, t, 4*n-2*(h+1)-1, round(t/(n*h),3))
