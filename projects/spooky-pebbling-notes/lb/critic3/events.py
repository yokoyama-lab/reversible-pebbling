"""主張 K と二重計上の検定を独立に再実装し，τ・子・窓端の取り方を振る．"""
import sys
import itertools
from common import load, replay_ql, subtree, kids, height

def prep(path, h, cap):
    mv = load(path)
    S, _ = replay_ql(mv, h, cap)
    n = 2 ** h - 1
    place = {v: [] for v in range(n)}
    rem = {v: [] for v in range(n)}
    remop = {v: [] for v in range(n)}
    for t, (op, v) in enumerate(mv):
        if op in ('pebble', 'unghost'):
            place[v].append(t)
        else:
            rem[v].append(t)
            remop[v].append(op)
    return mv, S, n, place, rem, remop

def empty_at(S, T, t):
    if t < 0:
        return True
    st = S[t]
    return all(st[x] != 1 for x in T)

def greedy_count(demands, place):
    """demands: list of (v, lo, hi) = v の置く手で lo < t < hi．頂点ごとに区間と点のマッチング（右端昇順の貪欲＝最大）．"""
    byv = {}
    for i, (v, lo, hi) in enumerate(demands):
        byv.setdefault(v, []).append((hi, lo, i))
    got = 0
    unmatched = []
    for v, ds in byv.items():
        used = set()
        for hi, lo, i in sorted(ds):
            cand = [t for t in place[v] if lo < t < hi and t not in used]
            if cand:
                used.add(min(cand))
                got += 1
            else:
                unmatched.append(demands[i])
    return got, unmatched

def main(path, h, cap):
    mv, S, n, place, rem, remop = prep(path, h, cap)
    END = len(mv)
    U = [u for u in range(1, n) if kids(u, n) and kids(kids(u, n)[0], n) is not None]
    U = [u for u in range(1, n) if 2 * u + 1 < n]
    # Lemma 3 の確認: 根以外の最後の除去は unpebble
    bad = [v for v in range(1, n) if remop[v][-1] != 'unpebble']
    print(f"== {path.split('/')[-1]} h={h} 手数 {END} 置く手 {sum(len(x) for x in place.values())}; 最後の除去が unpebble でない頂点: {bad}")
    info = {}
    for u in U:
        t0, f = place[u][0], rem[u][-1]
        E = {}
        for c in kids(u, n):
            T = subtree(c, n)
            E[c] = [t for t in range(t0, f + 1) if empty_at(S, T, t)]
        info[u] = (t0, f, E)
    # 主張 K の割合（高さ別）: 端点を含めても変わらないことも確認
    byh = {}
    for u in U:
        t0, f, E = info[u]
        ok_open = any(t0 < t < f for c in E for t in E[c])
        ok_closed = any(t0 <= t <= f for c in E for t in E[c])
        assert ok_open == ok_closed
        byh.setdefault(height(u, h), []).append(ok_open)
    print("主張 K（高さ: 成立/全体）", {k: f"{sum(v)}/{len(v)}" for k, v in sorted(byh.items())})
    elig = {u: [c for c in kids(u, n) if any(info[u][0] < t < info[u][1] for t in info[u][2][c])] for u in U}
    both = [u for u in U if len(elig[u]) == 2]
    one = [u for u in U if len(elig[u]) == 1]
    print(f"事象のある u: {sum(1 for u in U if elig[u])}（両方の子が空になる u {len(both)}，片方だけ {len(one)}）")

    def build(choice, tau_rule='first', lo_rule='window', hi_rule='f'):
        D = []
        for u in U:
            if not elig[u]:
                continue
            c = choice[u]
            t0, f, E = info[u]
            T = subtree(c, n)
            if lo_rule == 'window':
                cand = [t for t in E[c] if t0 < t < f]
            elif lo_rule == 'after_c_first':
                # τ は c の初回配置より後で f より前，T(c) が空（t0 より前も可）
                cand = [t for t in range(place[c][0] + 1, f) if empty_at(S, T, t)]
            if tau_rule == 'first':
                tau = min(cand)
            elif tau_rule == 'last':
                tau = max(cand)
            else:
                tau = tau_rule[u]
            if hi_rule == 'f':
                hi = f
            elif hi_rule == 'end':
                hi = END
            elif hi_rule == 'tight':
                hi = min(t for t in place[c] if t > tau) + 1  # c の τ 後の最初の配置まで（c 自身はその手を含む）
            for v in T:
                D.append((v, tau, hi))
        return D

    base = {u: elig[u][0] for u in U if elig[u]}
    for label, kw in [("台本どおり（左優先・最初の τ・窓 (τ,f)）", {}),
                      ("最後の τ", dict(tau_rule='last')),
                      ("窓の上端を c の τ 後の初回配置に締める（補題 R の強制そのもの）", dict(hi_rule='tight')),
                      ("τ を c の初回配置後まで広げる（t0 より前も可）", dict(lo_rule='after_c_first')),
                      ("上端を手順の終わりまで緩める（補題 R は強制しない）", dict(hi_rule='end'))]:
        D = build(base, **kw)
        got, um = greedy_count(D, place)
        print(f"  {label}: 要求 {len(D)} / 最大 {got}  未充足 {[(v, lo, hi) for v, lo, hi in um]}")
    print('両方の子に事象がある u:', both, flush=True)
    if len(both) > 14:
        return info, elig, place, S, n, U
    # 子の選択の最適化（全列挙）
    best = None
    for bits in itertools.product(*[elig[u] for u in both]):
        ch = dict(base)
        ch.update(dict(zip(both, bits)))
        for kw in [dict(), dict(lo_rule='after_c_first')]:
            D = build(ch, **kw)
            got, _ = greedy_count(D, place)
            key = (str(kw), )
            if best is None:
                best = {}
            b = best.get(key)
            if b is None or got > b[0]:
                best[key] = (got, len(D), dict(zip(both, bits)))
    for k, (got, tot, ch) in best.items():
        print(f"  子の選択を全列挙（{2**len(both)} 通り）{k[0] or '窓 (t0,f) 内の最初の τ'}: 最大 {got}/{tot}  最良の選択 {ch}")
    return info, elig, place, S, n, U

if __name__ == '__main__':
    for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
        main(path, h, cap)
