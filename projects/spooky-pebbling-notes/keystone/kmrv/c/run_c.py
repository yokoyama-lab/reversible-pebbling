# sf3 で: C の全数探索と構成（make_dp）を L=Lmin..Lmax，s=2..8，両方の終わり方で照らす．引数: c Lmin Lmax
import subprocess, sys, os
sys.path.insert(0, os.path.expanduser('~/kmrvw'))
from kmrv_weighted import make_dp, INF   # noqa: E402
c, Lmin, Lmax = map(int, sys.argv[1:4])
total, _ = make_dp(c); bad = n = 0
for L in range(Lmin, Lmax + 1):
    for mode in ('tng', 'round'):
        for s in range(2, 9):
            out = int(subprocess.run([os.path.expanduser('~/kmrvw/c/wbfs'), str(L), str(s), str(c), '1' if mode == 'tng' else '0'], capture_output=True, text=True, check=True).stdout)
            b = None if out < 0 else out; d = total(L, s, mode)
            ok = (b is None and d == INF) or b == d; bad += not ok; n += 1
            print(c, mode, L, s, b, d, 'OK' if ok else 'MISMATCH', flush=True)
print('c=%d checked %d bad %d' % (c, n, bad), flush=True)
