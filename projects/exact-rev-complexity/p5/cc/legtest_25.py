import os, subprocess, sys
TREEBFS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "treebfs")  # gcc -O2 -o treebfs treebfs.c
def M(par, S, root):
    inp = f"{len(par)} {S} {root} " + " ".join(map(str, par))
    return int(subprocess.run([TREEBFS], input=inp, capture_output=True, text=True).stdout)
def build(k, merged, a=2, b=5):
    # 0 = r, 1 = u, 2..2+k-1 = r の葉, 続いて A0..A_{a-1}, B0..B_{b-1}
    par = [-1, 0] + [0] * k
    A = list(range(len(par), len(par) + a)); par += [1] + [A[i - 1] for i in range(1, a)]
    Bv = list(range(len(par), len(par) + b)); par += [A[-1] if merged else 1] + [Bv[i - 1] for i in range(1, b)]
    return par
for k in range(0, int(sys.argv[1]) + 1):
    for S in range(3, 11):
        g, gm = M(build(k, False), S, 0), M(build(k, True), S, 0)
        flag = "  <-- legmerge で増えた" if gm > g >= 0 or (gm < 0 <= g) else ""
        if g >= 0 or gm >= 0: print(f"k={k} n={9+k} S={S}: M(G)={g} M(G')={gm}{flag}")
