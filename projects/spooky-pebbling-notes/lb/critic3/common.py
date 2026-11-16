"""独立実装（claimk.py / match.py を import しない）．
状態: 0=空, 1=ペブル, 2=幽霊．時刻 t の状態 = 手 t（0 始まり）の直後．S[-1] 相当 = 初期状態（全空）．"""
import sys

def load(path):
    out = []
    for ln in open(path):
        s = ln.strip()
        if not s or s.startswith('#') or s.startswith('T='):
            continue
        op, v = s.split()
        out.append((op, int(v)))
    return out

def kids(v, n):
    l = 2 * v + 1
    return (l, l + 1) if l < n else ()

def replay_ql(mv, h, cap):
    """QL 規則を直書きで検査．戻り値: 各時刻の状態列（手の直後）．違反で AssertionError．"""
    n = 2 ** h - 1
    st = [0] * n
    states = []
    mx = 0
    for t, (op, v) in enumerate(mv):
        ch = kids(v, n)
        ready = all(st[c] == 1 for c in ch)
        if op == 'pebble':
            assert st[v] == 0, (t, op, v, st[v])
            assert ready, (t, 'pebble without children', v)
            st[v] = 1
        elif op == 'unghost':
            assert st[v] == 2, (t, op, v, st[v])
            assert ready, (t, 'unghost without children', v)
            st[v] = 1
        elif op == 'unpebble':
            assert st[v] == 1, (t, op, v)
            assert ready, (t, 'unpebble without children', v)
            st[v] = 0
        elif op == 'ghost':
            assert st[v] == 1, (t, op, v)
            st[v] = 2
        else:
            raise ValueError(op)
        np_ = sum(1 for x in st if x == 1)
        assert np_ <= cap, (t, 'cap', np_)
        mx = max(mx, np_)
        states.append(tuple(st))
    assert st[0] == 1 and all(x == 0 for x in st[1:]), ('final', st)
    return states, mx

def subtree(c, n):
    out = [c]
    i = 0
    while i < len(out):
        out.extend(kids(out[i], n))
        i += 1
    return out

def height(v, h):
    return h - ((v + 1).bit_length() - 1)
