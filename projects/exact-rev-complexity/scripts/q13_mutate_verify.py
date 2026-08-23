#!/usr/bin/env python3
r"""`q13_verify_nstar.py` 自身への変異注入（2026-08-24）。

証明書への変異（`q13_verify_nstar.py --self-test`）が測るのは「悪い証明書を落とせるか」。
こちらが測るのは「**検査器の各検査が効いているか**」。検査を 1 つ壊したとき、
無傷の証明書が落ちるか、または自己試験が満点でなくなれば、その検査は効いている。

⚠ 打ち切り耐性: SIGTERM/SIGINT/例外/正常終了のいずれでも原本を必ず戻す。
"""
from __future__ import annotations
import atexit
import signal
import subprocess
import sys
from pathlib import Path

TARGET = Path(__file__).resolve().parent / "q13_verify_nstar.py"
ORIG = TARGET.read_text(encoding="utf-8")


def restore(*_a):
    TARGET.write_text(ORIG, encoding="utf-8")
    if _a:
        sys.exit(1)


atexit.register(restore)
for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
    signal.signal(sig, restore)

MUTANTS = [
    ("親が両方に居ることの検査を外す", "if not (sched[t][q] and sched[t + 1][q]):", "if False:"),
    ("ピークの検査を外す", "if peak > p:", "if False:"),
    ("空から始めることの検査を外す", "if any(sched[0]):", "if False:"),
    ("clean 到達の検査を外す", "if sched[T][v] != want:", "if False:"),
    ("時間最適 T=2n-1 の検査を外す", "if T != 2 * n - 1:", "if False:"),
    ("時刻の数の検査を外す", "if len(sched) != T + 1:", "if False and len(sched) != T + 1:"),
    ("主張 n との照合を外す", 'if doc["nstar"].get(p_str) != n:', "if False:"),
    ("親を 1 つ手前にずらす（鎖の定義を壊す）",
     "return [[] if i == 0 else [i - 1] for i in range(n)], n - 1",
     "return [[] if i <= 1 else [i - 2] for i in range(n)], n - 1"),
    ("sink を端でない頂点にする", "], n - 1", "], max(n - 2, 0)"),
    ("対照: 表示文言だけを変える",
     "=== Q13 の下界側（n*(p) >= n）の独立検証 ===",
     "=== Q13 の下界側（n*(p) >= n）の独立検証(c) ==="),
]


def run(args):
    try:
        return subprocess.run([sys.executable, "-B", str(TARGET)] + args,
                              capture_output=True, text=True, cwd=TARGET.parent.parent, timeout=180,
                              env={"PYTHONDONTWRITEBYTECODE": "1", "PATH": "/usr/bin:/bin"})
    except subprocess.TimeoutExpired:
        class R:  # 打ち切りは「棄却」ではなく失敗として扱う（結果と読まない）
            returncode, stdout, stderr = 124, "", "TIMEOUT"
        return R()


def main():
    base_v = run([])
    base_s = run(["--self-test"])
    assert base_v.returncode == 0 and base_s.returncode == 0, "原本が緑でない。変異注入の前提が崩れている"
    print(f"原本: verify rc={base_v.returncode} / self-test rc={base_s.returncode}（前提 OK）\n")

    npos = okpos = nneg = okneg = 0
    for name, old, new in MUTANTS:
        control = name.startswith("対照")
        assert ORIG.count(old) == 1, f"アンカーが一意でない: {name}（{ORIG.count(old)} 件）"
        TARGET.write_text(ORIG.replace(old, new), encoding="utf-8")
        v, s = run([]), run(["--self-test"])
        killed = (v.returncode != 0) or (s.returncode != 0)
        restore()
        if control:
            nneg += 1
            okneg += not killed
        else:
            npos += 1
            okpos += killed
        judge = "OK" if killed != control else "**NG**"
        why = []
        if v.returncode != 0:
            why.append("無傷の証明書が落ちた")
        if s.returncode != 0:
            why.append("自己試験が満点でなくなった")
        print(f"  [{judge}] {name}: {'棄却' if killed else '生存'}"
              + (f"（{'・'.join(why)}）" if why else ""))
    print(f"\n  変異 {okpos}/{npos} 棄却・対照 {okneg}/{nneg} 生存")
    return 0 if (okpos == npos and okneg == nneg) else 1


if __name__ == "__main__":
    sys.exit(main())
