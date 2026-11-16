#!/usr/bin/env python3
"""`sweep_s4.py` の**記録の規律**を検定する。

ここで守るのは値の正しさではなく、**測れなかったことを正しく書くこと**である。
2026-09-02 に、この規律が破れて艦隊の 4 本の線が偽の壁で止まっていた。

| 検定 | 何を守るか |
|---|---|
| 未着手 | **0 秒の「打ち切り」を書かない**。予算切れで入った点は「一度も試していない」 |
| 自己退避 | 1 点ごとに rc=85 で抜け、**測定済みは飛ばして**続きから測る |
| 冪等 | 同じ窓を 2 度回しても**同じ点を測り直さない**（実害あり: s3_UG.csv に重複が 3 組） |
| 中断 | SIGTERM を受けたら**中断の 1 行を書いてから**死ぬ |

⚠ **変異注入で検出力を測る**（「飛ばす」を壊したら重複と rc=85 の居座りで落ちること）。
⚠ 実ソルバを回すので n は最小のもの（11〜13。1 点 1〜4 秒）だけを使う。

    python3 test_sweep_s4.py
"""
import csv
import os
import signal
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SWEEP = os.path.join(HERE, "sweep_s4.py")
SEED = "kind,s,n,T,sec,note\nUP,4,11,39,1,両側確認\n"

ok = fail = 0


def check(name, got, want):
    global ok, fail
    if got == want:
        ok += 1
        print(f"  ok   {name}")
    else:
        fail += 1
        print(f"  NG   {name}（期待 {want!r} / 実際 {got!r}）")


def run(csv_path, script=SWEEP, extra=(), n0=12, n1=13, hours=1.0):
    cmd = [sys.executable, script, "--kind", "UP", "--s", "4",
           "--from", str(n0), "--to", str(n1), "--out", csv_path,
           "--hours", str(hours), *extra]
    # ⚠ **`cwd` では import は解決しない。** Python が sys.path に入れるのは
    #    **スクリプトの在るディレクトリ**なので、変異体を temp に置くと
    #    `import sat_spooky` が落ちて rc=1 になる（2026-09-02 にこれで
    #    変異検定が「検出できた」ように見えず 2 件落ちた）。PYTHONPATH で渡す。
    env = dict(os.environ, PYTHONPATH=HERE + os.pathsep + os.environ.get("PYTHONPATH", ""))
    p = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True,
                       timeout=900, env=env)
    return p.returncode, p.stdout + p.stderr


def rows(path):
    with open(path, newline="") as fh:
        return [r for r in csv.DictReader(fh)]


def measured(path):
    """(kind,s,n) -> 値の付いた行の数。**重複の検出に使う**。"""
    seen = {}
    for r in rows(path):
        if r["T"]:
            seen[(r["kind"], r["s"], r["n"])] = seen.get((r["kind"], r["s"], r["n"]), 0) + 1
    return seen


def t_uncharted():
    """予算切れの点を「打ち切り」と書かないこと。"""
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "a.csv")
        open(p, "w").write(SEED)
        rc, out = run(p, hours=0.0001)
        check("予算切れでも rc=0（異常終了ではない）", rc, 0)
        last = rows(p)[-1]
        check("値を書かない", last["T"], "")
        check("札は未着手", "未着手" in last["note"], True)
        check("**打ち切りとは書かない**", last["note"].startswith("打ち切り"), False)
        check("一度も試していないと明記", "一度も試していない" in last["note"], True)


def t_checkpoint():
    """1 点ごとに退避して抜け、続きから測ること。"""
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "a.csv")
        open(p, "w").write(SEED)
        rc1, out1 = run(p, extra=("--checkpoint-exit", "85"))
        check("1 回目は退避の符号で抜ける", rc1, 85)
        check("1 回目に測ったのは 1 点だけ", len([r for r in rows(p) if r["T"]]), 2)
        check("残りを言う", "残り n=13..13" in out1, True)
        rc2, out2 = run(p, extra=("--checkpoint-exit", "85"))
        check("2 回目は測定済みを飛ばす", "n=12 は測定済み" in out2, True)
        check("2 回目で最後まで行けば 0", rc2, 0)
        check("値は 3 点そろう", len([r for r in rows(p) if r["T"]]), 3)
        check("**同じ点を 2 度測っていない**", max(measured(p).values()), 1)


def t_mutation_no_skip():
    """⚠ 「測定済みは飛ばす」を壊したら落ちること（検出力の測定）。

    壊すと退避のたびに先頭からになり、**永久に 85 で居座って終わらない**。
    """
    with tempfile.TemporaryDirectory() as d:
        mut = os.path.join(d, "mutant.py")
        src = open(SWEEP, encoding="utf-8").read()
        marker = "            if n in measured:"
        if marker not in src:
            check("変異を作れる（飛ばす分岐が在る）", False, True)
            return
        head, _, tail = src.partition(marker)
        tail = tail.split("continue", 1)[1]
        open(mut, "w", encoding="utf-8").write(head + "            pass" + tail)
        for f in ("sat_spooky.py", "spooky.py", "lemmas.py", "kss.py", "upper_bound.py"):
            pass  # cwd=HERE で走らせるので複製は不要
        p = os.path.join(d, "b.csv")
        open(p, "w").write(SEED)
        rc1, out1 = run(p, script=mut, extra=("--checkpoint-exit", "85"))
        # ⚠ **変異体が「壊れて落ちた」のを「検出できた」と読まない。**
        #    1 回目が 85 で抜けていなければ、変異の作り方のほうが間違っている。
        check("変異体が動く（作り方が正しい）", rc1, 85)
        rc2, _ = run(p, script=mut, extra=("--checkpoint-exit", "85"))
        check("変異: 2 回目も 85 のまま（進まない）", rc2, 85)
        check("変異: 同じ点が 2 度記録される", max(measured(p).values()) > 1, True)


def t_sigterm():
    """外から殺されたら中断の 1 行を書いてから死ぬこと。"""
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "a.csv")
        open(p, "w").write(SEED)
        cmd = [sys.executable, SWEEP, "--kind", "UP", "--s", "4",
               "--from", "20", "--to", "20", "--out", p, "--hours", "1"]
        proc = subprocess.Popen(cmd, cwd=HERE, stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL)
        time.sleep(25)          # 校正を抜けて n=20 の探索に入るまで待つ
        proc.send_signal(signal.SIGTERM)
        try:
            proc.wait(timeout=60)
        except subprocess.TimeoutExpired:
            proc.kill()
        last = rows(p)[-1]
        check("中断の行が書かれる", "中断" in last["note"], True)
        check("値は書かない", last["T"], "")
        check("**打ち切りでも OOM でもないと明記**",
              "打ち切りでも OOM でもなく未測定" in last["note"], True)


if __name__ == "__main__":
    for t in (t_uncharted, t_checkpoint, t_mutation_no_skip, t_sigterm):
        print(f"--- {t.__name__} ---")
        t()
    print(f"\n--- {ok}/{ok + fail} 通過 ---")
    sys.exit(0 if fail == 0 else 1)
