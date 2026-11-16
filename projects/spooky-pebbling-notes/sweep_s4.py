#!/usr/bin/env python3
"""S=4 の厳密値 T(n,4) を n について掃引する（README §5「次の一手」2）。

BFS は 3^n で n=15 あたりが限界なので、SAT で先へ伸ばす。
**`sat_spooky.exact` は T を与える形**（T で SAT・T−1 で UNSAT を確かめる）なので、
ここでは **T を下から探して**から `exact` で締める。

設計:
 1. **校正を先に通す。** `sat_spooky.calibrate` が緑でなければ 1 点も測らない
    （符号化が壊れているときの数値は害にしかならない）。
 2. **T は下から増やす。** 最初に SAT になった T が最小。直後に T−1 の UNSAT を
    `exact` で確認して二重化する（片側だけ見ない）。
 3. **打ち切りは結果ではない。** ソルバが時間内に返さなければ `打ち切り` と書き、
    その n で掃引を止める（以降はもっと重いので続けても無駄）。
 4. **下界（UNSAT）側は DRAT を取る**（--proofs）。非存在の主張には証明ログが要る。

使い方:
  python3 sweep_s4.py --kind UP --from 11 --to 20 --out s4_UP.csv [--proofs proofs/]
"""
from __future__ import annotations

import argparse
import csv
import os
import signal
import sys
import time
from pathlib import Path

import sat_spooky as ss

# 既知値。探索の下限と予測に使う。
#  n=9,10 は sat_spooky.calibrate の校正ケース由来（BFS 確定）。
#  n=11..20 は 2026-08-23 の掃引で **両側確認（T で SAT・T-1 で UNSAT）**したもの。
#  ⚠ 階差は n<=17 が 6、n>=18 が 8。**n=17→18 に折れ目がある**（BFS は n=15 が
#    限界だったので、この折れ目はこの掃引で初めて見えた）。
KNOWN = {
    # ⚠ 鍵は **(kind, s, n)**。2026-08-23: 当初 (kind, n) にしていたため、
    #    s=5 で回すと **s=4 の値を種に探索を始める**（黙って誤った予測から入る）。
    ("UP", 4, 9): 27, ("UG", 4, 9): 28, ("UP", 4, 10): 33, ("UG", 4, 10): 32,
    ("UP", 4, 11): 39, ("UP", 4, 12): 45, ("UP", 4, 13): 51, ("UP", 4, 14): 57, ("UP", 4, 15): 63,
    ("UP", 4, 16): 69, ("UP", 4, 17): 75, ("UP", 4, 18): 83, ("UP", 4, 19): 91, ("UP", 4, 20): 99,
    ("UG", 4, 11): 38, ("UG", 4, 12): 44, ("UG", 4, 13): 50, ("UG", 4, 14): 56, ("UG", 4, 15): 62,
    ("UG", 4, 16): 68, ("UG", 4, 17): 74, ("UG", 4, 18): 82, ("UG", 4, 19): 90, ("UG", 4, 20): 98,
    # 2026-08-23 の掃引で追加（すべて両側確認つき）
    ("UG", 4, 21): 106, ("UG", 4, 22): 114, ("UG", 4, 23): 122, ("UG", 4, 24): 130, ("UG", 4, 25): 138,
    ("UG", 4, 26): 146, ("UG", 4, 27): 154, ("UG", 4, 28): 162, ("UG", 4, 29): 170,
    ("UG", 4, 30): 180, ("UG", 4, 31): 190, ("UG", 4, 32): 200,
    ("UP", 4, 21): 107, ("UP", 4, 22): 115, ("UP", 4, 23): 123, ("UP", 4, 24): 131, ("UP", 4, 25): 139,
    ("UP", 4, 26): 147, ("UP", 4, 27): 155, ("UP", 4, 28): 163, ("UP", 4, 29): 171,
    ("UP", 4, 30): 181, ("UP", 4, 31): 191,
}

# ⚠ **折れ目は n=18（6→8）と n=30（8→10）。間隔 12。**
#    素直に外挿すると **次の折れ目は n=42 で 10→12**。これは検定できる予測なので、
#    n=33..44 を掃くと跨げる。予測が外れたら「間隔 12」が誤りと分かる（それも成果）。


class SolverAborted(RuntimeError):
    """ソルバが SAT/UNSAT を返さずに死んだ（OOM kill・異常終了など）。

    ⚠ **これを UNSAT と同一視してはいけない。** `ss.run` は判定できないとき
    `不明(rc=...)` を返す。素朴に `r == "SAT"` を返すと、OOM で殺された呼び出しが
    **False（＝UNSAT）と読まれる**。すると:
      ・`find_min_T` の「下へ詰める」枝では **T-1 が UNSAT** と誤読して
        **嘘の厳密値**を返しうる（`exact` が最後の砦として弾くが、頼るべきでない）
      ・「上へ詰める」枝では窓を掃き切って None を返し、
        **本物でない「打ち切り」「窓外」**として記録される（＝嘘の下界）
    2026-08-27 の昼の申し送りで `q2/p13b.sh` の同型の欠陥が報告され、
    こちらを点検して同じ穴が空いていると分かった。
    """


def _sat(n: int, s: int, kind: str, T: int, st, go) -> bool:
    f, _ = ss.build(n, s, T, st, go)
    r = ss.run(f, None)
    print(f"  n={n} T={T}: {r}", flush=True)
    if r.startswith("不明"):
        raise SolverAborted(f"n={n} s={s} {kind} T={T}: {r}")
    return r == "SAT"


def find_min_T(n: int, s: int, kind: str, lo: int, hi: int, deadline: float,
               guess: int | None = None) -> int | None:
    """最小の T を返す。時間切れなら None。

    ⚠ **1 ずつ上げると呼び出しが無駄になる。** 実測（2026-08-23、n=11..20）:
      答えは `前の n の値 + 6`（n<=17）または `+ 8`（n>=18）で、`prev+1` から
      1 ずつ上げると **1 点あたり 8 回のうち 7 回が捨て呼び出し**だった
      （n=15..19 で計 34 回）。cadical が全体の 94% を占めるので、
      **減らすべきはソルバ呼び出しの回数**であって言語でも I/O でもない。

    そこで `guess`（直前の階差から予測した T）を先に試し、
    SAT なら下へ、UNSAT なら上へ 1 ずつ詰める。
    """
    st, go = ss.states(n, kind)
    if guess is not None and lo <= guess <= hi:
        if time.time() > deadline:
            return None
        if _sat(n, s, kind, guess, st, go):
            # 予測が当たり側。もっと小さい T が無いか下へ詰める
            T = guess
            while T - 1 >= lo:
                if time.time() > deadline:
                    return T
                if not _sat(n, s, kind, T - 1, st, go):
                    return T
                T -= 1
            return T
        # 予測が足りない。上へ詰める
        for T in range(guess + 1, hi + 1):
            if time.time() > deadline:
                return None
            if _sat(n, s, kind, T, st, go):
                return T
        return None
    for T in range(lo, hi + 1):
        if time.time() > deadline:
            return None
        if _sat(n, s, kind, T, st, go):
            return T
    return None



def _read_csv(path: str, kind: str, s: int) -> dict[int, int]:
    """既存の出力から測定済みの n -> T を読む（打ち切り・窓外の行は無視する）。"""
    out: dict[int, int] = {}
    if not os.path.exists(path):
        return out
    with open(path, newline="") as fh:
        for row in csv.DictReader(fh):
            try:
                if row["kind"] == kind and int(row["s"]) == s and row["T"]:
                    out[int(row["n"])] = int(row["T"])
            except (KeyError, ValueError):
                continue
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", default="UP", choices=["P", "UP", "UG"])
    ap.add_argument("--s", type=int, default=4)
    ap.add_argument("--from", dest="n0", type=int, required=True)
    ap.add_argument("--to", dest="n1", type=int, required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--proofs", type=Path, default=None)
    ap.add_argument("--hours", type=float, default=40.0, help="全体の時間予算")
    ap.add_argument("--step", type=int, default=None,
                    help="初回の予測に使う階差（既知の直近の階差。既定は KNOWN から推定）")
    ap.add_argument("--checkpoint-exit", type=int, default=None, metavar="CODE",
                    help="1 点測るごとに CODE で抜ける（HTCondor の self-checkpointing。"
                         "既定は 85＝Linux の ERESTART）。**残りが無ければ 0 で終わる**")
    a = ap.parse_args()

    # ── 1. 校正。ここが赤なら 1 点も測らない ─────────────────
    print("=== 校正 ===", flush=True)
    if ss.calibrate(None):
        print("🔴 符号化が既知値を再現しない。掃引しない", flush=True)
        return 1

    # ⚠ **証明ログの置き場が無ければ 1 点も測らない**（2026-08-31 追加）。
    #   `exact` は DRAT をここへ書く。ディレクトリが無いと cadical が rc=1 で落ち、
    #   その結果が「⚠ exact と不一致」として記録される——**値は出るが下界の証明ログが無い**。
    #   実際に s3 で n=39,40 がこうなった（sf2/t1 は手で mkdir してあったので正常だった）。
    #   下界の主張に証明ログは必須なので、ここは fail-closed にする。
    if a.proofs is not None:
        try:
            a.proofs.mkdir(parents=True, exist_ok=True)
            probe = a.proofs / ".writable"
            probe.write_text("ok")
            probe.unlink()
        except OSError as e:
            print(f"🔴 証明ログの置き場に書けない: {a.proofs} ({e})\n"
                  f"   下界の主張には DRAT が要る。掃引しない", flush=True)
            return 1
        print(f"証明ログ: {a.proofs}（書き込み確認済み）", flush=True)

    deadline = time.time() + a.hours * 3600
    new = not os.path.exists(a.out)
    with open(a.out, "a", newline="") as fh:
        w = csv.writer(fh)
        if new:
            w.writerow(["kind", "s", "n", "T", "sec", "note"])

        # 探索の下限: 直前の n の値（T は n について単調増加のはず）
        # ⚠ **出力 CSV を先に読む。** KNOWN はソース同梱の既知値しか持たないので、
        #    直前の run が測った値（例: UP(32)=201）を取りこぼす。
        #    2026-08-23 にこれで <host> が n=33 を lo=1,hi=61 で全走査し、
        #    答え 211 が窓の外にあるのに「打ち切り」と記録した（22 秒）。
        measured = _read_csv(a.out, a.kind, a.s)
        prev = measured.get(a.n0 - 1) or KNOWN.get((a.kind, a.s, a.n0 - 1))
        # 初回の予測用の階差。--step が無ければ直近 2 点から取る
        step = a.step
        if step is None:
            p2 = measured.get(a.n0 - 2) or KNOWN.get((a.kind, a.s, a.n0 - 2))
            if prev and p2:
                step = prev - p2
        print(f"種: prev(n={a.n0 - 1})={prev} step={step}", flush=True)
        # ⚠ **外から殺されたときに 1 行も書かないと、CSV の最後の行が最前線に見える。**
        #    2026-09-01 に 4 台（t1=OOM・<host>=OOM・m1/sf1=時間上限）で同じ誤読が起きかけた。
        #    **「行が無い」は「その n を測っていない」なのに、読み手には区別がつかない。**
        #    SIGTERM/SIGINT を受けたら、いま測っている n を「中断」として書いてから死ぬ。
        def _on_term(signum, _frame):
            nm = {signal.SIGTERM: "SIGTERM", signal.SIGINT: "SIGINT"}.get(signum, str(signum))
            cur = _state.get("n")
            if cur is not None and not _state.get("written"):
                sec = int(time.time() - _state.get("t0", time.time()))
                w.writerow([a.kind, a.s, cur, "", sec,
                            f"中断（{nm} を受けた）。**打ち切りでも OOM でもなく未測定**。"
                            f"{_state.get('hint','')}"])
                fh.flush(); os.fsync(fh.fileno())
                print(f"🔶 n={cur} を中断として記録した（{nm}・{sec}s）", flush=True)
            sys.exit(143 if signum == signal.SIGTERM else 130)
        _state = {}
        signal.signal(signal.SIGTERM, _on_term)
        signal.signal(signal.SIGINT, _on_term)

        # **1 点に要る最小の予算**。これを切ったら「未着手」と書いて止まる。
        # ⚠ 2026-09-02 に m2 で `UP,7,32,,0,打ち切り` を見つけた。**0 秒の打ち切りは
        #   測定ではない**——予算が尽きた状態で n=32 に入り、探索が即 None を返し、
        #   下の `time.time() > deadline` が真になって「打ち切り」と書かれていた。
        #   「時間内に決着しなかった（＝下界の主張）」と「そもそも試していない」を
        #   同じ札で書くと、`refill.py` が**一度も試していない点を壁と読んで
        #   その線を永久に止める**。→ memory: cutoff-reading-as-result /
        #   skipped-check-must-not-report-ok
        MIN_BUDGET_SEC = 60

        for n in range(a.n0, a.n1 + 1):
            # ⚠ **既に値がある n は測り直さない。** これが無いと、同じ窓を
            #    もう一度回したとき**先頭から全部計算し直す**。実害を確認している:
            #    `s3:s3_UG.csv` には n=41(464) と n=43(500) と n=44(518) が
            #    **2 度ずつ**記録されていた（13873s と 13580s など）。
            #    自己退避（--checkpoint-exit）は「抜けて再開」を繰り返すので、
            #    **ここが無いと退避のたびに最初からになり、永久に終わらない**。
            if n in measured:
                print(f"↷ n={n} は測定済み（T={measured[n]}）。飛ばす", flush=True)
                prev = measured[n]
                continue
            t0 = time.time()
            _state.update(n=n, t0=t0, written=False, hint="")
            left = deadline - time.time()
            if left < MIN_BUDGET_SEC:
                w.writerow([a.kind, a.s, n, "", 0,
                            f"未着手（予算切れ・残り {int(left)}s < {MIN_BUDGET_SEC}s）。"
                            f"**打ち切りではない。この n は一度も試していない**。"
                            f"--hours を増やせば測れる"])
                _state["written"] = True
                fh.flush()
                print(f"🔶 n={n} は未着手（予算切れ）。**打ち切りと混同しない**", flush=True)
                return 0
            lo = (prev + 1) if prev else 1
            hi = lo + 60
            guess = (prev + step) if (prev and step) else None
            try:
                T = find_min_T(n, a.s, a.kind, lo, hi, deadline, guess)
            except SolverAborted as e:
                # ⚠ **ソルバの異常死を「打ち切り」と書かない。** 打ち切りは
                #    「時間内に決着しなかった」という主張＝下界の主張であり、
                #    OOM で殺されただけのものをそう書くと台帳に嘘が載る。
                sec = int(time.time() - t0)
                w.writerow([a.kind, a.s, n, "", sec, f"ソルバ異常({e})"])
                _state["written"] = True
                fh.flush()
                print(f"🔴 n={n} でソルバが異常終了: {e}\n"
                      f"   これは打ち切りではない。メモリを疑う"
                      f"（app.slice の MemoryPeak と物理メモリを突き合わせる）", flush=True)
                return 1
            sec = int(time.time() - t0)
            if T is None:
                # ⚠ **「打ち切り」と「窓外」は別物。** 前者は時間が足りない、
                #    後者は答えが lo..hi の外にある（種の取り違え＝こちらの誤り）。
                #    2026-08-23 に窓外を打ち切りと書いて 22 秒で止まった。
                if time.time() > deadline and sec < MIN_BUDGET_SEC:
                    # 予算の境目で入ってしまった場合の保険。**0 秒台は測定ではない**
                    note = f"未着手（予算切れ・{sec}s）"
                    msg = (f"未着手（予算切れ・{sec}s）。"
                           f"**打ち切りではない。一度も試していない**")
                elif time.time() > deadline:
                    note, msg = "打ち切り", f"打ち切り（{sec}s）。以降はもっと重いので停止"
                else:
                    note = f"窓外(lo={lo},hi={hi})"
                    msg = (f"🔴 窓 lo={lo}..hi={hi} に答えが無い（{sec}s）。"
                           f"種が違う可能性が高い。--step か CSV の直前の値を確かめる")
                w.writerow([a.kind, a.s, n, "", sec, note])
                _state["written"] = True
                fh.flush()
                print(f"🔶 n={n} は{msg}", flush=True)
                return 0
            # 両側を締める（T で SAT・T-1 で UNSAT）。UNSAT 側の DRAT も取る
            bad = ss.exact(n, a.s, a.kind, T, a.proofs)
            note = "両側確認" if not bad else "⚠ exact と不一致"
            w.writerow([a.kind, a.s, n, T, int(time.time() - t0), note])
            _state["written"] = True
            fh.flush()
            if prev:
                step = T - prev      # 次の n の予測に使う
            print(f"✅ T({n},{a.s},{a.kind}) = {T}  [{note}]"
                  + (f" 階差 {step}" if step else ""), flush=True)
            prev = T
            measured[n] = T
            # ⚠ **自己退避（self-checkpointing）。** 1 点は不可分な仕事の単位なので、
            #    ここが唯一の安全な中断点である。CSV 自体が退避物になっており、
            #    再開時は上の「測定済みは飛ばす」で続きから入る。
            #    これがあると **窓の予算切れ（未着手）も外からの中断も構造的に消える**——
            #    残り時間で測れる点まで測って抜け、次の起動が続きを測るため。
            #    HTCondor では `checkpoint_exit_code = 85` がこの符号を待つ。
            if a.checkpoint_exit is not None and n < a.n1:
                os.fsync(fh.fileno())
                print(f"⏸ 退避して抜ける（rc={a.checkpoint_exit}）。"
                      f"残り n={n + 1}..{a.n1}。**打ち切りでも中断でもない**",
                      flush=True)
                return a.checkpoint_exit
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
