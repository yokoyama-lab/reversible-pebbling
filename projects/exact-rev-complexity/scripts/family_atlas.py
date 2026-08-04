"""グラフ族の厳密値台帳を作る／検証する（`data/families/`）。

## 二段構え（ループの合否をこの分離が支える）

- **生成** `--build`: 探索を回して $p_{\\min}$・$M^*$ を出し、CSV と**証書**を書く。重い。
- **検証** `--verify`: CSV の各行の証書を**独立の検証器で再生**する。軽い（1 秒未満）。

ループの 1 反復の合否（`tools/loopcheck.sh`）は **`--verify` だけ**を使う。
探索そのものは反復の中で 1 回走らせ、証書が残ればその値は以後ただで再検査できる。

## 証書が担保する範囲（誇張しないこと）

| 主張 | 証書 | 検証の重さ |
|---|---|---|
| $M^*(G,p) \\le m$（上界） | 長さ $m$ の合法スケジュール | 軽い（再生するだけ） |
| $M^*(G,p) \\ge m$（下界） | **無い**。全数 BFS が根拠 | 重い（再探索） |

したがって台帳の `status` は
`exhaustive`（全数 BFS。2 実装が一致した場合は `methods` に両方が入る）か
`ub_only`（上界のみ）で、**下界に再生可能な証書は付いていない**。
`docs/STATUS.md` の層でいえば全数 BFS は**層3**であり、層1（Lean）ではない。
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import exp01b_engine as fast  # noqa: E402
import revpebble as rp  # noqa: E402
from families import FAMILIES, anc, build  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "families"
CSV_PATH = OUT / "atlas.csv"
CERT_DIR = OUT / "certs"

#: 素朴実装（frozenset BFS）で照合する上限。これを超えると高速版のみ。
NAIVE_LIMIT = 13
#: 高速実装が訪問してよい状態数の上限。超えたら `timeout` として台帳に残す。
#: 状態は Python の dict/set に入るので 1 状態あたり ~100 バイト見当。
#: 4M で ~0.5GB。これ以上は探索時間よりメモリで死ぬので、ここで切る。
STATE_CAP = 4_000_000
#: 各インスタンスで測る p の範囲（p_min から数えて）。
P_EXTRA = 2

FIELDS = [
    "family", "params", "n", "anc_n", "pebbleable",
    "pmin", "p", "mstar", "methods", "status", "cert", "seconds",
]


def _cert_path(family: str, params: tuple[int, ...]) -> Path:
    return CERT_DIR / f"{family}_{'_'.join(map(str, params))}.json"


def _pebbleable(g: rp.Dag) -> int:
    return g.n - len(g.free)


def measure(family: str, params: tuple[int, ...]) -> tuple[list[dict], dict]:
    """1 インスタンスを測る。(CSV 行の列, 証書) を返す。"""
    g = build(family, params)
    ga, t = anc(g)
    nb = _pebbleable(ga)
    rows: list[dict] = []
    certs: dict[str, list[list]] = {}

    t0 = time.monotonic()
    # p_min の探索にも上限を効かせる（`fast.pmin_mask` は cap を取らないので自前で回す）。
    # 到達不能な p でも状態空間は全部展開されるため、ここを無防備にすると死ぬ。
    pmin: int | None = None
    for p in range(1, 41):
        try:
            if fast.mstar(ga, t, p, cap=STATE_CAP) is not None:
                pmin = p
                break
        except RuntimeError:
            break
    if pmin is None:
        rows.append({
            "family": family, "params": ":".join(map(str, params)),
            "n": g.n, "anc_n": ga.n, "pebbleable": nb,
            "pmin": "", "p": "", "mstar": "", "methods": "mask",
            "status": "timeout", "cert": "", "seconds": f"{time.monotonic() - t0:.2f}",
        })
        return rows, certs

    for p in range(pmin, pmin + P_EXTRA + 1):
        t1 = time.monotonic()
        methods = ["mask"]
        status = "exhaustive"
        try:
            m = fast.mstar(ga, t, p, cap=STATE_CAP)
        except RuntimeError:
            m = None
            status = "timeout"
        if m is not None and nb <= NAIVE_LIMIT:
            naive, _ = rp.bfs(ga, t, p)
            assert naive == m, f"{g.name} p={p}: 素朴 {naive} != 高速 {m}"
            methods.append("bfs")
        cert = ""
        if m is not None:
            seq = fast.schedule(ga, t, p)
            assert seq is not None and len(seq) == m, f"{g.name} p={p}: 証書の長さ不一致"
            fast.verify_schedule(ga, t, p, seq)
            certs[str(p)] = [[k, v] for k, v in seq]
            cert = _cert_path(family, params).name
        rows.append({
            "family": family, "params": ":".join(map(str, params)),
            "n": g.n, "anc_n": ga.n, "pebbleable": nb,
            "pmin": pmin, "p": p, "mstar": "" if m is None else m,
            "methods": "+".join(methods), "status": status, "cert": cert,
            "seconds": f"{time.monotonic() - t1:.2f}",
        })
        if m is None:
            break  # p を上げても状態数は増える一方なので打ち切る
    return rows, certs


def cmd_build(only: str | None) -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    for family, _fn, params_list in FAMILIES:
        if only and family != only:
            continue
        # 単調な打ち切り: 最後のパラメタ（サイズ）を上げるほど状態空間は増える一方なので、
        # 一度 timeout したら同じ接頭辞のより大きいものは走らせない。
        # **黙って落とさず `skipped` の行を残す**（手順書の禁止事項）。
        gave_up: set[tuple[int, ...]] = set()
        for params in params_list:
            if params[:-1] in gave_up:
                g = build(family, params)
                ga, _t = anc(g)
                rows.append({
                    "family": family, "params": ":".join(map(str, params)),
                    "n": g.n, "anc_n": ga.n, "pebbleable": _pebbleable(ga),
                    "pmin": "", "p": "", "mstar": "", "methods": "",
                    "status": "skipped", "cert": "", "seconds": "0.00",
                })
                print(f"{family}({':'.join(map(str, params))}) [skipped]", flush=True)
                continue
            r, certs = measure(family, params)
            if any(x["status"] == "timeout" for x in r) and r[0]["pmin"] == "":
                gave_up.add(params[:-1])
            rows.extend(r)
            if certs:
                _cert_path(family, params).write_text(
                    json.dumps(certs, separators=(",", ":")) + "\n", encoding="utf-8"
                )
            for row in r:
                print(f"{row['family']}({row['params']}) p={row['p']} "
                      f"M*={row['mstar']} [{row['status']}] {row['seconds']}s", flush=True)
    if only:  # 部分更新: 既存行を残して差し替える
        old = list(read_rows()) if CSV_PATH.exists() else []
        rows = [x for x in old if x["family"] != only] + rows
    with CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {CSV_PATH} ({len(rows)} rows)")
    return 0


def read_rows() -> list[dict]:
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        return list(csv.DictReader(fh))


def cmd_verify() -> int:
    """台帳の各行の証書を独立に再生する。**これがループの合否**。"""
    if not CSV_PATH.exists():
        print(f"NG: 台帳が無い（{CSV_PATH}）")
        return 1
    bad: list[str] = []
    checked = 0
    for row in read_rows():
        tag = f"{row['family']}({row['params']}) p={row['p']}"
        if row["status"] in ("timeout", "skipped"):
            continue
        params = tuple(int(x) for x in row["params"].split(":"))
        g = build(row["family"], params)
        ga, t = anc(g)
        if int(row["anc_n"]) != ga.n:
            bad.append(f"{tag}: anc_n が再現しない（{row['anc_n']} != {ga.n}）")
            continue
        if not row["cert"]:
            bad.append(f"{tag}: 証書が無いのに status={row['status']}")
            continue
        certs = json.loads((CERT_DIR / row["cert"]).read_text(encoding="utf-8"))
        seq = [(k, v) for k, v in certs[row["p"]]]
        m = int(row["mstar"])
        try:
            fast.verify_schedule(ga, t, int(row["p"]), seq)
        except AssertionError as exc:
            bad.append(f"{tag}: スケジュールが規則を満たさない — {exc}")
            continue
        if len(seq) != m:
            bad.append(f"{tag}: 証書の長さ {len(seq)} != 台帳の M* {m}")
            continue
        if m % 2 == 0:
            bad.append(f"{tag}: M*={m} が偶数（M*=2A-1 に反する）")
            continue
        if m < 2 * (ga.n - len(ga.free)) - 1:
            bad.append(f"{tag}: M*={m} が床 2N-1 を下回る")
            continue
        checked += 1
    for b in bad:
        print(f"NG: {b}")
    if bad:
        return 1
    print(f"OK  台帳 {checked} 行の証書を再生・検証した（{CSV_PATH.name}）")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", action="store_true", help="探索して台帳を作る（重い）")
    ap.add_argument("--only", help="この族だけ作り直す")
    ap.add_argument("--verify", action="store_true", help="証書を再生して検証（軽い）")
    ns = ap.parse_args()
    if ns.build:
        return cmd_build(ns.only)
    if ns.verify:
        return cmd_verify()
    ap.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
