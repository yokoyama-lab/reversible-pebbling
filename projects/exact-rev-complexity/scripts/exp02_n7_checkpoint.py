"""候補2: n=7 の同型除去を「時間予算つき・チェックポイント再開可能」に完走させる。

## 背景

`exp02_dags.canonical_key`（既に `tests/test_exp02_dags.py` で n<=6 の独立全探索と
一致することを検証済み・信用してよい実装）を使った同型除去は、n=7 の
615,195 件のラベル付き候補に対して素朴に走らせると約10〜15分かかり、
リポジトリの「1回の計算は10分以内」の目安を単発では超える
（`docs/idea02_separation_onset.md` §9 の前回報告）。

WL不変量での事前バケット分割も検討したが、n=7 のこの DAG 族では
バケットの94%が非自明（サイズ>1）になり、有効な高速化にならないことを確認済み
（縮減率6%程度。`data/exp02_results.md` 2026-07-27追記 参照）。
ヒューリスティックな正当性が未証明の高速化（色クラス制約つき順列探索など）を
拙速に投入するのは、厳密性が売りの本プロジェクトでは避けるべきリスクと判断した。

**採った方針**: アルゴリズムは変えず（= 既に信用済みの `canonical_key` のまま）、
**計算を時間予算で分割し、チェックポイントに保存して複数回の実行で完走させる**
（team-lead の指示通り）。1回の実行は `--budget` 秒（既定360秒）で必ず終了し、
チェックポイント `data/exp02_n7_checkpoint.json` に進捗を保存する。
再実行すれば続きから処理される。

## 実行

```bash
python3 scripts/exp02_n7_checkpoint.py --budget 360   # 完了するまで繰り返し実行
python3 scripts/exp02_n7_checkpoint.py --status        # 進捗だけ確認
```

完了（next_index == len(labeled)）したら `data/exp02_n7_classes.json` に
非同型類（辺リスト）を書き出す。
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp02_dags import canonical_key, generate_labeled  # noqa: E402

DATA_DIR = Path(__file__).resolve().parents[1] / "data"


def checkpoint_path(n: int) -> Path:
    return DATA_DIR / f"exp02_n{n}_checkpoint.json"


def classes_path(n: int) -> Path:
    return DATA_DIR / f"exp02_n{n}_classes.json"


def _edges_to_list(edges: frozenset[tuple[int, int]]) -> list[list[int]]:
    return sorted([list(e) for e in edges])


def _list_to_edges(lst: list[list[int]]) -> frozenset[tuple[int, int]]:
    return frozenset((a, b) for a, b in lst)


def load_checkpoint(n: int) -> dict:
    path = checkpoint_path(n)
    if path.exists():
        with open(path) as f:
            return json.load(f)
    return {"next_index": 0, "keys": [], "reps": []}


def save_checkpoint(n: int, state: dict) -> None:
    DATA_DIR.mkdir(exist_ok=True)
    path = checkpoint_path(n)
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w") as f:
        json.dump(state, f)
    tmp.replace(path)


def run_chunk(n: int, budget_sec: float, *, quiet: bool = False) -> dict:
    """チェックポイントから続きを最大 budget_sec 秒だけ処理し、状態を保存して返す。

    戻り値の state は保存後のもの（呼び出し側のテストで検証しやすくするため）。
    """
    t_gen0 = time.time()
    labeled = generate_labeled(n)
    if not quiet:
        print(f"labeled candidates: {len(labeled)} (生成 {time.time() - t_gen0:.1f}s)")

    state = load_checkpoint(n)
    next_index = state["next_index"]
    # keys は JSON では list-of-list-of-pair なので canonical_key の tuple 形式へ戻す。
    seen: dict[tuple, frozenset] = {
        tuple(tuple(p) for p in key): _list_to_edges(rep)
        for key, rep in zip(state["keys"], state["reps"])
    }
    if not quiet:
        print(f"resume from index {next_index}/{len(labeled)} (既知の非同型類: {len(seen)})")

    t0 = time.time()
    i = next_index
    while i < len(labeled):
        edges = labeled[i]
        key = canonical_key(edges, n)
        if key not in seen:
            seen[key] = edges
        i += 1
        if time.time() - t0 > budget_sec:
            break

    dt = time.time() - t0
    done = i >= len(labeled)
    if not quiet:
        print(
            f"processed this chunk: {i - next_index} graphs in {dt:.1f}s "
            f"(累積 {i}/{len(labeled)} = {100 * i / len(labeled):.1f}%)"
            + (" [完了]" if done else " [予算切れ、再実行で継続]")
        )
        print(f"現在の非同型類数: {len(seen)}")

    new_state = {
        "next_index": i,
        "keys": [[list(p) for p in key] for key in seen],
        "reps": [_edges_to_list(rep) for rep in seen.values()],
    }
    save_checkpoint(n, new_state)

    if done:
        DATA_DIR.mkdir(exist_ok=True)
        with open(classes_path(n), "w") as f:
            json.dump({"n": n, "classes": new_state["reps"]}, f)
        if not quiet:
            print(f"完走: {classes_path(n)} に {len(seen)} 非同型類を書き出した。")

    return new_state


def status(n: int) -> None:
    labeled = generate_labeled(n)
    path = checkpoint_path(n)
    if not path.exists():
        print(f"チェックポイント無し。labeled={len(labeled)}, 未着手。")
        return
    state = load_checkpoint(n)
    i = state["next_index"]
    print(
        f"進捗: {i}/{len(labeled)} ({100 * i / len(labeled):.1f}%), "
        f"現在の非同型類数: {len(state['reps'])}, "
        f"完了: {i >= len(labeled)}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=7)
    parser.add_argument("--budget", type=float, default=360.0)
    parser.add_argument("--status", action="store_true")
    args = parser.parse_args()
    if args.status:
        status(args.n)
    else:
        run_chunk(args.n, args.budget)
