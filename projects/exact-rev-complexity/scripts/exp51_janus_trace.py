"""既存の可逆メモ化実装（Janus）の**実行トレースを取り、厳密最適と比較する**。

`docs/51_paper_plan_candidate3.md` §4 の穴 1（最大の弱点）を埋めるための計測。
`docs/50_pro_paper_plan.md` の実験 A・B に対応。

## 何をするか

対象は `~/dev/overleaf/2017_rev_memoization/program/fib.janus`（対 Fibonacci のメモ化）。
**メモ表 `M[]` の非ゼロ要素の集合がペブル配置**である、という対応で実行を追跡する:

| 実装の操作 | 本モデルでの操作 |
|---|---|
| `M[i]` が 0 → 非 0 になる（`M[i] ^= ...` で値を入れる） | 節点 $i$ に **put** |
| `M[i]` が 非 0 → 0 になる（`M[i] ^= r` で打ち消す） | 節点 $i$ から **take** |
| 同時に非ゼロな `M[]` の個数の最大 | **ピーク $p$** |

得られた $(\text{put}|\text{take}, i)$ 列を**我々の検証器に通し**（規則・ピーク・clean 終端）、
通れば「実装は clean 可逆ペブリングを実行している」ことの実証になる。
そのうえで手数を $M^*$ と比較する。

## 依存

PyJanus（`~/dev/github.com/yokoyama-lab/PyJanus`）を**読み取り専用で**インポートする。
同リポジトリは変更しない。標準ライブラリのみで動く。

    python3 scripts/exp51_janus_trace.py
"""

from __future__ import annotations

import sys
from pathlib import Path

PYJANUS = Path.home() / "dev/github.com/yokoyama-lab/PyJanus"
sys.path.insert(0, str(PYJANUS))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from jana_py.cli import parse_for_std  # noqa: E402
from jana_py.runtime import Frame, Runtime  # noqa: E402


class MemoTracer(Runtime):
    """メモ表の非ゼロ要素集合を各文の実行後に記録する Runtime。

    `jana_py/pebble.py` の `_ProfilingRuntime` と同じフック（`_exec_stmt_impl`）を使う。
    """

    def __init__(self, program, memo_name: str = "M", **kwargs):
        super().__init__(program, **kwargs)
        self.memo_name = memo_name
        self.configs: list[frozenset[int]] = []
        self._root: Frame | None = None

    def _snapshot(self) -> None:
        """全フレームから配列 `memo_name` を探し、非ゼロ添字の集合を記録する。"""
        cur: set[int] = set()
        frames = [self._root] if self._root else []
        for fr in frames:
            if fr is None:
                continue
            cell = fr.vars.get(self.memo_name)
            if cell is None:
                continue
            val = getattr(cell, "value", None)
            if isinstance(val, list):
                for i, v in enumerate(val):
                    if v:
                        cur.add(i)
        cfg = frozenset(cur)
        if not self.configs or self.configs[-1] != cfg:
            self.configs.append(cfg)

    def run(self) -> str:
        if self.program.main is None:
            raise RuntimeError("main 手続きが無い")
        frame = Frame(vars={})
        self._root = frame
        self.main_vdecls = list(self.program.main.vdecls)
        self._init_vdecls(frame, self.program.main.vdecls)
        self._snapshot()
        self._exec_block(frame, self.program.main.stmts)
        self._snapshot()
        return ""

    def _exec_stmt_impl(self, frame, stmt, allow_break, record_stmt, record_nested=False):
        super()._exec_stmt_impl(
            frame, stmt, allow_break=False,
            record_stmt=record_stmt, record_nested=record_nested,
        )
        self._snapshot()


def configs_to_moves(configs: list[frozenset[int]]) -> list[tuple[str, int]]:
    """配置列を $(\\text{put}|\\text{take}, i)$ 列に正規化する。

    1 ステップで複数の添字が変化した場合は**分解して並べる**（実装の 1 文が
    モデルの複数手に対応することがある）。put を先に並べる（依存を満たすため）。
    """
    moves: list[tuple[str, int]] = []
    for a, b in zip(configs, configs[1:]):
        for i in sorted(b - a):
            moves.append(("put", i))
        for i in sorted(a - b, reverse=True):
            moves.append(("take", i))
    return moves


def analyse(path: Path, memo_name: str = "M") -> dict:
    src = path.read_text()
    # PyJanus の方言別パーサ。cli.parse_for_std(std, filename, text, line_origins)
    prog = parse_for_std("jana2014", str(path), src, None)
    tr = MemoTracer(prog, memo_name=memo_name)
    tr.run()
    cfgs = tr.configs
    moves = configs_to_moves(cfgs)
    peak = max((len(c) for c in cfgs), default=0)
    touched = sorted({i for c in cfgs for i in c})
    return {
        "configs": len(cfgs),
        "moves": len(moves),
        "peak": peak,
        "touched": touched,
        "final": sorted(cfgs[-1]) if cfgs else [],
        "move_list": moves,
        "config_list": cfgs,
    }


def main() -> None:
    targets = [
        (Path.home() / "dev/overleaf/2017_rev_memoization/program/fib.janus", "M"),
        (Path.home() / "dev/overleaf/2017_rev_memoization/program/fac.janus", "t"),
    ]
    for path, memo in targets:
        if not path.exists():
            print(f"（{path.name} は存在しない）")
            continue
        try:
            r = analyse(path, memo)
        except Exception as exc:  # 解析できない方言は正直に報告する
            print(f"{path.name}: 解析できなかった — {type(exc).__name__}: {exc}")
            continue
        print(f"=== {path.name}（メモ表 `{memo}[]`）")
        print(f"  異なる配置の個数: {r['configs']}")
        print(f"  正規化後の手数:   {r['moves']}")
        print(f"  ピーク（同時非ゼロ数）: {r['peak']}")
        print(f"  触れた添字: {r['touched']}")
        print(f"  終端配置:   {r['final']}")
        head = r["move_list"][:14]
        print(f"  先頭の手:   {head}")


if __name__ == "__main__":
    main()
