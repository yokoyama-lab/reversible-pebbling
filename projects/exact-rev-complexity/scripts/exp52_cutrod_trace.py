"""2021 の cut rod 実装を計測し、**メモ表とガベージスタックを同時に追跡**する。

`data/exp51_janus_trace_findings.md` §5-2 の続き。狙いは
`data/exp03_results.md` §D.5 で提案した**第 4 パラメータ $s$（ガベージ領域の深さ）の実測値**。

対象: `~/dev/overleaf/2021_rev_memoization2/programs/`（原本は読むだけ・変更しない）
- `topDownCutRod.janus`（ガベージスタック `g` を使う）
- `topDownCutRod_symmetric.janus`（局所 Bennett 法）
- `topDownCutRod_twoMemoTables.janus`（2 つのメモ表＝ペブルを増やして手数を減らす版）
- `bottomUpCutRod.janus`, `mfib_w_counters.janus`

記録するもの:
| 実装 | 本モデル |
|---|---|
| メモ表 `r[]` の非ゼロ添字集合 | ペブル配置 |
| 同時非ゼロ数の最大 | ピーク $p$ |
| **スタック `g` の深さ** | **第 4 パラメータ $s$** |

    python3 scripts/exp52_cutrod_trace.py
"""

from __future__ import annotations

import sys
from pathlib import Path

PYJANUS = Path.home() / "dev/github.com/yokoyama-lab/PyJanus"
sys.path.insert(0, str(PYJANUS))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from jana_py.cli import parse_for_std  # noqa: E402
from jana_py.runtime import Frame, Runtime  # noqa: E402

PROGDIR = Path.home() / "dev/overleaf/2021_rev_memoization2/programs"


class MemoStackTracer(Runtime):
    """メモ表の非ゼロ集合と、全フレームのスタック総深さを各文ごとに記録する。"""

    def __init__(self, program, memo_names=("r", "r2", "M", "t"), **kwargs):
        super().__init__(program, **kwargs)
        self.memo_names = memo_names
        self.samples: list[tuple[frozenset[str], int]] = []
        self._frames: list[Frame] = []
        self.steps = 0   # 総実行文数（時間の代理指標）

    def _collect(self) -> tuple[frozenset[str], int]:
        """メモ表の非ゼロ集合と、全フレームのスタック総深さ。

        PyJanus では Cell の `kind` が `"stack"` のものがスタック（`runtime.py:278`）。
        メモ表（配列）は `kind` が別で、値が list。
        """
        pebbles: set[str] = set()
        depth = 0
        for fr in self._frames:
            for name, cell in list(fr.vars.items()):
                if getattr(cell, "kind", None) == "stack":
                    val = getattr(cell, "value", None)
                    if hasattr(val, "__len__"):
                        depth += len(val)
                    continue
                val = getattr(cell, "value", None)
                if isinstance(val, list) and name in self.memo_names:
                    for i, v in enumerate(val):
                        if v:
                            pebbles.add(f"{name}[{i}]")
        return frozenset(pebbles), depth

    def _snap(self) -> None:
        s = self._collect()
        if not self.samples or self.samples[-1] != s:
            self.samples.append(s)

    def run(self) -> str:
        if self.program.main is None:
            raise RuntimeError("main 手続きが無い")
        frame = Frame(vars={})
        self._frames = [frame]
        self.main_vdecls = list(self.program.main.vdecls)
        self._init_vdecls(frame, self.program.main.vdecls)
        self._snap()
        self._exec_block(frame, self.program.main.stmts)
        self._snap()
        return ""

    def _exec_stmt_impl(self, frame, stmt, allow_break, record_stmt, record_nested=False):
        if frame not in self._frames:
            self._frames.append(frame)
        super()._exec_stmt_impl(
            frame, stmt, allow_break=False,
            record_stmt=record_stmt, record_nested=record_nested,
        )
        self.steps += 1
        self._snap()


def analyse(name: str) -> dict:
    path = PROGDIR / f"{name}.janus"
    prog = parse_for_std("jana2014", str(path), path.read_text(), None)
    tr = MemoStackTracer(prog)
    tr.run()
    peb = [s[0] for s in tr.samples]
    dep = [s[1] for s in tr.samples]
    moves = 0
    for a, b in zip(peb, peb[1:]):
        moves += len(b - a) + len(a - b)
    return {
        "steps": tr.steps,
        "samples": len(tr.samples),
        "moves": moves,
        "peak_pebbles": max((len(c) for c in peb), default=0),
        "peak_stack": max(dep, default=0),
        "final_pebbles": sorted(peb[-1]) if peb else [],
        "final_stack": dep[-1] if dep else 0,
    }


def main() -> None:
    names = [
        "topDownCutRod",
        "topDownCutRod_symmetric",
        "topDownCutRod_twoMemoTables",
        "bottomUpCutRod",
        "mfib_w_counters",
    ]
    print(
        f"{'プログラム':<30} {'総歩数':>7} {'メモ手数':>8} {'メモpeak':>8} "
        f"{'stack peak':>10} {'終端メモ':>8}"
    )
    for n in names:
        try:
            r = analyse(n)
        except Exception as exc:
            print(f"{n:<30} 実行できなかった — {type(exc).__name__}: {str(exc)[:40]}")
            continue
        clean = "空" if not r["final_pebbles"] else f"{len(r['final_pebbles'])}個"
        print(
            f"{n:<30} {r['steps']:>7} {r['moves']:>8} {r['peak_pebbles']:>8} "
            f"{r['peak_stack']:>10} {clean:>8}"
        )


if __name__ == "__main__":
    main()
