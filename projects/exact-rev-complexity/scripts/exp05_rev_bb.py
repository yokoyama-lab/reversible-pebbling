"""候補5 の駆動スクリプト: 可逆 Busy Beaver の全数枚挙。

    python3 scripts/exp05_rev_bb.py --states 3 --formalism quintuple
    python3 scripts/exp05_rev_bb.py --states 3 --formalism quadruple
    python3 scripts/exp05_rev_bb.py --states 3 --ordinary   # 通常 BB（実装検証用）

出力は決定的（乱数を使わない）。`--json` で機械可読。
"""

import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from revbb import enumerate_quadruple, enumerate_quintuple  # noqa: E402

KEYS = ("machines", "halt", "nonhalt_cycle", "nonhalt_translated",
        "nonhalt_no_halt_rule", "undecided", "cycle_not_initial",
        "best_steps", "best_ones")


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--states", type=int, required=True)
    ap.add_argument("--formalism", choices=("quintuple", "quadruple"),
                    default="quintuple")
    ap.add_argument("--ordinary", action="store_true",
                    help="可逆性制約を外す（通常 BB。実装検証用）")
    ap.add_argument("--limit", type=int, default=5000, help="ステップ上限")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)

    t0 = time.time()
    if a.formalism == "quintuple":
        s = enumerate_quintuple(a.states, a.limit, reversible=not a.ordinary,
                                collect_undecided=True)
    else:
        s = enumerate_quadruple(a.states, a.limit, reversible=not a.ordinary)
    dt = time.time() - t0

    out = {k: s[k] for k in KEYS}
    out["best_steps_machine"] = s["best_steps_machine"]
    out["best_ones_machine"] = s["best_ones_machine"]
    out["undecided_machines"] = s.get("undecided_machines", [])[:50]
    out["seconds"] = round(dt, 2)
    out["states"] = a.states
    out["formalism"] = a.formalism
    out["reversible"] = not a.ordinary
    out["step_limit"] = a.limit

    if a.json:
        print(json.dumps(out, ensure_ascii=False, indent=1))
        return 0

    label = ("通常" if a.ordinary else "可逆") + f" BB / {a.formalism} / k={a.states}"
    print(f"=== {label}  (上限 {a.limit} step, {dt:.1f}s)")
    print(f"  枚挙台数            : {s['machines']}")
    print(f"  停止                : {s['halt']}")
    print(f"  非停止(巡回)        : {s['nonhalt_cycle']}"
          f"  ／うち初期配置に戻らなかったもの: {s['cycle_not_initial']}")
    print(f"  非停止(並進型)      : {s['nonhalt_translated']}")
    print(f"  非停止(停止規則なし): {s['nonhalt_no_halt_rule']}")
    print(f"  未判定              : {s['undecided']}")
    verdict = "確定値" if s["undecided"] == 0 else "下界（未判定機械が残る）"
    print(f"  最大ステップ数      : {s['best_steps']}  [{verdict}]"
          f"  {s['best_steps_machine']}")
    print(f"  最大 1 の個数       : {s['best_ones']}  [{verdict}]"
          f"  {s['best_ones_machine']}")
    for m in s.get("undecided_machines", [])[:20]:
        print(f"    未判定: {m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
