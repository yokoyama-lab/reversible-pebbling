#!/usr/bin/env python3
"""2 つの層ファイル（各行 "深さ 状態数"）を突き合わせる.

    python3 compare_layers.py <A の層ファイル> <B の層ファイル> [--goal D]
完全一致なら 0、食い違いがあれば最初の食い違いを示して 1 を返す。
共通の深さの範囲だけでなく、行数（最後の深さ）が等しいことも確かめる。
--goal D を付けると、深さ D までの累計（ゴールに達した時点の総状態数）も出す。
"""
import sys


def load(path: str) -> list[tuple[int, int]]:
    out = []
    for line in open(path):
        if line.strip():
            d, n = line.split()
            out.append((int(d), int(n)))
    for i, (d, _) in enumerate(out):
        if d != i:
            raise SystemExit(f"{path}: {i} 行目の深さが {d}（連番でない）")
    return out


def main() -> int:
    a, b = load(sys.argv[1]), load(sys.argv[2])
    goal = int(sys.argv[sys.argv.index("--goal") + 1]) if "--goal" in sys.argv else None
    for (d, x), (_, y) in zip(a, b):
        if x != y:
            print(f"DIFFER: 深さ {d} で A={x} B={y}")
            return 1
    if len(a) != len(b):
        print(f"DIFFER: 層の数が違う A={len(a)} B={len(b)}（共通の {min(len(a), len(b))} 層は一致）")
        return 1
    tot = sum(n for _, n in a)
    msg = f"IDENTICAL: {len(a)} 層（深さ 0..{len(a) - 1}）、総状態数 {tot}"
    if goal is not None:
        msg += f"、深さ {goal} までの累計 {sum(n for d, n in a if d <= goal)}"
    print(msg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
