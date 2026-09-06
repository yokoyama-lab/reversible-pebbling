# PB-cert 継続セッション（2026-09-06）

> **判定（1 行）**: 前任の DRAT vs VeriPB 表は**再現した**（h=7・h=15 をバイト単位で一致・
> `s VERIFIED`）。dpr-trim の副題は**作業中**（この版では未完）。

作業中の版。末尾の「まだやっていないこと」を必ず読むこと。

## 0. 環境と道具（この版で使ったもの）

| 道具 | 版 | 所在 |
|---|---|---|
| VeriPB | 3.0.2 | `veripb`（`~/.local/bin`） |
| dpr-trim | （同梱例つき） | `dpr-trim`（`<local>/opt/tools/dpr-trim` に例） |
| drat-trim / cadical | — | `drat-trim` / `cadical` |
| nauty (`dreadnaut`) | — | `/home/linuxbrew/.linuxbrew/bin/dreadnaut` |
| **Exact** | **2.2.1** | ⚠ **前任の scratchpad の venv にしか無い** — 下記 |

⚠ **Exact 2.2.1 の在処が揮発性である。** リポジトリにも `~/.venvs/*` にも入っておらず、
実体は前任セッションの scratchpad の venv だけ:

```
/work/tmp/claude-1000/-work-a-dev-github-com-tetsuo-jp-exact-rev-complexity-notes-pbcert/\
2da29e28-dc48-4e24-ac19-c08f5929240e/scratchpad/pb313/bin/python   # Python 3.13.7 + Exact 2.2.1
```

（`pbvenv/` に Python 3.14 版もある。）**この scratchpad が消えると PB 経路は再現できない。**
恒久化（`~/.venvs/pb` を作って `pip install exact`）は**未実施**。→「まだやっていないこと」

## 1. 道具が効いていることの自己試験（陽性・陰性の対）— **10/10 OK**

`python3 scripts/pbcert_selftest.py`（2026-09-06 実行。生ログ `logs/selftest_2026-09-06.out`）

* VeriPB 5 件: 正しい `pol` 証明＝受理 / `pol` の足し算を 1 行壊した＝拒否 /
  基数伝播の `rup` 証明＝受理 / 充足可能な系で成り立たない `rup`＝拒否 /
  矛盾なしに `UNSAT` と結論＝拒否。
* dpr-trim 5 件: PHP(4,3) の cadical DRAT＝受理 / 充足可能な PHP(4,4) の偽反駁＝拒否 /
  hole20 の PR 証明（2,870 行）＝受理 / その 1 行目を壊した＝拒否 /
  **同じ PR 証明を `drat-trim` に渡すと拒否**（＝ DPR が DRAT より強いことの対照）。

⚠ 前任が残した注記を再確認: **UNSAT な系の DRAT はリテラルを 1 つ反転しても
たいてい別の妥当な証明になる**ので、「1 行壊す」型の陰性対照は DRAT では成立しない。
陰性対照は「充足可能な系を反駁したと主張する」形で取っている。

## 2. 符号化の二重実装照合 — OK

`python3 scripts/pbcert_pyr_opb.py --check` →
**生成 CNF は `q2_pyr_lower_cert.build` と節単位で一致**（h=2..8 × B∈{2h-2, 2h, 2h+2}）。
これがずれていたら以降の比較は無意味なので、毎回先に通す。

## 3. 【検算】前任の DRAT vs VeriPB 表 — **2 点とも再現（バイト単位で一致）**

`scripts/pbcert_measure.py --hs 7,15 --sat-side`（生ログ `logs/recheck_h7_h15_2026-09-06.out`）。
`runcap -m 16 -t 2400`、実測ピーク 111 MB / 4 秒。

| h | B | 経路 | 式 | 変数 | 証明 | 検査 | 前任の値と |
|---:|---:|---|---:|---:|---:|---|---|
| 7 | 15 | DRAT | 222,524 B | 6,825 | 178,976 B / 12,558 行 | `s VERIFIED` | **一致** |
| 7 | 15 | VeriPB | 99,715 B | 945 | **9,137 B / 546 行** | `s VERIFIED` | **一致** |
| 15 | 40 | DRAT | 6,175,528 B | 151,965 | 3,484,260 B / 203,390 行 | `s VERIFIED` | **一致** |
| 15 | 40 | VeriPB | 1,705,658 B | 7,965 | **91,397 B / 4,456 行** | `s VERIFIED` | **一致** |

* **比: h=7 で 19.59×、h=15 で 38.12×**（前任の報告値と同一）。
* SAT 側（h=7 B=16 / h=15 B=41）も両経路とも SAT を返した＝**符号化が UNSAT だけを
  出す壊れ方をしていない**（前任と一致）。
* 健全性（Exact の式が我々の OPB の部分集合）も再確認: **落とした制約 0 本**
  （h=7 で 3,389 本中 / h=15 で 52,049 本中）。

⇒ **決定点「VeriPB は DRAT より小さいか」は、検算した 2 点の範囲で支持を維持する。**
残る 6 点（h=8,9,10,11,12,16）は**前任の値のまま**で、私は再実行していない。

## まだやっていないこと

* **dpr-trim（対称性除去つき証明）— 未着手**。
* **自己同型群の位数 7.46e46 の真偽 — 未検証**（前任の疑いも未解決）。
* 表の残り 6 点（h=8,9,10,11,12,16）の再実行。
* **Exact 2.2.1 の恒久化**（いまは前任 scratchpad の venv 依存＝いつ消えてもおかしくない）。
