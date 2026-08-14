# $M^*(G,p,e)$ の下界を DRAT 証明付きで確認（2026-08-10）

## 結論

`scripts/sat_pebble.py` に決定問題

$$M^*(G,p,e)\le k\ ?$$

の一般 DAG 向け時間展開 CNF を実装した。指定された鎖 8 ケースはすべて、

- $k=M^*$: **SATISFIABLE**。CaDiCaL のモデルから復号した手順を独立検証器に通した。
- $k=M^*-2$: **UNSATISFIABLE**。CaDiCaL の ASCII DRAT を **全件 `drat-trim` で VERIFIED**。

となり、`landauer_bfs` の真値と一致した。したがって以下の表には
「CaDiCaL は UNSAT と言ったが証明は未検証」の行はない。下界側 8 件はすべて
独立な proof checker を通過している。

符号化を実装前に固定した文書は `data/sat_encoding_design.md`、回帰テストは
`tests/test_sat_pebble.py`。

## 符号化の要点

時刻 $0,\ldots,k$ の配置 $x_{t,v}$ と、各ステップの put / take / idle、可用性、
不可逆 take を表すブール変数を置いた。各スロットは exactly-one action、ピークと
消去予算は Sinz 型逐次カウンタで表す。

これは「ちょうど $k$ 手」ではなく**本当に $k$ 手以下**の決定問題である。
実手を先頭へ、idle を接尾辞へ置く節 $I_t\Rightarrow I_{t+1}$ を加えた。
任意の $L\le k$ 手の実行は末尾に $k-L$ 個の idle を足せ、逆向きには idle 接尾辞を
捨てられるので、充足可能性は変わらない。

グラフ同型を仮定する対称性除去は使っていない。idle 接尾辞だけを通常の CNF 入力節として
与え、証明形式は **DRAT**、検査器は **`drat-trim`** とした。DPR/SR は不要なので
`dpr-trim` は使っていない。

SAT モデルは CNF と別に手続き型検証器へ通し、初期・clean 終端、put の可用性、take、
ピーク、不可逆消去数、手数上限を再検査する。UNSAT は次の鎖で認証する。

```text
DIMACS CNF -> CaDiCaL 3.0.1 -> ASCII DRAT -> drat-trim -> s VERIFIED
```

## 指定 8 ケースの結果

実行環境は <host>、Intel Xeon Silver 4509Y、Linux 6.17、CaDiCaL 3.0.1。
下表の秒数は各プロセス内の wall time（3 桁丸め）。報告用走行は 4 プロセスずつの
並列バッチだったため、行の秒数は足し合わせた全体 wall timeではない。

| case | $p$ | $e$ | BFS $M^*$ | $k=M^*$ | CaDiCaL | 復号手順 | $k=M^*-2$ | vars | clauses | CaDiCaL | DRAT bytes | `drat-trim` |
|---|---:|---:|---:|---|---:|---|---|---:|---:|---:|---:|---|
| chain(4) | 3 | 0 | 9 | SAT | 0.003 s | VERIFIED (9 手) | 7: UNSAT | 310 | 745 | 0.003 s | 3,864 | **VERIFIED, 0.080 s** |
| chain(4) | 3 | 1 | 7 | SAT | 0.003 s | VERIFIED (7 手) | 5: UNSAT | 246 | 579 | 0.003 s | 4,105 | **VERIFIED, 0.081 s** |
| chain(6) | 4 | 0 | 15 | SAT | 0.005 s | VERIFIED (15 手) | 13: UNSAT | 914 | 2,205 | 0.004 s | 9,352 | **VERIFIED, 0.067 s** |
| chain(6) | 4 | 1 | 11 | SAT | 0.005 s | VERIFIED (11 手) | 9: UNSAT | 696 | 1,651 | 0.004 s | 10,131 | **VERIFIED, 0.069 s** |
| chain(8) | 4 | 0 | 25 | SAT | 0.012 s | VERIFIED (25 手) | 23: UNSAT | 2,110 | 5,165 | 0.010 s | 66,281 | **VERIFIED, 0.076 s** |
| chain(8) | 4 | 1 | 17 | SAT | 0.007 s | VERIFIED (17 手) | 15: UNSAT | 1,510 | 3,635 | 0.010 s | 54,339 | **VERIFIED, 0.080 s** |
| chain(12) | 5 | 0 | 39 | SAT | 0.139 s | VERIFIED (39 手) | 37: UNSAT | 5,474 | 13,321 | 0.154 s | 1,045,158 | **VERIFIED, 0.133 s** |
| chain(12) | 5 | 1 | 29 | SAT | 0.215 s | VERIFIED (29 手) | 27: UNSAT | 4,338 | 10,407 | 0.258 s | 1,516,850 | **VERIFIED, 0.229 s** |

丸めた行時間の合計は、SAT 側 CaDiCaL 0.389 秒、UNSAT 側 CaDiCaL 0.446 秒、
`drat-trim` 0.815 秒。UNSAT 8 本の DRAT は合計 2,710,080 bytes。

なお非 free 目標では $M^*$ は必ず奇数である。put 数を $a$、take 数を $r$ とすると、空配置から
1 ペブルだけの終端へ行くため $a-r=1$、従って手数 $a+r=2r+1$。このため
「一段短い候補」は 2 刻みの $M^*-2$ になる。本実装は at-most 決定問題そのものを
符号化しているので、$M^*-2$ の UNSAT はそれ以下の全手数を同時に排除する。

## DRAT ログ

報告用の CNF / DRAT は `/tmp/sat_pebble_final/` に生成した（git には追加していない）。
同じファイルは下の再現コマンドで生成できる。UNSAT 8 本の SHA-256 は次のとおり。

```text
f28bb5a97cd37683208b907897a7d436e558795d0cb7f2dc22d11a1dbceaa05e  chain4_p3_e0_k7.drat
46cb8e2bcedd9a5415fee3af4936242ec9939fe7e5bd5a9129513686398f52de  chain4_p3_e1_k5.drat
18f79b618a63d011b6f0bf94a0e1cf5cbecff3abe2ff54e247bf18800ff66eb3  chain6_p4_e0_k13.drat
71ea4ebac50dc51a1fff78896872178dd044ac7fd8974ec15d8afe28a75bdcf7  chain6_p4_e1_k9.drat
e85a2ade305cd67f52fe835f801977bef158359e4d182202858b2943dd821e7b  chain8_p4_e0_k23.drat
f8cb44fdf2d832dd5a3a39f82b9f51f9c2870be2c2f64ee1cc4695378892ff21  chain8_p4_e1_k15.drat
05e08e041829f8758eb571a3966c03aacb4cc5c6cdadedee92720ebfb71e36cc  chain12_p5_e0_k37.drat
31d4336d9a3c167c46d17209e79efecb9fdc58133bb7db32e6ea0ececa35e800  chain12_p5_e1_k27.drat
```

例（最大の $e=0$ 下界）:

```bash
.venv/bin/python scripts/sat_pebble.py \
  --n 12 --p 5 --e 0 --k 37 \
  --workdir /tmp/sat_pebble_final

drat-trim \
  /tmp/sat_pebble_final/chain12_p5_e0_k37.cnf \
  /tmp/sat_pebble_final/chain12_p5_e0_k37.drat
```

CLI は `drat-trim` の終了コードが 0 **かつ**出力に `s VERIFIED` がある場合だけ
`CERTIFIED LOWER BOUND` と表示する。それ以外は必ず
「CaDiCaL は UNSAT と報告したが証明は未検証」と表示して非 0 終了する。

## 回帰検証

実行したコマンド:

```bash
.venv/bin/python -m pytest tests/test_sat_pebble.py -q
# 21 passed in 3.27s

.venv/bin/python -m pytest \
  tests/test_sat_lower_bound.py tests/test_sat_pebble.py -q
# 26 passed in 3.89s

ruff check --no-cache scripts/sat_pebble.py tests/test_sat_pebble.py
# All checks passed!

ruff format --check scripts/sat_pebble.py tests/test_sat_pebble.py
# 2 files already formatted
```

新規テストの照合範囲:

- 指定 8 ケースの BFS 真値、SAT 側、UNSAT + DRAT 側。
- chain($n$), $n=1..4$, $p=0..3$, $e=0..1$, $k=0..9$ の全 320 決定点。
- 先行点が 2 個ある完全二分木とピラミッド（一般 DAG の AND 可用性）。
- free target、偶数 $k$ での idle、入力境界。
- 逐次カウンタを入力数 0..4 の全 primary 割当てで真理値表照合。
- `drat-trim` 不在時は UNSAT でも `UNAVAILABLE` とし、認証済みにしない負例。

## 信頼境界

DRAT 検査が直接保証するのは「出力した DIMACS CNF が UNSAT」である。
ゲームと CNF の同値性まで `drat-trim` が理解するわけではない。その境界は、実装前に固定した
健全性・完全性の議論（`data/sat_encoding_design.md`）、BFS との全点照合、SAT witness の
独立検査という別層で覆った。これは CP-SAT / MIP の `INFEASIBLE` だけに依存する従来の
下界より、少なくとも SAT ソルバの誤判定を独立検査できる分だけ強い。
