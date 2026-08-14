# 引き継ぎ: `reach(p,e)` の族拡張（2026-08-12）

セッション `Opus5-xhigh`（2026-08-10 夜〜08-12）の記録。
**このセッションは 3 リポジトリにまたがる。** 本ファイルは `exact-rev-complexity` の分が主で、
残り 2 つは §7 にポインタを置く。

---

## 0. 読む順（新セッションはこの順）

1. **本ファイル**（全体像・確定事実・落とし穴）
2. `data/reach_families_findings.md` — **所見の正本。§9 が最新の核心**
3. `data/reach_families.md` — 表（自動生成。手編集禁止）
4. `docs/24_survey_reach_pe.md` — 鎖の `reach(p,e)` の先行研究調査（既存）
5. **`docs/25_survey_family_dichotomy.md` — 並行セッションの成果。同じ問いで私より先へ進んでいる。
   本ファイルより先に読むべき場合がある**（§6.1 参照）
6. `data/e0_boundary.md` — 同じく並行セッション（境界族の探索）

---

## 1. 何をしたか

定理 B2 `reach(p,e) = (e+2)2^{p-2}` は**鎖でしか成り立っていない**ので、他の族へ広げた。

| 新規ファイル | 中身 |
|---|---|
| `scripts/exp03_reach_dag.py` | 一般 DAG の `reachable_dag` / `min_erasures_dag` / 族ドライバ / 族 `fib_chain` |
| `tests/test_exp03_reach_dag.py` | **実装より先に書いた**回帰テスト |
| `scripts/reach_log_to_csv.py` | 実行ログから CSV を復元する救出用 |
| `scripts/gen_reach_families.py` | `data/reach_families.md` の生成器 |
| `data/reach_families_findings.md` | 所見（**正本**） |
| `data/reach_{chain,pyramid,fib,cbt}.csv` | 厳密値 |

> **`scripts/exp03_reach_dag.py` と `tests/` は並行セッションも編集している**（族を 12 個追加済み）。
> 触る前に `git log` と現物を確認すること。§6 参照。

---

## 2. 確定している事実（再確認不要）

### 2.1 検証ゲート（これが通らなければ以下の数値は使えない）

`python3 tests/test_exp03_reach_dag.py` → **13/13 通過**（うち 2 本は並行セッション作）。

- 鎖で `exp03_reach.reachable` と **480 点 不一致 0**
- `e=0` が `revpebble.bfs` と一致
- **`reach(p)=2^{p-1}` と定理 B2 `(e+2)2^{p-2}` を再現**
- 独立第 2 実装 `landauer.landauer_profile` と木・ピラミッド **144 点 不一致 0**
- `<host>` でも `--selftest` が 480 点 不一致 0（環境非依存）
- **監視側が独立に再現済み**（鎖 31 点で定理 B2 と一致）

### 2.2 数値（すべて厳密・全数計算）

**pyramid は完走**（`data/reach_pyramid.csv` 49 升すべて `exact`）:

| p \ e | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| 3 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| 4 | 2 | 3 | 3 | 3 | 3 | 3 | 3 |
| 5 | 3 | 4 | 4 | 4 | 4 | 4 | 4 |
| 6 | 4 | 5 | 5 | 5 | 5 | 5 | 5 |
| 7 | 5 | 5 | 5 | 6 | 6 | 6 | 6 |
| 8 | 6 | 6 | 6 | 7 | 7 | 7 | 7 |

ピラミッドの `P`（標準ペブル数）・`R`（可逆ペブル数）:

| h | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| `P` | 1 | 3 | 4 | 5 | 6 | 7 | 8 |
| `R` | 1 | 3 | 5 | 6 | 7 | 8 | **10** |
| 差 | 0 | 0 | 1 | 1 | 1 | 1 | **2** |

`reach_fib(p,0)`（`p=1..9`）= **1, 2, 3, 5, 7, 11, 15, 23, 31** = **OEIS A052955**
（漸化式 `a(n)=2a(n−2)+1`。二重照合済み。A052955 に可逆ペブリングのコメントは無い）。

`P(band_w(n)) = w+1`（`n` に依らない。`w=1..4`, `n=6..24` で確認）。

### 2.3 中心的な結論

> **`reach_F(p,e)` は `e=0` の可逆ペブル数 `R` と `e=∞` の標準ペブル数 `P` を補間する量で、
> 消去がどれだけ買えるかは `P` が族の中で伸びるかどうかで決まる。**
>
> - `reach_F(p,0) = max{k : R(F(k)) ≤ p}`
> - `reach_F(p,∞) = max{k : P(F(k)) ≤ p}`
> - `P` が有界（`sup_k P = c < ∞`）なら `p ≥ c` で `reach_F(p,∞) = ∞`（消去は無限に効く）

**検算**: ピラミッドの両端 14 点すべて一致（不一致 0）、
中間も含めた **49 升すべてが区間 `[reach(p,0), reach(p,∞)]` に収まる**（逸脱 0）。

### 2.4 潰れた仮説（再提出しないこと）

| 仮説 | 反例 |
|---|---|
| 「分岐 ≥ 2 の DAG では消去は高々 1 回しか効かない」 | **`fib`（入次数 2、両方 non-free）で `e=20` まで伸び続ける。帯幅 3 でも同様** |
| 「`R−P` はいつも 1」 | **`h=7` で 2**（`h=3..6` は 1） |
| `reach_fib(p,e)=2·reach_fib(p−2,e)+1` | `p=5→7` は 7 点全部合うが **`(6,2)` で落ちる**（14 対 13） |
| `reach_fib(p,0)` は素数列 | `p=7` で 15（合成数） |

**「4〜5 点の当てはめは信用しない」が本セッションだけで 4 回当たった。**

---

## 3. 決まっていないこと（`?`＝打ち切り、`·`＝未計算。**どちらも「不可解」ではない**）

| 対象 | 状態 | 次にやること |
|---|---|---|
| `reach_cbt(p,e)` の `p ≥ 6` | **29 升で停止**。`p=6,e=1` で `runcap` のメモリ上限 20GB に到達（`cbt(6)` は 58.8M 状態・1219 秒） | `-m 40` 以上、または疎な表現（dict）へ |
| `pyr(8)` の `P`・`R` | 打ち切り | `movable=36`、`p≤13` で訪問表が大きい |
| `reach_fib(10,0)` | 打ち切り。**予測 47**（A052955 の次項） | 訪問表 6.9GB。ローカルなら可能 |
| `min_erasures_dag` の `emax` | **253 が上限**（訪問表 1 バイト）。超えると `ValueError` | 2 バイト表への拡張 |

---

## 4. 紙証明・層の昇格（**未着手**）

**層の昇格判断はしていない。** §2.3 の中心的結論は**紙証明を書いていない**:
`reach_F(p,∞) = max{k : P(F(k)) ≤ p}` を `landauer.py` の上端整合性テスト
（`e` 十分大 = `standard_bfs`）とつなぐ議論が未記述。
**ここを書くのが次の一手の筆頭。** 書けたら Lean へ。

---

## 5. 落とし穴（**同じ轍を踏まないこと**）

`data/reach_families_findings.md` §9.5・§9.8・§9.9 に詳述。要点だけ:

1. **`minE` の失敗値と `0` を混同しない。** 成功時は消去回数（`0` を含む）を返すので、
   失敗を `False` にすると `False == 0` で壊れる。**専用番人 `UNREACHABLE` を置いた**
   （`__bool__` も `__eq__` も `TypeError`）。`reachable_dag` の `UNKNOWN` も同様。
2. **`minE` の失敗は必ず `emax` を添えて読む。** `emax=60` で `P(chain(64))=3` と誤読した
   （正しくは 2。鎖は `p=2` で `n−2` 回の消去が要る）。
3. **`echo "rc=$?"` の直前にコマンド置換を書かない。** `$(date)` が `$?` を上書きし、
   `<host>` の cbt クラッシュを「rc=0 完走」と誤報告しかけた。
4. **救出・バックアップは「増える方向にしか書かない」。** 5 分ごとの復元ループが
   権威 CSV（49 升）を部分再構成（44 升）で上書きして壊した。
5. **`pgrep -f <文字列>` は自分自身を拾う。** これで 2 回誤判定した。
   `ps -eo args | grep "[r]clone"` のようにブラケットで囲む。
6. **長時間ジョブの出力を「全部か無か」にしない。** `--out` は 1 升ごとに
   `append`+`flush`+`fsync` に直した（旧版は最後に 1 回。実際に 1.5 時間分が消えかけた）。
7. **`--out` は絶対パスで渡す。** ジョブの cwd がリポジトリ外だと落ち先が消える。

---

## 6.1 並行セッションの成果と、突き合わせるべき一致（**最重要**）

**同じ「族の二分法」を、別セッションが `docs/25_survey_family_dichotomy.md` で先へ進めている。**
向こうの確定事実（`CLAUDE.md` の現状節より）:

- **第3ジャンプ `i*=6`、`S̄min(7)=10`、`reach_cbt(p,0)=p−2` は `p=9` で崩壊**（`reach(9,0)=6`）
- **`e_sat(h) = 1,1,1,3,3`（`h=3..7`、全探索確定）**
- `reach_cbt(9,1) ≥ 7`、「`e=1` で `p−1`」は `p=7` で反証済み

> ### ⚠ 突き合わせるべき一致
>
> 向こうの **cbt の `e_sat(h) = 1,1,1,3,3`（h=3..7）** と、
> 私の **pyramid の `minE(pyr(h), P(pyr(h)))`**（h=2..7 で `0,1,1,1,3,3` → h=3..7 で `1,1,1,3,3`）は
> **完全に同じ数列**である。
>
> - 同じ量なのか（添字規約のずれ。向こうの文書は
>   「Královič Bt(h) ↔ 我々の cbt(h) の非free部 ↔ treedp の m=h−1」と 3 通りずれていると注意している）
> - それとも**異なる族に同じ数列が現れた**のか
>
> **どちらかで意味がまるで違う。次のセッションはここから始めるとよい。**
> 私は pyramid、向こうは cbt を測っているので、**後者なら族をまたぐ現象**として面白い。
> 私の値は `min_erasures_dag` の 0-1 BFS（`data/reach_families_findings.md` §3.2 の表）で、
> 向こうは商 BFS の全探索。**実装も独立**なので、一致は偶然ではない可能性が高い。

同様に、向こうの「`reach_cbt(p,0)=p−2` は `p=9` で崩壊」と、
私の「`R−P=1` は `h=7` で崩壊」（§2.2）も、**同じ崩れ方の別表現である可能性**がある。

## 6.2 分担（**重要**）

このリポジトリは**複数セッションが同時に触っている**。

- `scripts/exp03_reach_dag.py` / `tests/test_exp03_reach_dag.py` に、別セッションが
  族を 12 個追加した（`branch1`, `caterpillar`, `diamond3/4/5`, `diamond_sqrt`,
  `kary2/3/4`, `unbalanced1/2/3`）＋テスト 2 本。`data/e0_boundary.md` も向こうの成果。
- **監視側の問い 2（二分法の境界はどこか）を、向こうが同じエンジンで進めている。**
  私の反例（`fib`・帯幅3）と突き合わせると境界が早く決まるはず。
- 現在 **138 ファイルがステージ済み**（別セッションの準備中コミット）。**index に触らないこと。**
- 私は衝突回避のため、以後の編集を `data/reach_families_findings.md` と本ファイルに限定した。

---

## 7. 同セッションの他リポジトリ（別作業）

| リポジトリ | 内容 | 正本 |
|---|---|---|
| `yokoyama-lab/quantum-resource-bounds` | ICNC 2012 のゴミ最小化を**エネルギーと量子ビットへ換算** | `docs/resource-accounting-icnc2012-garbage.md`, `docs/garbage-measure-composition.md`（各々に検証スクリプト付き） |
| `yokoyama-lab/cslib-reversible-private` | ゴミの**合成代数**を Lean で機械証明（`sorry` 0、公理は既存と同じ） | `CslibReversible/Complexity/GarbageComposition.lean`（**別セッションが `e0d0f92` で取り込み済み**） |

こちらは `reach(p,e)` とは独立の作業。詳細は各ファイル冒頭に書いてある。

---

## 8. 次の作業候補（費用対効果順）

1. **§2.3 の中心的結論の紙証明を書く**（§4）。書けたら層2、その先で Lean。
   **これが唯一「定理になりうる」もの。**
2. **`cbt` を `-m 40` 以上で回し切る**（§3）。追記式なので途中で死んでも確定分は残る。
3. **並行セッションの `data/e0_boundary.md` と突き合わせる**（§6）。
   二分法の境界（`P` が伸びる/伸びない）を族の設計で確定させる。
4. `reach_fib(10,0)` を確認して A052955 の一致を 10 点にする（予測 47）。
5. **新規性の判定**: 本セッションの量（族ごとの `reach_F`、`minE`、`R−P` による補間）は
   **未調査**。`docs/22_known_facts_ledger.md` と `idea02_separation_onset.md`（`P` と `R` の分離）に
   当ててから。**`docs/24` は鎖の `reach(p,e)` の調査であって本件ではない。**

---

## 9. 再現手順

```bash
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
python3 tests/test_exp03_reach_dag.py            # 13/13 が前提
python3 scripts/exp03_reach_dag.py --selftest    # 鎖 480 点 + 定理 B2
# 族の掃引（--out は絶対パス・追記式）
~/.claude/bin/runcap -m 40 -t 21600 -- python3 scripts/exp03_reach_dag.py \
    --family cbt --pmin 2 --pmax 9 --emax 6 --kmax 7 --verbose \
    --out "$PWD/data/reach_cbt.csv"
python3 scripts/gen_reach_families.py --csv data/reach_*.csv
# ログしか残っていないとき（救出）
python3 scripts/reach_log_to_csv.py --family cbt --log run.log --out "$PWD/data/reach_cbt.csv"
```

**実行環境**: `<host>` は**メモリ 7GB のみ**（`runcap -m 40` は掛けられない）。
かつ現在は別セッションと共用（SCIP が動いていた）。重い族はローカル（61GB）へ。
**`<host>` の SCIP 10.0 は exact solve 非対応で VIPR 証明書を出せない**（監視側の実測）。
下界に証明ログを付けるなら DRAT（cadical+drat-trim）か VeriPB。
