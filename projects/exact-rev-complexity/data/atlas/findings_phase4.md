# アトラス Phase 4（3 層検証の被覆と、未計測コーパスへの拡張）の結果（2026-08-09）

生成:
- `python3 scripts/atlas_coverage.py`（131 行、111 秒）→ `data/atlas/coverage_l123.csv`
- `python3 scripts/atlas_extend.py --corpus both`（219 本、90 秒、最大メモリ 27 MB）
  → `data/atlas/atlas_corpus.csv`（219 行）・`data/atlas/atlas_corpus_arrays.csv`（427 行）

回帰テスト 4 件 pass（`tests/test_atlas_coverage.py`）。
層はすべて **層 3（機械実験）**。定理は主張しない（`docs/STATUS.md` の運用）。

対象の 2 コーパス:
- **reversible-algorithms**（`github.com/yokoyama-lab/reversible-algorithms`）— アルゴリズムを
  目的に集めた 131 本。本フェーズで**初計測**。
- **PyJanus fixtures**（`github.com/yokoyama-lab/PyJanus`）— 処理系のフィクスチャ 101 本。
  Phase 1 で 97 本として計測済み（改名あり、下記 0-1）。

## 0. 重複チェックで見つかった陳腐化 2 件

Phase 4 の着手前に「同じ実測が既に済んでいないか」を確認したところ、
**PyJanus fixtures 101 本の検証被覆マトリクス（11 列）が
`PyJanus/docs/corpus-coverage.md` に既存**だった（`tools/corpus_coverage.py` が
junitxml から生成）。作り直していない。L2 参照差分（40 アルゴリズム × 200 ケース × 3 シード）も
`tools/reftest.py` ＋ `.github/workflows/reftest.yml` で **CI ゲート済み**だったので、
新規に測らず CI 同条件で 1 回再現しただけである。

**空白だったのは reversible-algorithms 側の L2 対応表と L3 全体**で、そこだけを進めた。
その過程で次の 2 件の陳腐化が出た。

### 0-1. PyJanus の fixtures は全件が改名され、97 → 101 本になった

`gcd.ja` → `gcd_g.ja`、`injective_gcd.ja` → `gcd_c.ja` のように、
「終端にゴミが残るか否か」で `_g` / `_c` を付ける規約に変わり、`injective_` 接頭辞は廃止された。
**`data/atlas/atlas.csv` の `name` 列は、現在の木のどのファイルも指していない。**

JSSST レター（`~/dev/overleaf/2026_resource_atlas_letter/`）は題名からして「111 本」に
固定されており（`main.tex` L20 / L23 / L33）、PyJanus のコミットハッシュが本文に無い。
**投稿前にハッシュを 1 行足すのが安全**（原稿は本フェーズの対象外なので触っていない）。

### 0-2. `catalog.json` は 2 件で現状と食い違う

`build_catalog.py` の判定を独立に再実装して掃き直した結果、`by_design` 8 件の短絡差を除き、
2 件が実際には L1 を通らない。

| ファイル | catalog | 実測 | 理由 |
|---|---|---|---|
| `qsort/queue5e.j` | `reversible` | `validate_err` | 53 行 `uncall pushpush_front(...)`、その手続きは存在しない（`push_front` の重複打鍵） |
| `rank/rank.j` | `reversible` | `validate_err` | 164 行 `uncall unrank(...)`、その手続きは存在しない |

コーパス側の git は clean なので、**PyJanus の validator が `uncall` の呼び先まで見るよう
厳しくなった**結果である。CI の catalog ジョブは次の push で落ちる。
どちらも「到達しないコード中の未定義手続き呼び出し」で、
原稿 A（`2027_reversible_corpus`）§6 のバグ分類に 1 類として足せる。

## 1. 3 層検証の被覆（`coverage_l123.csv`）

L1 を通る 118 本について:

| カテゴリ | L1 可逆 | L2 登録 | L3 検証済みインタプリタ | L3 C++ 生成 |
|---|--:|--:|--:|--:|
| Sorting | 45 | 10 | 32 | 44 |
| Searching | 24 | 2 | 24 | 24 |
| Permutation/ranking | 13 | 4 | 4 | 12 |
| Graph | 11 | 8 | 7 | 11 |
| Data structure | 10 | 4 | 3 | 8 |
| Combinatorics/Numeric | 6 | 2 | 4 | 5 |
| Dynamic programming | 4 | 4 | 4 | 4 |
| Numeric | 3 | 3 | 2 | 3 |
| Geometry | 2 | 2 | 2 | 2 |
| **計** | **118** | **39** | **82** | **113** |

1. **L2 の穴が最大。118 本中 79 本（67%）が参照差分に未登録。** 登録は 39 ファイル・
   40 アルゴリズム（`avl/avl_insert.j` が 2 つに使われるので 1 ずれる）。偏りも大きい
   （Searching 24 本中 2 本、Sorting 45 本中 10 本）。
   **原稿 A の中心テーゼを支えるのは L2 なので、ここが最も薄い。**
2. **L3 は本フェーズ以前は 0 本**だった（処理系横断差分は PyJanus のリポジトリ内でしか
   走っていなかった）。118 本すべてに当てて 82 / 113 本まで到達させた。
3. **3 層すべてに通るのは 24 本（20%）のみ。L1 だけのものが 21 本ある。**

### L3 が走らなかった 36 本の理由（沈黙にしない）

| 理由 | 本数 |
|---|--:|
| 局所変数つき自己再帰（抽出コアにフレームスタックが無い） | 24 |
| 定数でない次元の局所配列 | 4 |
| 未対応の文 | 3 |
| `*=` | 2 |
| **ハーネスが `Unsupported` を投げずに素の例外で落ちた** | **3** |

ここまでは表現力の限界だが、最後の 3 件は PyJanus 側の堅牢性の欠陥である
（`minheap_GPC2018.j`・`minheap_Nohr2015.j` が `TypeError: 'NoneType' object is not
subscriptable`、`isort/code/isort2.j` が `KeyError: 'lval'`）。

## 2. 新規に見つかった 3 件の欠陥（L1 も L2 も通るのに L3 で落ちる）

`codegen_diff.py` の契約では CFAIL は skip ではなく失敗。
PyJanus 自身の 101 本では出ないものが 3 件出た。互いに別の類である。

| ファイル | g++ | 正体 |
|---|---|---|
| `perm/code/perm2decfac_nolex.j` | `'make_p' was not declared in this scope` | **識別子中のプライム `'` を全くエスケープしていない**。生成物は `void make_p'(int* p, int* p', int& n)` という不正な C++ |
| `others/examples/factorization.j` | `candidate 2: 'void div(int&, int&)'` | 手続き名 `div` が C 標準ライブラリの `div` と衝突。既知の `delete` 予約語衝突と同型だが**ライブラリ名との衝突** |
| `isort/code/isort2.j` | `lvalue required as left operand of assignment` | **配列要素どうしの交換 `a[i] <=> a[i+1]`** が左辺値でない形で出力される |

再現:

```bash
cd <local>/dev/github.com/yokoyama-lab/PyJanus
PYTHONPATH=$PWD python3 coq/harness/codegen_diff.py \
  <local>/dev/github.com/yokoyama-lab/reversible-algorithms/perm/code/perm2decfac_nolex.j
PYTHONPATH=$PWD python3 -m jana_py.cli --std jana2014 -c \
  <local>/dev/github.com/yokoyama-lab/reversible-algorithms/perm/code/perm2decfac_nolex.j | sed -n '19p'
```

## 3. L2 の実測

```bash
for s in 1 42 99; do PYJANUS=… python3 tools/reftest.py --cases 200 --seed $s; done
```

3 シードとも **40/40 が 200 ケース全一致**。事前条件で捨てたケースは 19・21・24 件。
**現時点で L2 の失敗は無い。** 原稿 A §6 の AVL delete / shell sort のバグ事例はすべて
修正済みの過去の記録であり、「いま落ちているもの」ではないと読めるよう書く必要がある。

## 4. 資源ベクトル（未計測分を埋めた）

失敗 0 本。

| 指標 | reversible-algorithms（118、**初計測**） | PyJanus fixtures（101、うち 13 本が新規） |
|---|---|---|
| `steps` min / 中央値 / max | 10 / **146** / 1,926（`apsp.j`） | 4 / 85 / 11,846（`bwt_plain_c.ja`） |
| `stack_peak` 中央値 | **6** | **0** |
| **スタックを使う本数** | **69/118（58%）** | 32/101（32%） |
| `final_live_bits` 中央値 | **38** | 21 |
| `call_depth_peak` max | 9（`stackPermut.j`） | 8（`ackermann_c.ja`） |
| 終端で全状態がゼロ | **0 本** | **0 本** |

**最も効く発見**: レターが報告する「111 本中 36 本（32%）がスタックを使う」は、
**母集団が処理系のフィクスチャであることの反映**だった。アルゴリズムを目的に集めた
コーパスでは **58%（69/118）**、中央値も 0 ではなく 6 である。
「可逆化の代償はスタックへ移る」という主張はアルゴリズム集で測るほうが強く出る。
レターの数字は誤りではないが、**母集団依存を限界として書くべき**である。

一方、**終端で全状態がゼロのプログラムは、独立な 2 コーパス 219 本のどこにも無い**
（Phase 1 の 0/111 が 0/219 で再現）。配列の「書きっぱなし」も再現した
（take を一度もしない配列は 141/240＝59% と 121/177＝68%、終端で空は 25/240＝10% と
23/177＝13%。Phase 1 は 65%・13%）。

## 5. 2 実装照合

- 実装 A: `scripts/atlas_measure.py`（`Runtime` 継承、`id(cell)` でデデュープする自作トレーサ）
- 実装 B: PyJanus 純正 `python3 -m jana_py.cli --profile`（`jana_py/pebble.py`。共有コード無し）

共通定義のある `steps` と `call_depth` で照合 → **219/219 本で一致。不一致 0 本。**

**改名をまたいだ再現**も取れた。`steps`・`stack_peak`・`final_live_bits`・`call_depth_peak`
の 4 値が **97/97 完全一致**。

> **2026-08-09 訂正**: 初版はここを「名寄せできた 87 本で 87/87」と書いていた。
> 名前から `_g` / `_c` を推測する名寄せだったため、**改名で入れ替わった対**
> （`gcd` ↔ `injective_gcd`）を落として 87 本に減っていた。PyJanus の git の
> **改名記録**から対応表を作り直すと 97 本すべてが対応づき、4 値とも一致する。
> レター（`~/dev/overleaf/2026_resource_atlas_letter/`）には再導出できる 97/97 を書いた。
> **名前の規約から対応を推測しない**——改名記録が正本である。

### 照合の途中で踏んだ偽陰性 1 件

`differentialar` は `python3 -m jana_py.cli` に shell out するので、
**PYTHONPATH を通し忘れると全数が `skip`**（＝「検査していない」が「異常なし」に化ける）になる。
`scripts/atlas_coverage.py` の `_pyjanus_on_path()` で恒久対応し、回帰テストに固定した。

## 6. 限界と残った未解決点

1. **`stack_peak`・`final_live_bits` は依然 1 実装のみ**（PyJanus 純正側に対応する定義が無い）。
   Phase 1 からの持ち越しの限界。
2. **L3 の PASS は固定入力 1 本での store 一致**であり、L2 のような乱択反復ではない。
3. L2 の被覆率 33% は「登録の有無」であって、未登録 79 本が誤っているという意味ではない
   （オラクル未執筆）。
4. PyJanus 側の欠陥 6 件（CFAIL 3・例外漏れ 3）は**修正していない**
   （読み取り専用、並行セッションの可能性）。issue 化が必要。
5. `catalog.json` の 2 件（`queue5e.j`・`rank.j`）は、直すか `by_design` に落とすかの判断が要る。
6. 固定入力なので規模比較はできない（Phase 2 のスケーリングは 9 族のみ）。

**次に効く順**: (1) L2 の穴を埋める（Searching 24→2、Sorting 45→10 は参照実装が容易）、
(2) PyJanus へ issue 2 本、(3) `catalog.json` 再生成の方針決め、
(4) レターに PyJanus のコミットハッシュ 1 行。
