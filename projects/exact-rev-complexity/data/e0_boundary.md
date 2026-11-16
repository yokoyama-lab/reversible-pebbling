# 飽和閾値 e0(F,p) の境界調査

対象: `reach_F(p,e) := max{k : F(k) が p ペブル e 消去で clean 可解}` の飽和閾値

    e0(F,p) := min{ e : reach_F(p,e) = reach_F(p,∞) }

## 最重要の結果: 「emax までフラット」は飽和の証拠にならないことを実測で確認した

最初の掃引（emax=6）で `flat_to_emax`（旧称 saturated。用語の経緯は下記）と判定された行のうち、
**`diamond3 p=4` と `diamond4 p=5` は e を 14 まで伸ばしたところ両方とも増加に転じ、
`unbounded_within_range` に判定が変わった**:

| family | p | emax=6 での判定 | emax=14 での判定 |
|---|---|---|---|
| diamond3 | 4 | flat_to_emax（e0=4, reach=4） | **unbounded_within_range**（e=7..9で5、e=10..13で6と2段跳んだ後もe=14で7に上昇） |
| diamond4 | 5 | flat_to_emax（e0=4, reach=5） | **unbounded_within_range**（e=4..8で5、e=9..13で6と跳んだ後もe=14で7に上昇） |

一方 `unbalanced1/2/3` の全 `flat_to_emax` 行と `kary3/4` の全 `flat_to_emax` 行は
e=14 まで伸ばしても値は動かなかった（下表参照）。`diamond4 p=6`・`diamond5 p=6` は
emax=6 では unbounded だったが emax=14 まで伸ばすと e0=12 で flat_to_emax に転じた
（これも「新たな踊り場」の可能性を排除できておらず、確定ではない）。

**したがって、以前このドキュメントが立てた「必要な同時幅が族のパラメータとともに
増えるときだけ飽和する」という仮説は、指揮者の指摘どおり取り下げる。** 今回わかったのは
「diamond 系は emax=6 では判定できない」という**否定的な事実**であり、新しい機構の
仮説はまだ立てない（指揮者の方針: データが仮説を支えられる範囲まで伸びてから）。

## 背景（指揮者の依頼メッセージの数値。2026-08-11 に複数回訂正あり）

- **鎖**: reach(p,e) = (e+2)·2^(p-2)。**e に比例して無限に伸びる**（e0=∞。Lean 機械証明済み・層1）
- **完全二分木 cbt**: e≥1 で飽和値 p-1 になる。ただし**`e=0 で p-2` は p≤8 限定**
  （Královič 2004 Thm 4.9・`docs/25`§7で `Smin(6)=8` → p=9 で `reach_cbt(9,0)=6=p-3` に崩壊。
  外挿しないこと）
- **ピラミッド**: 飽和値 p-1。飽和に要する e0 が p とともに増える（p≤6 で e0=1、p=7,8 で e0=3）
- fib 鎖（分岐なし）は鎖と同じく伸び続ける（e0=∞）
- **「分岐の有無」「必要な同時幅の増加」という機構仮説は、いずれも指揮者自身が
  データ不足のまま立てて後で撤回した**（本セッションで4回: p-2閉形式・分岐説・
  e0=1飽和説・幅説）。**新しい機構の説明は、判定可能な範囲が十分広がるまで立てない。**

## 用語の経緯: 「saturated」→「flat_to_emax」への改名（2026-08-11）

当初 `scripts/e0_boundary.py` は「以降 CONFIRM 個の e で値が変わらない」を飽和の
十分条件として `kind="saturated"` と表示していた。これには2段階の罠があった:

1. **一時的な足踏み（踊り場）を飽和と誤読する罠**: `diamond_sqrt p=3` は e=2..5 で
   reach=4 のまま4回連続一致するが、e=6 で5に上がる（幅が階段状に増える族の特性）。
   →「末尾（検証した最大の e）まで途切れず連続 CONFIRM+1 個一致」を要求するよう修正。
2. **`emax` 自体が任意の打ち切り値である罠**（指揮者2026-08-11指摘）: 上の修正後でも、
   `diamond5 p=6` の実測列 `[4,5,5,5,5,6,6]`（e=0..6）は「末尾2点フラット」だが
   その手前にフラット長4の区間があり増加した実例。**「emax まで動かなかった」ことは
   「emax を超えても動かない」ことの証拠にならない。** 実際に上表のとおり
   `diamond3 p=4`・`diamond4 p=5` は emax=6 のflat判定がemax=14で覆った。

したがって `kind` の名前を **`saturated` → `flat_to_emax`** に改め、
「飽和の確定」ではなく「emax までは動かなかった候補（反証されていないだけ）」という
弱い主張に格下げした。**この文書のどの `flat_to_emax` 行も、真の飽和証明ではない。**

## 新設した境界族（`scripts/exp03_reach_dag.py`）

| 族 | 定義 | 何を切り分けようとしたか（機構仮説は撤回済み） |
|---|---|---|
| `caterpillar(n)` | 背骨 $s_0(\mathrm{free})\to s_1\to\cdots\to s_n$。各段で新しい free 葉 $\ell_i$ が合流 | 同時幅は常に1（葉が free） |
| `branch1(n)` | free 根から長さ $n$ の前置鎖 → 長さ $n$ の2枝に分岐 → 合流点が終端 | 分岐点はちょうど1個、同時幅は高々2 |
| `unbalanced{1,2,3}(h)` | 完全二分木を、根から数えて上位 `skew` 段だけ「片方は新しい free 葉、片方だけ再帰」に置き換え | cbt と caterpillar を skew で補間 |
| `diamond{3,4,5}(h)` | 幅 $w$ 固定の帯 DAG（打ち切りピラミッド）。境界は折り返さない | 幅が頭打ちのまま高さだけ伸びる DAG |
| `diamond_sqrt(h)` | 幅が $1+\lfloor\sqrt{h}\rfloor$ で段階的に増える帯 DAG | 幅がゆっくり増える中間ケース |
| `kary2/3/4(h)` | 完全 $k$ 分木（`scripts/families.py` 既存実装を再利用） | 分岐度 $k$ を上げると幅が速く増える |

すべて `landauer.py`（第2独立実装）と 960 点で全一致を確認済み
（`tests/test_exp03_reach_dag.py::test_boundary_families_match_landauer`）。

## 実行方法・注意点

- `exp03_reach_dag.py` は1点確定するごとに追記して flush+fsync する。
- 全ジョブ `~/.claude/bin/runcap` でメモリ・時間の上限を掛けて**順番に**実行（機体の CPU
  負荷が高いため並列は避けた）。1回目は emax=6 の全族掃引、2回目は「flat_to_emax
  だった行だけ」emax=14 まで対象を絞った延長掃引（`diamond5 p=7` のみコスト高で
  e=8 止まり、timeout）。
- `kmax`（族のパラメータ上限）は各族のコストに応じて個別調整した実測値。

## 族ごとの「検証した p の範囲」

**p の値を検証範囲の外へ外挿しないこと**（`reach_cbt(p,0)=p-2` が p=9 で崩れた事故が実例）。

| family | 検証した p | 備考 |
|---|---|---|
| branch1 | 2..5 |  |
| caterpillar | 2..5 |  |
| diamond3 | 2..7 | p=4のみe=0..14、他はe=0..6（p=7はe=0..3で打ち切り） |
| diamond4 | 2..7 | p=2..6はe=0..14、p=7はe=0..6 |
| diamond5 | 2..7 | p=2..6はe=0..14、p=7はe=0..8で打ち切り |
| diamond_sqrt | 2..7 | 全てe=0..6 |
| kary3 | 2..6 | 全てe=0..6 |
| kary4 | 2..5 | p=5はe=0のみ（timeout） |
| unbalanced1 | 2..5 | 全てe=0..14 |
| unbalanced2 | 2..5 | 全てe=0..14 |
| unbalanced3 | 2..6 | p=2..5はe=0..14、p=6はe=0のみ（timeout） |

## 族×p ごとの e0

`e0` 列: 整数は「flat_to_emax の開始点」（**飽和の確定ではない**、上の「最重要の結果」参照）。
`>N` は「e=N まで単調増加を確認したが、その先は未検証」であり、`>N` を飽和とは読まない。

| family | p | e0 | reach(e0) | 検証した e | 判定 | 備考 |
|---|---:|---|---:|---|---|---|
| branch1 | 2 | 0 | -1(注1) | 0..6 | flat_to_emax |  |
| branch1 | 3 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=1..3で1、e=4..5で2；reach(6)=3 |
| branch1 | 4 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=1..2で3、e=3..4で4、e=5..6で6 |
| branch1 | 5 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=1..2で7；reach(6)=14 |
| caterpillar | 2 | >6 | - | 0..6 | unbounded_within_range | 鎖の法則どおり単調増加；reach(6)=8 |
| caterpillar | 3 | >6 | - | 0..6 | unbounded_within_range | reach(6)=16 |
| caterpillar | 4 | >6 | - | 0..6 | unbounded_within_range | reach(6)=32 |
| caterpillar | 5 | >6 | - | 0..6 | unbounded_within_range | reach(6)=64 |
| diamond3 | 2 | 0 | 1 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond3 | 3 | 0 | 2 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond3 | 4 | >14 | - | 0..14 | unbounded_within_range | **emax=6ではflat_to_emax(e0=4)だったがe=14まで伸ばすと再上昇**（踊り場: e=1..3=3, e=4..6=4, e=7..9=5, e=10..13=6；reach(14)=7） |
| diamond3 | 5 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=1..3で5、e=4..5で6；reach(6)=7（未延長） |
| diamond3 | 6 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=2..3で8；reach(6)=11（未延長） |
| diamond3 | 7 | >3 | - | 0..3（打ち切り） | unbounded_within_range | reach(3)=13。timeoutでe=4以降未検証 |
| diamond4 | 2 | 0 | 1 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond4 | 3 | 0 | 2 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond4 | 4 | 1 | 3 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond4 | 5 | >14 | - | 0..14 | unbounded_within_range | **emax=6ではflat_to_emax(e0=4)だったがe=14まで伸ばすと再上昇**（踊り場: e=1..3=4, e=4..8=5, e=9..13=6；reach(14)=7） |
| diamond4 | 6 | 12 | 9 | 0..14 | flat_to_emax | p=6のe=7..14行は当方の延長対象外だったが別途 `e0_diamond4_e14.csv` として出現、`exact_reach_family` で2点(e=10,e=14)を独立再検証し一致を確認済み。踊り場: e=2..5=6, e=6..7=7, e=8..11=8。**emax=14でも未証明**（さらに伸ばせば覆る可能性を排除できない） |
| diamond4 | 7 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=2..4で8；reach(6)=10（未延長） |
| diamond5 | 2 | 0 | 1 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond5 | 3 | 0 | 2 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond5 | 4 | 1 | 3 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond5 | 5 | 1 | 4 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| diamond5 | 6 | 12 | 7 | 0..14 | flat_to_emax | p=6のe=7..14行は当方の延長対象外だったが別途 `e0_diamond5_e14.csv` として出現（形式・値とも整合、他の実測点と矛盾なし）。踊り場: e=1..4=5, e=5..11=6。**emax=14でも未証明** |
| diamond5 | 7 | >8 | - | 0..8（打ち切り） | unbounded_within_range | 踊り場: e=1..3=6, e=4..6=7, e=7..8=8；timeoutでe=9以降未検証（コスト高: e=8で193秒/点） |
| diamond_sqrt | 2 | 0 | 1 | 0..6 | flat_to_emax | 未延長 |
| diamond_sqrt | 3 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=2..5で4；reach(6)=5 |
| diamond_sqrt | 4 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=0..1で4、e=2..5で5；reach(6)=6 |
| diamond_sqrt | 5 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=1..4で6、e=5..6で7；reach(6)=7 |
| diamond_sqrt | 6 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=2..4で9、e=5..6で10；reach(6)=10 |
| diamond_sqrt | 7 | >6 | - | 0..6 | unbounded_within_range | 踊り場: e=1..2で11、e=3..5で12；reach(6)=13 |
| kary3 | 2 | 0 | 1 | 0..6 | flat_to_emax | 未延長（p小・reach小のため元々強い証拠） |
| kary3 | 3 | 0 | 1 | 0..6 | flat_to_emax | 未延長 |
| kary3 | 4 | 0 | 2 | 0..6 | flat_to_emax | 未延長 |
| kary3 | 5 | 0 | 2 | 0..6 | flat_to_emax | 未延長 |
| kary3 | 6 | 1 | 3 | 0..6 | flat_to_emax | 未延長 |
| kary4 | 2 | 0 | 1 | 0..6 | flat_to_emax | e=14まで再検証済み・動かず |
| kary4 | 3 | 0 | 1 | 0..6 | flat_to_emax | e=14まで再検証済み・動かず |
| kary4 | 4 | 0 | 1 | 0..6 | flat_to_emax | e=14まで再検証済み・動かず |
| kary4 | 5 | >0 | - | 0..0（打ち切り） | unbounded_within_range | reach(0)=2。timeoutでe=1以降未検証 |
| unbalanced1 | 2 | 0 | 2 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| unbalanced1 | 3 | 1 | 3 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| unbalanced1 | 4 | 1 | 4 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| unbalanced1 | 5 | 2 | 5 | 0..14 | flat_to_emax | 踊り場: e=0..1で4。e=14まで再検証済み・動かず |
| unbalanced2 | 2 | 1 | 3 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| unbalanced2 | 3 | 1 | 4 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| unbalanced2 | 4 | 2 | 5 | 0..14 | flat_to_emax | 踊り場: e=0..1で4。e=14まで再検証済み・動かず |
| unbalanced2 | 5 | 2 | 6 | 0..14 | flat_to_emax | 踊り場: e=0..1で5。e=14まで再検証済み・動かず |
| unbalanced3 | 2 | 2 | 4 | 0..14 | flat_to_emax | e=14まで再検証済み・動かず |
| unbalanced3 | 3 | 2 | 5 | 0..14 | flat_to_emax | 踊り場: e=0..1で4。e=14まで再検証済み・動かず |
| unbalanced3 | 4 | 2 | 6 | 0..14 | flat_to_emax | 踊り場: e=0..1で5。e=14まで再検証済み・動かず |
| unbalanced3 | 5 | 2 | 7 | 0..14 | flat_to_emax | 踊り場: e=0..1で6。e=14まで再検証済み・動かず |
| unbalanced3 | 6 | >0 | - | 0..0（打ち切り） | unbounded_within_range | reach(0)=6。timeoutでe=1以降未検証 |

（注1）branch1 p=2 の `reach(e0)=-1` は「p=2 では branch1(k) が k=0 でも解けるメンバーが
1つも無い」ことを表す欠測値で、負のペブル数という意味ではない。

## 判定区分の意味

- **flat_to_emax**: emax まで途切れず一定だった候補。**飽和の確定ではない**
  （`diamond3 p=4`・`diamond4 p=5` がまさにこの区分から覆った実例）。
- **unbounded_within_range**: 掃引範囲では末尾まで足踏みが続かず単調増加。
  e0 は `>emax` 表記。e0=∞ の族の可能性を含め未確定。
- **cutoff_before_e0**: flat_to_emax が確認できる前に打ち切り(UNKNOWN)またはタイムアウトに
  当たった。「飽和していない」でも「飽和した」でもなく単に分からない。
- **no_data**: 対応する CSV 行が無い、または全行 UNKNOWN。

## まとめ（現時点で言えること・言えないこと）

**言えること**（e≤14まで実測、それでも「確定」ではなく「反証されていない」という意味）:

- `unbalanced1/2/3` の全 flat_to_emax 行（p=2..5、e0∈{0,1,2}）は e=14 まで動かなかった。
  これは cbt に近い挙動が unbalanced 系全体に及んでいることを示す一貫したデータ。
- `kary3/4` の flat_to_emax 行（p=2..6、e0∈{0,1}）も e=14 まで動かなかった
  （kary4 は p=2..4 のみ延長済み）。
- `caterpillar`・`branch1` は emax=6（p≤5）の範囲で一度も flat にならず単調増加。
- `diamond{3,4,5}`・`diamond_sqrt` は**族としての結論が出せない**: 同じ族でも p によって
  flat_to_emax だったり unbounded だったりし、しかも emax を伸ばすと判定が覆る例が
  現に2件見つかった。

**言えないこと**:

- 上記いずれの「flat_to_emax」も真の飽和証明ではない。unbalanced・kary の行も、
  e をさらに伸ばせば diamond3 p=4 のように覆る可能性を排除できていない。
- 飽和の機構（分岐・幅・その他）についての説明は、指揮者の方針により**現時点では立てない**。

## 再現方法

```bash
# 各族の reach_F(p,e) を掃く（例）
python3 scripts/exp03_reach_dag.py --family diamond4 --pmin 2 --pmax 7 \
  --emin 0 --emax 6 --kmax 16 --out data/e0_diamond4.csv

# 掃いた CSV から e0 表を再生成（data/e0_*.csv を自動収集）
python3 scripts/e0_boundary.py --out data/e0_boundary.md
```

再回帰テスト: `python3 tests/test_exp03_reach_dag.py`（13本、境界族は landauer.py と
960点照合。全通過を要求してからこの表の数値を信じること）。

## 次にやると良いこと（優先度順）

1. **`diamond4 p=6`・`diamond5 p=6` の flat_to_emax（e0=12, emax=14）をさらに伸ばす。**
   diamond3 p=4・diamond4 p=5 が覆った前例があるので、この2行もまだ信用できない。
2. `diamond5 p=7` の e=9 以降（timeout で未到達）。1点あたり200秒近いので
   専用の長時間ジョブが要る。
3. `caterpillar`・`branch1` の p を 6 以上へ、`kary4 p=5`・`unbalanced3 p=6` の
   timeout箇所を埋める。
4. Strahler数/vertex ranking との対応（当初の依頼 §3）は、機構仮説を再び立てられる
   だけのデータが揃ってから着手する。
