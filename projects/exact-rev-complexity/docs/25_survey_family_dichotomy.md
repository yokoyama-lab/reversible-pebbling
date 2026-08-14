# サーベイ: 族二分法（木では消去階層が有限で潰れる）の既知性（2026-08-10）

**このファイルの目的**: 同じ調査を二度やらないため。`reach_F(p,e)` の族依存性
（鎖 vs 木・ピラミッド）の新規性を論じる前に**まずここを読むこと**。
前提となる鎖側・BTV 系の調査は `docs/24_survey_reach_pe.md`（済み）。

対象の主張（2026-08-10 発見・小域で数値検証済み）:
鎖は `reach(p,e) = (e+2)·2^{p-2}`（e で無限に伸びる）、cbt・ピラミッドは
有限の e で飽和し飽和値は p−1（= 標準ペブリング）。

---

## 0. 結論（3 行）

1. **「木 × 消去予算」の交差はどこにも見つからない**（Královič 被引用 10 件・BTV 被引用
   22 件〔docs/24〕・spooky 系 3 本・標準ペブリング側の検索、いずれも該当なし）。
   **二分法そのもの（分岐の有無で消去の効きが質的に変わる）を述べた文献も見つからない**
2. **ただし e=0 の端点は既知で、しかも我々の「p−2」と矛盾する。**
   Královič 2004 が cbt の可逆ペブル空間を **h + Θ(lg\* h)** で tight に決めており
   （本文 Thm 4.9・逐語確認）、彼の厳密機構＋我々の検証値から
   **「reach_cbt(p,0) = p−2」は p=9 でちょうど崩壊する**（§3.1 で区間 [9,21] を導出し、
   §7 の計算で下端に確定。reach(9,0) = 6）
3. **「可逆と不可逆のギャップは 1 ペブル」も一般には偽**（ギャップは Θ(lg\* h) で非有界）。
   飽和に要する消去数も定数でない: **e_sat(h) = 1,1,1,3,3（h=3..7、§8.4 で全探索確定）**。
   ピラミッドと同型の曲線であり、二分法は「鎖 vs 分岐」に純化された。
   **成長則（なぜ 2 を飛ぶか・次はいつ跳ぶか）が本当の新規領域**である

---

## 1. 一次情報（本文 PDF / LaTeX で確認済み）

### Královič 2004 — **cbt の e=0 側はここで解決済み（消去は無い）**

- `Time and space complexity of reversible pebbling`, RAIRO-ITA 38 (2004) 137–161
- Paperpile: `All Papers/K/Královič 2004 - Time and space complexity of reversible pebbling.pdf`
- 対象トポロジ: **鎖・完全二分木・バタフライ**（ピラミッドは無い）

**定義（本文 §2・§4、逐語で確認）**:

- R1/R2: 置くのも外すのも「全直前者にペブルが載っているとき」のみ。**消去は存在しない**
- **semicomplete computation** = 空配置から「根のみペブル」への計算（Def 4.1）。
  **これは我々の clean 到達そのもの**。その最小ペブル数が S̄min(h)
- 彼の Bt(1) は 1 頂点（**我々の cbt(0)**）。**葉もペブルを消費する**（free ではない）。
  ただし我々の cbt(h) の非 free 部分（葉を除いた 2^h−1 頂点）は彼の Bt(h) と**遷移系ごと同型**
  （葉の直前者条件が空 ⟷ 我々の free 葉が常時可用）。
  **したがって我々の pmin(cbt(h)) = 彼の S̄min(h)**。実測一致:
  pmin(cbt(3))=5=S̄min(3), pmin(cbt(4))=6, treedp の pmin_tree(4)=7=S̄min(5),
  pmin_tree(5)=8=S̄min(6)

**主要結果（逐語。⚠ 2026-08-10 同日訂正: Lemma 4.2 の bar 割り当てを §7 の方法で確定）**:

> **Lemma 4.2.** Smin(h) + 1 ≥ S̄min(h) ≥ Smin(h).（**semicomplete は complete 以上・高々 +1**。
> 初稿は逆に書いていた。`-raw` テキストでは overbar つき S̄ が「S␤min」と改行で出るため
> 機械的に区別でき、証明文の不等式の向きとも一致する）
> **Lemma 4.3.** S̄min(h + 1) = Smin(h) + 2.
> **Corollary 4.4.** S̄min(h) equals to h plus the number of different numbers i such
> that i < h and Smin(i) = S̄min(i).
> **Lemma 4.6.** h2 − h1 ≤ 2^{h1+p+1}.  **Lemma 4.7.** h2 − h1 ≥ 2^{h1+p−2}.
> （h1 = S̄min^{-1}(p), h2 = S̄min^{-1}(p+1)）
> **Lemma 4.8.** 2^{S̄min^{-1}(p)} ≤ S̄min^{-1}(p+1) ≤ 2^{3·S̄min^{-1}(p)}（p ≥ 2）
> **Theorem 4.9.** Smin(h) = h + Θ(lg∗(h)).

（pdftotext は S̄ の overbar を落とす。上の S̄/S の割り当ては証明本文から復元した。
Lemma 4.3 は「semicomplete(h+1) = complete(h) + 2」である）

標準ペブリングの木の値は同論文が引用（p.139、逐語）:

> As proven in [7], minimal space complexity for standard pebble game on a
> complete binary tree of height h is h + 1.

[7] = **Paterson–Hewitt, Comparative Schematology (1970)**。原典は未読（§5）。

### Komarath–Sarma–Sawlani (arXiv 1604.05510) — **木の可逆ペブル数の特徴づけ（消去なし）**

⚠ 依頼文の「Komarath–Sarma–Sunil」は誤り。**第三著者は Saurabh Sawlani**（要 bib 訂正）。

アブストラクト確認（本文 PDF は未読・§5）:

> for any rooted directed tree T, its reversible pebble game number is always
> **just one more than the edge rank coloring number** of the underlying undirected tree

- 木の可逆ペブル数は**多項式時間で計算可能**（一般 DAG は PSPACE 困難）
- **Chan (2013)**: 可逆ペブル数 = Dymond–Tompa 数 = Raz–McKenzie 数（single-sink DAG）
- cbt の陽な閉形式は与えていない。時間側は n^{O(log log n)} 手
- **消去・予算の概念は無い**

### spooky pebble game 系 3 本 — **測定は非有界。予算モデルではない**

| 論文 | 対象 | 測定の扱い |
|---|---|---|
| Kornerup–Sadun–Soloveichik (2110.08973, Quantum 2025) | **鎖 tight**・二分木（最小ペブル戦略）・一般 DAG（近似も PSPACE 困難） | **非有界**。qubit を classical bit に移す「借金」で、終端までに返す |
| Quist–Laarman (2401.10579) | 一般回路・SAT ソルバによる求解 | 同上（有界なのはペブル数） |
| Kahanamoku-Meyer–Ragavan–Van Kirk (2510.08432) | 鎖のみ（並列 spooky） | 同上 |

**「reset を k 回だけ許す」型の予算化は 3 本とも無い。** また spooky の測定は
恒久廃棄（我々の消去）ではなく位相誤差つきの一時退避であり、モデルとして別物
（docs/24 §2 の判定を維持）。

### 前方引用の追跡

- **Královič 2004 の被引用（OpenAlex, W1976150152）: 10 件全確認**。証明複雑性
  （Chan 2013, Chan–Lauria–Nordström–Vinyals 2015, resolution-space 2 本, Nullstellensatz）、
  量子算術回路（Toom, Karatsuba）、総説のみ。**木 × 消去は皆無**
- Semantic Scholar は本日 **2 連続 429**（健全性チェックの BTV クエリ自体が 429 になったため
  「0 件」誤読は無し）。OpenAlex に切替（[[api-error-parsed-as-zero-hits]] の型）
- BTV 1997 の被引用 22 件は **docs/24 §8 で全数確認済み**（clean × 消去は無い）

---

## 2. 主張ごとの判定表

| 主張 | 判定 | 層 |
|---|---|---|
| 消去予算モデル（鎖・τ 側） | **既知**（BTV 1997 / LTV 1998。docs/24） | 本文確認 |
| **cbt の e=0（可逆ペブル空間）** | **既知**: S̄min(h) = h + Θ(lg\* h) tight（Královič Thm 4.9）。特徴づけは Cor 4.4、多項式時間計算は Komarath | 本文確認（Komarath はアブストのみ） |
| **我々の「reach_cbt(p,0) = p−2（p≥4）」** | **p ≤ 8 でのみ正。p = 9 でちょうど崩壊**（§7 で計算により確定。reach(9,0) = 6） | 本文確認＋計算 |
| ピラミッドの e=0（可逆） | **見つからず**（Královič は扱わず、Komarath は木のみ、DT/RM 同値経由でも陽な値は見つからず）＝無い証明ではない | 検索のみ |
| **「木 × 消去予算」の交差・二分法** | **見つからず**（§1 の全経路） | 検索のみ |
| 飽和値 = 標準ペブル数（e=∞ 極限） | 定義から従う（e 無制限の可逆 = 標準）。標準側の h+1 は Paterson–Hewitt 1970 | 二次情報（Královič の引用文） |
| 「可逆と不可逆のギャップ = 1 ペブル」（一般） | **偽**（ギャップは cbt で Θ(lg\* h)、鎖でも非有界）。「検証域でギャップ 1」に限定して正 | 本文確認 |
| 量子側の「測定 k 回」予算 | **見つからず**（spooky 3 本とも非有界） | アブスト＋一部本文 |

---

## 3. 我々の主張への影響（このサーベイの本体）

### 3.1 「p−2」は検証域のすぐ外で必ず崩れる（導出）

Cor 4.4 より S̄min(h) = h + #{i < h : Smin(i) = S̄min(i)}（「ジャンプ」の個数）。
検証値 S̄min(1)=1, S̄min(2)=3, S̄min(3..6)=h+2 から、ジャンプは i=1,2 の 2 回で
i=3,4,5 には無い。第 3 ジャンプの高さ i\* について:

- 下から: 検証値より **i\* ≥ 6**
- 上から: Lemma 4.6（p=1, h1=S̄min^{-1}(1)=2）より S̄min^{-1}(2) ≤ 2 + 2^4 = **18**、
  ゆえに i\* ≤ 18

reach_cbt(p,0) = p−2 ⟺ S̄min(p−2) = p は p−2 ≤ i\* の間だけ成立。したがって
**崩れる最初の p は i\*+3 ∈ [9, 21]**。我々の直接計算は p ≤ 8（h ≤ 6）で止まっており、
**「4 点の当てはめが h=5 で崩れた」exp01 の型がここでも起きる**寸前だった。

→ ~~次の一手: `pmin_tree(6)` の直接計算~~ **→ §7 で決着済み**（直接計算はメモリで
詰み、Lemma 4.3 で complete 側に帰着して 13 秒。i\* = 6、崩壊点は p=9）。

### 3.2 生き残る新規性（絞った形）

1. **「木 × 消去予算」の交差そのもの**（reach_F(p,e) の e>0 側）は空白のまま
2. ただし主張の正しい形は「e=0 で p−2 / e≥1 で p−1」ではなく:
   **「消去 e 回は Královič のジャンプを何段消せるか」**。~~検証域では e=1 で全段消えた~~
   **→ §8.4 で訂正: e=1 が標準値まで届くのは h ≤ 5 のみ**（h=6 では 1 ペブルも
   買えないことを全探索で確定）。必要消去数の成長則が真の問い——文献に無い
3. ピラミッドは e=0 側から空白（ただし §5 の未読分を先に潰すこと）
4. 「飽和までの e が p とともに増える」（pyramid: p≤6 で 1、p=7,8 で 3）は
   上の 2 の実データであり、既知の何とも重ならない

### 3.3 用語の注意（執筆時の事故防止）

- 高さ規約: **Královič Bt(h) = 我々の cbt(h) の非 free 部分**（彼の Bt(1)=1 頂点）。
  treedp の m は **我々の cbt(m+1)**。3 つの規約が全部ずれている
- 「可逆ペブル数」を引くときは semicomplete（S̄min ＝ 我々の clean）か
  complete（Smin）かを毎回明示する（差は高々 1: Lemma 4.2）

---

## 4. 使った検索経路（見つからなかったことの範囲を示す）

- Královič 被引用 10 件（OpenAlex）・BTV 被引用 22 件（docs/24・S2）
- WebSearch: `pebble game "limited erasures"/"erasure budget"/"few deletions" reversible tree`、
  `"partially reversible"/"semi-reversible" pebbling`、`"Dymond-Tompa"/"Raz-McKenzie" pyramid` —
  いずれも LTV/BTV 系・spooky 系・証明複雑性系しか出ない
- spooky 3 本の本文/アブスト（§1）

---

## 5. まだやっていないこと（正直に）

- **Komarath–Sarma–Sawlani の本文 PDF 精読**（アブストのみ。edge rank coloring の
  cbt での値、彼らの木の規約（葉のコスト・根の向き）は未確認）
- **edge ranking 文献側**から cbt の厳密値（小さい h の表）が既に出ていないか
- **Paterson–Hewitt 1970 の原典**（標準 h+1 は Královič の引用文経由）
- **ピラミッドの標準ペブリング数の原典**（Cook 1974 / Klawe 系。飽和値の照合先）
- **Komarath / Chan / LTV 1998 の前方引用**（S2 が 429。OpenAlex では Komarath の
  journal 版の被引用 0 件表示＝過小の可能性が高く、S2 復帰後に再試行すべき）
- Královič **§4.2（バタフライ）**と**博士論文**（同 Paperpile ディレクトリ）の読了
- **「見つからず」は無い証明ではない**。特に量子回路合成の実務側
  （uncomputation with bounded resets）はキーワードが揺れており取りこぼしうる

---

## 6. 再現用コマンド

```sh
# 一次資料
rclone copy "gdrive:Paperpile/All Papers/K/Královič 2004 - Time and space complexity of reversible pebbling.pdf" /tmp/survey/
pdftotext -layout k.pdf k_layout.txt && pdftotext -raw k.pdf k_raw.txt  # 両方で読む（overbar 消失に注意）

# 前方引用（S2 429 時の代替）
curl -s "https://api.openalex.org/works?filter=doi:10.1051/ita:2004008&select=id,cited_by_count"
curl -s "https://api.openalex.org/works?filter=cites:W1976150152&select=title,publication_year,doi&per-page=25"

# 検証値との突き合わせ（本リポジトリ）
.venv/bin/python -c "import sys; sys.path.insert(0,'scripts'); from treedp import pmin_tree; print([pmin_tree(m) for m in range(1,6)])"
# → [3, 5, 6, 7, 8] = S̄min(2..6)。次の一手は pmin_tree(6)
```

---

## 7. 第3ジャンプの確定（2026-08-10 追記）— **i\* = 6、「p−2」は p=9 で崩壊**

§3.1 の宿題を `scripts/treedp_complete.py` で消化した。**高さ 7 の直接計算は
メモリで詰む**（`pmin_tree(6)` は _SHIFT=36 でも 10分45秒・19.5GB 時点で増加中）が、
**Lemma 4.3（S̄min(h+1) = Smin(h) + 2）で高さ 6 の complete 側に帰着すると
13 秒・376 MB で決着**した。

### 7.1 定義の確定（bar 割り当ての機械的判別）

pdftotext は overbar を落とすが、**`-raw` では S̄ が「S␤min」（改行入り）、
S が「Smin」（連続）に出る**ため機械的に区別できる。これで

- **Lemma 4.2**: `Smin(h)+1 ≥ S̄min(h) ≥ Smin(h)`（complete ≤ semicomplete ≤ complete+1）
- **Lemma 4.3**: `S̄min(h+1) = Smin(h) + 2`
- **Cor 4.4** の LHS は S̄min、ジャンプ条件は `Smin(i) = S̄min(i)`

と確定（初稿 §1 は Lemma 4.2 が逆。同日訂正済み）。検算: 実測
S̄min(2..6)=[3,5,6,7,8] に Lemma 4.3 を当てると Smin(1..5)=[1,3,4,5,6] が導出され、
Lemma 4.2 の挟み撃ち・Cor 4.4 の再帰と完全整合。なお Lemma 4.2 証明文の
「we obtain a semicomplete computation」（2 回目）は complete の誤植と判断
（不等式の向きから一意）。

### 7.2 complete 側への帰着

Královič §2 の定義（空→空・全頂点被覆）は次と同値:
**Smin(h) = min{p : 空配置から「根が載る任意の配置」へピーク ≤ p で到達可能}**。
（被覆は根の put の前提から帰納的に自動。往復は遷移の対称性から同コスト。
`treedp_complete.py` の docstring に証明を書いた。）

### 7.3 検証（三層）と結果

| 層 | 内容 | 結果 |
|---|---|---|
| 理論導出との照合 | smin_tree(0..4) = Smin(1..5) = [1,3,4,5,6] | **5 点全一致** |
| 独立実装 | 商なし・被覆集合明示の総当り（m ≤ 2） | 一致 |
| 打ち切りでないこと | p=7 の「到達不能」は BFS の**全探索完了**（queue 枯渇）。13 秒・376 MB（runcap 上限 24GB/5400s に遠く及ばず） | 確定 |

**結果: Smin(6) = 8**（p=7 到達不能・p=8 到達可能）。したがって

- Smin(6) = S̄min(6) = 8 → **ジャンプ条件成立、i\* = 6**（S̄min^{-1}(2) = 6 が確定）
- **S̄min(7) = 10**（Lemma 4.3）
- **reach_cbt(p,0) = p−2 は p=9 で崩壊**: reach(9,0) = 6（= 9−3）。
  §3.1 の区間 [9,21] は**下端でちょうど的中**

### 7.4 崩壊後の形（Lemma 4.8 による見通し）

S̄min^{-1}(2) = 6 が確定したので、Lemma 4.8（p=2）より
**S̄min^{-1}(3) ∈ [2^6, 2^18] = [64, 262144]**。つまり

- reach_cbt(p,0) = **p−3 が p ∈ [9, 66 以上] で成立**（第 4 ジャンプは高さ ≥ 65 —
  計算可能域のはるか外。lg\* の글로벌な遅さがここで実感できる）

### 7.5 開いた問い（消去側・本サーベイの本体への影響）

p=9 で e=0 の値が p−3 に落ちたことで、消去側の問いが具体化した:

- **reach_cbt(9, e=1) はいくつか。** 検証済み域（p≤8）では e=1 で飽和値 p−1 に届いたが、
  p=9 では可逆と標準のギャップが「2 段」になった。**1 消去で 2 段買い戻せるのか、
  e=2 が要るのか**——これが「消去 e 回はジャンプを何段消せるか」（§3.2-2）の
  最初の判定点になる。treedp は e=0 専用なので、消去つき商 BFS か
  ステージ CP-SAT（`data/mip_stage_findings.md`）の適用が次の実装課題

### 7.6 再現

```sh
runcap -m 24 -t 5400 -- .venv/bin/python scripts/treedp_complete.py
# 検証 5+3 点 → m=5, p=6,7: 到達不能 / p=8: 到達可能 → Smin(6)=8
```

---

## 8. 消去 1 回の力の実測（2026-08-11 追記）— **reach_cbt(9,1) ≥ 7 確定、ただし「e=1 で p−1」は p=7 で既に破れていた**

§7.5 の決定点（reach_cbt(9, e=1)）に取り組んだ記録。道具は
`scripts/treedp_erase.py`（消去つき商木 BFS）。

### 8.1 商の消去つき拡張と検証

Aut は「子根が揃っているか」という局所条件を保つので put/take/erase いずれも
Aut 同変であり、**状態 (shape, 消去使用数 u) の商は到達可能性を保存する**
（u はスカラータグ。予算優越: 同一 shape はより小さい u が支配）。検証:

| 層 | 内容 | 結果 |
|---|---|---|
| 全点照合 | landauer_bfs（検証済み・商なし）と m≤3 × p≤8 × e≤3 の **96 点** | 全一致 |
| 深部スポット | m=4（31 頂点）× p∈{6,7} × e∈{0,1} の 4 点 | 全一致 |
| e=0 回帰 | S̄min(2..6) = [3,5,6,7,8] の再現 | 一致 |
| 回帰テスト | `tests/test_treedp_erase.py` 4 件 | pass |

⚠ m=5 以上は landauer_bfs が届かないため**商実装単独**（検証境界を明示しておく）。

### 8.2 打ち切りの記録（結果ではない）

m=6, p=9 の一方向全探索（e=0 側）は **34M 状態・24GB 上限で停止**（runcap、14分43秒）。
7 月の e=0 到達不能判定（104 秒）は**双方向 BFS が goal 側の小ささを使えた**ため。
一方向の消去つき全探索で p=9 空間を掃くのは現行 Python 表現では不可能と判断し、
**肯定側は構成で、否定側は p を下げた全探索で**確定させる方針に切替えた。

### 8.3 構成: S̄min_{e=1}(h+1) ≤ max(S̄min(h)+1, 3)

Bt(h+1) を（S̄min(h)+1 ペブル・消去 1 回で）clean に解く 5 段:
①左 Bt(h) を semicomplete（S̄min(h) ペブル）→ {L}
②L を保持し右 Bt(h) を semicomplete（ピーク 1+S̄min(h)）→ {L,R}
③根を put（3 ペブル時点）
④ **L を erase**（L の子は空 → 消去合法。予算 1 消費）→ {root,R}
⑤右 semicomplete の逆行（遷移対称性による。ピーク 1+S̄min(h)）→ {root} clean ✓

h=6 に適用: S̄min(6)=8（機械検証 2 経路: pmin_tree(5) と §7 の回帰）を前提に
**Bt(7)@(p=9, e=1) 到達可能、ゆえに reach_cbt(9, e=1) ≥ 7**。
層: 紙の合成（部品は機械検証済み）。なお m=4 の最適 e=1 スケジュール現物
（landauer_schedule、115 手）は**消去をちょうど 1 回、根の子に、根 put 直後**に
使っており（move 84/115）、この構成の機構と一致する（ただし部分木側は
より賢く、素朴合成の S̄min(h)+1 を下回る場合がある。下の 8.4）。

### 8.4 e=1..3 の梯子（全探索完了・打ち切りなし）

| 命題 | 結果 | 時間/メモリ |
|---|---|---|
| Bt(6) @ (p=7, e=1) | **到達不能**（全探索） | 4 秒 |
| Bt(6) @ (p=7, e=2) | **到達不能**（全探索） | 7 秒 |
| Bt(6) @ (p=7, e=3) | **到達可能** | 5 秒 |
| Bt(7) @ (p=8, e=1) | **到達不能**（全探索） | 302 秒・6.5GB |
| Bt(7) @ (p=8, e=2) | **到達不能**（全探索） | 424 秒・6.6GB |
| Bt(7) @ (p=8, e=3) | **到達可能** | 529 秒・7.0GB |

構成側（≤）と合わせて **S̄min_{e=1}(6) = 8・S̄min_{e=1}(7) = 9 が確定**。
さらに **飽和 e（p = 標準値 h+1 で Bt(h) に届く最小 e）の曲線が h=3..7 で確定**:

| h | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| e_sat | 1 | 1 | 1 | **3** | **3** |

**e=2 を飛ばして 1→3 に跳ぶ**。しかもこれは**ピラミッドの実測（p≤6 で 1、
p=7,8 で 3。冒頭の対象主張）と完全に同型**であり、「cbt は e=1 で足りるが
ピラミッドは伸びる」という当初の族内対比は消えた。**二分法は「鎖（e で無限に
伸びる）vs 分岐（有限 e で飽和、飽和 e は 1,1,1,3,3,…）」の一本に純化される**。
1→3 のスキップが第 3 ジャンプ（i\*=6）と同じ高さで起きることも含め、
成長則の解明が §3.2-2 の問いの具体形になった。したがって

- **reach(7, e=1) = 5（= p−2）**・**reach(8, e=1) = 6（= p−2）**
- **当初主張「cbt は e=1 で p−1（e=20 でも同じ）」は p=7 で既に偽。**
  元データは h ≤ 5（直接計算可能域）の観察の外挿だったと思われる。
  §3.1 に続き**今夜 2 つ目の外挿トラップ**
- e=1 の効きは単調でない: h=3,4,5 では標準値まで届き（+0）、h=6 では
  1 ペブルも買えず（S̄min_{e=1}(6) = S̄min(6)）、h=7 では 1 だけ買う
  （10→9）。**第 3 ジャンプ（i\*=6）と「e=1 が効かない高さ」が一致**するのは
  示唆的だが、現時点では観察にすぎない
- cbt の飽和に要する e も p とともに増える（ピラミッドと同型）。
  **「分岐があると有限の e で飽和する」という族二分法の骨格は生きるが、
  「cbt は e=1 で足りる」という定量的主張は死んだ**

### 8.5 残る問い

- **reach_cbt(9, e=1) は 7 か 8 か**: 8 には Bt(8)@(9,1) が必要。m=7 の商は
  現行表現で爆発するため未決。状況証拠（両子に S̄min_{e=1}(7)=9 と S̄min(7)=10 を
  同時に払えない）は 7 を示唆するが、交互構築を排除する証明は無い
- **e_sat の成長則**: 1,1,1,3,3 の次（h=8）は 3 か、また跳ぶのか。なぜ 2 を飛ばすのか
  （消去は「根の子の uncompute 踏み倒し」として使うとき対で要る？——未証明の観察）
- ⚠ 8.4 の 2 件は m=5 以上＝商実装単独の検証境界の外。**独立実装
  （消去つき双方向 or 別エンジン）での再確認が挙証水準を上げる次の一手**

### 8.6 再現

```sh
.venv/bin/python scripts/treedp_erase.py --verify   # 96 点照合
.venv/bin/python -m pytest tests/test_treedp_erase.py -q
runcap -m 24 -t 10800 -- .venv/bin/python scripts/treedp_erase.py  # 決定計算一式
```
