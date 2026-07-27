# 20 — 先行プロジェクトで確定した既知事実（着手前に必読）

出典: `~/dev/overleaf/2026_exact_reversible_pebbling/notes/{survey,research-plan,optimal-schedules}.md`
（一次確認済み: Knill 1995・Královič 2001/2004 本文精読・Pesu–Phillips 2015 本文精読）。
**ここを知らずに始めると、ほぼ確実に既知結果を再発明する。**

## 1. モデル（本リポジトリ共通の定義）

clean reachability reversible pebbling game:
- DAG 上で、先行点が全てペブル済み（または常時可用な入力源）な頂点に対し、
  ペブルを**置く／取る**のどちらもできる（toggle 規則 = 可逆性）。
- 初期状態はペブル無し、終端は**目標頂点だけにペブルがある clean 状態**。
- ピーク（同時ペブル数の最大）を $p$ で抑え、**手数**を最小化する。$M^*$ と書く。

実装は `scripts/revpebble.py`。鎖 `chain(n)` が Bennett のゲームに対応する。

## 2. 鎖について確定していること

- **到達可能性**: ピーク $p$ で clean 到達できる最大鎖長は $\mathrm{reach}(p)=2^{p-1}$。
  これは **Královič 2001 Thm 3.1**（$S^{-1}(p)=2^p-1$）の系であり **既知**。
  （先行プロジェクトでは当初 Conjecture として書いていたが、本文精読の結果 降格した。）
  同値な形で Knill 1995 Thm 2.3: $F(n,S)<\infty \iff n \le 2^{S-1}$。
- **厳密最小手数** $M^*(n)$（$p=p_{\min}$ で評価）、$n=1..16$:
  `1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53, 61, 71`
  → **OEIS 未登録**（2026-07-23 確認）。$p_{\min}(n) = \lceil \log_2 n\rceil + 1$。
- **Knill 1995 (LAUR-95-2258)** が $F(n,S)$ の厳密再帰・$n\le100,S\le20$ の数表・
  最適分割点の構造補題・$\gamma=(\log n)/S \le 1/2$ 域の漸近・
  $TS(n)=2^{2\sqrt{\log n}(1+o(1))}n$ を既に与えている。**閉じた式は無い**（本人明言）。
- **Pesu–Phillips 2015 の k-ratic 族は厳密最適でない**: $n=8$ で $B(2,3)=27$ vs $M^*=25$、
  $n=16$ で $81$ vs $71$。$n=4,9$ では一致。中間域 $n=5..7$ で乖離最大。
  同論文は Knill 1995 を引用していない（= 前方引用を辿る重要性の実例）。
- **最適スケジュールの構造**（第一の構造知見）: 最適解は葉スケールで
  「$p$ 本を連続配置して逆順に剥がす**飽和直線スイープ**」（コスト $2p-1$）を基本操作に使い、
  族の 2 分再帰（再配置を伴う）に勝つ。
- **トレードオフ**: ペブルを $p_{\min}+2$ まで増やすと $2n-1$ 下界に接近（$n=16$: 71→51→49）。
- **完全計算変種の厳密時間** $T(2^p-1,p) = 2, 8, 26, 76, 218$（OEIS 未登録）。
  Královič Cor 3.5 の未解決ギャップ $\Omega(n\lg n)$〜$O(n^{\log_2 3})$ に対し、
  $p\le3$ では $3^p-1$ に一致し $p=4$ から真に下回る。
  **$\Theta(n^{\log_2 3})$ 予想は p=10 まで厳密計算した結果ほぼ確実に偽**（教訓: 予想は上限まで回してから出す）。

## 3. 木・一般 DAG について既知のこと

- **Královič**: 完全二分木の可逆ペブル**空間**は $h+\Theta(\lg^* h)$（標準は $h+1$）。
  バタフライの空間も与えている。任意グラフへは「標準ペブル × 鎖」の合成上界。
  **手数（$M^*$）の厳密値は与えていない** ← 候補1の空白。
- **Chan 2013**: 可逆ペブル数は Dymond–Tompa ゲーム・Raz–McKenzie ゲームと同値。
- **Chan–Lauria–Nordström–Vinyals FOCS 2015**: 可逆ペブル空間の決定は **PSPACE 完全**。
  任意の加法定数以内の近似も PSPACE 困難。標準との分離は乗法 $\log$ 倍。
  **最小反例（$R>P$ が初めて起きるグラフ）は与えていない** ← 候補2の空白。
- **de Rezende–Meir–Nordström–Robere (CCC 2019)**: 「$G$ を時間 $t$・空間 $s$ で
  可逆ペブル可能 $\iff$ ペブリング式の Nullstellensatz 反駁がサイズ $t+1$・次数 $s$」
  という体に依らない厳密対応。**厳密ペブリング値は NS 反駁サイズの厳密値に直訳される**
  ← 候補1・2の結果に副産物の意味を与える重要な接続。
- **Lange–McKenzie–Tapp 2000**: 可逆空間 = 決定性空間（空間増ゼロ・時間指数）。
  Buhrman–Tromp–Vitányi 2001 が中間領域を接続。

## 4. 再利用できる計算資産

| 資産 | 場所 |
|---|---|
| DAG 一般の可逆ペブリング BFS | 本リポジトリ `scripts/revpebble.py`（鎖で上記数値を再現、テスト済み） |
| 先行プロジェクトの BFS・区間代数・下界証書 | `~/dev/overleaf/2026_exact_reversible_pebbling/scripts/`（`pebble_data.py`, `count_algebra.py`, `m6_lower_certificate.py` 等） |
| Lean の表検証 | `~/dev/github.com/tetsuo-jp/gen_janus/260612/formal/GenJanus/Hard18.lean`（`mstar_table`, `pmin_table`） |
| 可逆言語処理系 | `rwhile-C-ocaml`, `rcore-python`, `PyJanus`, `ROOPLPP-interpreter`, `lambda2comb` |
| 可逆アルゴリズム実装 | `RevLZ`（LZ77/78/LZW）, `2025_Rabin_Karp_Plus`, `rev_PE`, `rev_alg` |
| 平均時計算量の形式検証 + 計算オラクル | `analysis-at-home`（`work-units/`, `verifier/`） |

## 5. 引用時の注意

- Královič: 雑誌版 **RAIRO-ITA 38(2):137–161, 2004, doi:10.1051/ita:2004008**、
  会議版 SOFSEM 2001, LNCS 2234, pp.292–303, doi:10.1007/3-540-45627-9_26。
- Knill 1995 は技術報告 **LAUR-95-2258**（査読誌版が無いので引用時に明記）。
- 裏取りできない書誌項目は捏造せず「要確認」と書く。

## 12. 完走事例（方法論の移植実証）

2点反射クエリゲームの厳密値 q(N, ℓ) = min(ℓ−2, k₁*) を本パイプラインで
確定した（periodic-tm, 2026-07）。二重実装照合が下界補題の適用範囲バグを
検出した実証例を含む。詳細は [`21_case_two_point_reflection.md`](21_case_two_point_reflection.md)。
