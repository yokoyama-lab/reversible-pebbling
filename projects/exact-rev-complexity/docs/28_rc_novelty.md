# サーベイ: RC（Reversible Computation）会議 12 巻との照合（2026-08-12）

**このファイルの目的**: 同じ照合を二度やらないため。
**RC 会議を根拠に「既知だ」「新しい」と論じる前に、まずここを読む。**

前提: UCNC 側の照合は `docs/27_ucnc_2023_2025_novelty.md`（3 巻・48,845 行、`pebbl` 0 件）。
`docs/27` §3 が自ら「**UCNC は可逆計算の主戦場ではない。RC 会議は未照合**」と限界を書いた。
**その宿題を消化したのが本文書。**

## 0. 結論（3 行）

1. **消去予算つき clean 到達の競合は RC 12 巻にも無い。**
   「erasure budget / bounded irreversibility / limited erasure」系の語は **12 巻で 1 件のみ**、
   それも文脈が別（下表）
2. `pebbl` のヒット 335 件は **2 つの既知系統に集中**していた——
   **spooky pebble game**（RC 2023、`docs/24` が既に別モデルと判定済み）と
   **Bennett 系の量子回路コンパイル**（RC 2017・2015）
3. **最新の RC 2025・2026 は `pebbl` が 0 件。** 直近で先を越された形跡は無い

## 1. 照合したデータ

`gdrive:Paperpile` から 12 巻を取得し `pdftotext -raw` で抽出（**`-layout` は数式を壊す**）。

| 巻 | 行数 | `pebbl` | 消去予算系 | `garbage` | 証明ログ | RLEM/2-17 |
|---|---:|---:|---:|---:|---:|---:|
| RC2014 | 13,419 | — | — | 43 | 2 | — |
| RC2015 | 14,773 | **59** | — | 22 | 5 | — |
| RC2016 | 17,081 | — | — | 13 | 11 | — |
| RC2017 | 12,220 | **7** | — | 32 | — | — |
| RC2019 | 11,263 | 1 | — | 27 | 3 | — |
| RC2020 | 13,637 | — | — | 27 | 7 | — |
| RC2021 | 13,064 | — | **1** | 11 | 4 | **69** |
| RC2022 | 13,432 | — | — | 5 | 4 | — |
| RC2023 | 18,800 | **268** | — | 8 | 8 | 1 |
| RC2024 | 11,201 | — | — | 19 | 2 | — |
| **RC2025** | 8,507 | **0** | — | 13 | 3 | — |
| **RC2026** | 13,337 | **0** | — | 2 | 4 | 1 |
| **合計** | 160,734 | **335** | **1** | 222 | 53 | 71 |

⚠ RC 2018 は Paperpile の命名が別形式で拾えていない（**未検査**。0 件ではない）。

## 2. `pebbl` の大口を全部当たった

| 巻 | 論文 | 判定 |
|---|---|---|
| **RC 2023**（268 件） | **Quist & Laarman, "Optimizing Quantum Space Using Spooky Pebble Games"** (p.134)。spooky pebble game を一般回路に初適用し、**SAT ソルバで解く**。量子空間の上界を証明 | **別モデル**。spooky は**測定で再利用する「返す借金」**で、我々の消去は**返さない破壊**。`docs/24` §2 の判定を維持。**本文に消去予算に相当する語は 0 件** |
| **RC 2017**（7 件） | ⚠ **帰属を訂正**（2026-09-12）。実測は **#16 Roetteler–Svore, "Tools for Quantum and Reversible Circuit Compilation" が 5 件・#11 "REVS" が 2 件**で、7 件が 1 本に集中しているのではない。Bennett の compute-copy-uncompute に対し**空間を 75% 削減**。キーワードに "Pebble games · Dirty ancillas" | **競合なし**（実装ヒューリスティクスの実測で、下界も消去予算も無い）。⚠ **ただし「道具として言及されるだけ」は弱すぎた**——#16 §2 の逐語「a strategy that can be interpreted as a particular **pebble game** played on the nodes of the data flow graph, **constitute the main innovation of the present work**」。**"dirty ancillas" は汚れた補助ビットの再利用**であって消去予算ではない、は維持 |
| **RC 2015（59 件）** | ⚠ **精査した**（2026-09-12。従来「未精査（要確認）」）。**59 件すべてが #16 Pesu & Phillips, "Real-Time Methods in Reversible Computation" に集中**（他 19 本は 0 件）。しかも**可逆ペブリングそのものを扱う論文**で、Bennett の線形時間アルゴリズムに対し新提案 **k-ratic** を与える。逐語「We offer an improvement on his linear-time algorithm, which we call the **k-ratic algorithm**. This operates at essentially the same rate as Bennett's algorithm, but **uses roughly half as much space**.」 | **競合なし**（消去予算も clean 到達も扱わない）。⚠ **ただし「無関係」ではない。厳密値の比較対象になりうる。** 到達 `A(n,k) = n^k/k! + O(n^(k−1))`（Prop 3.3）、空間比 `(k^k/k!)^(1/k) → e`（Prop 3.5）。**⚠ 本論文は最後の石を盤上に残す版**（脚注 1 が Li–Vitányi 版との違いを自ら明記）なので、**厳密値表と突き合わせる前に規約を揃えること** |
| **RC 2017 #1**（`pebbl` 0 件） | ⚠ **語の照合が取り逃がしていたもの**（2026-09-12 追加）。Holzer–Kutrib, "Reversible Nondeterministic Finite Automata" は **「degree of irreversibility」＝非可逆状態の個数 k による厳密無限階層**を作る。逐語「**Theorem 10.** For all k ≥ 0, L(IREV_k-NFA) ⊂ L(IREV_{k+1}-NFA).」 | **競合ではない**（モデルが別物。オートマトンの状態数であってペブル数ではない）。**ただし「有界非可逆性の階層」の先行例として related work に引く価値がある。** `erasure budget` / `bounded irreversibility` / `limited erasure` のどの検索語にも当たらなかった |

## 3. 判定表

| 主張 | 判定 | 層 |
|---|---|---|
| 消去予算つき **clean** 到達（`reach(p,e)`） | **RC 12 巻に競合なし** | 語の照合＋大口の文脈確認 |
| spooky pebble game との違い | **別モデルであることを再確認**（RC 2023 の本文で） | 本文で確認 |
| 直近（2025・2026）で先を越されたか | **`pebbl` が 0 件。形跡なし** | 語の照合 |
| RLEM/2-17 | RC 2021 に 69 件（Morita 系の議論）。**Cook & Palmiere は UCNC 2025 側** | 語の照合のみ |

## 4. まだやっていないこと（正直に）

- ~~**RC 2015 の 59 件を精査していない。**~~ → **2026-09-12 に精査した**（上の表。全件が #16 Pesu & Phillips）
- ~~**RC 2018 が抽出できていない**（命名が別形式）。**0 件ではなく未検査**~~
  → **2026-09-12 に解消**。`yokoyama-lab/rc-survey` が正本 PDF を
  `K/Kari and Ulidowski 2018 - RC2018 - Reversible Computation.pdf`（18,195 行）として確定した。
  **「0 件ではなく未検査」という当時の断り書きは正しかった。**
- **語での照合なので、別の用語で同じことをしている論文は拾えない**
  （我々の「消去予算」を全く違う言い方で呼ぶ論文があれば漏れる）。
  ⚠ **これは実際に起きた**——RC 2017 #1 の「degree of irreversibility」による無限階層は
  どの検索語にも当たらなかった（上の表の最終行）。**語の照合だけで「競合なし」を結論しない。**
- MCU・証明複雑性側（**ペブリングはむしろこちらで盛ん**。Nordström 系）は**未照合**

## 5. 再現用

```sh
rclone lsf gdrive:Paperpile -R | grep -iE "reversible computation.*proceedings|^All Papers/Other/RC ?20[0-9]{2}"
rclone copyto "gdrive:Paperpile/<path>" RC2023.pdf
pdftotext -raw RC2023.pdf RC2023.txt        # -layout は数式を壊す
grep -niE "pebbl|erasure budget|garbage|DRAT" RC2023.txt
```

抽出スクリプト: `scratchpad/rc/fetch.sh`（12 巻を 5 分で抽出）。
⚠ **`systemd --user` は brew の PATH を失う**ので `--setenv=PATH=` が要る。

---

## 訂正の記録（2026-09-12）

`yokoyama-lab/rc-survey`（RC 会議録 2011–2026 の**全 278 論文**を原典で読み直した論文単位サーベイ）
からの報告 3 件を、**一次情報で再確認したうえで**反映した。

**本文書の結論「消去予算つき clean 到達に RC 12 巻で競合なし」は維持されている。** 変えたのは:

1. **RC 2015 の 59 件の正体**（従来「未精査（要確認）」）→ 全件が #16 Pesu & Phillips。
   **可逆ペブリングそのものの論文**で、k-ratic を提案。⚠ 規約（最後の石を残す版）が違う。
2. **RC 2017 の 7 件の帰属**（従来 1 本に帰属）→ **#16 が 5 件・#11 が 2 件**。
   かつ #16 では pebble game が "the main innovation" と自己申告されており、
   「道具として言及されるだけ」は弱すぎた。**「競合なし」の判定自体は維持。**
3. **語の照合の穴**（新規）→ RC 2017 #1 の「degree of irreversibility」の無限階層は
   どの検索語にも当たらない。**related work に引く価値がある先行例。**

検証方法（再現できる形で残す）:

```sh
# rc-survey が抽出した論文単位テキストに対して 1 本ずつ数える
for f in <papers>/RC2015/*.txt; do n=$(grep -oic 'pebbl' "$f"); [ "$n" -gt 0 ] && echo "$n $(basename $f)"; done
#   -> 59 RC2015-16-real-time-methods-in-reversible-computation.txt   （他 19 本は 0）
for f in <papers>/RC2017/*.txt; do n=$(grep -oic 'pebbl' "$f"); [ "$n" -gt 0 ] && echo "$n $(basename $f)"; done
#   -> 2 RC2017-11-revs-...  /  5 RC2017-16-tools-for-quantum-...
```

→ 報告元: `yokoyama-lab/rc-survey` の `docs/40_discrepancies.md` B 節。

