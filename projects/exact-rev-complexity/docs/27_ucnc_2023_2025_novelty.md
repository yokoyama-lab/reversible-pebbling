# UCNC 2023–2025 に対する autoresearch テーマの新規性照合（2026-08-11）

**このファイルの目的**: 同じ照合を二度やらないため。
**UCNC の新しい巻を根拠に「既知だ」「新しい」と論じる前に、まずここを読む。**

前提: 旧巻（UC 2007–UCNC 2021 の 13 巻）の照合は
`small-urtm/docs/04_morita_open_problems.md` の後半にある（未解決問題 36 件を抽出済み）。

## 0. 結論（3 行）

1. **「pebbling」は UCNC 2023・2024・2025 の 3 巻に 1 度も出てこない。**
   ペブリング系のテーマ（T1′・T2′・T10′・R2・R4・本日の幅規則）は**この会場に競合なし**
2. 紛らわしい語のヒットは**全部別分野だった**（下表）。**重複するテーマは 1 件も無い**
3. ただし **UCNC は可逆計算の主戦場ではない**。RC（Reversible Computation）会議・
   MCU・TCS/RAIRO 等は**別途照合が要る**（§4）

## 1. 照合したデータ

| 巻 | 抽出行数 | 出所 |
|---|---:|---|
| UCNC 2023（Jacksonville） | 11,075 | `gdrive:Paperpile/All Papers/G/Genova et al. 2023 - …UCNC 2023…proceedings.pdf` |
| UCNC 2024（Pohang） | 14,653 | `…/C/Cho and Kim 2024 - …UCNC 2024…proceedings.pdf` |
| UCNC 2025（Nice） | 23,117 | `…/F/Formenti et al. 2026 - …UCNC 2025…proceedings.pdf` |

（`pdftotext -raw`。**`-layout` は数式を壊すので使わない**）

## 2. テーマ別の照合結果

| テーマ | 検索語 | ヒット | 判定 |
|---|---|---:|---|
| T1′ 木 × 消去予算の `reach` | `pebbl` | **0** | **競合なし** |
| T2′ / R2 / R4 証明ログつき下界 | 同上 ＋ `DRAT|certifi` | pebbl 0 / 証明語 10 | **競合なし**（証明語は DNA・量子側の文脈） |
| T10′ 消去の構造 | `erasure|irreversible step|erase` | 2（2025） | **競合なし** |
| **本日の幅規則（飽和）** | `antichain|level width|saturat` | 6 | **競合なし**——**神経素子とリザバーの飽和**であって我々の飽和ではない |
| T3′ ゴミ最小性 | `garbage` | 5（2025） | 要確認だが文脈は別（§3） |
| R6 可逆 LZ の膨張率 | `Lempel|LZW|compress` | **36**（2024 に 27） | **競合なし**——**DNA のロッシー圧縮**と画像圧縮。可逆 LZ ではない |
| R5 判定木のコスト | `decision tree` | **0** | **競合なし** |
| R3 非同型 DAG の全数列挙 | `non-isomorphic|nauty|enumerat` | 6 | 一般語のヒット。competing な列挙研究は見当たらず |

**最も驚くべきは `pebbl` の 0 件**である。3 巻・48,845 行に 1 度も出てこない。

## 3. ⚠ この照合の限界（正直に）

- **UCNC は可逆計算の主戦場ではない。** 0 件は「UCNC に無い」であって
  「どこにも無い」ではない。**RC（Reversible Computation）会議・MCU・
  TCS・RAIRO-ITA・証明複雑性の会議（SAT/CP/STACS）は未照合**
- **語での照合なので、別の用語で同じことをしている論文は拾えない**
  （例: 我々の「消去予算」を "bounded irreversibility" と呼ぶ論文があれば漏れる）
- T3′ の `garbage` 5 件は文脈まで読んでいない（**要確認**）

## 4. 次に照合すべき会場（優先順）

1. **RC（Reversible Computation）** — 可逆計算の主戦場。**ここが最重要**
2. **MCU（Machines, Computations and Universality）** — 小さい機械・万能性
3. 証明複雑性側（**ペブリングはこちらで盛ん**。Nordström らの系統）
4. TCS / RAIRO-ITA のジャーナル

## 5. 副産物: Cook & Palmiere の本文が読めた

**"The Morita Gate is Universal", UCNC 2025, pp.194–213**（抽出行 9759–10519）。

- **Morita gate = RLEM 2-17** = 2 状態 2 入力で、**トークンが通るたびに状態が反転する回転子**
  （論文の Fig.1(B) は、玉が通るとローターが回る物理装置として描いている）
- **万能であると証明し、2 入力ゲートは万能になれないという長年の予想を反証した**
- **さらに重要**: 逐語で
  > this result also **finishes the classification of all 2-state RLEMs** (of all sizes),
  > regarding which RLEMs or groups of RLEMs are able to implement which others.

  ＝ **単一ゲートの解決にとどまらず、2 状態 RLEM の完全分類が完成した**
- 論文中の整理（既知の補題として）: RE は任意の RTM を実装できる（Lemma 2）／
  RE は任意の RLEM を実装できる（Lemma 3）／3 入力以上の非退化ゲートは全て万能（Theorem 1）／
  Integrator(2-3) と Differentiator(2-4) は互いを実装できない（Lemma 9）

**したがって `small-urtm/docs/04` の A1 は「要旨で確認」から「本文で確認」に上がる。**

## 6. 再現用

```sh
rclone lsf gdrive:Paperpile -R | grep -iE "UCNC 202[3-5]" | grep -i proceedings
rclone copyto "gdrive:Paperpile/<path>" UCNC_2025.pdf
pdftotext -raw UCNC_2025.pdf UCNC_2025.txt      # -layout は数式を壊す
grep -niE "pebbl|erasure|garbage|DRAT" UCNC_2025.txt
```

⚠ **`systemd --user` は brew の PATH を失う**ので、バッチ化するなら `--setenv=PATH=` が要る
（rclone が黙って動かず「0 巻処理で完了」になる）。
