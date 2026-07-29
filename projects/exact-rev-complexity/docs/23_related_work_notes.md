# 23 — 文献の知見メモ（`/related-work` の収穫置き場）

`/related-work` や個別調査で読んだものの要約と BibTeX をここに貯める。
**要約はここ、判定に使う 1 行は [`22_known_facts_ledger.md`](22_known_facts_ledger.md)** という分業。
台帳に落として初めて調査は完了する（手順は `docs/22` の「`/related-work` からの流入手順」）。

書式: 1 テーマ 1 節。各節に (a) 何を確かめたかったか、(b) 分かったこと、
(c) 台帳へ落とした ID、(d) BibTeX、(e) 未確認として残ったもの。

---

## 1. 文字列照合の厳密比較回数下界（候補9、2026-07-30）

**(a) 確かめたかったこと**
`docs/idea09` §2 は「可逆計算における問題固有の操作数下界という研究自体が薄い」を前提に、
可逆パターンマッチングの厳密下界を空白と見ていた。非可逆側にどれだけ蓄積があるかを確認する。

**(b) 分かったこと**
非可逆側は**定数まで詰まっている**。時系列は次のとおり。

- Galil–Giancarlo 1991（下界）: 一般アルゴリズムに対し、長さ $m$ のあるパターンで
  $(1+\frac{1}{2m})n-O(1)$、オンラインで $(1+\frac{2}{m+3})n-O(1)$ 回の文字比較が必要。
  $m=3$ のオンラインでは $\frac43 n-\frac13 m$。アルファベットを事前に知らない設定。
- Cole–Hariharan–Paterson–Zwick 1995（下界の改良）: 一般で約 $(1+\frac{2}{m+3})n$、
  オンラインで約 $(1+\frac{9}{4(m+1)})n$。会議版は Cole–Hariharan, FOCS 1992。
- 上界側にも対応する厳密結果がある（*Tighter Upper Bounds on the Exact Complexity of
  String Matching*, SIAM J. Comput.）。接頭辞照合には tight な比較限界の結果もある
  （Breslauer–Colussi–Toniolo）。

つまり**「厳密な操作数下界を出す」こと自体は、この問題では成熟した営み**である。
候補9 が空白を主張できるのは「可逆制約の下で定数がどう動くか」だけになる。

**(c) 台帳へ**: [KF-21](22_known_facts_ledger.md)（種別を 要確認 → 既知 に更新）

**(d) BibTeX**

```bibtex
@article{GalilGiancarlo1991,
  author  = {Galil, Zvi and Giancarlo, Raffaele},
  title   = {On the Exact Complexity of String Matching: Lower Bounds},
  journal = {SIAM Journal on Computing},
  volume  = {20},
  number  = {6},
  pages   = {1008--1020},
  year    = {1991},
  doi     = {10.1137/0220063}
}

@article{ColeHariharanPatersonZwick1995,
  author  = {Cole, Richard and Hariharan, Ramesh and Paterson, Mike and Zwick, Uri},
  title   = {Tighter Lower Bounds on the Exact Complexity of String Matching},
  journal = {SIAM Journal on Computing},
  volume  = {24},
  number  = {1},
  pages   = {30--45},
  year    = {1995},
  doi     = {10.1137/S0097539793245829}
}
```

書誌は Crossref と SIAM の論文ページで照合済み（2026-07-30）。

**(e) 未確認として残ったもの**

- **下界の定数は二次情報からの引用**であり、本文 PDF での確認をしていない。
  候補9 に着手するなら、まず 2 本の PDF を入手して定理番号まで押さえる。
- 可逆制約下で比較回数の下界がどう変わるかを論じた文献は**未探索**。
  「reversible string matching」「reversible pattern matching」で改めて当たる必要がある
  （KF-19 のとおりキーワード検索は当てにならないので、上記 2 本の前方引用を辿るのが早い）。
- KMP の比較回数最適性・Galil–Seiferas は `docs/idea09` §2 が挙げていた名前だが、
  今回の確認では上の 2 本のほうが厳密下界の主線であった。idea09 の記述は KF-21 に合わせて直した。
