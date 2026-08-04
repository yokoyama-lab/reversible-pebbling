# 作業キュー: 可逆ペブリングの厳密値を新しいグラフ族へ

**このファイルは手で更新する作業台帳である**（`data/families/atlas.csv` とは別物。あちらは生成物）。
手順は `docs/90_family_loop_protocol.md`。

## 目的

可逆シミュレーションの厳密定数（$p_{\min}$ と $M^*$）を、**まだ表の無いグラフ族**へ広げる。
既に表がある族は 鎖・完全二分木・ピラミッド・spinal・バタフライ・小 DAG 全数。
ここで足すのは **円筒（トーラスの DAG 対応物）・$k$ 分木・ビット反転**の 3 族。

新規性の所在: Královič 2004 は木とバタフライの**空間**しか与えていない（手数の表は無い）。
Lengauer–Tarjan のビット反転グラフは**標準**ペブリングの定番例で、可逆版の厳密値は無い。
円筒はメモリハード関数の文献に構造は出てくるが、可逆ペブリングの厳密値は無い。

## 進め方の原則（このループ固有）

- **失敗が完全に安全**。外部への書き込みが無く、結果は数値表として単調に増える。
- 届かなかったセルは `status: timeout` として**行を残す**（黙って落とさない）。
- **閉形式は計算可能域の上限まで回してから**しか書かない（4 回崩壊している）。

---

## U1 — 族の定義と、端での退化の検証

**状態: done**（2026-08-05）

完了条件: `scripts/families.py` に `cylinder(k,h)` / `kary_tree(k,h)` / `bitrev(k)` を置き、
`tests/test_families.py` で (a) 構造の不変量 (b) 端での既知族への退化 (c) 素朴 BFS との一致
(d) $M^*$ が奇数 (e) スケジュールが検証器を通る、を固定する。

結果: 10 テスト pass。退化は
`cylinder(1,h)` = 鎖（$M^*$ が確定値 1,3,5,9,11,15,19 と一致）、
`cylinder(k,h)`（$k\ge h+1$、祖先に制限）= ピラミッド、
`kary_tree(2,h)` = 完全二分木（$M^*$ = 1,5,17）。
**トーラスは向きづけると巡回するので DAG にならない**ことを `families.py` の冒頭に明記した。
書けるのは円筒（片方向だけ巻いたピラミッド）の値である。

## U2 — 台帳の生成器と、証書による検証

**状態: done**（2026-08-05）

完了条件: `scripts/family_atlas.py --build` が `data/families/atlas.csv` と
`data/families/certs/*.json` を作り、`--verify` が全行の証書を再生して 1 秒未満で終わる。
`tools/loopcheck.sh` がこの検証を含めて約 10 秒で合否を返す。

結果: 90 行（30 インスタンス × $p\in\{p_{\min},p_{\min}+1,p_{\min}+2\}$）。全行 `exhaustive`。
`pebbleable <= 13` の行は素朴 BFS と高速版の 2 実装で一致（`methods: mask+bfs`）。
検証は $M^*$ の奇数性と床 $2N-1$ も併せて見る。

## U3 — 円筒の前線を広げる

**状態: todo**

完了条件: `FAMILIES` の `cylinder` を $k\in[2,7]$・$h\in[2,10]$ へ広げ、`--build --only cylinder`
を回して台帳を更新する。届かないセルは `status: timeout` の行として残す。
`data/families/findings.md` に「どこまで届いたか」と「$p$ を 1 上げたときの落差」を書く。

着目点（U1–U2 で既に見えている異常）: `cylinder(4,6)` は $p_{\min}=8$ で $M^*=93$、
$p=9$ で 57 へ**落差 36**。`cylinder(5,6)` も 103→63。
一方 $h\le5$ では落差は 6 以下である。**$h=6$ で何かが変わる。**
これは exp01 のピラミッドが $h=5$ で跳ねたのと同じ型の現象かもしれない。

## U4 — $k$ 分木の前線を広げる

**状態: todo**

完了条件: `kary_tree` を $k\in[3,6]$・$h\in[1,4]$ へ広げる（$k^h$ が効くので早く詰まる。
詰まったら `timeout` 行を残す）。$p_{\min}(k,h) - h$ を表にし、
Královič の $h+\Theta(\lg^* h)$（$k=2$）が $k$ でどう動くかを findings に書く。

## U5 — ビット反転の前線を広げる

**状態: todo**

完了条件: `bitrev(k)` を $k\le5$ まで試す（$k=4$ で 32 頂点・31 がペブル可能なので、
`STATE_CAP` に当たる可能性が高い。当たったら `timeout` を残し、
`--only bitrev` で `P_EXTRA` を落とすなどの回避を試す）。

## U6 — 新しい数列を OEIS に照合する

**状態: todo**

完了条件: 台帳から数列を切り出し（$k$ 固定で $h$ を動かした $M^*$、$p_{\min}$ の列）、
OEIS に照合して結果を `data/families/findings.md` に書く。
**照合は「一致した」で終えない**（`docs/00_overview.md` §2.1 #4: grid が A001845 に
4 点一致してから $k=5$ で消滅した）。一致したら、必ず次の項まで計算して確認する。

## U7 — 既知性の一次確認

**状態: todo**

完了条件: Královič 2004・Knill 1995・Lengauer–Tarjan 1982 の**本文**で、
円筒・$k$ 分木・ビット反転の可逆ペブリング**手数**が与えられていないことを確認し、
`docs/22_known_facts_ledger.md` に ID を振って追記する。
アブストラクトだけで判断しない（`docs/00_overview.md` §2.2）。前方引用も辿る。

## U8 — 最大セルの最適性を CP-SAT で独立に確認する

**状態: todo**

完了条件: 台帳の各族の最大セル（BFS が届いた最大の $h$/$k$）について
`scripts/cpsat_interval.py` を回し、`status=OPTIMAL` と BFS の値が一致することを確認する。
一致しなければ**どちらかにバグがある**ので、その反復は失敗として理由を書く。
台帳に `methods` として `cpsat` を足す。

## U9 — 下界を CaDiCaL の UNSAT で固める

**状態: todo**

完了条件: 各族の 1 セルについて `scripts/sat_lower_bound.py` で
「$M^*-2$ 手で可能か」を CNF にし、CaDiCaL が UNSAT を返すこと（可能なら DRAT 証明つき）を
確認する。`data/families/findings.md` に記録し、その行の `status` を `unsat_lb` にする。
これが**下界側に再生可能な根拠が付く唯一の単位**である。

## U10 — $p$ を 1 上げたときの落差の構造

**状態: todo**

完了条件: U3 で見えた落差（`cylinder(4,6)`: 93→57）について、$p=p_{\min}$ と $p_{\min}+1$ の
最適スケジュールを証書から取り出し、**何が変わったか**を分類して findings に書く。
exp01 の「ピラミッド $h=5$ の跳ね」と同じ型かを判定する。

## U11 — findings をまとめる

**状態: todo**

完了条件: `data/families/findings.md` を、`data/exp01_findings.md` と同じ体裁
（実装の妥当性 → 表 → 読み取り → 次の一手）で書き上げる。
層の断り書き（全数 BFS は層3）を必ず入れる。

---

## 次のトラックへの引き継ぎ

このキューが尽きたら（または `blocked` ばかりになったら）、
**トラック A（Jones 最適性の機械証明・`jones-agenda`）**へ移る。
順番と切り替えの規則は `~/dev/github.com/yokoyama-lab/jones-agenda/docs/bac-agenda.md`。
