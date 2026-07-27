# 予想 B2（到達則の等号）を IC3 で検証（2026-07-27）

実装 `scripts/ic3_reach.py`。`docs/31_tool_import.md` §8.3・§10.4 の原則の実例:

> 下界側（存在しないことを示す）は成熟した道具が必須。
> IC3/PDR は**到達不可能性を証明する帰納的不変量を自動構成する**。

## 1. 何を検証したか

定理 B1（証明済み）は下界 $\mathrm{reach}(p,e)\ge(e+2)2^{p-2}$。
**予想 B2 は等号**で、これは「$n=(e+2)2^{p-2}+1$ には clean 到達**できない**」という
**不到達性**の主張である。従来は BFS の全数探索で $p\le6$ まで確認していた。

鎖の $e$-消去ペブリングを SMV に符号化し（状態 = 各節点のペブル＋消去カウンタ、
入力 = 操作する節点と put/take、`INVARSPEC` = 「節点 $n$ のみがペブル済み」に到達しない）、
nuXmv の `check_invar_ic3`（SMT ベース IC3）で検査した。

## 2. 結果

| $p$ | $e$ | 予想値 $(e+2)2^{p-2}$ | $n=$ 予想値 | $n=$ 予想値$+1$ | 判定 |
|---:|---:|---:|---|---|---|
| 3 | 0 | 4 | REACHABLE | **UNREACHABLE** | ○ |
| 4 | 0 | 8 | REACHABLE | **UNREACHABLE** | ○ |
| 4 | 1 | 12 | REACHABLE | **UNREACHABLE** | ○ |
| 5 | 0 | 16 | REACHABLE | **UNREACHABLE** | ○ |
| 5 | 1 | 24 | REACHABLE | **UNREACHABLE** | ○ |

**両側が一致**（予想値には到達し、+1 には到達しない）。**予想 B2 は反例なし。**
$p=6,7$ の掃引は実行中。

**BFS との違い**: BFS は状態を明示的に列挙するので $\sum_{k\le p}\binom{n}{k}$ で詰まる。
IC3 は**到達不可能性の帰納的不変量**を構成するので、状態空間を列挙しない。
$p=7,e=1$（$n=97$）は BFS では $\sum_{k\le7}\binom{98}{k}\approx1.3\times10^{10}$ で不可能だが、
IC3 なら射程に入る可能性がある。

## 3. 本命は「不変量を人間の証明に育てる」こと（未達）

IC3 の価値は判定そのものより**副産物の帰納的不変量**にある。それは
「ピーク $p$・消去 $e$ でこの先へ進めない」ことの**理由**を述べる述語であり、
人間が一般 $n$・一般 $p$ の証明に育てる素材になる（機械が見つけ、人間が一般化する分業）。

**現状の障害**:
- **nuXmv の `check_invar_ic3` は不変量をダンプしない**（`help check_invar_ic3` を確認。
  オプションは検証方法の制御のみで、不変量出力は無い）。
- **ABC の `pdr -I <file>` は不変量を書き出せる**が、
  nuXmv の `write_aiger_model` が出す AIGER には **liveness property が含まれ**、
  ABC が `Reading AIGER files with liveness properties is currently not supported` で拒否する。

**次の一手（優先度: 高。これが B2 の証明への最短路）**:
1. AIGER から liveness 部分を除去する（ヘッダの `B`/`J`/`F` セクションを落とす小スクリプト）か、
2. **自前で AIGER を出力する**（状態遷移は単純なので、`scripts/ic3_reach.py` に
   AIGER エミッタを足すのは現実的）。そのうえで `abc -c "read_aiger m.aig; pdr -I inv.txt"`。
3. 得られた不変量の節を読み、$p$ や $e$ に関する規則性を探す
   （例: 「ペブルの位置の重み付き和が単調に有界」型の量が出れば、それが定理の核）。

## 4. 手続き上の注意（記録）

- **符号化は既知値で必ず検証する。** $p=3,e=0$（reach $=4$）で
  「4 は到達可能・5 は不到達」を確認してから未知領域に進んだ。
  これをせずに UNREACHABLE を得ても、符号化が過剰に制約されているだけかもしれない。
- nuXmv は `read_model` の後に
  `flatten_hierarchy; encode_variables; build_boolean_model` が必要（AIGER 出力時）。
- nuXmv 2.2.0 は `libxml2.so.2` を要求する（本機は `.so.16`）。
  `LD_LIBRARY_PATH` に private shim を渡す（`docs/33_install_notes.md` §1）。
