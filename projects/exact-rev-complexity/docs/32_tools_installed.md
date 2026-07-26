# 32 — 導入済みツールと疎通確認（2026-07-27）

`docs/31_tool_import.md` の計画に基づき導入した。**すべて無償。全て疎通確認済み。**

## 導入結果

| ツール | 版 | 場所 | 疎通確認 |
|---|---|---|---|
| **OR-Tools CP-SAT** | 9.15.6755 | `.venv/`（リポジトリ内、gitignore 済み） | ✅ `status: OPTIMAL` を返し**最適性を証明して停止**することを確認 |
| **clingo**（ASP） | 5.8.0 | brew | ✅ `q(1) q(2)` / `SATISFIABLE` |
| **CaDiCaL**（SAT） | 3.0.1 | brew | ✅ `s SATISFIABLE` / `v -1 2 0` |
| **Kissat**（SAT） | 4.0.4 | brew | ✅ 版表示 |
| **graphillion**（ZDD） | 2.1 | `.venv/` | ✅ 集合族の演算（濃度制約つき部分集合族の数え上げ）を確認 |
| **ABC**（IC3/PDR） | 1.01（2026-07-27 ビルド） | `~/dev/infra/tools/abc/abc` | ✅ `pdr` コマンドの存在確認（"property directed reachability (aka IC3)"） |
| **Alloy** | dist（最新） | `~/dev/infra/tools/alloy.jar` | ✅ jar 起動確認（Java 21） |
| **TLA+ / TLC** | 最新 | `~/dev/infra/tools/tla2tools.jar` | ✅ `tlc2.TLC` の起動確認 |
| **nauty**（既存） | — | brew（`geng`,`directg`,`labelg`,`shortg`） | 既に導入済み・**未使用**（候補2 の $n=8,9$ 用） |

## 使い方の入口

```bash
cd ~/dev/github.com/tetsuo-jp/exact-rev-complexity

# CP-SAT（最適化＋最適性証明）
.venv/bin/python -c "from ortools.sat.python import cp_model; ..."

# ZDD（集合族の記号的操作）
.venv/bin/python -c "from graphillion import setset; ..."

# SAT（DIMACS CNF を渡す。UNSAT の証明ログは --proof で）
cadical problem.cnf
kissat problem.cnf

# ASP（規則をほぼそのまま書ける。#minimize で最適化）
clingo model.lp

# IC3/PDR（到達不可能性の帰納的不変量を自動構成）
~/dev/infra/tools/abc/abc -c "read_aiger m.aig; pdr; write_invariant inv.txt"

# 有限モデル発見（対応定理の反例探索）
java -jar ~/dev/infra/tools/alloy.jar model.als
java -cp ~/dev/infra/tools/tla2tools.jar tlc2.TLC Spec.tla
```

## 導入しなかったもの（理由つき）

| ツール | 理由 |
|---|---|
| **nuXmv** | 手動でライセンス同意の上ダウンロードする必要があり、Claude が代理で同意すべきでない。**IC3/PDR は ABC で代替できたので不要**。必要なら先生が取得 |
| **AProVE**（TRS 停止性） | **Java 25 が必要**（本機は 21）。加えて Z3/Yices/MiniSat と非商用ライセンスの確認が要る。導入は別途判断 |
| **CSI / TTT2**（Innsbruck） | 旧 URL が **404**（サイト再編）。**CoCoWeb** から web で試すのが摩擦が低い |
| **Gurobi 等の商用ソルバ** | CP-SAT で足りる |
| **Sage / ore_algebra** | holonomic は自前実装で足り、結果は「存在しない」だった（`data/holonomic_findings.md`） |

## 注意事項

- **`.venv/` はリポジトリ内だが `.gitignore` 済み**。エージェントに「標準ライブラリのみ」と
  指示していた制約は、**CP-SAT/ZDD を使う作業では明示的に解除する**必要がある
  （解除する際は「どのスクリプトが `.venv` を要求するか」を明記すること）。
- ABC のバイナリは 160MB。`~/dev/infra/tools/abc/` はソースツリーごと置いてある
  （`~/dev/infra/` は配置規約上「ツーリング・連携スクリプト」のバケット）。
- graphillion のビルドには `CC=gcc CXX=g++` の指定が必要だった
  （Homebrew python が gcc-13 を要求するが本機は g++ 15 のみ）。再構築時の注意点。
