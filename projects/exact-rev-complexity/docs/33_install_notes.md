# 33 — インストール手順（再現用・2026-07-27 実施）

本機（p1gen7, Linux, Homebrew, JDK 21/25 併存）で実際に通った手順のみを載せる。
**別マシンで再現する場合はこのファイルをそのまま辿ればよい。**

---

## 1. nuXmv 2.2.0（IC3/PDR・SMT ベースのモデル検査器）— **導入済み（2026-07-27）**

先生から直接 URL の指示があったので取得した（ライセンス同意は先生が実施）。

```bash
cd ~/dev/infra/tools
curl -sL -o nuXmv.tar.xz "https://nuxmv.fbk.eu/downloads/2.2.0/nuXmv-2.2.0-linux64.tar.xz"
tar xJf nuXmv.tar.xz
chmod +x nuXmv-2.2.0-linux64/usr/local/bin/nuXmv
ln -sf ~/dev/infra/tools/nuXmv-2.2.0-linux64/usr/local/bin/nuXmv ~/dev/infra/tools/nuXmv
```

**⚠️ 罠: `libxml2.so.2` が無い。** nuXmv 2.2.0 は旧 ABI の `libxml2.so.2` を要求するが、
本機の libxml2 は soname が **`.so.16`**（Ubuntu 15 系 / brew 2.15）に上がっており、
そのままでは `error while loading shared libraries: libxml2.so.2` で起動しない。

**対処（システムを汚さない private shim）**:

```bash
mkdir -p ~/dev/infra/tools/nuxmv-libs
ln -sf /usr/lib/x86_64-linux-gnu/libxml2.so.16 ~/dev/infra/tools/nuxmv-libs/libxml2.so.2
# 実行時に LD_LIBRARY_PATH を渡す
LD_LIBRARY_PATH=$HOME/dev/infra/tools/nuxmv-libs ~/dev/infra/tools/nuXmv -int
```

起動時に `no version information available` の警告が 2 行出るが**動作する**。
（soname を偽装しているため。nuXmv が libxml2 を使うのは XML トレース入出力の経路のみなので、
IC3/PDR による有限モデルの検査には影響しない。厳密にやるなら libxml2 2.9 系の
`.so.2` を別途用意して同じ場所に置く。）

**機能確認（IC3 が反例を出すこと）**:

```bash
cat > counter.smv <<'EOF'
MODULE main
VAR c : 0..7;
ASSIGN init(c) := 0; next(c) := (c + 1) mod 8;
INVARSPEC c < 6;   -- 偽（反例が出る）
INVARSPEC c < 8;   -- 真
EOF
LD_LIBRARY_PATH=$HOME/dev/infra/tools/nuxmv-libs ~/dev/infra/tools/nuXmv -int <<'CMD'
read_model -i counter.smv
go_msat
check_invar_ic3
quit
CMD
# → "invariant c < 6 is false" ＋ IC3 smt counterexample のトレース（c=0,1,2,3,4,...）
```

**ABC との使い分け**: ABC の `pdr` は AIG（ビットレベル有限状態）向け。
nuXmv は **整数変数を持つモデルを SMT ベースで扱える**（`go_msat` + `check_invar_ic3`）。
ペブリングの下界を「ペブル数 $\le p$」のような算術制約付きで書くなら nuXmv 側が向く。

## 2. AProVE（TRS の停止性・複雑度解析）

**要点: Java 25 が必要（本機の既定は 21）。ライセンスは非商用のみ。**

```bash
# (a) JDK 25 を入れる
brew install openjdk@25
/home/linuxbrew/.linuxbrew/opt/openjdk@25/bin/java --version   # openjdk 25.0.4

# (b) jar を取得（GitHub リリース。click-through 無し）
mkdir -p ~/dev/infra/tools/trs && cd ~/dev/infra/tools/trs
curl -sL -o aprove.jar \
  "https://github.com/aprove-developers/aprove-releases/releases/download/master_2026_02_15/aprove.jar"

# (c) 疎通確認（TPDB/WST 形式の TRS を渡す）
printf '(VAR x)\n(RULES\n f(s(x)) -> f(x)\n)\n' > t.trs
/home/linuxbrew/.linuxbrew/opt/openjdk@25/bin/java -jar aprove.jar -m wst t.trs
# → YES   （停止性が示された）
```

**実測: JDK 21 でも起動して `YES` を返した**（公称は Java 25 用）。
ただし公称に従い 25 を使うのが安全。

> ⚠️ **副作用（2026-07-27 に確認）**: `brew install openjdk@25` を入れた結果、
> **PATH 上の `java` が 25.0.4 に変わった**（`/home/linuxbrew/.linuxbrew/bin/java` が
> `/usr/bin/java`＝system の 21 より先に来る）。当初 "既定は 21 のまま" と書いたのは誤り。
> 影響を確認したもの: **Alloy と TLA+/TLC は Java 25 でも問題なく動作**した。
> 21 を明示したい場合は `/usr/bin/java` を直接呼ぶ（`/etc/alternatives/java` → openjdk 21.0.11）。

**外部ソルバ（任意）**: 複雑度解析や一部の手法で Z3 / Yices / MiniSat / KoAT / LoAT / CoFloCo を
呼ぶ。本機は `minisat`・`yices2`（brew）と `koat2`・`CoFloCo`（§5）を導入済み。
AProVE から使わせるにはパス設定が必要（未設定。必要になった時点で対応）。

**ライセンス**: 非商用利用のみ（学術利用は可）。商用は別途契約。

---

## 3. graphillion（ZDD = 集合族の圧縮表現）

**罠: Homebrew の Python は `g++-13` を要求するが、本機には `g++` 15 しか無い。**
そのまま `pip install` すると `command 'g++-13' failed: No such file or directory` で落ちる。

```bash
cd ~/dev/github.com/tetsuo-jp/exact-rev-complexity
python3 -m venv .venv                      # 既に .gitignore 済み
.venv/bin/pip install --upgrade pip
.venv/bin/pip install setuptools wheel     # ← これが無いと BackendUnavailable で落ちる
CC=gcc CXX=g++ .venv/bin/pip install graphillion    # ← コンパイラを明示するのが要点

# 疎通確認
.venv/bin/python -c "
from graphillion import setset
setset.set_universe(range(1,6))
print(len(setset({'include':[1]})))          # 16 = 2^4
print(len(setset({}).larger(0) - setset({}).larger(2)))   # 濃度<=2 の集合族の個数
"
```

つまずいた順序: ①`g++-13` が無い → `CC/CXX` を明示 → ②`setuptools.build_meta` が
無い（venv が新しく setuptools 未同梱）→ `setuptools wheel` を先に入れる → 成功。

### 3.1 恒久対応（2026-07-27 実施）— 以後は `CC/CXX` の指定が不要

罠①は graphillion 固有ではなく、**Homebrew python の `sysconfig` が `gcc-13`/`g++-13` を
記録している**ことに起因する。したがって**他の C 拡張パッケージでも同じ失敗が起きる**。
そこで `~/.local/bin`（PATH 上）に shim を置いて恒久的に解消した:

```bash
mkdir -p ~/.local/bin
for v in 13 14; do for c in gcc g++; do
  printf '#!/bin/sh\nexec %s "$@"\n' "$(command -v $c)" > ~/.local/bin/${c}-${v}
  chmod +x ~/.local/bin/${c}-${v}
done; done
g++-13 --version   # → g++ (Ubuntu 15.2.0) が応答
```

**検証**: 環境変数なしでソースから再ビルドできることを確認した。

```bash
.venv/bin/pip install --force-reinstall --no-cache-dir --no-binary :all: graphillion
# → Successfully installed graphillion-2.1（CC/CXX の指定なし）
```

罠②（`setuptools wheel` の先行導入）は venv を作るたびに必要なので、
**新しい venv を作ったら最初に `pip install setuptools wheel` を実行する**こと。

---

## 4. 既に導入済みのもの（`docs/32_tools_installed.md` 参照）

```bash
brew install clingo cadical kissat zstd minisat yices2
.venv/bin/pip install ortools
# ABC（IC3/PDR）はソースからビルド:
mkdir -p ~/dev/infra/tools && cd ~/dev/infra/tools
git clone --depth 1 https://github.com/berkeley-abc/abc.git
cd abc && make -j8 ABC_USE_NO_READLINE=1        # 約数分、バイナリ 160MB
echo -e "pdr -h\nquit" | ./abc                   # IC3 の存在確認
# Alloy / TLA+:
curl -sL -o ~/dev/infra/tools/alloy.jar \
  "https://github.com/AlloyTools/org.alloytools.alloy/releases/latest/download/org.alloytools.alloy.dist.jar"
curl -sL -o ~/dev/infra/tools/tla2tools.jar \
  "https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar"
```

---

## 5. TRS 系ツール（2026-07-27 導入分）

配置は `~/dev/infra/tools/trs/`。

### 5.1 CeTA 3.9（Isabelle/HOL で正しさが証明された証明書検証器）

```bash
cd ~/dev/infra/tools/trs
curl -sL -o ceta "https://isafor-ceta.uibk.ac.at/bin/linux_intel/ceta"
chmod +x ceta && ./ceta --version     # → 3.9
```
単体バイナリで依存なし（Isabelle からコード生成された Haskell プログラム）。

### 5.2 Maude 3.5.1（rewriting logic の実行系＋LTL モデル検査）

```bash
cd ~/dev/infra/tools/trs
curl -sL -o maude.zip "https://github.com/maude-lang/Maude/releases/download/Maude3.5.1/Maude-3.5.1-linux-x86_64.zip"
unzip -oq maude.zip -d maude
printf 'fmod T is protecting NAT . op f : Nat -> Nat . var X : Nat . eq f(X) = X + 1 . endfm\nreduce f(41) .\nquit\n' \
  | ./maude/maude -no-banner        # → result NzNat: 42
```
brew には formula が無い（`brew search maude` は無関係な候補のみ）。GitHub リリースを使う。

### 5.3 ACP v0.74（自動合流性証明器・青戸–豊田、新潟大）— **パッチが必要だった**

```bash
brew install smlnj minisat yices2          # SML/NJ 2026.1 が入る
cd ~/dev/infra/tools/trs
curl -sL -o acp.tgz "https://www.nue.ie.niigata-u.ac.jp/tools/acp/acp-v0.74.tgz"
tar xzf acp.tgz && cd acp-v0.74
```

**⚠️ ここで素の `make` は失敗する。** ACP は SML/NJ **110.79** 前提で書かれており、
本機の 2026.1 では標準ライブラリの `ORD_SET` シグネチャが拡張されているため
`src/util/ord_key2.sml` が「unmatched value specification: toList / minItem / maxItem /
disjoint / combineWith / mapPartial」で落ちる。

**適用したパッチ**（`fun toString xs =` の直前、101 行目付近に挿入。
オリジナルは `src/util/ord_key2.sml.orig` に保存済み）:

```sml
   (* 2026-07-27 追加: 新しい SML/NJ の ORD_SET が要求する追加メンバを委譲する *)
   val toList = Set.toList
   val minItem = Set.minItem
   val maxItem = Set.maxItem
   val disjoint = Set.disjoint
   val combineWith = Set.combineWith
   val mapPartial = Set.mapPartial
```

その後:

```bash
make                                        # work/acp/acp.amd64-linux が生成される
cd work/acp && sml @SMLload=acp.amd64-linux sample.trs
# → YES / 「Innermost Terminating (hence Terminating), WCR」「Knuth & Bendix」
```
`minisat`・`yices` へのシンボリックリンクは `make` が自動で張る（brew 導入済みなら成功）。

### 5.4 KoAT2 v2.1.0（整数遷移システムの複雑度解析。AProVE のバックエンド）

```bash
cd ~/dev/infra/tools/trs
curl -sL -o koat2.zst "https://github.com/aprove-developers/KoAT2-Releases/releases/download/v2.1.0/koat2_static.zst"
zstd -d -f koat2.zst -o koat2 && chmod +x koat2 && ./koat2 --help
```

### 5.5 CoFloCo（書き換え/整数プログラムの複雑度解析）

```bash
cd ~/dev/infra/tools/trs
git clone --depth 1 https://github.com/aeflores/CoFloCo.git
# 実行には SWI-Prolog が必要（未導入。必要になったら brew install swi-prolog）
```

### 5.6 NaTT（名古屋・SMT ベースの停止性証明器）— **入力形式に注意**

```bash
brew install z3                            # SMT バックエンド（必須。4.16.0 が入る）
cd ~/dev/infra/tools/trs
git clone --depth 1 https://github.com/akihisayamada/NaTT.git
opam install -y ocamlgraph xml-light       # 他に unix, str, re が必要（re は既存）
eval $(opam env) && cd NaTT && make        # bin/NaTT.exe が生成される（数分）
```

**⚠️ 2つの罠**:

1. **`bin/NaTT.sh`（ラッパー）は動かない。** ARI 形式を XTC XML に変換するために
   `bin/txtr-0.jar` を呼ぶが、**この jar はリポジトリに含まれていない**
   （別プロジェクト `AkihisaYamada/TXtruct` v1.0.0 が実体だがリリース資産が無く要ビルド）。
   → **`bin/NaTT.exe` に XTC XML を直接渡せば動く。**
2. **XML には `<signature>` が必須。** 省くと
   `expecting <signature> but encountered </trs>` で落ちる。

疎通確認に使った最小の入力（`f(s(x)) -> f(x)` の停止性）:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<problem type="termination"><trs><rules>
<rule><lhs><funapp><name>f</name><arg><funapp><name>s</name><arg><var>x</var></arg></funapp></arg></funapp></lhs>
<rhs><funapp><name>f</name><arg><var>x</var></arg></funapp></rhs></rule>
</rules><signature><funcsym><name>f</name><arity>1</arity></funcsym><funcsym><name>s</name><arity>1</arity></funcsym></signature></trs><strategy>FULL</strategy></problem>
```

```bash
./bin/NaTT.exe input.xml
# → Direct Order(PosReal,>,Poly) ... removes: 1
#    s(x1) weight: (/ 1 4) + x1 / f(x1) weight: 2 * x1
#    YES
```

（バイナリの自称は `NaTT ver.2.2`、リポジトリのタグは `ver.2.3.3`。）

### 5.7 **入手できなかったもの**（ネットワーク/サイト側の問題）

| ツール | 状況 |
|---|---|
| **CSI**（合流性、v1.2.5 / 2021） | 説明ページは生存（`cl-informatik.uibk.ac.at/research/software/csi`）だが、**バイナリの実体は `cl-informatik-old.uibk.ac.at` と `colo6-c703.uibk.ac.at` にあり、本機から到達不能**（curl 000＝DNS/接続失敗） |
| **TTT2**（停止性） | 旧 URL は **404**、代替ホスト `colo6-c703.uibk.ac.at/ttt2/` も到達不能 |
| **mkbTT**（Knuth–Bendix 完備化） | 同上（404） |
| **KBCV** | 公式ソフトウェア一覧に**掲載されていない**（配布終了と思われる） |
| **CoCoWeb** | `cocoweb.uibk.ac.at` に到達不能 |
| **TcT**（複雑度） | GitHub にリリース無し。Haskell stack でのソースビルドが必要（未実施） |
| **txtr / TXtruct** | NaTT のラッパーが要求する jar。`AkihisaYamada/TXtruct` v1.0.0 にリリース資産が無く要ビルド（未実施）。**NaTT.exe に XML を直接渡せば回避できる** |

→ **CSI / TTT2 は Innsbruck 側のホスト移行で実質入手困難な状態。**
必要なら CoCo の参加者ページや著者への直接連絡（`csi@informatik.uibk.ac.at`）が確実。
**なお合流性は ACP で、停止性は AProVE と NaTT で代替できるので、当面の支障は無い。**

---

## 6. まとめ: 何がどこにあるか

| 用途 | ツール | 場所 |
|---|---|---|
| 最適化＋最適性証明 | CP-SAT | `.venv/`（リポジトリ内） |
| SAT（証明ログ可） | CaDiCaL, Kissat | brew |
| ASP | clingo | brew |
| ZDD | graphillion | `.venv/` |
| IC3/PDR | ABC | `~/dev/infra/tools/abc/abc` |
| 有限モデル発見 | Alloy, TLA+ | `~/dev/infra/tools/*.jar` |
| グラフ同型 | nauty | brew（`geng`,`directg`,`labelg`,`shortg`） |
| **TRS 証明書検証** | **CeTA 3.9** | `~/dev/infra/tools/trs/ceta` |
| **TRS 停止性** | **AProVE**, NaTT | `~/dev/infra/tools/trs/aprove.jar`, `.../NaTT/bin/NaTT.exe` |
| SMT | z3 4.16.0 | brew（NaTT のバックエンド） |
| **TRS 合流性** | **ACP v0.74** | `~/dev/infra/tools/trs/acp-v0.74/work/acp/` |
| rewriting logic | Maude 3.5.1 | `~/dev/infra/tools/trs/maude/maude` |
| 複雑度解析 | KoAT2, CoFloCo | `~/dev/infra/tools/trs/` |
| SMT/SAT 補助 | minisat, yices2 | brew |
