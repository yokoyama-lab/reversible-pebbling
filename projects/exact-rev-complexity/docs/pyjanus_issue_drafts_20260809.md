# PyJanus の欠陥 6 件の issue ドラフトと、`catalog.json` のずれ 2 件の方針案（2026-08-09）

前段: `data/atlas/findings_phase4.md` §0-2 / §2 / §6-4,5。

**この文書は投稿していない。** `gh issue create` は実行していない。PyJanus・
reversible-algorithms のファイルは 1 バイトも書き換えていない（再現はすべて
`git archive` で scratchpad に取り出した複製、または読み取りのみ）。

---

## 0. 再現の結果と、前段の記述の訂正

**6 件すべて再現した（6/6）。** ただし正体は前段の記述と 2 か所で違っていた。
また 6 件は互いに独立ではなく、**根本原因は 5 つ**で、そのうち 1 つが 2 件を生んでいる。

| # | 症状 | 再現 | 根本原因 |
|---|---|---|---|
| 1 | `perm2decfac_nolex.j` → `'make_p' was not declared in this scope` | ✅ | **A** 識別子中の `'` を C++ 名へ写像していない |
| 2 | `factorization.j` → `candidate 2: 'void div(int&, int&)'` | ✅ | **B** 改名対象が C++ 予約語のみで、大域スコープのライブラリ名を含まない |
| 3 | `isort2.j` → `lvalue required as left operand of assignment` | ✅ | **C** 第 1 引数が左辺値でない `push` を `<定数> = 0;` と出力 |
| 4 | `minheap_GPC2018.j` → `TypeError: 'NoneType' object is not subscriptable` | ✅ | **D** `differentialar` が配列宣言の次元を無検査で `int(d["value"])` |
| 5 | `minheap_Nohr2015.j` → 同上 | ✅ | **D**（4 と同一） |
| 6 | `isort2.j` → `KeyError: 'lval'` | ✅ | **E** `differentialar` が `push` の第 1 引数を左辺値と仮定 |

### 訂正 1: #3 の正体は `<=>` ではない

前段は「配列要素どうしの交換 `a[i] <=> a[i+1]` が左辺値でない形で出力される」と
していたが、**これは誤り**。`<=>` は `std::swap(a[i], a[i+1])` と出力され、
問題なくコンパイルされる（`perm2decfac_nolex.j` の生成物にも
`std::swap(p[i], p[p'[i]]);` が出ていて、そこは通っている）。

真の原因は `isort2.j` の手続き `min_sub` にある **`push(1,gb)` / `push(0,gb)`**。
生成される C++ は

```cpp
gb.push_back(1); 1 = 0;        // 順方向（min_sub）
gb.push_back(0); 0 = 0;        // 順方向（min_sub）
1 = gb.back(); gb.pop_back();  // 逆手続き（min_sub__inv）
0 = gb.back(); gb.pop_back();  // 逆手続き（min_sub__inv）
```

で、g++ は 4 か所すべてで `lvalue required` を出す。**順方向にも出るので、
反転（`invert`）のバグではなく `c_codegen` そのもののバグ**である。
`codegen_diff.py` が報告する行番号が逆手続き側だったため、`<=>` に見えていた。

なお `min` / `min_sub` は `main` から一度も呼ばれない。インタプリタは
そこへ到達しないので L1 も L2 も通る。C++ 生成だけが全手続きを出力するため
落ちる、という構図である。

### 訂正 2: catalog の CI は「次の push」では落ちない

§3 に詳述するが、**CI がクローンするのは PyJanus の公開既定ブランチ `main` で、
そこには未定義手続きの検査がまだ無い。** 実測で、committed の
`catalog.json` / `CATALOG.md` は `main` で再生成するとバイト一致する。
CI の catalog ジョブは**現時点で緑**であり、赤くなるのは
PyJanus の `development` が `main` へマージされたときである。

### 分け方について

指示は「コード生成 3 件で 1 本、堅牢性 3 件で 1 本」だったが、**#3 と #6 は
同一のトリガ（左辺値でない `push`）から出ている**。issue を機械的に 2 本へ
割ると、同じ 1 行の入力に対する 2 つの症状が別々の issue に散る。
そこで **issue A（C++ バックエンド、#1・#2・#3）／ issue B（harness の堅牢性、
#4・#5・#6）の 2 本という枠は保ちつつ、両方に「#3 と #6 は同根」と相互参照を
書く**構成にした。修正の担当者が別でも取りこぼさないための措置である。

### 投稿先についての重要な注意

**`yokoyama-lab/PyJanus` は public、`yokoyama-lab/reversible-algorithms` は
private。** したがって issue 本文にコーパスのパス・コード片を貼ってはいけない。
下の 2 本のドラフトは、そのために**依存ゼロの最小再現プログラム 4 本**
（`prime.j` / `div.j` / `litpush.j` / `nodim.j`）を issue 本文に埋め込む形で
書いてある。**5 本すべて公開ブランチ `main` に対して再現を確認済み**なので、
外部の読者がそのまま踏める。

### 投稿前に確認すべきこと

`jana_py/c_codegen.py` に**別セッションの未コミット変更（+78/−7）がある**
（`_jdiv`/`_jmod` ヘルパ、`fi` 条件・`from` 条件・`assert`・`delocal` の表明追加）。
上の 3 件のいずれにも触れていないので競合はしないが、**issue を立てる前に
その作業の完了を待つか、少なくとも一声かけたほうがよい**。

---

## 1. issue ドラフト A（C++ バックエンド）

> 投稿先: `yokoyama-lab/PyJanus`（対象ブランチ **`development`**）
> ラベル案: `bug`, `codegen`

### 表題

`c_codegen: three ways the emitted C++ fails to compile (primed identifiers, global-scope library-name collision, push of a non-lvalue)`

### 本文

The C++ back-end emits code that `g++` rejects for three unrelated reasons.
Each is reproducible with a self-contained Janus program of at most six lines,
against `development` **and** against `main`.

Environment: g++ 15 / glibc, `-std=c++17`, checked on 2026-08-09.

---

#### (1) An identifier containing `'` is copied verbatim into C++

The lexer explicitly admits a prime in identifiers
(`parser_jana2014.py`: `(?P<IDENT>[A-Za-z][A-Za-z0-9_']*)`), so primed names are
a language feature, not an accident. `_esc()` (`c_codegen.py:128`) only rewrites
C++ keywords, so the prime survives into the output.

```janus
procedure inc'(int x')
  x' += 1

procedure main()
  int a = 0
  call inc'(a)
```

```bash
git clone https://github.com/yokoyama-lab/PyJanus.git && cd PyJanus
PYTHONPATH=$PWD python3 coq/harness/codegen_diff.py /path/to/prime.j
```

**Expected**: `PASS` (or, at worst, an explicit `Unsupported`).
**Actual**:

```
CFAIL  prime.j: <stdin>:18:3: error: 'inc' was not declared in this scope; did you mean 'int'?
```

The generated declaration is literally `void inc'(int& x');`, which is not C++
at all — the `'` starts a character literal, so the diagnostic is far from the
cause.

**Where**: `_esc()` in `jana_py/c_codegen.py:128` (`development`). Note that
`main` has no `_esc`/`_CPP_KEYWORDS` machinery at all, so on `main` even the
`delete`-keyword case is unhandled.

**Guess at a fix** (unverified): make `_esc` total — map every character outside
`[A-Za-z0-9_]` to an escape (e.g. `'` → `_prime`, and a generic `_uXXXX`
fallback), then apply the same freshness loop that `_resolve_keyword_renames`
already uses so the rewritten name cannot collide with an existing one.
Keying the rename on the *name* (as the keyword path already does) keeps
declaration, call and inverse consistent.

---

#### (2) A procedure name that is a global-scope library name collides

```janus
procedure div(int x, int y)
  x += y

procedure main()
  int a = 1
  int b = 2
  call div(a, b)
```

**Expected**: `PASS`.
**Actual**:

```
CFAIL  div.j: <stdin>:8:6: note: candidate 2: 'void div(int&, int&)'
```

`<cstdlib>` (pulled in transitively by `<iostream>`) declares `::div` at global
scope, so the emitted `void div(int&, int&)` participates in overload
resolution against it and the call at the use site is ambiguous.

This is the same failure mode as the already-handled `procedure delete`, but the
existing defence is a **fixed keyword list** (`_CPP_KEYWORDS`,
`c_codegen.py:79`), and `div` is not a keyword — it is a library name. The list
cannot be completed by enumeration: which library names are visible at global
scope depends on the libstdc++/glibc version and on which headers the generator
emits, so a program that compiles on one toolchain can fail on another.

**Measured exposure**: of the names we could plausibly worry about, `div` is
currently the *only* one that actually collides under
`<iostream> + <utility> + <vector>` on this toolchain — `min`, `max`, `count`,
`next`, `prev`, `data`, `size`, `swap`, `sort`, `round`, `pow`, `log`, `abs`,
`y0`, `y1`, `index`, `link`, `time` and `qsort` all compile, because they live in
`std::` rather than at global scope here. **That is exactly why we think an
allowlist is the wrong shape of fix** — the set is toolchain-dependent, and the
next libstdc++ release can move a name into it.

**Guess at a fix** (unverified): stop trying to enumerate the hazard. Either
(a) emit every user procedure and variable inside a generated
`namespace jana_user { ... }` and qualify the call sites, or (b) prefix every
emitted user identifier unconditionally (`j_div`). (a) keeps the output readable
and is a strictly local change to `format_program`; (b) is simpler but makes the
generated code diverge from the source names, which hurts the differential
harness's readability.

---

#### (3) `push` of a non-lvalue emits an assignment to a literal

```janus
procedure main()
  stack s = nil
  int m = 0
  push(1, s)
  pop(m, s)
  m -= 1
```

**Expected**: either `PASS`, or a clean rejection by `validate_program` (see
"the deeper question" below).
**Actual**:

```
CFAIL  litpush.j: <stdin>:8:19: error: lvalue required as left operand of assignment
```

`c_codegen.py:501`:

```python
if isinstance(stmt, PushStmt):
    val = format_expr(stmt.expr)
    return [f"{pad}{_esc(stmt.ident.name)}.push_back({val}); {val} = 0;"]
```

`{val} = 0` assumes `stmt.expr` is an lvalue. For `push(1, s)` it emits
`s.push_back(1); 1 = 0;`. `PopStmt` (`c_codegen.py:505`) has the mirror problem
and emits `1 = s.back();`.

Note this fires in the **forward** direction too, not only in the generated
inverse — it is not an inversion bug.

**The interpreter is already asymmetric here**, which is probably where the
divergence crept in:

- `runtime.py` `PushStmt`: `if isinstance(stmt.expr, LvalExpr): ...zero the source`
  — i.e. a literal push is silently accepted and simply skips the zero-clear.
- `runtime.py` `PopStmt`: raises `"Only l-values are supported for pop"`.

and `validate_program` accepts both. So a program with `push(1, s)` passes L1,
runs under the interpreter as long as the statement is reachable-free, and only
explodes in the C++ back-end.

**The deeper question** (we do not think we should decide this for you): is
`push(<expr>, s)` with a non-lvalue argument *legal* Janus? The 2014 reference
takes a variable. If it is not legal, the right fix is in `validate_program`
(reject it, symmetrically with `pop`), and `c_codegen` merely inherits the
guarantee. If it is a deliberate dialect extension, then `c_codegen` needs a
`push_back(<expr>)` with no zero-clear, and `runtime.py`'s `pop` needs the
matching relaxation. **Either way the current state — accepted by the validator,
half-implemented by the interpreter, miscompiled by the back-end — is the one
answer that is definitely wrong.**

---

#### Scope

Across the two corpora we sweep (150 parsed Janus programs), the number of files
that contain each trigger:

| trigger | files |
|---|--:|
| identifier that is not a valid C++ identifier | 1 |
| identifier colliding with a global-scope library name | 1 (`div`) |
| `push`/`pop` with a non-lvalue first argument | **6** |

(3) is much wider than the single failing program suggests: five of the six
files do not surface today only because they are libraries with no `main`, or
because the interpreter rejects them earlier for unrelated reasons. One of them
alone yields four `lvalue required` diagnostics once compiled.

#### Cross-reference

Trigger (3) also crashes the `differentialar` harness with an unguarded
`KeyError` — see issue B, item (2).

---

## 2. issue ドラフト B（harness の堅牢性）

> 投稿先: `yokoyama-lab/PyJanus`（対象ブランチ **`development`**、`main` でも同様）
> ラベル案: `bug`, `harness`

### 表題

`coq/harness/differentialar.py: two unsupported inputs escape as raw TypeError / KeyError instead of Unsupported`

### 本文

`differentialar.check()` documents `Unsupported` as the way a program outside
the extracted core is reported, and callers catch it to record a *skip*. Two
input shapes bypass that contract and propagate a raw Python exception, which
callers must either crash on or swallow with a bare `except Exception`.

This matters more than a normal crash: a harness that raises the wrong exception
type turns **"we did not check this"** into **"this failed"** (or, with a broad
`except`, into "no problem found"). We hit exactly that confusion while
measuring a third-party corpus.

Both are reproducible against `main` and `development`.

```bash
git clone https://github.com/yokoyama-lab/PyJanus.git && cd PyJanus
cat > /tmp/repro.py <<'EOF'
import sys
sys.path.insert(0, "."); sys.path.insert(0, "coq/harness")
import differentialar
for p in sys.argv[1:]:
    try:
        print("OK", p, differentialar.check("coq/harness/driverar", p))
    except differentialar.Unsupported as e:
        print("Unsupported", p, e)
    except Exception as e:
        print("LEAK", p, type(e).__name__ + ":", e)
EOF
PYTHONPATH=$PWD python3 /tmp/repro.py /tmp/nodim.j /tmp/litpush.j
```

---

#### (1) An array declared without an explicit dimension

```janus
procedure main()
  int A[] = {1, 2, 3}
  A[0] += 1
```

**Expected**: `Unsupported`, or (better) support — the length is statically
known from the initializer.
**Actual**:

```
LEAK /tmp/nodim.j TypeError: 'NoneType' object is not subscriptable
```

```
File "coq/harness/differentialar.py", line 447, in translate
    L *= int(d["value"])
```

`int A[] = {...}` parses with `dimensions == [None]` — the length comes from the
initializer, not from a dimension expression — and the two `size(A)` resolution
loops index `d["value"]` without checking. There are two such sites:
`differentialar.py:320` (procedure-local declarations) and `:447` (main's
declarations); we only trip `:447` here, but `:320` looks identical.

**A working pattern already exists in the sibling harness**: `codegen_diff.py`'s
`_dims_of()` raises its own `_Ragged` for exactly this case:

```python
if d is None or not hasattr(d, "value"):
    raise _Ragged("array with a non-constant dimension")
```

and `codegen_diff.py` correctly reports `SKIP: array with a non-constant
dimension` for the program above. **Guess at a fix** (unverified): apply the
same guard at both `differentialar.py` sites, raising `Unsupported`. Resolving
`len(initializer)` instead would be strictly better, but the guard is the part
that is clearly correct.

---

#### (2) `push`/`pop` whose first argument is not an lvalue

```janus
procedure main()
  stack s = nil
  int m = 0
  push(1, s)
  pop(m, s)
  m -= 1
```

**Expected**: `Unsupported`.
**Actual**:

```
LEAK /tmp/litpush.j KeyError: 'lval'
```

```
File "coq/harness/differentialar.py", line 385, in stmt
    lval = s["expr"]["lval"]
```

The statement translator assumes the `push`/`pop` argument node carries an
`lval` key. For a constant argument it does not.

**Guess at a fix** (unverified): `if "lval" not in s["expr"]: raise
Unsupported("push/pop of a non-lvalue")` — but see the cross-reference: if
`validate_program` is tightened to reject this shape (issue A item (3)), the
harness inherits the guarantee and only needs the guard as defence in depth.

---

#### Cross-reference

Item (2) has the same trigger as the third C++-back-end defect in issue A.
Whoever decides whether `push(<literal>, s)` is legal Janus should fix both.

#### Scope

Across 150 parsed Janus programs in the two corpora we sweep: 2 files hit (1),
6 files contain the trigger for (2). Three of them are the programs on which we
originally observed this, so the leak rate on a real corpus is about 2%.

#### Suggestion

Consider adding a harness-level regression test that asserts the *exception
type*: for each file in a small "known-unsupported" fixture set, `check()` must
raise `Unsupported` and nothing else. `Unsupported` is raised in 23 places in
`differentialar.py`, so the contract is clearly intended — it is just not
enforced anywhere.

---

## 3. `catalog.json` のずれ 2 件 — 方針案

### 3-1. 実測でわかったこと（前段からの更新）

前段は「CI の catalog ジョブは次の push で落ちる」としていたが、**落ちない。**
scratchpad に取り出した複製で catalog を実際に 2 通り再生成して確かめた。

| `PYJANUS` に与えたもの | committed の `catalog.json` / `CATALOG.md` との差 |
|---|---|
| PyJanus **`origin/main`**（＝ CI がクローンする公開既定ブランチ） | **バイト一致（差 0）** |
| PyJanus **`development`**（手元の作業ブランチ） | `qsort/queue5e.j` と `rank/rank.j` の 2 レコードのみ `reversible` → `validate_err` |

`.github/workflows/reftest.yml` の catalog ジョブは
`git clone --depth 1 https://github.com/yokoyama-lab/PyJanus.git` を実行する。
`gh api repos/yokoyama-lab/PyJanus --jq .default_branch` は `main`。
そして未定義手続きの検査は `development` にしか無い:

```python
# origin/main  jana_py/validate.py — 名前が main かどうかしか見ていない
if isinstance(stmt, (CallStmt, UncallStmt)) and stmt.ident.name == "main":

# origin/development — 呼び先が定義済みかを見る
if isinstance(stmt, (CallStmt, UncallStmt)):
    ...
    raise JanaError(stmt.ident.pos, f"Procedure `{stmt.ident.name}' is not defined", ...)
```

**したがって赤くなる時期は「reversible-algorithms への次の push」ではなく、
「PyJanus の `development` が `main` にマージされた次に catalog ジョブが走った
とき」。** ジョブは `pull_request:` に paths フィルタが無いので、その後は
**master 宛の任意の PR で落ちる**（`.j` を 1 行も触らなくても落ちる）。
猶予は PyJanus のリリース次第で、こちら側からは制御できない。

### 3-2. 中身は本物のバグである（validator の過剰検出ではない）

| ファイル | 場所 | 内容 |
|---|---|---|
| `qsort/queue5e.j` | 53 行 | `procedure pop_front` 内の `uncall pushpush_front(...)`。`push_front` の重複打鍵。**`pop_front` はどこからも呼ばれていない** |
| `rank/rank.j` | **164 行と 169 行**（前段は 164 のみ） | `procedure rankC` の `uncall unrank(...)` と `procedure unrankC` の `call unrank(...)`。手続き `unrank` は存在せず、`unrankCC` へ改名された痕跡。**`rankC` / `unrankC` はどちらもどこからも呼ばれていない** |

どちらも「呼ばれない手続きの中の、存在しない手続きへの参照」。改名時に
呼び出し側 2 か所を直し忘れた、典型的な取り残しである。
`main` は `rankCC` / `unrankCC` しか呼ばないので、実行時には露見しない。

**前段の記述に 1 か所抜けがある: `rank.j` の壊れた参照は 2 か所（164・169）で、
164 だけ直しても `validate_err` は消えない。**

### 3-3. 選択肢と帰結

| 案 | 内容 | 帰結 |
|---|---|---|
| **(a) コーパスを直す** | `pushpush_front` → `push_front`、`unrank` → `unrankCC`（2 か所）。計 3 語 | 実測: **`catalog.json`・`CATALOG.md` はバイト一致のまま**（`reversible` → `reversible`）。CI は今も、PyJanus リリース後も緑。改名の取り残しという実在のバグが消える。ただし `rankC`/`unrankC` が `unrankCC` を呼んで**意味的に正しいか**は未検証（どこからも呼ばれないので実行では確かめられない） |
| **(b) `by_design` に落とす** | `BY_DESIGN` に 2 件追加 | `catalog.json` の 2 レコードが `reversible` → `by_design` に変わるので、**いま catalog を再生成してコミットする必要がある**。既存の `BY_DESIGN` の趣旨は「意図的に実行可能な jana2014 ではない（テンプレート・デモ・歴史的資料）」であり、**打鍵ミスは「意図的」ではない**。分類を嘘にする |
| **(c) validator を戻す** | PyJanus の未定義手続き検査を外す/警告に落とす | 全 PyJanus 利用者にとって静的検査が弱くなる。この 2 件は**本物のバグ**なので、検査を弱める理由にならない。しかも別リポジトリの CI を緑に保つために処理系の検査を弱めるのは依存の向きが逆 |
| **(d) 到達不能コードの扱いを decide する** | 「未定義手続きへの参照は、到達不能なら警告に留める」と決める | 到達可能性は一般に決定不能で、実装は保守的な近似になる。「呼ばれていない手続き」で近似するとしても、それは静的検査を諦める方向。**得られるものは 3 語の編集の回避だけで、代償が大きすぎる**。ただし副産物として「どこからも呼ばれない手続き」を lint として報告するのは独立に有用（下記） |

### 3-4. 推奨: **(a) コーパスを直す**

理由を効く順に。

1. **churn がゼロであることを実測で確かめた。** 修正後に公開 `main` の PyJanus
   で catalog を再生成すると、committed の `catalog.json` / `CATALOG.md` と
   バイト一致する。つまり **catalog を再生成してコミットする必要すらない**。
   (b) は逆に、いま再生成コミットを要求する。
2. **CI が 2 度緑になる。** 今も緑、PyJanus リリース後も緑。時限爆弾を外せる。
   (b) も外せるが、(c)(d) は PyJanus 側の作業が要るうえ検査を弱める。
3. **内容が本物のバグである。** 改名の取り残しであって設計判断ではない。
   `by_design` に入れれば、その分類が将来の読者に嘘をつく。
4. **修正が 3 語で、意味を変えない。** 該当手続きはどこからも呼ばれないので、
   実行される振る舞いは 1 ビットも変わらない。原稿 A §6 のバグ分類には
   「改名の取り残しによる、到達不能コード中の宙吊り参照」として**そのまま
   1 類として載る**（むしろ直した記録があるほうが事例として強い）。

**ただし条件を 1 つ付ける。** `rankC` / `unrankC` が `unrankCC` を呼んで意味的に
正しいかは、どこからも呼ばれない以上テストで確かめられない。したがって
**`unrank` → `unrankCC` の置換は「名前の取り残しをコンパイル可能にする最小の
措置」であって「この 2 手続きが正しいことの主張ではない」と、コミットメッセージ
に明記する。** それが嫌なら、`rankC` / `unrankC` を丸ごと削除する（どこからも
呼ばれていないので削除も無害）という選択肢もあり、こちらのほうが主張が弱くて
安全である。**先生の判断を仰ぐべきはここ 1 点だけ**: 直すか、消すか。

### 3-5. 副産物の提案（任意）

`build_catalog.py` に「`main` からも他のどの手続きからも到達しない手続き」を
報告する行を足すと、今回のような取り残しが次からは catalog 側で先に見つかる。
`queue5e.j` の `pop_front`/`pop_back`、`rank.j` の `rankC`/`unrankC` が
まさにそれで、**壊れていることに気づかれないまま残っていた理由が
「呼ばれていないから」**なので、原因に対して効く。

なお `build_catalog.py` の `check()` にはすでに
`"dialect: literal push/pop"` という理由文字列がある。つまりコーパス側は
`push(<定数>, s)` という方言の存在を知っている。issue A の item (3) で
「これは legal Janus か」を PyJanus 側に決めてもらう価値は、そこにもある。

---

## 4. 再現に使ったもの（すべて読み取り、または scratchpad 上の複製）

```
scratchpad/pyjanus-HEAD/   git archive HEAD          （development の作業木の HEAD）
scratchpad/pyjanus-main/   git archive origin/main   （CI がクローンするもの）
scratchpad/ra/             git archive HEAD          （reversible-algorithms）
scratchpad/min/{prime,div,litpush,nodim}.j           （最小再現 4 本）
```

- CFAIL 3 件は working tree・`HEAD`・`origin/main` の 3 状態すべてで再現。
- 例外漏れ 3 件は working tree・`origin/main` で再現。
- catalog の 2 通りの再生成は `scratchpad/ra`（複製）の上でのみ実行しており、
  `reversible-algorithms` 本体の `catalog.json` / `CATALOG.md` は触っていない。
- 実行はすべて `runcap -m 4000 -t 900` 以下で上限を掛けた（最大メモリ 45 MB）。
