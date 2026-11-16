# ループを進めるためのプロンプト集（コピペ用）

`docs/90_family_loop_protocol.md` を回すための入力を、そのまま貼れる形で置く。
**プロンプトを毎回書き直さないこと**が要点である。書き直すとループの規律
（1 反復 1 単位 1 commit・落ちたら全部捨てる）が少しずつ緩む。

3 トラック（B → A → C）の順番と切り替え規則は
`~/dev/github.com/yokoyama-lab/jones-agenda/docs/bac-agenda.md`。

---

## 1. これを使う（トラック B・現在の既定）

```
/loop <local>/dev/github.com/tetsuo-jp/exact-rev-complexity/docs/90_family_loop_protocol.md に従って 1 反復 1 単位ずつ進めて。作業ディレクトリは <local>/dev/github.com/tetsuo-jp/exact-rev-complexity、キューは docs/91_family_queue.md。合否は tools/loopcheck.sh の終了コードだけ。落ちたら変更を全部捨ててキューに理由を書く。push はしない。
```

**各句がなぜ要るか**（削ると壊れる順）:

| 句 | 無いとどうなるか |
|---|---|
| 作業ディレクトリを絶対パスで | シェルのカレントがリセットされ、**別リポジトリで gate を走らせる**（2026-08-05・U7c で実際に起きた）。**バックグラウンド起動では特に効く**: U9 で `.venv/bin/python scripts/…` と相対で書いたらプロセスが起動せず、**エラーも出ずに空振り**した。長時間の探索は必ず絶対パスで |
| キューを名指し | jones-agenda の `while-numbering-queue.md` と取り違える |
| 合否は終了コードだけ | 「だいたい通った」で残してしまう |
| 落ちたら全部捨てる | 検証されていない数値が台帳に残る |
| push はしない | 人のレビュー前に外へ出る |

**セッション固有の追記**: jones-agenda で別セッションのループが動いているなら、
末尾に「jones-agenda には別セッションのループが動いているので触らない。」を足す。
動いていないなら足さない（無用な制約になる）。

## 2. 1 反復だけ回す（ループにしない）

様子を見たいとき、あるいはトークンを使いたくないとき。

```
<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/docs/90_family_loop_protocol.md に従って 1 反復だけ進めて。キューは docs/91_family_queue.md。合否は tools/loopcheck.sh の終了コードだけ。落ちたら変更を全部捨ててキューに理由を書く。push はしない。
```

## 3. 新しいセッションで引き継ぐ

```
<local>/dev/github.com/tetsuo-jp/exact-rev-complexity で動いているループを引き継いで。docs/90_family_loop_protocol.md（手順）→ docs/91_family_queue.md（どこまで来たか）→ data/families/findings.md（何が分かったか）→ docs/22_known_facts_ledger.md の KF-23〜KF-28（何が既知と判明したか）の順に読んで、現状を 10 行以内でまとめてから次の単位に入って。
```

読む順を指定するのが肝心である。`findings.md` だけ読むと**既知性の降格
（KF-23・KF-25・KF-26・KF-28）を見落として、既に降格した主張を成果として書く**。

## 4. トラックを切り替える

切り替えてよいのは「キューに `todo` が無い」か「残りが全部 `blocked`」のときだけ
（`bac-agenda.md`）。**1 反復の中でトラックをまたがない**（commit が混ざると捨てられなくなる）。

### トラック A（Jones 最適性の機械証明・jones-agenda）

⚠️ **先に jones-agenda で動いている別セッションのループを止めること。**
同じリポジトリで 2 つ回すと commit が混ざり、あちらの失敗パス（`git checkout -- .`）が
こちらの未コミット分を巻き戻す。

```
/loop <local>/dev/github.com/yokoyama-lab/jones-agenda/docs/loop-protocol.md に従って 1 反復 1 単位ずつ進めて。ただし読むキューは docs/jones-optimality-queue.md（while-numbering-queue.md ではない）。作業ディレクトリは <local>/dev/github.com/yokoyama-lab/jones-agenda。合否は tools/loopcheck.sh の終了コードだけ。Numbering の場を増やしてはならない。push はしない。
```

### トラック C（可逆 TRS・未着手）

キューがまだ無い。**最初の 3 反復は定義を決める作業**になる（`bac-agenda.md` に
決めるべき 3 点がある）ので、ループではなく対話で始めるほうがよい。

```
<local>/dev/github.com/yokoyama-lab/jones-agenda/docs/bac-agenda.md の「トラック C を始める前に決めること」の 3 点（可逆 TRS の定義・問う命題・台帳の母集団）を順に検討して、決まったところまでで docs/ にキューの草稿を作って。gate は CeTA 3.9 になる想定。
```

## 5. 止める・棚卸しする

```
ループを止めて。ここまでの成果と、降格した主張と、未決のまま残っているものを分けて 20 行以内でまとめて。次に再開するときの推奨単位を 3 つ、費用対効果順に添えて。
```

---

## 6. 書くときに毎回効いた注意（プロンプトに足す候補）

過去の反復で**実際に効いた**もの。必要になったら上のプロンプトに 1 行足す。

- **「閉形式を思いついても、計算可能域の上限まで回してからしか書かない」**
  — `docs/00_overview.md` §2.1 の当てはめ崩壊が 5 件ある。
- **「検索が空振りしても新規性の証拠にしない」**
  — U7 は Crossref と Semantic Scholar が空振りしたあと、arXiv 全文検索 1 回で
  直撃の後続文献が 2 本出た（KF-25・KF-26）。**検索先を 1 つで諦めない。**
- **「一次資料を読んでも前方引用を辿るまで空白判定をしない」**
  — U7 は底本 2 本を精読して「木の手数は文献に無い」と書き、U7b で撤回した。
- **「打ち切りは下界の記録でもある」**
  — cap に当たった $p$ より小さい $p$ は全探索が完了しているので $p_{\min}\ge p$ が
  証明されている（`status: pmin_lb`）。`timeout` として捨てると情報が消える。
- **「長い計算は 1 行ごとに書き出す。まとめて最後に書かない」**
  — U9 で 50 分の走行が全体の `timeout` に当たり結果を丸ごと失った。さらに
  `... | tail` に通していたためパイプの終了コードが `tail` のものになり、
  **強制終了が exit 0 に見えた**。パイプを挟まずログへ直接書くこと。
- **「cap は安全側に小さく取らず、実際に走らせて決める」**
  — `STATE_CAP` 4M は前線をわずかに手前で切っていた（U6・14M で 19 秒で解けた）。
