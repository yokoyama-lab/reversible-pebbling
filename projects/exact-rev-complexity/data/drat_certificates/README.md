# DRAT 証明書の記録（本体は保持しない）

DRAT 本体は数十 GB になるためリポジトリにも手元にも置かない。
**ここに置くのは「何を検証したか」と「再生成に必要なもの」だけ**：
CNF 本体（小さい）・検証器の出力・DRAT の SHA-256。

DRAT を消しても、**CNF が残っていれば同じ主張を再生成できる**
（ソルバの出力はビット単位で再現しないが、UNSAT であること自体は再検証できる）。
逆に CNF を失うと何も再現できない。CNF は必ず残すこと。

## T_5, peak ≤ 7, ≤154 手（対称性破りなし）

**主張**: T_5（完全二分木・高さ5）の clean reversible pebbling は、
peak ≤ 7 では **154 手では不可能**。上界 155 と合わせて **M*(T_5) = 155**。

**これが効くのは「対称性破りの前提が要らない」ことを示す点。**
先行して `t5_k154_sym`（対称性破りあり）でも UNSAT が出ていたが、
そちらは符号化に前提が乗る。plain 版が通ったので前提が消えた。

| 項目 | 値 |
|---|---|
| CNF | `t5_k154_plain.cnf`（`oci_t5_t6_cnf_logs.tar.gz` 内、2,700,329 bytes） |
| CNF ヘッダ | `c T_5 clean reversible pebbling (heap numbering, free leaves), peak<=7, <=154 moves (noop allowed)` |
| CNF SHA-256 | `1ba8f7ce3876e2b9b83fa17e2f58291dde40fc63574e0b0c8fbdf3a537b570ef` |
| 規模 | 43,368 変数 / 170,221 節 |
| ソルバ結果 | `s UNSATISFIABLE` |
| DRAT サイズ | 14,908,865,615 bytes（13.9 GiB） |
| **DRAT SHA-256** | `281aae072a4afbc40fcdf132315061da654f9eddb241a1a3c353bf65a0236046` |
| 検証器 | drat-trim（binary mode、backward checking） |
| **検証結果** | **`s VERIFIED`**（rc=0） |
| 検証時間 | 7,266.706 秒（約 2 時間） |
| core | 134,835 / 170,221 節、28,047,364 / 150,510,188 lemma、830,439,195 解決ステップ |
| RAT lemma | **0**（＝ RUP のみ。より強い形） |
| 実行日時 | 2026-08-12 09:58（oci, UTC） |
| 実行ホスト | oci（OCI E5） |
| 検証ログ | `t5_k154_plain_verify.log` |
| DRAT 本体 | oci 版は **2026-08-18 に削除**（SHA-256 を採って破棄）。⭐ **同一ファイルが `s3:/tmp/t5_k154_plain.drat` に現存**し、sha256 が上の値と完全一致することを確認済み。`bigfile` 台帳に登録（期限 2026-12-31） |

### 再生成の手順

1. `oci_t5_t6_cnf_logs.tar.gz` から `t5_k154_plain.cnf` を取り出し、SHA-256 を照合
2. `cadical t5_k154_plain.cnf t5_k154_plain.drat`（UNSAT・DRAT 出力）
3. `drat-trim t5_k154_plain.cnf t5_k154_plain.drat`（`s VERIFIED` を確認）
4. メモリと時間: DRAT 14GB 級・drat-trim 2 時間・ディスク 40GB 以上を見込む

⚠ 再生成した DRAT の SHA-256 は上の値と**一致しない**（ソルバの探索順が非決定的）。
一致を要求するのは誤り。確かめるのは `s VERIFIED` が再び出ることのみ。

## 同時期の関連ファイル（DRAT 本体は oci の /tmp にある。未処理）

| CNF | SHA-256 | 状態 |
|---|---|---|
| `t5_k154_sym.cnf`（対称性破りあり、2,702,325 bytes） | `d1580992434192743c36d7a568a7ac910a3ee77a81d076aa6c3306d4019663f9` | **`s VERIFIED` 済み**（探索 4h06m・DRAT 16,242,933,271 bytes・核 2245万/1億5563万・6.73億 resolution・検証 **5842 秒**）。詳細は `docs/STATUS.md` の候補1 行が正本。DRAT 本体は oci に残置・未ハッシュ |
| `t6_k200.cnf`（11,511,090 bytes） | `70a3e6dcfc0a6b126e7f30d031e801b974c4490274267d0ed45b5952f04e7cb6` | **rc=124 = 時間切れ**（2026-08-12 15:16）。DRAT 4.4GB は途中まで。結論は出ていない |

⚠ `t6_k200` を「結果」と読まないこと。打ち切りであって UNSAT ではない。

## 全ホストを走査して判明した残りの DRAT（2026-08-18、`bigfile scan`）

| 場所 | サイズ | 状態 |
|---|---|---|
| `<host>:/tmp/t5_k140.drat` | 6.7GB | **`s VERIFIED`**（RAT 0・核 1229万/7191万・3.82億 resolution・検証 6577 秒）。T_5 peak≤7 の $k\le140$ が UNSAT ＝ **$M^*(T_5)\ge141$**。⚠ **k154 の結果（$\ge155$）に包含されるので不要**。破棄候補 |
| `<host>:/tmp/t6_k250.drat` | 4.4GB | **`rc=124`（55 分で打ち切り）＝未完成**。部分 DRAT は何も証明しない。破棄候補 |
| `s3:/tmp/t6_k300.drat` | 2.5GB | 同上。破棄候補 |

**したがって $M^*(T_6)=429$ に証明書は無い**（`t6_k200`・`k250`・`k300` の 3 本とも打ち切り）。
STATUS.md が層3 [機械実験] としているのは正しい。層2 に上げるには、まず
打ち切らずに完走する計算資源か符号化の改良が要る。

## ⚠ 検証の成否を終了コードで判定しない（2026-08-12 に実際に起きた）

s3 側の `verify154_plain.log` は **`rc=0` で終わっているのに `s VERIFIED` の行が無い**
（11 分で終了。oci 側の成功例は 2 時間かかっている）。再試行した
`verify_plain2.log` は `Killed` / `rc=137` ＝ **OOM**。
つまり s3 では検証は成功していない。成功したのは oci の `verify_plain3.log` だけ。

**`drat-trim` の成否は `s VERIFIED` の行があるかで判定する。`rc` は見ない。**

⚠ **この README の初版は sym を「未検証」と書いていたが誤り**（2026-08-18 訂正）。
`/tmp/k154_sym.log` に cadical の `s UNSATISFIABLE` しか残っていないのを見て
そう判断したが、drat-trim による検証は別に実施され `docs/STATUS.md` に記録されていた。
**証拠の所在を1か所しか見ずに「無い」と言わないこと。**

## この記録が生まれた経緯（再発防止のため残す）

`s VERIFIED` は 2026-08-12 09:58 に出ていたが、**2026-08-17 まで誰にも届かなかった**。
監視が Claude Code の Bash ツール内の `while true` ループで書かれており、
**ツール呼び出しが返らないので `echo` した内容がモデルに渡らなかった**ため。
同じ日の autoresearch レポートは `FAIL 行8 T_5 p=7 exact M=155: cnf/drat が無い`
と記録しており、ローカルの検証器は「証拠が無い」と言い続けていた。

**監視は Bash の無限ループで書かない。Monitor ツールか、状態をファイルに書いて
次回の run が読む形にする。**
