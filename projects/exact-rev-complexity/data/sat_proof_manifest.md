# SAT 証明ログのマニフェスト（2026-08-10）

`data/sat_findings.md` の下界の主張を裏づける証明ログの所在と検査結果。
**本体はリポジトリに入っていない**（`.gitignore` の `data/families/sat_work/` と
同じ方針。5.7MB あるため）。

- 永続化先: `<local>/proofs/exact-rev-complexity/2026-08-10-sat`（zstd 圧縮、計 1.1 MB）
- チェックサム: 同ディレクトリの `SHA256SUMS`
- 検査器: `drat-trim`（`~/dev/TOOLS.md`）

## 検査結果

**`k = M*` の行が `NOT VERIFIED` になるのは正しい。**
そちらは充足可能で空節が無く、検証すべき UNSAT 証明が存在しないため。
逆にここが VERIFIED なら符号化が壊れている。

| インスタンス | 判定 | 検査秒 | 意味 |
|---|---|---:|---|
| `chain12_p5_e0_k37` | s VERIFIED | 0.14 | **下界**: この手数では不可能 |
| `chain12_p5_e0_k39` | s NOT VERIFIED | 0.10 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain12_p5_e1_k27` | s VERIFIED | 0.19 | **下界**: この手数では不可能 |
| `chain12_p5_e1_k29` | s NOT VERIFIED | 0.12 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain4_p3_e0_k7` | s VERIFIED | 0.06 | **下界**: この手数では不可能 |
| `chain4_p3_e0_k9` | s NOT VERIFIED | 0.07 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain4_p3_e1_k5` | s VERIFIED | 0.06 | **下界**: この手数では不可能 |
| `chain4_p3_e1_k7` | s NOT VERIFIED | 0.08 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain6_p4_e0_k13` | s VERIFIED | 0.07 | **下界**: この手数では不可能 |
| `chain6_p4_e0_k15` | s NOT VERIFIED | 0.09 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain6_p4_e1_k11` | s NOT VERIFIED | 0.08 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain6_p4_e1_k9` | s VERIFIED | 0.07 | **下界**: この手数では不可能 |
| `chain8_p4_e0_k23` | s VERIFIED | 0.07 | **下界**: この手数では不可能 |
| `chain8_p4_e0_k25` | s NOT VERIFIED | 0.08 | 上界側（充足可能）。UNSAT 証明は無い |
| `chain8_p4_e1_k15` | s VERIFIED | 0.07 | **下界**: この手数では不可能 |
| `chain8_p4_e1_k17` | s NOT VERIFIED | 0.08 | 上界側（充足可能）。UNSAT 証明は無い |

**VERIFIED 8 件 / NOT VERIFIED 8 件。**
後者はすべて `k = M*`（充足可能）であることを確認すること。

## 再生成

```sh
.venv/bin/python scripts/sat_pebble.py      # CNF と DRAT を作り直す
.venv/bin/python scripts/gen_proof_manifest.py > data/sat_proof_manifest.md
```
