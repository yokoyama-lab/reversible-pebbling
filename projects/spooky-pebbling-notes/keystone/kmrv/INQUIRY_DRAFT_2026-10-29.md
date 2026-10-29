# KMRV の著者への問い合わせの下書き（未送信．送るかはユーザー判断）

宛先の候補: arXiv:2510.08432 の連絡著者（論文の記載で確認すること．ここには書かない）．
目的: 表 5・6 の最適化で使った「アンシラの重み」の定義を確定し，こちらの逐次 cost の厳密値と比べられるようにする．

---

Subject: Question on the ancilla-weighted space in Tables 5–6 of arXiv:2510.08432

Dear authors,

We are studying exact sequential costs of spooky pebbling on line graphs and would like to compare them with your Regev results (Tables 5 and 6).
Appendix B says that the space of the temporary register t is included for Pebble(i) and Unpebble(i) with i ≡ 1 (mod w+1).
Could you tell us:

1. how many "pebble units" the register t counts as (for w = 2 and n = 2048 / 4096), or the exact space function used in the search;
2. whether the s in Tables 5–6 counts the output register at position ℓ (touch-and-go, as in Section 4.1 item 2) and whether position 0 is excluded as in Definition 2.8;
3. whether the weighted search code is available (the public v0.1 seems to contain only the unweighted search).

With weight 1 and touch-and-go we obtain sequential multiplication counts 10–18% below the "Per run" column, while with weight 2 our construction exceeds 500 at (ℓ, s) = (88, 5);
also Remark 4.3 (no solution for s ≤ 3) is consistent with weight 2 but not with weight 1 under our reading. We would like to make sure we read the model correctly before reporting the comparison.

Best regards,
（署名．送る場合は本人のアドレスから本人が送る）
