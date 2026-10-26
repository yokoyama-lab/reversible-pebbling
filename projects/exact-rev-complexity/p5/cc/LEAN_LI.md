# 系 LI（毛虫型の木で予想 CC）の Lean 化 — 作業記録

2026-10-27 起稿（セッション winf-progress-web の続き．ユーザーの依頼「4 か 5 の簡単そうな方を示す．途中経過も保存」）．
4（予想 CC の 2 本の鎖への帰着，補題 L と定理 R）より 5（PROOF.md §4 の補題 LI と系 LI）が軽いので 5 を選んだ．

## 段取り

1. **補題 LI**（`lean/Revgarbage/P5TreeLeaf.lean`）: 一般の `pred` で，葉 t（親は u だけ）を u と u の子 c の間に差し込んだ
   `pred'` について `Pebbling pred B a b k n → Pebbling pred' B a b k n`（t ∉ a, b）．
   紙の証明は「最短の手順で，t の極大区間の最初と最後の u の手に t の手を寄せる」．Lean では最短性を使わず，
   - t の手の規則だけを変えた 1 手の関係 `TStep pl rm`（pl: 置く手に c が要る，rm: 外す手に c が要る）を作り，
   - 「t を置く手を次の u の手の直前まで遅らせる」変換 `lazy` を列の帰納法で示す（手数は増えない．保留中の t を持つ），
   - 反転してもう一度 `lazy` をかけ（外す手が直前の u の手のすぐ後ろに寄る），再び反転すると `TStep true true`＝G' で合法．
2. **毛虫型 → 道**: 各頂点の葉でない子が高々 1 個の木に LI を繰り返し，余分な子の数 Σ(|pred v|−1)⁺ を 1 ずつ減らして道にする．
   M(G,S) ≥ M(道,S)．
3. **道 = 鎖**: M(P_n,S) = F_c(n,S) は Knill の定理．Lean は `reversible-pebbling-lean` の
   `Unconditional.gameF_eq_Fpre_uncond`（Mathlib は両リポとも fabf563a7c95）．つなぐかは 1, 2 の後で決める．

## 進捗

- [x] 1. 補題 LI（2026-10-27）: `lean/Revgarbage/P5TreeLeaf.lean` の `pebbling_leafIns`．
  仮定は構造体 `LeafIns`（t ≠ c，t ∉ B，pred t = ∅，t の親は u だけ，c ∈ pred u，pred' の 3 式）．t ∈ pred u は使わない．
  `lazyPass` は `induction L generalizing` で書いた（パターン照合の再帰は `lazy` の名前が解決されず通らなかった）．
  公理は標準 3 つのみ．変異 4 種（t_par を外す，c_mem を外す，手数を n−1 にする，t ∉ a を外す）は赤．
- [ ] 2. 毛虫型 → 道
- [ ] 3. 道 = 鎖（Knill）
