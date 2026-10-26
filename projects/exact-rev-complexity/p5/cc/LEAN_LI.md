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
- [x] 2. 毛虫型 → 道（2026-10-27）: `lean/Revgarbage/P5TreeCaterpillar.lean` の `caterpillar_path`（抽象形）と
  `RootedTree.caterpillar_path`．不変条件 `CatInv`（親は 1 つ，根に親なし，自己ループなし，根から全頂点に届く，葉でない子は高々 1 個）を
  余分な子の数 `excess` の強い帰納法で保つ．各段の c は「葉でない子があればそれ」を選ぶ（任意の子だと毛虫型が崩れる）．
  結論: 子が高々 1 個で `CatInv` を満たす pred'（根から全頂点を通る道）があり，`Pebbling T.children ∅ ∅ {r} k n → Pebbling pred' ∅ ∅ {r} k n`．
  公理は標準 3 つのみ．変異 3 種（cat を外す，子の数 ≤ 0，手数 n−1）は赤．
- [x] 2'. 道であること（2026-10-27．独立ゲート〔/work/tmp/claude-1000/p5gate3/GATE_REPORT.md，5 点緑，追加変異 10 種，BFS で LI 23813 組・毛虫型 16475 組に違反 0〕の
  指摘「pred' が道であることは Lean に無い」を受けて追加）: `path_list`（根から始まり全頂点を 1 回ずつ通り，前の頂点の子はちょうど次の頂点，
  最後の頂点に子なし）と，これを含めた `RootedTree.caterpillar_path_list`．公理は標準 3 つ．変異 3 種（長さ card+1，root を外す，最後に子あり）は赤．
- [—] 3. 道 = 鎖（Knill）: **Lean ではつながない**．`reversible-pebbling-lean` は PRIVATE で，ゲームの表し方（Bool の盤と legalB/execB，番号のずれ s+3）が違い，
  公開予定の tree-pebbling-lean が非公開リポに依存することになるため．紙の証明も Knill の定理を引用しているので，紙だった部分（LI と道への帰着）はすべて Lean になった．
- 原稿: Overleaf fdfb4dc（6 節 (3) を「帰着は層: 紙の証明，後者は層: 定理証明系」に．4 頁に収めるため Lee らの証明確認の注と「ほとんどの点が等号」を削った）．ポスターは［紙］→［Lean］（道の値は Knill の定理）．
- 公開用 tree-pebbling-lean: Leaf.lean・Caterpillar.lean（c4ca3a6，26a577a）．全モジュールを素の状態から型検査，CheckAxioms 25 文が標準 3 公理のみ．
- 台帳: R-Q14-03（層 1．topic-mining ba101c9，未 push）．
- 未 push: exact-rev-complexity の f2eccc8，f2b5bf4，dc4f2a3 と本記録のコミット，topic-mining ba101c9（push は確認待ち）．

## 残り（締切後の候補）
- 3. Knill の定理を P5 の定義につなぐ（鎖のリポの公開か，P5 側で M(P_n,S) ≥ F_c(n,S) を直接示す）．
- 4（予想 CC の 2 本の鎖への帰着．PROOF.md §3 の補題 L と定理 R）の Lean 化．

