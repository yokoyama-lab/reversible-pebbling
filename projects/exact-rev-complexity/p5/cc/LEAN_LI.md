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
- [x] 3. 道 ≥ 鎖（Knill の `≥` の向き．2026-10-28，ユーザーの依頼「1 の紙の証明を Lean にして」）:
  `lean/Revgarbage/P5TreeKnill.lean`．10-27 には「非公開のリポに依存するのでつながない」としていたが，
  非公開の `reversible-pebbling-lean`（0d3feab）の `HpkResolved.gameF_recursion_ge_final`（最適な手順を Knill の 3 つに切る）が
  P5 と同じペブル数の意味（配置の大きさの最大．番号のずれは `rowIter` の添字だけで，`gameF`・`ReachIn` には無い）で証明済みだったので，それを使った．
  - `Fc_succ_le`（ペブルが増えても `Fc` は増えない），`Fc_le_of_reachIn`（鎖のゲームの手順は `Fc` 以上．`(S, n)` の帰納法．
    切った下側・上側も手順であることは `RowExact.reachIn_lower_suffix`，`reachIn_upper`）
  - `path_reachIn`（P5 の道の手順を鎖のゲームの手順に写す．頂点 `L.reverse[j]` をマス `j` に．同じペブル数・同じ手数以下）
  - `path_Fc_le`，`RootedTree.caterpillar_Fc_le`（毛虫型の木で `Fc |T| k ≤ n`．M(T,k) ≥ F_c(|T|,k)）
  - 公理は標準 3 つのみ（RevPebbling 側の閉包も）．変異 7 種（手数 t−1，単調性の向き，n ≥ 1 を外す，木のペブル数を k+1，
    道の鎖の仮定を外す，Nodup を外す，手数 n−1）は赤．照合 `P5TreeKnillTests.lean`（native_decide）: Fc(4,3)=9，Fc(8,4)=25，
    Fc(12,5)=39，Fc(16,5)=71，Fc(5,5)=9 は鎖のリポが BFS の値と照合した点と一致．3 頂点の道は 2 個では終えられないことを定理から導いた．
  - 検査: `revgarbage` の lakefile は RevPebbling に依存しないので `Revgarbage.lean` には登録していない（`lake build` はこのファイルに触れない）．
    両リポを `git archive`（exact-rev-complexity 4ab7976，reversible-pebbling-lean 0d3feab）で scratch に出し，Mathlib（両リポ fabf563a7c95）の
    olean と同じ `LEAN_PATH` に並べて `lean --root=. -o` を依存の順に走らせた（RevPebbling は RowExact の閉包 36 モジュール）．
  - 独立ゲート: `/work/tmp/claude-1000/p5gate4/GATE_REPORT.md`（結果は下に追記）．
  - **公開の制約**: 公開用 tree-pebbling-lean にこのファイルを入れるには RevPebbling の RowExact の閉包（36 モジュール）も要る．
    鎖のリポを公開するか，閉包を写すかは未決（ユーザー判断）．
- 原稿: Overleaf fdfb4dc（6 節 (3) を「帰着は層: 紙の証明，後者は層: 定理証明系」に．4 頁に収めるため Lee らの証明確認の注と「ほとんどの点が等号」を削った）．ポスターは［紙］→［Lean］（道の値は Knill の定理）．
- 公開用 tree-pebbling-lean: Leaf.lean・Caterpillar.lean（c4ca3a6，26a577a）．全モジュールを素の状態から型検査，CheckAxioms 25 文が標準 3 公理のみ．
- 台帳: R-Q14-03（層 1．topic-mining ba101c9，未 push）．
- 未 push: exact-rev-complexity の f2eccc8，f2b5bf4，dc4f2a3 と本記録のコミット，topic-mining ba101c9（push は確認待ち）．

## 残り（締切後の候補）
- 3'. P5TreeKnill.lean の公開の形（鎖のリポの公開か，RowExact の閉包を tree-pebbling-lean へ写すか）．
- 4（予想 CC の 2 本の鎖への帰着．PROOF.md §3 の補題 L と定理 R）の Lean 化．

