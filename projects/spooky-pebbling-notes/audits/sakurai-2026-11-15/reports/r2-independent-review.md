# R2独立査読・一次文献照合
記録ID: SPOOKY-R2-INDEPENDENT-REVIEW-20261115
担当: lower_audit。対象R2: https://drive.google.com/file/d/16swDvb43jIrgrDnYeir3kFqvKVf-4gqZ/view
対象TeX SHA256 ae4214b9cce1cd011c658a6682266dee949dbd18bf1c6a3eba6e0865a637a0e8。
原稿・既存showaファイルは変更していない。<host>送信は拒否後の承認待ちを維持。

## 結論・限定
固定完全二分木 n=2^H−1、unit-cost、空→ghostなしrootOnly、W≤3n、s_H=ceil(6*2^H/H)、H≥16384でH floor(log2 H)/16≤Dopt≤3H floor(log2 H)+2Hの定理と数値に不整合は発見しなかった。一般Θ定数、任意線形work係数、実量子回路へ拡張しない。反例未発見は完全な無誤り証明ではない。世界的新規性とS評価は留保。

## R2修正指摘
1. 合法操作条件を本文に明記: computeはtarget∉Pかつ全children⊆P、uncomputeはtargetと全children⊆P。各roundのold configurationで判定、active setsは相互素。Sはold/first-phase後の和集合、ghostはWに不算入、葉は計数。
2. 中心証明の不足: 最後のroot compute後のcut、全cut pebbleと例外nonrootの削除集合Bを定義する。例外はcut非pebbleでpostCompute=postUncompute=1でない頂点。局所課金から3n+B≤W+2p+1、したがってB≤e+2s+1を導く。account_workはpre-uncomputeを省くためactual W以下。
3. good forestでは唯一C/Uの間にghostできない理由、Cchild<Cparent<Uparent<Uchildを示す。同時active-set非交差とfinal child emptyが厳密不等号に必要。深さjの滞在2j+1と累積空間の交換和、cut境界の添字を補う。Lean側にはTraceBridge/Exceptions/DepthArea/SumAreaの接続があるが、R2の短い主張だけでは紙上追試しにくい。
4. 文献をabstractのみ確認した旨は今回の本文/定理照合へ更新できる。ただし全世界の非包含を証明したとしない。
5. 独立recompile未実施という記述を更新: 独立R1は固定依存oleanを再使用しSandwich.leanのみ1回rc0。元開発者の39-module source-only clean buildとは別物。独立R1: https://drive.google.com/file/d/1od3a860iDCRXTrXfK0XGsmVMgITAZxv_/view 。標準3公理のみ、source scan sorry/admit/native_decide/axiomなし。今回の査読で追加compileは実施していない。

## 一次文献: 同種下界の含有確認
KSS https://arxiv.org/pdf/2110.08973v3
Thm4.13（印刷p15）/Cor4.24（p19）はlineの逐次下界。Defs4.14以後のbinary treeはline再帰を表す補助cost treeであり依存完全二分木の下界ではない。Thm5.5（p21）はcomplete binary treeのh+1 pebbles,O(n log n) steps上界。ghostもstepsとして扱うため本稿Wとも区別。これらから固定work並列下界の直接含意は確認されない。

KMRV https://arxiv.org/html/2510.08432v3
Cor2.11はline長ℓとbinomial条件からΩ(mℓ/s) depth。Thm2.12はℓ≥7のlineでdepth2ℓ、space約2.47logℓの上界。§2.4は有限line探索。root-leaf path制限ではglobal s≈2^H/Hが巨大で必要下界を与えず、全頂点をline化する議論は依存条件を保存しない。これらから本稿HlogH下界の含意は確認されない。

Quist–Laarman https://lmcs.episciences.org/17091/pdf
Thm3.1/3.7はPSPACE完全性。Thm3.2（29:8）は不可逆計算C space,T timeからspooky C+m space、T+(T+1)(|V|−m) timeの上界。Thm3.5（29:9）の3n+4はQBF変数に由来するspaceでありwork3nではない。§5はISCAs85有限実験、Alg9はSATのparallel scheduleの逐次化。固定完全二分木の同work下界はこれらの定理からは確認されない。キーワード不在だけを非包含根拠にしていない。

Lee–Lee–Jeong https://arxiv.org/html/2610.09434v1
§§2.2–2.3の操作・境界・union space規約と照合。§4のfinal-uncompute intervalは前駆手法。§5.3 Eq38 W≥cnL−sD/L, L=1+log* nよりW≤3nでsD≥cnL²−3nL、指定sでΩ(H(log* n)²)。これは本稿Ω(HlogH)とは異なる。上界は既存block/skeleton法の適応であり発明と誇張しない。

## 引継ぎ
上記具体定理位置と修正案をspooky_dpへ直接共有済。E3の新系は本査読対象外。原稿修正は既存担当が新コピーで行う。査読区間の開始/終了は確実な実測がないため推測しない。保存時刻だけを別記する。

保存観測UTC: 2026-11-15T19:35:16.226232+00:00
