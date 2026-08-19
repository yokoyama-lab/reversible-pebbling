# `nohup … &` の背景ジョブは、後続のツール呼び出しがタイムアウトすると道連れに死ぬ

2026-08-18、Q11 の作業中に `nohup ./desc_time.sh &`・`nohup ./runcp.sh &` で起動した
cadical / CP-SAT の掃引が、**別の**前景コマンド（`lake build`、2 分でタイムアウト）が
打ち切られた瞬間に消えた（出力ファイルは 0 バイトのまま、`ps` にも居ない）。
`earlyoom` の kill 記録は無い。同時刻に **`runcap`（systemd-run のスコープ）で起動した
`cadical` は生き残っていた**（`systemctl --user list-units --type=scope` で確認）。

**教訓**: セッションをまたいで生かす背景ジョブは `nohup` ではなく `runcap`（＝ systemd の
スコープ）に置く。`nohup` は SIGHUP を無視するだけで、プロセスグループごとの SIGKILL には
無力。`verify-build` スキルの「素で起動しない」はこの意味でも正しい。

- 起動の型: `(setsid nohup runcap -m 8 -t 7200 -n <名前> -- <cmd> > log 2>&1 &)`
- 生死の確認: `systemctl --user list-units --type=scope | grep <名前>`
  （`ps aux | grep` はスコープ内のプロセスを見落とすことがあった。unit を見る）
- 5 分程度で終わるもの（今回の `recheck.sh`）は `nohup` でも生き残ったが、運に頼らない
