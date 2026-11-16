#!/usr/bin/env python3
"""Build the markdown table of the 34 PEBBLING units from paper-audits
(read-only) and the local rebuild results."""
import json
import pathlib
import re
import sys

SRC = pathlib.Path('<local>/paper-audits')
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}

GRADE = {  # from SCOPE.txt / REPORT.txt wording (sakurai's own grade); '-' = not stated
 'BEFORE-TRACE-A1': 'C', 'COMPLETION-EXACT-A1': 'B候補', 'COMPLETION-MAP-A1': 'B候補',
 'COMPLETION-ORDER-A1': 'C', 'CONSTANT-COST-SIGNATURE-A1': 'B候補', 'COST-MAP-A1': 'C',
 'EXTENSION-BEFORE-A2': 'C', 'GUARD-ASSEMBLY-A1': 'C', 'PAIRWISE-CONNECTIVITY-A2': 'B候補（既知の形式化）',
 'PATH-MAP-A1': 'C', 'SIGNATURE-COVER-CARD-A1': 'A候補', 'SIGNATURE-COVER-UNIQUE-A1': 'A候補',
 'SIGNATURE-COVER-CORE-A1': '記載なし（S ではない）', 'SIGNATURE-INVARIANT-A1': 'C', 'SIGNATURE-SWAP-STD-A1': 'C',
 'SIGNATURE-COST-A1': 'C（失敗）',
}


def short(u):
    return re.sub(r'^PEBBLING-|-20261115', '', u)


def main(results_path):
    res = json.loads(pathlib.Path(results_path).read_text())
    rows = []
    for d in sorted(SRC.glob('PEBBLING-*-20261115-A[12]')):
        if not d.is_dir():
            continue
        u = d.name
        s = short(u)
        stop = json.loads((d / 'STOP.json').read_text()) if (d / 'STOP.json').exists() else {}
        rc = stop.get('rc')
        rc_s = str(rc) if rc is not None else f"なし（{stop.get('error')}）"
        log = (d / 'lean.log').read_text() if (d / 'lean.log').exists() else ''
        axs = {}
        for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log, re.S):
            axs[m.group(1).split('.')[-1]] = [a.strip() for a in (m.group(3) or '').replace('\n', ' ').split(',') if a.strip()]
        allax = sorted(set(a for v in axs.values() for a in v))
        sorry = 'あり' if 'sorryAx' in log else ('なし' if axs else '印字なし')
        thms = ', '.join(list(axs)[:3]) + (' …' if len(axs) > 3 else '')
        r = res.get(u)
        if r is None:
            rb = '対象外（rc≠0）' if rc != 0 else '対象外（Python のみ。同一コードで再実行し一致）'
        elif r['green']:
            rb = '**緑**' + ('（Mathlib 既存ビルド使用）' if r['mathlib'] else '')
        else:
            rb = '**赤**'
        grade = GRADE.get(s, '記載なし')
        rows.append(f"| {s} | {rc_s} | {sorry} | {', '.join(allax) if allax else ('公理なし' if axs else '—')} | {grade} | {thms or '—'} | {rb} |")
    print('| 単位（試行） | rc | sorryAx | 印字された公理（和集合） | SCOPE の評価 | 主な定理 | 手元の再ビルド |')
    print('|---|---|---|---|---|---|---|')
    print('\n'.join(rows))


if __name__ == '__main__':
    main(sys.argv[1])
