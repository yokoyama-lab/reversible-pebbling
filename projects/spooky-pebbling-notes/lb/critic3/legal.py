import sys
from common import load, replay_ql
for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
    mv = load(path)
    states, mx = replay_ql(mv, h, cap)
    npl = sum(1 for o, v in mv if o in ('pebble', 'unghost'))
    print(f"{path.split('/')[-1]}: h={h} 手数 {len(mv)} 最大ペブル {mx} (上限 {cap}) 置く手 {npl} 合法(QL)")
