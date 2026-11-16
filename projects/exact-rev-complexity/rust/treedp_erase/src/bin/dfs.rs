//! 消去つき到達可能性を**メモリ定数**で判定する（2026-08-13）。
//!
//! # ❌ **使用禁止: 校正に落ちた（2026-08-13）**
//!
//! `--verify` が **900 秒で 1 件も通らない**。校正事例 `Bt(6)@(p=7,e=3)` は
//! **BFS 版なら数秒**で解けるものであり、IDDFS は桁違いに遅い。
//!
//! | | メモリ | 校正 |
//! |---|---|---|
//! | BFS（`main.rs`） | 2.16GB（m=6） | **11 点通過** |
//! | IDDFS（本ファイル） | **1MB**（狙いどおり） | **❌ 900 秒で 0 件** |
//!
//! **効かなかった理由**: この探索空間は **合流が多い**（同じ shape へ多数の経路）。
//! 訪問済み集合こそが効いていたので、それを捨てると再展開が指数的に効く。
//! 枝刈りも `u > e` と `popcount > p` しかなく弱い。
//! **IDDFS が効くのは木に近い空間**（15 パズル等）であって、ここではない。
//!
//! **このファイルの数値を使ってはならない。** 記録として残す（同じ手を再試行しないため）。
//! 次に試すなら **双方向 BFS の消去つき拡張**（§1.2）——訪問済み集合は保つが半分の深さで済む。
//!
//! # なぜ必要か（実測）
//!
//! | 実装 | m=7, p=9, e=1 |
//! |---|---|
//! | Python（dict） | 18 分で **30GB** に達し打ち切り |
//! | Rust（ビット配列） | 24 分 47 秒で **31.7GB** に達し打ち切り |
//!
//! **Rust 化で 1 状態 7,273 バイト → 1 ビットにしても足りない。**
//! 状態数そのものが多すぎるので、**訪問済み集合を持たない探索**が要る。
//!
//! # 技法（競技プログラミングの標準手法。論文には書かれない）
//!
//! **反復深化深さ優先探索（IDDFS）**。メモリは**経路長ぶんだけ**（数百バイト）。
//!
//! - 深さ上限 `d` を 1 ずつ（実際は倍々で）上げながら深さ優先探索する
//! - `d` を超えたら打ち切って戻る。**訪問済み集合を持たない**
//! - 代償: **同じ状態を何度も訪れる**（時間とメモリのトレードオフ）
//!
//! ## この問題で効く理由
//!
//! 1. **判定問題である**（「e 回の消去で到達できるか」）。最短経路は要らない
//! 2. **消去数 `u` が単調に増える**ので、`u > e` で強力に枝刈りできる
//! 3. **ピーク制約 `p`** も枝刈りになる（`popcount > p` で即座に戻る）
//! 4. 幅優先だと `visited` が爆発するが、深さ優先なら**スタックの深さだけ**
//!
//! ## 代償（正直に）
//!
//! **同じ状態を何度も展開する**ので、状態数が少ない問題では BFS より遅い。
//! **メモリで詰んだときにだけ使う。**
//!
//! # 校正
//!
//! `--verify` で BFS 版と同じ既知値を再現する。**通らなければ数値を使わない。**

use std::collections::HashMap;
use std::env;
use std::time::Instant;

const SHIFT: u32 = 32;

struct Quotient {
    m: usize,
    keys: Vec<Vec<u64>>,
    pc: Vec<Vec<u32>>,
    rb: Vec<Vec<u8>>,
    index: Vec<HashMap<u64, u32>>,
}

impl Quotient {
    fn new(m: usize) -> Self {
        let mut q = Quotient {
            m,
            keys: vec![Vec::new(); m + 1],
            pc: vec![Vec::new(); m + 1],
            rb: vec![Vec::new(); m + 1],
            index: vec![HashMap::new(); m + 1],
        };
        for b in 0u64..2 {
            q.keys[0].push(b);
            q.pc[0].push(b as u32);
            q.rb[0].push(b as u8);
            q.index[0].insert(b, b as u32);
        }
        q
    }
    fn pack(b: u64, i: u32, j: u32) -> u64 {
        let (i, j) = if i > j { (j, i) } else { (i, j) };
        b | ((i as u64) << 1) | ((j as u64) << (1 + SHIFT))
    }
    fn intern(&mut self, k: usize, key: u64) -> u32 {
        if let Some(&id) = self.index[k].get(&key) {
            return id;
        }
        let id = self.keys[k].len() as u32;
        assert!((id as u64) < (1u64 << SHIFT), "shape id が 2^{} を超えた", SHIFT);
        self.keys[k].push(key);
        if k == 0 {
            self.pc[k].push(key as u32);
            self.rb[k].push(key as u8);
        } else {
            let b = (key & 1) as u32;
            let ci = ((key >> 1) & ((1u64 << SHIFT) - 1)) as usize;
            let cj = (key >> (1 + SHIFT)) as usize;
            let pc = b + self.pc[k - 1][ci] + self.pc[k - 1][cj];
            self.pc[k].push(pc);
            self.rb[k].push(b as u8);
        }
        self.index[k].insert(key, id);
        id
    }
    fn mk(&mut self, k: usize, b: u64, i: u32, j: u32) -> u32 {
        let key = Self::pack(b, i, j);
        self.intern(k, key)
    }
    fn empty_id(&mut self, k: usize) -> u32 {
        if k == 0 {
            return 0;
        }
        let e = self.empty_id(k - 1);
        self.mk(k, 0, e, e)
    }
    fn goal_id(&mut self, k: usize) -> u32 {
        if k == 0 {
            return 1;
        }
        let e = self.empty_id(k - 1);
        self.mk(k, 1, e, e)
    }
    fn neighbors(&mut self, k: usize, sid: u32) -> Vec<(u32, u8)> {
        if k == 0 {
            return vec![(1 - sid, 0)];
        }
        let key = self.keys[k][sid as usize];
        let b = key & 1;
        let ci = ((key >> 1) & ((1u64 << SHIFT) - 1)) as u32;
        let cj = (key >> (1 + SHIFT)) as u32;
        let mut out = Vec::new();
        let both = self.rb[k - 1][ci as usize] == 1 && self.rb[k - 1][cj as usize] == 1;
        if both {
            let n = self.mk(k, 1 - b, ci, cj);
            out.push((n, 0u8));
        } else if b == 1 {
            let n = self.mk(k, 0, ci, cj);
            out.push((n, 1u8));
        }
        for (c2, cost) in self.neighbors(k - 1, ci) {
            let n = self.mk(k, b, c2, cj);
            out.push((n, cost));
        }
        if cj != ci {
            for (c2, cost) in self.neighbors(k - 1, cj) {
                let n = self.mk(k, b, ci, c2);
                out.push((n, cost));
            }
        }
        out
    }
}

/// 深さ制限つき深さ優先探索。**訪問済み集合を持たない**（メモリは経路ぶんだけ）。
/// 直前の状態へ戻る手だけは除く（2-cycle の除去。これは正しさを損なわない）。
fn dfs(
    q: &mut Quotient,
    sid: u32,
    prev: u32,
    u: usize,
    depth: usize,
    limit: usize,
    p: u32,
    e: usize,
    goal: u32,
    nodes: &mut u64,
) -> bool {
    if sid == goal {
        return true;
    }
    if depth >= limit {
        return false;
    }
    *nodes += 1;
    let top = q.m;
    for (nsid, cost) in q.neighbors(top, sid) {
        if nsid == prev {
            continue; // 直前に戻るだけの手を除く
        }
        let nu = u + cost as usize;
        if nu > e {
            continue;
        }
        if q.pc[top][nsid as usize] > p {
            continue;
        }
        if dfs(q, nsid, sid, nu, depth + 1, limit, p, e, goal, nodes) {
            return true;
        }
    }
    false
}

/// 反復深化。深さ上限を倍々で上げる。
/// **`max_depth` に達しても見つからなければ `None`（＝未確定。到達不能ではない）。**
fn iddfs(q: &mut Quotient, p: u32, e: usize, max_depth: usize, progress: bool) -> Option<bool> {
    let start = q.empty_id(q.m);
    let goal = q.goal_id(q.m);
    let mut limit = 8usize;
    while limit <= max_depth {
        let mut nodes = 0u64;
        let t0 = Instant::now();
        if dfs(q, start, u32::MAX, 0, 0, limit, p, e, goal, &mut nodes) {
            if progress {
                eprintln!("  深さ {} で到達（{} nodes, {:.1}s）", limit, nodes, t0.elapsed().as_secs_f64());
            }
            return Some(true);
        }
        if progress {
            eprintln!(
                "  深さ {} まで到達せず（{} nodes, {:.1}s）",
                limit,
                nodes,
                t0.elapsed().as_secs_f64()
            );
        }
        limit *= 2;
    }
    None // **未確定**。到達不能とは違う
}

fn verify() -> i32 {
    // BFS 版と同じ既知値。**IDDFS は「到達可能」しか確定できない**ので、
    // 到達可能な事例だけで校正する（到達不能の確定は BFS 版の役目）。
    let cases = [(5usize, 7u32, 3usize), (6, 8, 3)];
    let mut bad = 0;
    for (m, p, e) in cases {
        let mut q = Quotient::new(m);
        let r = iddfs(&mut q, p, e, 1 << 20, false);
        let ok = r == Some(true);
        println!(
            "  Bt({})@(p={},e={}) = {:?} （既知 到達可能） {}",
            m + 1,
            p,
            e,
            r,
            if ok { "○" } else { "**✗**" }
        );
        if !ok {
            bad += 1;
        }
    }
    if bad == 0 {
        println!("校正 OK");
    } else {
        println!("**校正 NG: {} 件。数値を使ってはいけない**", bad);
    }
    bad
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && args[1] == "--verify" {
        std::process::exit(if verify() == 0 { 0 } else { 1 });
    }
    if args.len() < 4 {
        eprintln!("usage: dfs <m> <p> <e> [max_depth] [--progress]");
        eprintln!("       dfs --verify");
        eprintln!("⚠ 到達可能なら確定。見つからなくても **到達不能ではなく未確定**");
        std::process::exit(2);
    }
    let m: usize = args[1].parse().unwrap();
    let p: u32 = args[2].parse().unwrap();
    let e: usize = args[3].parse().unwrap();
    let max_depth: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(1 << 22);
    let progress = args.iter().any(|a| a == "--progress");
    let t0 = Instant::now();
    let mut q = Quotient::new(m);
    match iddfs(&mut q, p, e, max_depth, progress) {
        Some(true) => println!(
            "Bt({}) @ p={} e={}: **到達可能**  {:.1}s",
            m + 1,
            p,
            e,
            t0.elapsed().as_secs_f64()
        ),
        _ => println!(
            "Bt({}) @ p={} e={}: 深さ {} までで見つからず — **未確定（到達不能ではない）**  {:.1}s",
            m + 1,
            p,
            e,
            max_depth,
            t0.elapsed().as_secs_f64()
        ),
    }
}
