//! 消去つき商木 BFS の Rust 実装（2026-08-13）。
//!
//! # なぜ書き直したか（実測）
//!
//! Python 版 `scripts/treedp_erase.py` は **1 エントリ 7,273 バイト**を使っていた
//! （m=6 の実測: 941,388 エントリの近傍キャッシュ + `best: dict` で peak 6.38GB）。
//! m=7 は shape 数が約 13 倍（1.3e7 → 推定 1.5〜2e8）で、**30GB でも足りず打ち切られた**。
//!
//! ここでの対策は 3 つ:
//!   1. **状態を 1 ビットで持つ**（`(shape_id, u)` の訪問済みフラグ）。`e` は小さいので
//!      `(e+1)` 本のビット配列で足りる
//!   2. **最上位の近傍をキャッシュしない**（Python 版と同じ方針だが、
//!      Python では下位のキャッシュだけで GB 級になっていた）
//!   3. shape id を `u32`、キーを `u64` にして intern する
//!
//! # 正しさの担保（**これを通さない限り数値を使わない**）
//!
//! `--verify` で Python 版と同じ既知値を再現するか検査する:
//!   - `S̄min(2..6) = [3,5,6,7,8]`（e=0 で解ける最小 p）
//!   - `Bt(6)@(p=7,e=1)` と `(p=7,e=2)` は到達不能、`(p=7,e=3)` は到達可能
//!   - `Bt(7)@(p=8,e=1)` と `(p=8,e=2)` は到達不能、`(p=8,e=3)` は到達可能
//!
//! # 表現（Python 版と同一。ここがずれると全部無駄になる）
//!
//! 高さ 0: `b ∈ {0,1}`。高さ k: `(b, i, j)` で `i ≤ j`（兄弟入れ替えの商）。
//! パックは `b | (i << 1) | (j << 33)`（Python の `_SHIFT=36` に対し、
//! ここでは u64 に収めるため 32 ビット。**id が 2^31 を超えたら assert で落とす**）。

use std::collections::HashMap;
use std::collections::VecDeque;
use std::env;

const SHIFT: u32 = 32;

struct Quotient {
    m: usize,
    /// 高さごとの key（intern 済み）
    keys: Vec<Vec<u64>>,
    /// 高さごとの popcount
    pc: Vec<Vec<u32>>,
    /// 高さごとの root ビット
    rb: Vec<Vec<u8>>,
    /// key -> id
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
        // 高さ 0 は b ∈ {0,1} の 2 つ
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
        assert!(
            (id as u64) < (1u64 << SHIFT),
            "shape id が 2^{} を超えた（SHIFT を上げる）",
            SHIFT
        );
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

    /// (次 shape, 消去コスト 0|1) の列。**ピーク制約は課さない**（Python 版と同じ）。
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
            out.push((n, 0u8)); // 可逆トグル
        } else if b == 1 {
            let n = self.mk(k, 0, ci, cj);
            out.push((n, 1u8)); // 消去（子根が不揃いなのに外す）
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

/// 訪問済みを (e+1) 本のビット配列で持つ。**1 状態 1 ビット。**
struct Visited {
    bits: Vec<Vec<u64>>, // [u][word]
}

impl Visited {
    fn new(e: usize) -> Self {
        Visited {
            bits: vec![Vec::new(); e + 1],
        }
    }
    fn ensure(&mut self, u: usize, id: u32) {
        let w = (id as usize) / 64 + 1;
        if self.bits[u].len() < w {
            self.bits[u].resize(w, 0);
        }
    }
    /// 「u 以下のいずれかで既に訪問済み」なら true（消去数は少ないほど支配的）
    fn dominated(&self, u: usize, id: u32) -> bool {
        let w = (id as usize) / 64;
        let b = 1u64 << ((id as usize) % 64);
        for uu in 0..=u {
            if let Some(word) = self.bits[uu].get(w) {
                if word & b != 0 {
                    return true;
                }
            }
        }
        false
    }
    fn set(&mut self, u: usize, id: u32) {
        self.ensure(u, id);
        let w = (id as usize) / 64;
        let b = 1u64 << ((id as usize) % 64);
        self.bits[u][w] |= b;
    }
    fn count(&self) -> usize {
        self.bits
            .iter()
            .map(|v| v.iter().map(|w| w.count_ones() as usize).sum::<usize>())
            .sum()
    }
}

/// 空配置から clean（根のみ）へ、ピーク ≤ p・消去 ≤ e で到達できるか。
/// **false は全探索完了**（queue 枯渇）を意味する。
fn reach_clean(q: &mut Quotient, p: u32, e: usize, progress: bool) -> bool {
    let top = q.m;
    let start = q.empty_id(top);
    let goal = q.goal_id(top);
    let mut vis = Visited::new(e);
    vis.set(0, start);
    let mut queue: VecDeque<(u32, u8)> = VecDeque::new();
    queue.push_back((start, 0));
    let mut n_pop: u64 = 0;
    while let Some((sid, u)) = queue.pop_front() {
        if sid == goal {
            return true;
        }
        n_pop += 1;
        if progress && n_pop % 5_000_000 == 0 {
            eprintln!(
                "  … {}M pop, |visited|={:.1}M, queue={}",
                n_pop / 1_000_000,
                vis.count() as f64 / 1e6,
                queue.len()
            );
        }
        for (nsid, cost) in q.neighbors(top, sid) {
            let nu = u as usize + cost as usize;
            if nu > e {
                continue;
            }
            if q.pc[top][nsid as usize] > p {
                continue;
            }
            if vis.dominated(nu, nsid) {
                continue;
            }
            vis.set(nu, nsid);
            queue.push_back((nsid, nu as u8));
        }
    }
    false
}

/// 既知値を再現するか検査する。**これが通らない限り新しい数値を使わない。**
fn verify() -> i32 {
    let mut bad = 0;
    // S̄min(k+1) = e=0 で解ける最小 p。既知: m=1..5 で 3,5,6,7,8
    let known = [(1usize, 3u32), (2, 5), (3, 6), (4, 7), (5, 8)];
    for (m, want) in known {
        let mut got = 0;
        for p in 1..=12u32 {
            let mut q = Quotient::new(m);
            if reach_clean(&mut q, p, 0, false) {
                got = p;
                break;
            }
        }
        let ok = got == want;
        println!(
            "  pmin(m={}) = {} （既知 {}） {}",
            m,
            got,
            want,
            if ok { "○" } else { "**✗**" }
        );
        if !ok {
            bad += 1;
        }
    }
    // 消去梯子（docs/25 §8.4 で全探索確定）
    let ladder = [
        (5usize, 7u32, 1usize, false),
        (5, 7, 2, false),
        (5, 7, 3, true),
        (6, 8, 1, false),
        (6, 8, 2, false),
        (6, 8, 3, true),
    ];
    for (m, p, e, want) in ladder {
        let mut q = Quotient::new(m);
        let got = reach_clean(&mut q, p, e, false);
        let ok = got == want;
        println!(
            "  Bt({})@(p={},e={}) = {} （既知 {}） {}",
            m + 1,
            p,
            e,
            got,
            want,
            if ok { "○" } else { "**✗**" }
        );
        if !ok {
            bad += 1;
        }
    }
    if bad == 0 {
        println!("校正 OK（既知値を全て再現）");
    } else {
        println!("**校正 NG: {} 件が既知値と食い違う。数値を使ってはいけない**", bad);
    }
    bad
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && args[1] == "--verify" {
        std::process::exit(if verify() == 0 { 0 } else { 1 });
    }
    if args.len() < 4 {
        eprintln!("usage: treedp_erase <m> <p> <e> [--progress]");
        eprintln!("       treedp_erase --verify");
        std::process::exit(2);
    }
    let m: usize = args[1].parse().unwrap();
    let p: u32 = args[2].parse().unwrap();
    let e: usize = args[3].parse().unwrap();
    let progress = args.iter().any(|a| a == "--progress");
    let t0 = std::time::Instant::now();
    let mut q = Quotient::new(m);
    let r = reach_clean(&mut q, p, e, progress);
    println!(
        "Bt({}) @ p={} e={}: {}  {:.1}s",
        m + 1,
        p,
        e,
        if r { "到達可能" } else { "到達不能（全探索完了）" },
        t0.elapsed().as_secs_f64()
    );
}
