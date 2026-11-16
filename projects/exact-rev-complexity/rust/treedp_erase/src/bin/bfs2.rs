//! 消去つき商木 BFS — **捨てる状態を intern しない**版（2026-08-13）。
//!
//! # 何を変えたか
//!
//! `main.rs` の `neighbors` は、**ピーク制約で即座に捨てる近傍まで intern していた**。
//!
//! ```text
//! for (nsid, cost) in q.neighbors(top, sid) {   // ← ここで既に intern 済み
//!     if q.pc[top][nsid] > p { continue; }      // ← 捨てるのに表に残る
//! ```
//!
//! 最上位（k=m）の shape が状態空間そのものなので、**捨てる分だけ intern 表・
//! keys/pc/rb ベクタが太る**。ここでは最上位だけ「intern せずに popcount を先に計算」する:
//!
//! ```text
//! pc(b, ci, cj) = b + pc[m-1][ci] + pc[m-1][cj]     // id が無くても計算できる
//! ```
//!
//! 下位（k<m）は状態数が桁違いに小さく（m=6 で 1.3e7）、共有もされるので intern したまま。
//!
//! # 期待
//!
//! `m=7` は `main.rs` で **24分47秒・31.7GB** に達して打ち切られた。
//! 捨てる分が多ければここが縮む。**縮まなければこの手は無効**——測って判断する。
//!
//! # 校正
//!
//! `--verify` は `main.rs` と同一の 11 点（`S̄min(2..6)` と消去梯子 6 点）。
//! **同じ答えを出さなければ使ってはいけない。**

use std::collections::HashMap;
use std::collections::VecDeque;
use std::env;
use std::fs::{rename, File};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::Path;
use std::time::Instant;

const SHIFT: u32 = 32;

struct Quotient {
    m: usize,
    keys: Vec<Vec<u64>>,
    pc: Vec<Vec<u32>>,
    rb: Vec<Vec<u8>>,
    index: Vec<HashMap<u64, u32>>,
}

/// 最上位の候補。**まだ intern していない**（popcount だけ先に分かる）。
struct Cand {
    b: u64,
    ci: u32,
    cj: u32,
    cost: u8,
    pc: u32,
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

    /// 下位（k < m）の近傍。**main.rs と同一**（ここは intern したまま）。
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

    /// 最上位の近傍を **intern せずに** 返す。popcount は id 無しで計算できる。
    fn neighbors_top(&mut self, sid: u32) -> Vec<Cand> {
        let k = self.m;
        debug_assert!(k >= 1);
        let key = self.keys[k][sid as usize];
        let b = key & 1;
        let ci = ((key >> 1) & ((1u64 << SHIFT) - 1)) as u32;
        let cj = (key >> (1 + SHIFT)) as u32;
        let mut out = Vec::new();
        let mut push = |q: &Quotient, b: u64, i: u32, j: u32, cost: u8, out: &mut Vec<Cand>| {
            let pc = b as u32 + q.pc[k - 1][i as usize] + q.pc[k - 1][j as usize];
            out.push(Cand { b, ci: i, cj: j, cost, pc });
        };
        let both = self.rb[k - 1][ci as usize] == 1 && self.rb[k - 1][cj as usize] == 1;
        if both {
            push(self, 1 - b, ci, cj, 0, &mut out);
        } else if b == 1 {
            push(self, 0, ci, cj, 1, &mut out);
        }
        for (c2, cost) in self.neighbors(k - 1, ci) {
            push(self, b, c2, cj, cost, &mut out);
        }
        if cj != ci {
            for (c2, cost) in self.neighbors(k - 1, cj) {
                push(self, b, ci, c2, cost, &mut out);
            }
        }
        out
    }
}

struct Visited {
    bits: Vec<Vec<u64>>,
}
impl Visited {
    fn new(e: usize) -> Self {
        Visited { bits: vec![Vec::new(); e + 1] }
    }
    fn ensure(&mut self, u: usize, id: u32) {
        let w = (id as usize) / 64 + 1;
        if self.bits[u].len() < w {
            self.bits[u].resize(w, 0);
        }
    }
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
}

// ---------------- 検査点（途中から再開できるようにする） ----------------
//
// 2026-08-13: **2 時間 2 分・30.2GB まで進んだ探索を、無関係な作業で止めて全部失った。**
// ユーザーの指示「途中で復活できる形で実験して」を受けて追加。
//
// 保存するのは **keys / visited / queue の 3 つだけ**。
// `index`(HashMap) と `pc` / `rb` は keys から決定的に再構成できる（id = 挿入順）。
// これで書き出す量が 1/3 程度になる。

const CKPT_MAGIC: &[u8; 8] = b"BFS2CKP1";

fn wr_u64<W: Write>(w: &mut W, v: u64) {
    w.write_all(&v.to_le_bytes()).unwrap();
}
fn rd_u64<R: Read>(r: &mut R) -> u64 {
    let mut b = [0u8; 8];
    r.read_exact(&mut b).unwrap();
    u64::from_le_bytes(b)
}

fn save_ckpt(path: &str, q: &Quotient, vis: &Visited, queue: &VecDeque<(u32, u8)>, n_pop: u64,
             p: u32, e: usize) {
    let tmp = format!("{}.tmp", path);
    {
        let f = File::create(&tmp).expect("検査点を作れない");
        let mut w = BufWriter::with_capacity(1 << 22, f);
        w.write_all(CKPT_MAGIC).unwrap();
        wr_u64(&mut w, q.m as u64);
        wr_u64(&mut w, p as u64);
        wr_u64(&mut w, e as u64);
        wr_u64(&mut w, n_pop);
        for k in 0..=q.m {
            wr_u64(&mut w, q.keys[k].len() as u64);
            for &x in &q.keys[k] { wr_u64(&mut w, x); }
        }
        wr_u64(&mut w, vis.bits.len() as u64);
        for v in &vis.bits {
            wr_u64(&mut w, v.len() as u64);
            for &x in v { wr_u64(&mut w, x); }
        }
        wr_u64(&mut w, queue.len() as u64);
        for &(id, u) in queue { wr_u64(&mut w, (id as u64) | ((u as u64) << 32)); }
        w.flush().unwrap();
    }
    // **原子的に差し替える**（書き途中で落ちても前の検査点が残る）
    rename(&tmp, path).expect("検査点を差し替えられない");
}

/// 返り値: (Quotient, Visited, queue, n_pop)。パラメータが違う検査点は拒否する。
fn load_ckpt(path: &str, p: u32, e: usize, m: usize)
    -> Option<(Quotient, Visited, VecDeque<(u32, u8)>, u64)> {
    let f = File::open(path).ok()?;
    let mut r = BufReader::with_capacity(1 << 22, f);
    let mut magic = [0u8; 8];
    r.read_exact(&mut magic).ok()?;
    if &magic != CKPT_MAGIC { eprintln!("  検査点の形式が違う。無視する"); return None; }
    let (cm, cp, ce, n_pop) = (rd_u64(&mut r) as usize, rd_u64(&mut r) as u32,
                               rd_u64(&mut r) as usize, rd_u64(&mut r));
    if (cm, cp, ce) != (m, p, e) {
        eprintln!("  **検査点のパラメータが違う (m={},p={},e={})。使わない**", cm, cp, ce);
        return None;
    }
    let mut q = Quotient::new(m);
    // keys を読み直し、intern と同じ順で pc/rb/index を再構成する
    for k in 0..=m {
        let n = rd_u64(&mut r) as usize;
        q.keys[k].clear(); q.pc[k].clear(); q.rb[k].clear(); q.index[k].clear();
        for i in 0..n {
            let key = rd_u64(&mut r);
            q.keys[k].push(key);
            if k == 0 {
                q.pc[k].push(key as u32);
                q.rb[k].push(key as u8);
            } else {
                let b = (key & 1) as u32;
                let ci = ((key >> 1) & ((1u64 << SHIFT) - 1)) as usize;
                let cj = (key >> (1 + SHIFT)) as usize;
                let pc = b + q.pc[k - 1][ci] + q.pc[k - 1][cj];
                q.pc[k].push(pc);
                q.rb[k].push(b as u8);
            }
            q.index[k].insert(key, i as u32);
        }
    }
    let nb = rd_u64(&mut r) as usize;
    let mut vis = Visited::new(if nb == 0 { 0 } else { nb - 1 });
    for u in 0..nb {
        let n = rd_u64(&mut r) as usize;
        vis.bits[u].clear();
        for _ in 0..n { vis.bits[u].push(rd_u64(&mut r)); }
    }
    let nq = rd_u64(&mut r) as usize;
    let mut queue = VecDeque::with_capacity(nq);
    for _ in 0..nq {
        let v = rd_u64(&mut r);
        queue.push_back(((v & 0xffff_ffff) as u32, (v >> 32) as u8));
    }
    Some((q, vis, queue, n_pop))
}

/// `false` は **全探索完了**（queue 枯渇）。打ち切りではない。
fn reach_clean(q: &mut Quotient, p: u32, e: usize, progress: bool,
               ckpt: Option<&str>, ckpt_secs: u64) -> bool {
    let top = q.m;
    let goal_key_m = q.m;
    let mut vis;
    let mut queue: VecDeque<(u32, u8)>;
    let mut n_pop: u64;

    // **検査点があれば再開する**（無ければ最初から）
    let resumed = ckpt.and_then(|path| {
        if Path::new(path).exists() {
            eprintln!("  検査点を読み込む: {}", path);
            let t = Instant::now();
            let r = load_ckpt(path, p, e, goal_key_m);
            if r.is_some() { eprintln!("  読み込み {:.1}s", t.elapsed().as_secs_f64()); }
            r
        } else { None }
    });
    if let Some((q2, v2, qu2, np)) = resumed {
        *q = q2; vis = v2; queue = qu2; n_pop = np;
        eprintln!("  **再開**: {}M pop 済み / queue {} / intern {}",
                  n_pop / 1_000_000, queue.len(), q.keys[top].len());
    } else {
        let start = q.empty_id(top);
        vis = Visited::new(e);
        vis.set(0, start);
        queue = VecDeque::new();
        queue.push_back((start, 0));
        n_pop = 0;
    }
    let goal = q.goal_id(top);
    let mut last_ckpt = Instant::now();
    let mut n_pruned: u64 = 0;
    let mut n_interned: u64 = 0;
    while let Some((sid, u)) = queue.pop_front() {
        if sid == goal {
            if progress {
                eprintln!("  到達。intern {} / ピーク超で捨てた {}", n_interned, n_pruned);
            }
            return true;
        }
        n_pop += 1;
        // **一定時間ごとに検査点を落とす**。書き途中で落ちても前のが残る（tmp→rename）
        if let Some(path) = ckpt {
            if n_pop % 1_000_000 == 0 && last_ckpt.elapsed().as_secs() >= ckpt_secs {
                let t = Instant::now();
                save_ckpt(path, q, &vis, &queue, n_pop, p, e);
                eprintln!("  検査点を保存（{}M pop, {:.1}s）", n_pop / 1_000_000,
                          t.elapsed().as_secs_f64());
                last_ckpt = Instant::now();
            }
        }
        if progress && n_pop % 5_000_000 == 0 {
            eprintln!(
                "  … {}M pop, intern {:.1}M, 捨てた {:.1}M（{:.0}%）, queue {:.1}M",
                n_pop / 1_000_000,
                n_interned as f64 / 1e6,
                n_pruned as f64 / 1e6,
                100.0 * n_pruned as f64 / (n_pruned + n_interned).max(1) as f64,
                queue.len() as f64 / 1e6
            );
        }
        for c in q.neighbors_top(sid) {
            let nu = u as usize + c.cost as usize;
            if nu > e {
                continue;
            }
            // **ここが本題: intern する前に捨てる**
            if c.pc > p {
                n_pruned += 1;
                continue;
            }
            let nsid = q.mk(top, c.b, c.ci, c.cj);
            n_interned += 1;
            if vis.dominated(nu, nsid) {
                continue;
            }
            vis.set(nu, nsid);
            queue.push_back((nsid, nu as u8));
        }
    }
    if progress {
        eprintln!("  全探索完了。intern {} / 捨てた {}", n_interned, n_pruned);
    }
    false
}

/// `main.rs` と同一の 11 点。**答えがずれたら使ってはいけない。**
fn verify() -> i32 {
    let mut bad = 0;
    for (m, want) in [(1usize, 3u32), (2, 5), (3, 6), (4, 7), (5, 8)] {
        let mut got = 0;
        for p in 1..=12u32 {
            let mut q = Quotient::new(m);
            if reach_clean(&mut q, p, 0, false, None, 0) {
                got = p;
                break;
            }
        }
        let ok = got == want;
        println!("  pmin(m={}) = {} （既知 {}） {}", m, got, want, if ok { "○" } else { "**✗**" });
        if !ok {
            bad += 1;
        }
    }
    for (m, p, e, want) in [
        (5usize, 7u32, 1usize, false),
        (5, 7, 2, false),
        (5, 7, 3, true),
        (6, 8, 1, false),
        (6, 8, 2, false),
        (6, 8, 3, true),
    ] {
        let mut q = Quotient::new(m);
        let got = reach_clean(&mut q, p, e, false, None, 0);
        let ok = got == want;
        println!(
            "  Bt({})@(p={},e={}) = {} （既知 {}） {}",
            m + 1, p, e, got, want, if ok { "○" } else { "**✗**" }
        );
        if !ok {
            bad += 1;
        }
    }
    if bad == 0 {
        println!("校正 OK（11 点すべて main.rs と同一）");
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
        eprintln!("usage: bfs2 <m> <p> <e> [--progress] [--ckpt <path>] [--ckpt-secs <n>]");
        eprintln!("       bfs2 --verify");
        eprintln!("  --ckpt: 検査点。**同じ path で再実行すると途中から再開する**");
        std::process::exit(2);
    }
    let m: usize = args[1].parse().unwrap();
    let p: u32 = args[2].parse().unwrap();
    let e: usize = args[3].parse().unwrap();
    let progress = args.iter().any(|a| a == "--progress");
    let ckpt = args.iter().position(|a| a == "--ckpt").and_then(|i| args.get(i + 1)).cloned();
    let ckpt_secs: u64 = args.iter().position(|a| a == "--ckpt-secs")
        .and_then(|i| args.get(i + 1)).and_then(|s| s.parse().ok()).unwrap_or(600);
    let t0 = std::time::Instant::now();
    let mut q = Quotient::new(m);
    let r = reach_clean(&mut q, p, e, progress, ckpt.as_deref(), ckpt_secs);
    println!(
        "Bt({}) @ p={} e={}: {}  {:.1}s",
        m + 1, p, e,
        if r { "到達可能" } else { "到達不能（全探索完了）" },
        t0.elapsed().as_secs_f64()
    );
}
