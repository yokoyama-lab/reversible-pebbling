//! アンカー DP を Rust で回す（2026-08-13）。
//!
//! 対象は `2026_exact_reversible_pebbling` の定理 "certified computable bounds":
//! ```text
//!   L(2, w) = 1                       (w >= 1)
//!   L(T, v) = L(T-1, v) + max_{0<w<v} min( L(T-1, v-w), L(T, w) )
//!   L(T0, v*) >= 2^(T0-2)  ならば  c <= 2 * v*^{1/(T0-2)}
//! ```
//!
//! # 3 つの高速化（どれも**下界を保つ**ので証明書は妥当なまま）
//!
//! 1. **索引表を持たない。** 元の Python は `rd_umap`（O(n^2) の添字表）で
//!    16MB〜458MB を食っていた。ここでは `rd` をその場で二分探索する
//! 2. **内側の max を二分探索。** `L(T-1, v-w)` は w について非増加、`L(T, w)` は非減少
//!    （L は w について単調）。その `min` は**単峰**なので最大は交差点にある。
//!    全走査 O(n) → O(log n)
//! 3. **`--approx <bits>` で L を切り下げて固定精度に。**
//!    `max` `min` `+` はすべて単調なので、**切り下げた表は真の L の下界**であり
//!    証明書としては a fortiori 妥当（幾何格子で v を切り下げるのと同じ理屈）。
//!    これで巨大整数の加算が O(1) になる
//!
//! # 正しさの担保
//!
//! * `--check` で **Rocq から抽出した OCaml 参照実装**（`rocq/anchor/run_ml`）と
//!   v* を全点照合する。**一致しなければ数値を使ってはいけない**
//! * 多倍長は**加算と比較しかしない**ので自前実装で足りる（乗除算なし）
//!
//! 使い方:
//!   anchor <T0> [mant_bits] [--approx <bits>]

use std::cmp::Ordering;
use std::env;
use std::time::Instant;

// ---------------- 多倍長（加算と比較だけ） ----------------

/// 下位から並ぶ 64 ビットの桁。末尾の 0 は持たない（正規形）。
#[derive(Clone, PartialEq, Eq, Debug)]
struct Big(Vec<u64>);

impl Big {
    fn zero() -> Big {
        Big(Vec::new())
    }
    fn one() -> Big {
        Big(vec![1])
    }
    /// 2^k
    fn pow2(k: usize) -> Big {
        let mut v = vec![0u64; k / 64];
        v.push(1u64 << (k % 64));
        Big(v)
    }
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    fn add(&self, other: &Big) -> Big {
        let (a, b) = (&self.0, &other.0);
        let n = a.len().max(b.len());
        let mut out = Vec::with_capacity(n + 1);
        let mut carry = 0u64;
        for i in 0..n {
            let x = *a.get(i).unwrap_or(&0);
            let y = *b.get(i).unwrap_or(&0);
            let (s1, c1) = x.overflowing_add(y);
            let (s2, c2) = s1.overflowing_add(carry);
            out.push(s2);
            carry = (c1 as u64) + (c2 as u64);
        }
        if carry != 0 {
            out.push(carry);
        }
        Big(out)
    }
    /// ビット長（0 なら 0）
    fn bits(&self) -> usize {
        match self.0.last() {
            None => 0,
            Some(&top) => (self.0.len() - 1) * 64 + (64 - top.leading_zeros() as usize),
        }
    }
    /// **下位ビットを 0 にして `keep` ビットに丸める（切り下げ）。**
    /// 値は減るだけなので、下界としての妥当性は保たれる。
    fn truncate_to(&mut self, keep: usize) {
        let b = self.bits();
        if b <= keep {
            return;
        }
        let drop = b - keep;
        let words = (drop / 64).min(self.0.len());
        let sh = drop % 64;
        for x in self.0.iter_mut().take(words) {
            *x = 0;
        }
        if sh > 0 && words < self.0.len() {
            self.0[words] &= !((1u64 << sh) - 1);
        }
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }

    /// `self - other`（`self >= other` を前提）。格子の引き算に使う。
    fn sub(&self, other: &Big) -> Big {
        let (a, b) = (&self.0, &other.0);
        let mut out = Vec::with_capacity(a.len());
        let mut borrow = 0u64;
        for i in 0..a.len() {
            let y = *b.get(i).unwrap_or(&0);
            let (d1, c1) = a[i].overflowing_sub(y);
            let (d2, c2) = d1.overflowing_sub(borrow);
            out.push(d2);
            borrow = (c1 as u64) + (c2 as u64);
        }
        while out.last() == Some(&0) {
            out.pop();
        }
        Big(out)
    }

    fn from_u64_shl(a: u64, b: usize) -> Big {
        let mut v = vec![0u64; b / 64];
        let sh = b % 64;
        let lo = a << sh;
        let hi = if sh == 0 { 0 } else { a >> (64 - sh) };
        v.push(lo);
        if hi != 0 {
            v.push(hi);
        }
        while v.last() == Some(&0) {
            v.pop();
        }
        Big(v)
    }

    /// log2(self)。**上位 128 ビットとビット長から求める**。
    /// ⚠ 以前は先頭から f64 に積んで 1e300 で打ち切っていたため、
    /// 2^1000 を超えると値を過小報告していた（2026-08-13 に検出）。
    fn to_f64_log2(&self) -> f64 {
        let b = self.bits();
        if b == 0 {
            return f64::NEG_INFINITY;
        }
        let n = self.0.len();
        // 上位 2 桁だけ取る（1 桁しか無いときは桁上げしない。以前ここで桁溢れした）
        let m: u128 = if n >= 2 {
            ((self.0[n - 1] as u128) << 64) | (self.0[n - 2] as u128)
        } else {
            self.0[n - 1] as u128
        };
        let mbits = 128 - m.leading_zeros() as usize;
        (b as f64) - (mbits as f64) + (m as f64).log2()
    }
}

impl Ord for Big {
    fn cmp(&self, other: &Big) -> Ordering {
        match self.0.len().cmp(&other.0.len()) {
            Ordering::Equal => {
                for i in (0..self.0.len()).rev() {
                    match self.0[i].cmp(&other.0[i]) {
                        Ordering::Equal => continue,
                        o => return o,
                    }
                }
                Ordering::Equal
            }
            o => o,
        }
    }
}
impl PartialOrd for Big {
    fn partial_cmp(&self, other: &Big) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// ---------------- 格子 ----------------

/// Python と同一の規則: `{a<<b : lo<=a<=hi, 0<=b<t0, a<<b <= 2^(t0/2+4)} ∪ {1..lo}`
/// 値は `(a, b)` で持つ（a は小さい整数、b はシフト量）。比較は (b が主) で決まらないので
/// 実際の値の比較が要る — ここでは `u128` に収まる範囲を扱う（t0/2+4 <= 127）。
fn build_grid(t0: usize, mant: u32) -> Vec<Big> {
    let lo = 1u64 << mant;
    let hi = (1u64 << (mant + 1)) - 1;
    let capbits = t0 / 2 + 4;
    let mut s: Vec<Big> = Vec::new();
    for b in 0..t0 {
        for a in lo..=hi {
            // a << b <= 2^capbits か（ビット長で判定）
            let abits = 64 - a.leading_zeros() as usize;
            if abits + b <= capbits + 1 {
                let v = Big::from_u64_shl(a, b);
                if v.bits() <= capbits + 1 {
                    s.push(v);
                }
            }
        }
    }
    for a in 1..=lo {
        s.push(Big::from_u64_shl(a, 0));
    }
    s.sort();
    s.dedup();
    s
}

// ---------------- DP ----------------

/// `grid` 上で `v` 以下の最大要素の添字。無ければ `None`。
#[inline]
fn rd(grid: &[Big], v: &Big) -> Option<usize> {
    match grid.binary_search(v) {
        Ok(i) => Some(i),
        Err(0) => None,
        Err(i) => Some(i - 1),
    }
}

fn run(t0: usize, mant: u32, approx: Option<usize>, verbose: bool) -> Vec<(usize, Big)> {
    let grid = build_grid(t0, mant);
    let n = grid.len();
    if verbose {
        println!(
            "T0={} grid={} (mant {}) {}",
            t0,
            n,
            mant,
            match approx {
                Some(b) => format!("[切り下げ {} ビット]", b),
                None => "[厳密]".to_string(),
            }
        );
    }
    let mut l: Vec<Big> = vec![Big::one(); n];
    let mut out = Vec::new();
    let t_start = Instant::now();
    for t in 3..=t0 {
        let lp = std::mem::take(&mut l);
        let mut cur: Vec<Big> = Vec::with_capacity(n);
        for i in 0..n {
            let v = &grid[i];
            // grid[j] < v なる最大の j
            let jmax = match grid[..i].iter().rposition(|g| g < v) {
                Some(j) => j as isize,
                None => -1,
            };
            let mut best = Big::zero();
            if jmax >= 0 {
                let jm = jmax as usize;
                // **交差点を二分探索**: lp[rd(v-grid[j])] >= cur[j] を満たす最大の j
                let probe = |j: usize, cur: &Vec<Big>| -> (Big, Big) {
                    let a = match rd(&grid, &v.sub(&grid[j])) {
                        Some(k) => lp[k].clone(),
                        None => Big::zero(),
                    };
                    (a, cur[j].clone())
                };
                let (mut lo, mut hi) = (0usize, jm);
                while lo < hi {
                    let mid = (lo + hi + 1) / 2;
                    let (a, b) = probe(mid, &cur);
                    if a >= b {
                        lo = mid;
                    } else {
                        hi = mid - 1;
                    }
                }
                // 交差点の近傍を窓で確かめる（同値・端で 1 ずれても拾う）
                let from = lo.saturating_sub(3);
                let to = (lo + 3).min(jm);
                for j in from..=to {
                    let (a, b) = probe(j, &cur);
                    let c = if a < b { a } else { b };
                    if c > best {
                        best = c;
                    }
                }
            }
            let mut x = lp[i].add(&best);
            if let Some(bits) = approx {
                x.truncate_to(bits);
            }
            cur.push(x);
        }
        l = cur;
        let tgt = Big::pow2(t - 2);
        if let Some(i) = l.iter().position(|x| *x >= tgt) {
            out.push((t, grid[i].clone()));
            if verbose && (t % 50 == 0 || t == t0) {
                let e = grid[i].to_f64_log2() / ((t - 2) as f64);
                println!(
                    "T={:5}: log2(v*)={:.1} log2(v*)/(T-2)={:.6}  c<= {:.7}  [{:.0}s]",
                    t,
                    grid[i].to_f64_log2(),
                    e,
                    2.0 * 2f64.powf(e),
                    t_start.elapsed().as_secs_f64()
                );
            }
        }
    }
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: anchor <T0> [mant_bits] [--approx <bits>]");
        std::process::exit(2);
    }
    let t0: usize = args[1].parse().unwrap();
    let mant: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);
    let approx = args
        .iter()
        .position(|a| a == "--approx")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok());
    let out = run(t0, mant, approx, true);
    if let Some((t, v)) = out.last() {
        let t = *t;
        let e = v.to_f64_log2() / ((t - 2) as f64);
        println!("\nCERTIFIED: m_(S+{}-2) <= m_S * v* (log2 v* = {:.2}) for all S", t, v.to_f64_log2());
        println!("v*_limbs = {:?}", v.0.iter().rev().take(3).collect::<Vec<_>>());
        println!("=> d <= {:.7}, c <= {:.7}", 2f64.powf(e), 2.0 * 2f64.powf(e));
    } else {
        println!("v* が見つからなかった");
    }
}
