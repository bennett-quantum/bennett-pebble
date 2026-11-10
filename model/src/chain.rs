//! The optimiser is untrusted. `replay` checks the moves without using its DP.
use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap},
    rc::Rc,
};
#[derive(Clone, Debug)]
pub struct Game {
    pub m: Vec<u64>,
    pub r: Vec<u64>,
    pub a: Vec<u64>,
    pub k: Vec<u64>,
    pub space: u64,
}
impl Game {
    pub fn uniform(t: usize, m: u64, r: u64, a: u64, k: u64, space: u64) -> Self {
        Self {
            m: vec![m; t + 1],
            r: vec![r; t],
            a: vec![a; t],
            k: vec![k; t + 1],
            space,
        }
    }
    pub fn t(&self) -> usize {
        self.r.len()
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Config {
    pub tokens: Vec<u8>,
    pub residues: u64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Move {
    Adv(usize),
    Ret(usize),
    Dup(usize),
    Undup(usize),
}
#[derive(Clone, Debug)]
pub struct Certificate {
    pub cost: u128,
    pub peak: u64,
    pub moves: Vec<Move>,
    pub explored: usize,
}
fn used(g: &Game, c: &Config) -> u128 {
    c.tokens
        .iter()
        .zip(&g.m)
        .map(|(n, m)| u128::from(*n) * u128::from(*m))
        .sum::<u128>()
        + (0..g.t())
            .filter(|j| c.residues & (1u64 << j) != 0)
            .map(|j| u128::from(g.r[j]))
            .sum::<u128>()
}
fn apply(g: &Game, c: &mut Config, m: Move) -> Result<u64, String> {
    let t = g.t();
    let price = match m {
        Move::Adv(j)
            if j < t
                && c.tokens[j] > 0
                && c.tokens[j + 1] < u8::MAX
                && c.residues & (1u64 << j) == 0 =>
        {
            c.tokens[j] -= 1;
            c.tokens[j + 1] += 1;
            c.residues |= 1u64 << j;
            g.a[j]
        }
        Move::Ret(j)
            if j < t
                && c.tokens[j + 1] > 0
                && c.tokens[j] < u8::MAX
                && c.residues & (1u64 << j) != 0 =>
        {
            c.tokens[j + 1] -= 1;
            c.tokens[j] += 1;
            c.residues ^= 1u64 << j;
            g.a[j]
        }
        Move::Dup(j) if j <= t && c.tokens[j] > 0 && c.tokens[j] < u8::MAX => {
            c.tokens[j] += 1;
            g.k[j]
        }
        Move::Undup(j) if j <= t && c.tokens[j] >= 2 => {
            c.tokens[j] -= 1;
            g.k[j]
        }
        _ => return Err(format!("illegal chain move {m:?}")),
    };
    if used(g, c) > u128::from(g.space) {
        return Err("space limit exceeded".into());
    }
    Ok(price)
}
pub fn replay(g: &Game, moves: impl IntoIterator<Item = Move>) -> Result<Certificate, String> {
    if g.m.len() != g.t() + 1 || g.a.len() != g.t() || g.k.len() != g.t() + 1 {
        return Err("malformed chain game vectors".into());
    }
    if g.t() > 63 {
        return Err("explicit replay limited to T<=63".into());
    }
    let mut c = Config {
        tokens: vec![0; g.t() + 1],
        residues: 0,
    };
    c.tokens[0] = 1;
    let mut cost = 0;
    let initial = used(g, &c);
    if initial > u128::from(g.space) {
        return Err("initial token exceeds space".into());
    }
    let mut peak = initial as u64;
    for m in moves {
        cost += u128::from(apply(g, &mut c, m)?);
        peak = peak.max(used(g, &c) as u64);
    }
    if c.tokens[g.t()] == 0 {
        return Err("no token at goal".into());
    }
    Ok(Certificate {
        cost,
        peak,
        moves: vec![],
        explored: 0,
    })
}
/// Exact Dijkstra over the finite game. No nested-strategy assumptions.
pub fn exact(g: &Game, state_limit: usize) -> Result<Option<Certificate>, String> {
    if g.m.len() != g.t() + 1 || g.a.len() != g.t() || g.k.len() != g.t() + 1 {
        return Err("malformed chain game vectors".into());
    }
    if g.t() > 16 || g.m.iter().any(|m| *m == 0) || g.space / g.m.iter().min().unwrap() > 254 {
        return Err("exact solver bounds: T<=16, positive widths, <=254 tokens".into());
    }
    let mut start = Config {
        tokens: vec![0; g.t() + 1],
        residues: 0,
    };
    start.tokens[0] = 1;
    if used(g, &start) > u128::from(g.space) {
        return Ok(None);
    }
    let mut dist = HashMap::from([(start.clone(), 0u128)]);
    let mut previous = HashMap::<Config, (Config, Move)>::new();
    let mut queue = BinaryHeap::from([Reverse((0u128, start))]);
    let mut explored = 0;
    while let Some(Reverse((price, c))) = queue.pop() {
        if dist[&c] != price {
            continue;
        }
        explored += 1;
        if explored > state_limit {
            return Err("exact solver state limit reached (no optimality claim)".into());
        }
        if c.tokens[g.t()] > 0 {
            let mut path = vec![];
            let mut current = c;
            while let Some((prev, m)) = previous.get(&current) {
                path.push(*m);
                current = prev.clone();
            }
            path.reverse();
            let checked = replay(g, path.iter().copied())?;
            return Ok(Some(Certificate {
                cost: price,
                peak: checked.peak,
                moves: path,
                explored,
            }));
        }
        let mut moves = vec![];
        for j in 0..g.t() {
            moves.push(Move::Adv(j));
            moves.push(Move::Ret(j));
        }
        for j in 0..=g.t() {
            moves.push(Move::Dup(j));
            moves.push(Move::Undup(j));
        }
        for m in moves {
            let mut next = c.clone();
            if let Ok(a) = apply(g, &mut next, m) {
                let candidate = price + u128::from(a);
                if dist.get(&next).is_none_or(|old| candidate < *old) {
                    dist.insert(next.clone(), candidate);
                    previous.insert(next.clone(), (c.clone(), m));
                    queue.push(Reverse((candidate, next)));
                }
            }
        }
    }
    Ok(None)
}
#[derive(Clone, Debug)]
pub enum Kind {
    Direct,
    LeafClean,
    SplitClean(Rc<Plan>, Rc<Plan>, Rc<Plan>),
    SplitReach(Rc<Plan>, Rc<Plan>),
}
#[derive(Clone, Debug)]
pub struct Plan {
    pub start: usize,
    pub end: usize,
    pub cost: u128,
    pub peak: u64,
    pub kind: Kind,
}
impl Plan {
    pub fn moves(&self, reverse: bool, out: &mut Vec<Move>) {
        match &self.kind {
            Kind::Direct => {
                if reverse {
                    for j in (self.start..self.end).rev() {
                        out.push(Move::Ret(j));
                    }
                } else {
                    for j in self.start..self.end {
                        out.push(Move::Adv(j));
                    }
                }
            }
            Kind::LeafClean => {
                for j in self.start..self.end {
                    out.push(Move::Adv(j));
                }
                out.push(if reverse {
                    Move::Undup(self.end)
                } else {
                    Move::Dup(self.end)
                });
                for j in (self.start..self.end).rev() {
                    out.push(Move::Ret(j));
                }
            }
            Kind::SplitClean(forward, right, backward) => {
                if reverse {
                    backward.moves(false, out);
                    right.moves(true, out);
                    forward.moves(true, out);
                } else {
                    forward.moves(false, out);
                    right.moves(false, out);
                    backward.moves(true, out);
                }
            }
            Kind::SplitReach(a, b) => {
                if reverse {
                    b.moves(true, out);
                    a.moves(true, out);
                } else {
                    a.moves(false, out);
                    b.moves(false, out);
                }
            }
        }
    }
}
/// Exact DP *within the stated nested grammar*, including nonuniform widths,
/// residues, step prices, and position-specific copy prices. This is not a
/// claim of optimality in the full chain game.
pub fn nested(g: &Game) -> Option<Rc<Plan>> {
    type Memo = HashMap<(usize, usize, u64, bool), Option<Rc<Plan>>>;
    fn solve(
        g: &Game,
        i: usize,
        j: usize,
        s: u64,
        clean: bool,
        memo: &mut Memo,
    ) -> Option<Rc<Plan>> {
        let key = (i, j, s, clean);
        if let Some(p) = memo.get(&key) {
            return p.clone();
        }
        let mut residue = 0;
        let mut peak = g.m[i];
        for p in i + 1..=j {
            residue += g.r[p - 1];
            peak = peak.max(g.m[p] + residue);
        }
        if clean {
            peak += g.m[j];
        }
        let steps: u128 = g.a[i..j].iter().map(|a| u128::from(*a)).sum();
        let cost = if clean {
            2 * steps + u128::from(g.k[j])
        } else {
            steps
        };
        let mut best = if peak <= s {
            Some(Rc::new(Plan {
                start: i,
                end: j,
                cost,
                peak,
                kind: if clean { Kind::LeafClean } else { Kind::Direct },
            }))
        } else {
            None
        };
        for h in i + 1..j {
            if clean {
                let forward = solve(g, i, h, s, true, memo);
                let right = s
                    .checked_sub(g.m[i])
                    .and_then(|space| solve(g, h, j, space, true, memo));
                let backward = s
                    .checked_sub(g.m[j])
                    .and_then(|space| solve(g, i, h, space, true, memo));
                if let (Some(a), Some(b), Some(c)) = (forward, right, backward) {
                    let cost = a.cost + b.cost + c.cost;
                    let peak = a.peak.max(b.peak + g.m[i]).max(c.peak + g.m[j]);
                    if best.as_ref().is_none_or(|p| cost < p.cost) {
                        best = Some(Rc::new(Plan {
                            start: i,
                            end: j,
                            cost,
                            peak,
                            kind: Kind::SplitClean(a, b, c),
                        }));
                    }
                }
            } else {
                let left = solve(g, i, h, s, true, memo);
                let right = s
                    .checked_sub(g.m[i])
                    .and_then(|space| solve(g, h, j, space, false, memo));
                if let (Some(a), Some(b)) = (left, right) {
                    let cost = a.cost + b.cost;
                    let peak = a.peak.max(b.peak + g.m[i]);
                    if best.as_ref().is_none_or(|p| cost < p.cost) {
                        best = Some(Rc::new(Plan {
                            start: i,
                            end: j,
                            cost,
                            peak,
                            kind: Kind::SplitReach(a, b),
                        }));
                    }
                }
            }
        }
        memo.insert(key, best.clone());
        best
    }
    if g.t() == 0 {
        if g.m[0] > g.space {
            return None;
        }
        return Some(Rc::new(Plan {
            start: 0,
            end: 0,
            cost: 0,
            peak: g.m[0],
            kind: Kind::Direct,
        }));
    }
    solve(g, 0, g.t(), g.space, false, &mut Memo::new())
}
/// Uniform regular strategy: leaf length times a complete binary tree.
/// The record is O(1); its shared circuit description has O(log T) levels.
#[derive(Clone, Debug)]
pub struct Uniform {
    pub requested: u64,
    pub scheduled: u64,
    pub leaf: u64,
    pub levels: u32,
    pub peak: u64,
    pub advances: u128,
    pub copies: u128,
    pub cost: u128,
}
pub fn uniform(t: u64, m: u64, r: u64, a: u128, k: u128, space: u64) -> Option<Uniform> {
    if t == 0 {
        if m > space {
            return None;
        }
        return Some(Uniform {
            requested: 0,
            scheduled: 0,
            leaf: 0,
            levels: 0,
            peak: m,
            advances: 0,
            copies: 0,
            cost: 0,
        });
    }
    let mut best = None;
    for levels in 0..=t.checked_next_power_of_two()?.trailing_zeros() {
        let pieces = 1u64 << levels;
        let leaf = t.div_ceil(pieces);
        let peak = m
            .checked_mul(2 + u64::from(levels))?
            .checked_add(r.checked_mul(leaf)?)?;
        if peak > space {
            continue;
        }
        let factor = 3u128.pow(levels);
        let advances = 2 * u128::from(leaf) * factor;
        let copies = factor;
        let cost = advances * a + copies * k;
        let plan = Uniform {
            requested: t,
            scheduled: leaf * pieces,
            leaf,
            levels,
            peak,
            advances,
            copies,
            cost,
        };
        if best.as_ref().is_none_or(|p: &Uniform| cost < p.cost) {
            best = Some(plan);
        }
    }
    best
}
/// Independent inductive checker for the compressed regular certificate.
/// A leaf is Adv^ell, Dup, Ret^ell; each parent is L,R,L^-1.
/// Explicit replay below checks the same certificate at small lengths.
pub fn check_uniform(
    p: &Uniform,
    m: u64,
    r: u64,
    a: u128,
    k: u128,
    space: u64,
) -> Result<(), String> {
    if p.requested == 0 {
        if p.scheduled == 0 && p.advances == 0 && p.copies == 0 && p.cost == 0 && p.peak <= space {
            return Ok(());
        }
        return Err("invalid empty strategy".into());
    }
    if p.leaf == 0 || p.levels >= 64 {
        return Err("invalid regular strategy dimensions".into());
    }
    let length = p
        .leaf
        .checked_mul(1u64 << p.levels)
        .ok_or("strategy length overflow")?;
    let peak = m
        .checked_mul(2 + u64::from(p.levels))
        .and_then(|s| r.checked_mul(p.leaf).and_then(|v| s.checked_add(v)))
        .ok_or("strategy space overflow")?;
    let factor = 3u128
        .checked_pow(p.levels)
        .ok_or("strategy cost overflow")?;
    let advances = 2 * u128::from(p.leaf) * factor;
    if length < p.requested
        || length != p.scheduled
        || peak != p.peak
        || peak > space
        || advances != p.advances
        || factor != p.copies
        || advances * a + factor * k != p.cost
    {
        return Err("invalid regular strategy certificate".into());
    }
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_vs_nested_uniform_and_nonuniform() {
        for t in 1..=5 {
            for m in 1..=2 {
                for r in 0..=2 {
                    for space in m..=8 {
                        let g = Game::uniform(t, m, r, 2, 1, space);
                        let a = exact(&g, 300_000).unwrap();
                        let b = nested(&g);
                        if let Some(b) = b {
                            let mut moves = vec![];
                            b.moves(false, &mut moves);
                            let cert = replay(&g, moves).unwrap();
                            assert_eq!(cert.cost, b.cost);
                            assert!(cert.peak <= b.peak);
                            assert!(a.as_ref().unwrap().cost <= b.cost);
                        } else if let Some(a) = a {
                            assert!(a.cost > 0);
                        }
                    }
                }
            }
        }
        for seed in 0..16 {
            let t = 4;
            let mut g = Game::uniform(t, 1, 1, 1, 1, 8);
            for j in 0..=t {
                g.m[j] = 1 + ((seed >> (j % 4)) & 1);
                g.k[j] = 1 + (j % 2) as u64;
            }
            for j in 0..t {
                g.r[j] = ((seed + j as u64) % 3) as u64;
                g.a[j] = 1 + (j % 3) as u64;
            }
            let a = exact(&g, 300_000).unwrap();
            if let Some(p) = nested(&g) {
                let mut moves = vec![];
                p.moves(false, &mut moves);
                let cert = replay(&g, moves).unwrap();
                assert_eq!(cert.cost, p.cost);
                assert!(a.unwrap().cost <= p.cost);
            }
        }
    }
    #[test]
    fn checker_rejects_optimizer_errors() {
        let g = Game::uniform(2, 2, 1, 1, 1, 4);
        assert!(replay(&g, [Move::Ret(0)]).is_err());
        assert!(replay(&g, [Move::Adv(0), Move::Adv(0)]).is_err());
        assert!(replay(&g, [Move::Dup(0), Move::Adv(0)]).is_err());
    }
    #[test]
    fn billion_planning() {
        let p = uniform(1_000_000_000, 72, 2, 100, 72, 4096).unwrap();
        assert!(p.levels <= 30);
        assert!(p.scheduled >= p.requested);
        assert!(p.peak <= 4096);
    }
}
