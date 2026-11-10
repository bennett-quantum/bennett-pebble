//! Polynomial-size Boolean evaluators, lowered exclusively to X/CX/CCX/MCX.
use crate::{
    bits::Bits,
    circuit::{self as c, Term},
};
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bit {
    Const(bool),
    Wire(usize),
}
#[derive(Clone, Default)]
pub struct Builder {
    pub gates: Vec<Term>,
    pub next: usize,
}
impl Builder {
    pub fn new(next: usize) -> Self {
        Self {
            gates: vec![],
            next,
        }
    }
    pub fn fresh(&mut self) -> usize {
        let i = self.next;
        self.next += 1;
        i
    }
    pub fn xor(&mut self, a: Bit, b: Bit) -> Bit {
        match (a, b) {
            (Bit::Const(false), b) | (b, Bit::Const(false)) => b,
            _ if a == b => Bit::Const(false),
            _ => {
                let w = self.fresh();
                self.copy(a, w);
                self.copy(b, w);
                Bit::Wire(w)
            }
        }
    }
    pub fn not(&mut self, a: Bit) -> Bit {
        self.xor(a, Bit::Const(true))
    }
    pub fn and(&mut self, a: Bit, b: Bit) -> Bit {
        match (a, b) {
            (Bit::Const(false), _) | (_, Bit::Const(false)) => Bit::Const(false),
            (Bit::Const(true), b) | (b, Bit::Const(true)) => b,
            _ if a == b => a,
            (Bit::Wire(a), Bit::Wire(b)) => {
                let w = self.fresh();
                self.gates.push(c::gate(&[a, b], w));
                Bit::Wire(w)
            }
        }
    }
    pub fn or(&mut self, a: Bit, b: Bit) -> Bit {
        let x = self.xor(a, b);
        let y = self.and(a, b);
        self.xor(x, y)
    }
    pub fn mux(&mut self, p: Bit, a: Bit, b: Bit) -> Bit {
        let x = self.xor(a, b);
        let y = self.and(p, x);
        self.xor(b, y)
    }
    pub fn copy(&mut self, a: Bit, d: usize) {
        match a {
            Bit::Const(false) => {}
            Bit::Const(true) => self.gates.push(c::gate(&[], d)),
            Bit::Wire(w) => self.gates.push(c::gate(&[w], d)),
        }
    }
    pub fn vector(&mut self, a: &[Bit], b: &[Bit], op: &str) -> Vec<Bit> {
        match op {
            "add" | "sub" => {
                let mut carry = Bit::Const(op == "sub");
                a.iter()
                    .zip(b)
                    .map(|(&a, &b)| {
                        let b = if op == "sub" { self.not(b) } else { b };
                        let x = self.xor(a, b);
                        let z = self.xor(x, carry);
                        let ab = self.and(a, b);
                        let xc = self.and(x, carry);
                        carry = self.xor(ab, xc);
                        z
                    })
                    .collect()
            }
            "and" | "or" | "xor" => a
                .iter()
                .zip(b)
                .map(|(&a, &b)| match op {
                    "and" => self.and(a, b),
                    "or" => self.or(a, b),
                    _ => self.xor(a, b),
                })
                .collect(),
            "mul" => {
                let n = a.len();
                let mut out = vec![Bit::Const(false); n];
                for (i, &bi) in b.iter().enumerate().take(n) {
                    let mut part = vec![Bit::Const(false); i];
                    part.extend(a.iter().take(n - i).map(|ai| self.and(*ai, bi)));
                    out = self.vector(&out, &part, "add");
                }
                out
            }
            "shl" | "lshr" | "ashr" => {
                let n = a.len();
                let mut out = a.to_vec();
                for (j, &bj) in b.iter().enumerate() {
                    if j >= usize::BITS as usize || (1usize << j) >= n {
                        let nb = self.not(bj);
                        for v in &mut out {
                            let z = self.and(*v, nb);
                            *v = z;
                        }
                        continue;
                    }
                    let k = 1usize << j;
                    let old = out.clone();
                    for i in 0..n {
                        let shifted = if op == "shl" {
                            if i >= k {
                                old[i - k]
                            } else {
                                Bit::Const(false)
                            }
                        } else {
                            old.get(i + k).copied().unwrap_or(if op == "ashr" {
                                old[n - 1]
                            } else {
                                Bit::Const(false)
                            })
                        };
                        out[i] = self.mux(bj, shifted, old[i]);
                    }
                }
                // For non-powers of two the low shift bits can also exceed n.
                if !n.is_power_of_two() {
                    let lim = constant(n, n as u64);
                    let valid = self.compare(b, &lim, "ult");
                    for v in &mut out {
                        *v = self.and(*v, valid);
                    }
                }
                out
            }
            _ => panic!("unknown Boolean operation {op}"),
        }
    }
    pub fn inverse_odd(&mut self, a: &[Bit], coefficient: u64) -> Vec<Bit> {
        let out: Vec<_> = (0..a.len()).map(|_| self.fresh()).collect();
        for (v, w) in a.iter().zip(&out) {
            self.copy(*v, *w);
        }
        self.gates.push(c::adj(multiply_odd(&out, coefficient)));
        out.into_iter().map(Bit::Wire).collect()
    }
    pub fn compare(&mut self, a: &[Bit], b: &[Bit], op: &str) -> Bit {
        let mut eq = Bit::Const(true);
        let mut lt = Bit::Const(false);
        for (&a, &b) in a.iter().zip(b) {
            let na = self.not(a);
            let ab = self.and(na, b);
            let diff = self.xor(a, b);
            let same = self.not(diff);
            let lower = self.and(same, lt);
            lt = self.or(ab, lower);
            eq = self.and(eq, same);
        }
        if op == "slt" || op == "sle" {
            let sa = a[a.len() - 1];
            let sb = b[b.len() - 1];
            let diff = self.xor(sa, sb);
            lt = self.mux(diff, sa, lt);
        }
        match op {
            "eq" => eq,
            "ne" => self.not(eq),
            "ult" | "slt" => lt,
            "ule" | "sle" => self.or(lt, eq),
            _ => panic!("unknown comparison"),
        }
    }
    /// XOR outputs, then reverse every temporary. Clean scratch is a precondition;
    /// the emitted gate sequence remains a permutation on arbitrary scratch.
    pub fn finish(self, external: usize, outputs: &[(usize, Bit)]) -> Term {
        let allocated = self.next - external;
        let body = c::seq(self.gates);
        let mut commit = Builder::new(self.next);
        for (d, b) in outputs {
            commit.copy(*b, *d);
        }
        c::with(
            external,
            allocated,
            c::seq(vec![body.clone(), c::seq(commit.gates), c::adj(body)]),
        )
    }
}
pub fn wires(start: usize, n: usize) -> Vec<Bit> {
    (start..start + n).map(Bit::Wire).collect()
}
pub fn constant(n: usize, x: u64) -> Vec<Bit> {
    Bits::from_u64(n, x).0.into_iter().map(Bit::Const).collect()
}
pub fn swap(a: usize, b: usize) -> Term {
    c::seq(vec![c::gate(&[a], b), c::gate(&[b], a), c::gate(&[a], b)])
}
pub fn add_inplace(a: &[usize], b: &[usize]) -> Term {
    assert_eq!(a.len(), b.len());
    let mut out = vec![];
    for (i, &ai) in a.iter().enumerate() {
        for j in ((i + 1)..b.len()).rev() {
            let controls: Vec<_> = std::iter::once(ai).chain(b[i..j].iter().copied()).collect();
            out.push(c::gate(&controls, b[j]));
        }
        out.push(c::gate(&[ai], b[i]));
    }
    c::seq(out)
}
pub fn add_constant(w: &[usize], value: u64) -> Term {
    let mut out = vec![];
    for i in 0..w.len().min(64) {
        if value & (1u64 << i) == 0 {
            continue;
        }
        for j in ((i + 1)..w.len()).rev() {
            out.push(c::gate(&w[i..j], w[j]));
        }
        out.push(c::gate(&[], w[i]));
    }
    c::seq(out)
}
/// Descending source order preserves each original control until its use.
pub fn add_shifted_self(w: &[usize], k: usize) -> Term {
    assert!(k > 0);
    let mut out = vec![];
    for i in (0..w.len().saturating_sub(k)).rev() {
        for j in ((i + k + 1)..w.len()).rev() {
            let cs: Vec<_> = std::iter::once(w[i])
                .chain(w[i + k..j].iter().copied())
                .collect();
            out.push(c::gate(&cs, w[j]));
        }
        out.push(c::gate(&[w[i]], w[i + k]));
    }
    c::seq(out)
}
/// Any odd unit can be factored into (1+2^k) factors mod 2^n, by correcting
/// its bits from low to high. Each factor is the checked shifted-self gadget.
pub fn multiply_odd(w: &[usize], value: u64) -> Term {
    multiply_odd_bits(w, &Bits::from_u64(w.len(), value))
}
pub fn multiply_odd_bits(w: &[usize], value: &Bits) -> Term {
    assert_eq!(w.len(), value.width());
    assert!(value.0[0]);
    let n = w.len();
    let mut product = Bits::from_u64(n, 1);
    let mut terms = vec![];
    for k in 1..n {
        if product.0[k] != value.0[k] {
            terms.push(add_shifted_self(w, k));
            product = product.add(&product.shift(&Bits::from_u64(64, k as u64), "shl"));
        }
    }
    c::seq(terms)
}
pub fn evaluator(n: usize, op: &str) -> Term {
    let output = 2 * n;
    let width = if ["eq", "ne", "ult", "ule", "slt", "sle"].contains(&op) {
        1
    } else {
        n
    };
    let external = output + width;
    let mut b = Builder::new(external);
    let a = wires(0, n);
    let v = wires(n, n);
    let z = if width == 1 && ["eq", "ne", "ult", "ule", "slt", "sle"].contains(&op) {
        vec![b.compare(&a, &v, op)]
    } else {
        b.vector(&a, &v, op)
    };
    b.finish(
        external,
        &z.into_iter()
            .enumerate()
            .map(|(i, z)| (output + i, z))
            .collect::<Vec<_>>(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{Simulator, cost};
    fn tuple(n: usize, x: u64) -> Vec<bool> {
        Bits::from_u64(n, x).0
    }
    #[test]
    fn all_evaluators_all_interface_states() {
        for n in 1..=3 {
            for op in [
                "add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr", "eq", "ne", "ult",
                "ule", "slt", "sle",
            ] {
                let cmp = ["eq", "ne", "ult", "ule", "slt", "sle"].contains(&op);
                let zlen = if cmp { 1 } else { n };
                let term = evaluator(n, op);
                let external = 2 * n + zlen;
                for raw in 0..(1u64 << external) {
                    let initial = tuple(external, raw);
                    let a = Bits(initial[..n].to_vec());
                    let b = Bits(initial[n..2 * n].to_vec());
                    let z = Bits(initial[2 * n..].to_vec());
                    let answer = if cmp {
                        Bits::from_u64(1, u64::from(a.cmp(&b, op)))
                    } else {
                        a.bin(&b, op)
                    };
                    let mut sim = Simulator::new(initial.clone());
                    sim.run(&term).unwrap();
                    assert_eq!(&sim.wires[..2 * n], &initial[..2 * n]);
                    assert_eq!(
                        Bits(sim.wires[2 * n..].to_vec()),
                        z.xor(&answer),
                        "n={n} {op} raw={raw}"
                    );
                    assert_eq!(sim.executed, cost(&term).total());
                }
            }
        }
    }
    #[test]
    fn all_allocated_wire_states_at_width_one() {
        for op in [
            "add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr", "eq", "ne", "ult",
            "ule", "slt", "sle",
        ] {
            let t = evaluator(1, op);
            let c::Node::With {
                external,
                allocated,
                body,
            } = t.as_ref()
            else {
                unreachable!()
            };
            let total = external + allocated;
            assert!(total <= 16);
            for raw in 0..(1u64 << total) {
                let init = tuple(total, raw);
                let mut sim = Simulator::new(init.clone());
                sim.run(body).unwrap();
                assert_eq!(&sim.wires[*external..], &init[*external..]);
                sim.run(&c::adj(body.clone())).unwrap();
                assert_eq!(sim.wires, init);
            }
            let mapped = c::call(t.clone(), (1..=external.to_owned()).collect());
            let controlled = c::ctrl(vec![0], mapped);
            for raw in 0..(1u64 << (external + 1)) {
                let init = tuple(external + 1, raw);
                let mut sim = Simulator::new(init.clone());
                sim.run(&controlled).unwrap();
                if !init[0] {
                    assert_eq!(sim.wires, init);
                }
                sim.run(&c::adj(controlled.clone())).unwrap();
                assert_eq!(sim.wires, init);
            }
        }
    }
    #[test]
    fn controlled_select_casts_and_permutations_all_states() {
        let mut cases = vec![];
        let mut b = Builder::new(4);
        let value = b.mux(Bit::Wire(0), Bit::Wire(1), Bit::Wire(2));
        cases.push((4, b.finish(4, &[(3, value)])));
        cases.push((
            3,
            Builder::new(3).finish(3, &[(1, Bit::Wire(0)), (2, Bit::Wire(0))]),
        ));
        for constant in 0..8 {
            cases.push((3, add_constant(&[0, 1, 2], constant)));
            if constant & 1 != 0 {
                cases.push((3, multiply_odd(&[0, 1, 2], constant)));
            }
        }
        cases.push((3, add_shifted_self(&[0, 1, 2], 1)));
        cases.push((3, add_shifted_self(&[0, 1, 2], 2)));
        for (external, term) in cases {
            if let c::Node::With {
                allocated, body, ..
            } = term.as_ref()
            {
                let total = external + allocated;
                assert!(total <= 16);
                for raw in 0..(1u64 << total) {
                    let init = tuple(total, raw);
                    let mut sim = Simulator::new(init.clone());
                    sim.run(body).unwrap();
                    assert_eq!(sim.wires[external..], init[external..]);
                    sim.run(&c::adj(body.clone())).unwrap();
                    assert_eq!(sim.wires, init);
                }
            }
            let controlled = c::ctrl(vec![0], c::call(term.clone(), (1..=external).collect()));
            for raw in 0..(1u64 << (external + 1)) {
                let init = tuple(external + 1, raw);
                let mut sim = Simulator::new(init.clone());
                sim.run(&controlled).unwrap();
                if init[0] {
                    let mut plain = Simulator::new(init[1..].to_vec());
                    plain.run(&term).unwrap();
                    assert_eq!(sim.wires[1..], plain.wires);
                } else {
                    assert_eq!(sim.wires, init);
                }
                sim.run(&c::adj(controlled.clone())).unwrap();
                assert_eq!(sim.wires, init);
            }
        }
    }
    #[test]
    fn odd_multiply_above_host_width() {
        let n = 65;
        let wires: Vec<_> = (0..n).collect();
        let term = multiply_odd(&wires, 3);
        for value in [0, 1, 12345, u64::MAX] {
            let mut x = Bits::from_u64(n, value);
            x.0[64] = true;
            let expected = x.bin(&Bits::from_u64(n, 3), "mul");
            let mut sim = Simulator::new(x.0.clone());
            sim.run(&term).unwrap();
            assert_eq!(Bits(sim.wires.clone()), expected);
            sim.run(&c::adj(term.clone())).unwrap();
            assert_eq!(sim.wires, x.0);
        }
    }
    #[test]
    fn inplace_all_states_controlled_and_inverse() {
        for n in 1..=4 {
            let a: Vec<_> = (0..n).collect();
            let b: Vec<_> = (n..2 * n).collect();
            let add = add_inplace(&a, &b);
            for raw in 0..(1u64 << (2 * n + 1)) {
                let init = tuple(2 * n + 1, raw);
                let mut sim = Simulator::new(init.clone());
                let term = c::ctrl(vec![2 * n], add.clone());
                sim.run(&term).unwrap();
                let expected = if init[2 * n] {
                    ((raw >> n) + (raw & ((1 << n) - 1))) & ((1 << n) - 1)
                } else {
                    (raw >> n) & ((1 << n) - 1)
                };
                assert_eq!(Bits(sim.wires[n..2 * n].to_vec()).low_u64(), expected);
                sim.run(&c::adj(term)).unwrap();
                assert_eq!(sim.wires, init);
            }
            for k in 0..(1u64 << n) {
                let term = add_constant(&a, k);
                for x in 0..(1u64 << n) {
                    let mut sim = Simulator::new(tuple(n, x));
                    sim.run(&term).unwrap();
                    assert_eq!(Bits(sim.wires.clone()).low_u64(), (x + k) & ((1 << n) - 1));
                    sim.run(&c::adj(term.clone())).unwrap();
                    assert_eq!(sim.wires, tuple(n, x));
                }
            }
            for k in 1..n {
                let term = add_shifted_self(&a, k);
                for x in 0..(1u64 << n) {
                    let mut sim = Simulator::new(tuple(n, x));
                    sim.run(&term).unwrap();
                    assert_eq!(Bits(sim.wires).low_u64(), (x + (x << k)) & ((1 << n) - 1));
                }
            }
            for k in (1..(1u64 << n)).step_by(2) {
                let term = multiply_odd(&a, k);
                for x in 0..(1u64 << n) {
                    let mut sim = Simulator::new(tuple(n, x));
                    sim.run(&term).unwrap();
                    assert_eq!(Bits(sim.wires).low_u64(), (x * k) & ((1 << n) - 1));
                }
            }
        }
    }
    #[test]
    fn select_and_casts_all_interface_states() {
        for n in 1..=3 {
            let external = 1 + 3 * n;
            let mut b = Builder::new(external);
            let out: Vec<_> = wires(1, n)
                .into_iter()
                .zip(wires(1 + n, n))
                .map(|(a, z)| b.mux(Bit::Wire(0), a, z))
                .enumerate()
                .map(|(i, z)| (1 + 2 * n + i, z))
                .collect();
            let t = b.finish(external, &out);
            for raw in 0..(1 << external) {
                let init = tuple(external, raw);
                let mut sim = Simulator::new(init.clone());
                sim.run(&t).unwrap();
                let src = if init[0] { 1 } else { 1 + n };
                for i in 0..n {
                    assert_eq!(
                        sim.wires[1 + 2 * n + i],
                        init[1 + 2 * n + i] ^ init[src + i]
                    );
                }
            }
            for m in 1..=4 {
                for signed in [false, true] {
                    let external = n + m;
                    let a = wires(0, n);
                    let out: Vec<_> = (0..m)
                        .map(|i| {
                            (
                                n + i,
                                a.get(i).copied().unwrap_or(if signed {
                                    a[n - 1]
                                } else {
                                    Bit::Const(false)
                                }),
                            )
                        })
                        .collect();
                    let t = Builder::new(external).finish(external, &out);
                    for raw in 0..(1 << external) {
                        let init = tuple(external, raw);
                        let mut sim = Simulator::new(init.clone());
                        sim.run(&t).unwrap();
                        let v = Bits(init[..n].to_vec()).cast(m, signed);
                        assert_eq!(
                            Bits(sim.wires[n..].to_vec()),
                            Bits(init[n..].to_vec()).xor(&v)
                        );
                    }
                }
            }
        }
    }
}
