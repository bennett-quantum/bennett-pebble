//! Bit-vector expressions and a deliberately small, checkable inverse calculus.
//! A failed inverse rule retains the old value. No optimisation is assumed.
use crate::{
    bits::Bits,
    block::Op,
    gadgets::{Bit, Builder},
    source::Row,
};
use std::{collections::BTreeMap, rc::Rc};
pub type E = Rc<Expr>;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub n: usize,
    pub kind: Kind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Var(usize),
    Input(usize),
    Const(Bits),
    Bin(String, E, E),
    Cmp(String, E, E),
    Select(E, E, E),
    Cast(String, E),
}
fn node(n: usize, kind: Kind) -> E {
    Rc::new(Expr { n, kind })
}
pub fn var(n: usize, id: usize) -> E {
    node(n, Kind::Var(id))
}
pub fn input(n: usize, id: usize) -> E {
    node(n, Kind::Input(id))
}
pub fn constant(v: Bits) -> E {
    node(v.width(), Kind::Const(v))
}
fn bin(op: &str, a: E, b: E) -> E {
    if let (Kind::Const(a), Kind::Const(b)) = (&a.kind, &b.kind) {
        return constant(a.bin(b, op));
    }
    node(a.n, Kind::Bin(op.into(), a, b))
}
pub fn expressions(ops: &[Op], values: &mut [E], widths: &[usize]) {
    for op in ops {
        match op {
            Op::Enter { clear, bind } => {
                let args: Vec<_> = bind.iter().map(|(_, s)| values[*s].clone()).collect();
                for d in clear {
                    values[*d] = constant(Bits::zero(widths[*d]));
                }
                for ((d, _), v) in bind.iter().zip(args) {
                    values[*d] = v;
                }
            }
            Op::Row(row) => match row {
                Row::Const(d, v) => values[*d] = constant(v.clone()),
                Row::Bin(d, o, a, b) => values[*d] = bin(o, values[*a].clone(), values[*b].clone()),
                Row::Cmp(d, o, a, b) => {
                    values[*d] = if let (Kind::Const(a), Kind::Const(b)) =
                        (&values[*a].kind, &values[*b].kind)
                    {
                        constant(Bits::from_u64(1, u64::from(a.cmp(b, o))))
                    } else {
                        node(
                            1,
                            Kind::Cmp(o.clone(), values[*a].clone(), values[*b].clone()),
                        )
                    };
                }
                Row::Select(d, p, a, b) => {
                    values[*d] = if let Kind::Const(p) = &values[*p].kind {
                        if p.0[0] {
                            values[*a].clone()
                        } else {
                            values[*b].clone()
                        }
                    } else {
                        node(
                            widths[*d],
                            Kind::Select(
                                values[*p].clone(),
                                values[*a].clone(),
                                values[*b].clone(),
                            ),
                        )
                    }
                }
                Row::Cast(d, o, a) => {
                    values[*d] = if let Kind::Const(a) = &values[*a].kind {
                        constant(a.cast(widths[*d], o == "sext"))
                    } else {
                        node(widths[*d], Kind::Cast(o.clone(), values[*a].clone()))
                    }
                }
                Row::Mov(ds, ss) => {
                    let args: Vec<_> = ss.iter().map(|s| values[*s].clone()).collect();
                    for (d, v) in ds.iter().zip(args) {
                        values[*d] = v;
                    }
                }
                _ => unreachable!(),
            },
        }
    }
}
pub fn eval(
    e: &E,
    b: &mut Builder,
    vars: &BTreeMap<usize, Vec<Bit>>,
    inputs: &BTreeMap<usize, Vec<Bit>>,
) -> Option<Vec<Bit>> {
    Some(match &e.kind {
        Kind::Var(i) => vars.get(i)?.clone(),
        Kind::Input(i) => inputs.get(i)?.clone(),
        Kind::Const(v) => v.0.iter().map(|v| Bit::Const(*v)).collect(),
        Kind::Bin(op, a, z) => {
            let a = eval(a, b, vars, inputs)?;
            let z = eval(z, b, vars, inputs)?;
            b.vector(&a, &z, op)
        }
        Kind::Cmp(op, a, z) => {
            let a = eval(a, b, vars, inputs)?;
            let z = eval(z, b, vars, inputs)?;
            vec![b.compare(&a, &z, op)]
        }
        Kind::Select(p, a, z) => {
            let p = eval(p, b, vars, inputs)?[0];
            let a = eval(a, b, vars, inputs)?;
            let z = eval(z, b, vars, inputs)?;
            a.into_iter().zip(z).map(|(a, z)| b.mux(p, a, z)).collect()
        }
        Kind::Cast(op, a) => {
            let a = eval(a, b, vars, inputs)?;
            (0..e.n)
                .map(|i| {
                    a.get(i).copied().unwrap_or(if op == "sext" {
                        a[a.len() - 1]
                    } else {
                        Bit::Const(false)
                    })
                })
                .collect()
        }
    })
}
/// Known expressions in immutable inputs at block entry. Unknown joins widen
/// immediately, so this analysis terminates independently of the step budget.
pub fn rematerializable(m: &crate::block::Machine) -> Vec<Vec<Option<E>>> {
    let mut entries: Vec<Option<Vec<Option<E>>>> = vec![None; m.blocks.len()];
    let mut start: Vec<_> = m
        .widths
        .iter()
        .map(|n| Some(constant(Bits::zero(*n))))
        .collect();
    for i in &m.inputs {
        start[*i] = Some(input(m.widths[*i], *i));
    }
    for (i, v) in &m.constants {
        start[*i] = Some(constant(v.clone()));
    }
    entries[0] = Some(start);
    let mut queue = std::collections::VecDeque::from([0]);
    while let Some(id) = queue.pop_front() {
        let current = entries[id].as_ref().unwrap();
        let mut values: Vec<_> = current
            .iter()
            .enumerate()
            .map(|(i, e)| e.clone().unwrap_or_else(|| var(m.widths[i], i)))
            .collect();
        expressions(&m.blocks[id].ops, &mut values, &m.widths);
        let outgoing: Vec<_> = values
            .into_iter()
            .map(|e| if has_variable(&e) { None } else { Some(e) })
            .collect();
        let next = match m.blocks[id].exit {
            crate::block::Exit::Jump(n)
            | crate::block::Exit::FaultIf(_, _, n)
            | crate::block::Exit::Stack { next: n, .. } => vec![n],
            crate::block::Exit::Branch(_, a, b) => vec![a, b],
            _ => vec![],
        };
        for n in next {
            let joined = if let Some(old) = &entries[n] {
                old.iter()
                    .zip(&outgoing)
                    .map(|(a, b)| if a == b { a.clone() } else { None })
                    .collect()
            } else {
                outgoing.clone()
            };
            if entries[n].as_ref() != Some(&joined) {
                entries[n] = Some(joined);
                queue.push_back(n);
            }
        }
    }
    entries
        .into_iter()
        .map(|v| v.unwrap_or_else(|| vec![None; m.widths.len()]))
        .collect()
}
fn has_variable(e: &E) -> bool {
    match &e.kind {
        Kind::Var(_) => true,
        Kind::Bin(_, a, b) | Kind::Cmp(_, a, b) => has_variable(a) || has_variable(b),
        Kind::Select(p, a, b) => has_variable(p) || has_variable(a) || has_variable(b),
        Kind::Cast(_, a) => has_variable(a),
        _ => false,
    }
}
fn contains(e: &E, id: usize) -> bool {
    match &e.kind {
        Kind::Var(i) => *i == id,
        Kind::Bin(_, a, b) | Kind::Cmp(_, a, b) => contains(a, id) || contains(b, id),
        Kind::Select(p, a, b) => contains(p, id) || contains(a, id) || contains(b, id),
        Kind::Cast(_, a) => contains(a, id),
        _ => false,
    }
}
fn literal(e: &E) -> Option<u64> {
    if let Kind::Const(v) = &e.kind {
        if v.0.iter().skip(64).any(|b| *b) {
            None
        } else {
            Some(v.low_u64())
        }
    } else {
        None
    }
}
#[derive(Clone, Debug)]
pub struct Saved {
    pub expr: E,
    pub bit: usize,
    pub guards: Vec<(E, bool)>,
}
#[derive(Clone)]
pub struct Inverter {
    pub builder: Builder,
    pub saved: Vec<Saved>,
    pub known: BTreeMap<usize, Vec<Bit>>,
    pub inputs: BTreeMap<usize, Vec<Bit>>,
    pub residue_base: usize,
    pub compact_inverse: bool,
    predicates: BTreeMap<usize, Bit>,
}
impl Inverter {
    pub fn new(next: usize, residue_base: usize, inputs: BTreeMap<usize, Vec<Bit>>) -> Self {
        Self {
            builder: Builder::new(next),
            saved: vec![],
            known: BTreeMap::new(),
            inputs,
            residue_base,
            compact_inverse: true,
            predicates: BTreeMap::new(),
        }
    }
    fn save(&mut self, e: &E, bit: usize, guards: &[(E, bool)]) -> Bit {
        let w = self.residue_base + self.saved.len();
        self.saved.push(Saved {
            expr: e.clone(),
            bit,
            guards: guards.to_vec(),
        });
        Bit::Wire(w)
    }
    fn predicate(&mut self, p: &E) -> Bit {
        if let Some(v) = eval(p, &mut self.builder, &self.known, &self.inputs) {
            return v[0];
        }
        let key = Rc::as_ptr(p) as usize;
        if let Some(p) = self.predicates.get(&key) {
            return *p;
        }
        let bit = self.save(p, 0, &[]);
        self.predicates.insert(key, bit);
        bit
    }
    pub fn solve(&mut self, id: usize, n: usize, outputs: &[(E, Vec<Bit>)]) {
        if self.known.contains_key(&id) {
            return;
        }
        let mut best = None;
        for (expr, result) in outputs {
            if !contains(expr, id) {
                continue;
            }
            let mut trial = self.clone();
            if let Some(v) = trial.invert(expr, result, id, &[], &BTreeMap::new()) {
                if best
                    .as_ref()
                    .is_none_or(|(old, _): &(Self, Vec<Bit>)| trial.saved.len() < old.saved.len())
                {
                    best = Some((trial, v));
                }
            }
        }
        if let Some((trial, v)) = best {
            if trial.saved.len() <= self.saved.len() + n {
                *self = trial;
                self.known.insert(id, v);
                return;
            }
        }
        let e = var(n, id);
        let v = (0..n).map(|i| self.save(&e, i, &[])).collect();
        self.known.insert(id, v);
    }
    fn invert(
        &mut self,
        e: &E,
        result: &[Bit],
        id: usize,
        guards: &[(E, bool)],
        facts: &BTreeMap<(usize, usize), bool>,
    ) -> Option<Vec<Bit>> {
        match &e.kind {
            Kind::Var(i) if *i == id => Some(result.to_vec()),
            Kind::Bin(op, a, z) => {
                let ca = contains(a, id);
                let cz = contains(z, id);
                if ca == cz {
                    return None;
                }
                let (child, other, left) = if ca { (a, z, true) } else { (z, a, false) };
                if ["shl", "lshr", "ashr"].contains(&op.as_str()) && left {
                    let k = literal(other)? as usize;
                    if op == "ashr" {
                        return None;
                    }
                    let k = k.min(e.n);
                    let mut reconstructed = vec![];
                    for i in 0..e.n {
                        let source = if op == "shl" {
                            i.checked_add(k).filter(|j| *j < e.n)
                        } else {
                            i.checked_sub(k)
                        };
                        reconstructed.push(if let Some(j) = source {
                            result[j]
                        } else {
                            match &child.kind {
                                Kind::Var(v) if facts.contains_key(&(*v, i)) => {
                                    Bit::Const(facts[&(*v, i)])
                                }
                                _ => self.save(child, i, guards),
                            }
                        });
                    }
                    return self.invert(child, &reconstructed, id, guards, facts);
                }
                let other = eval(other, &mut self.builder, &self.known, &self.inputs)?;
                let reconstructed = match op.as_str() {
                    "add" => self.builder.vector(result, &other, "sub"),
                    "sub" => {
                        if left {
                            self.builder.vector(result, &other, "add")
                        } else {
                            self.builder.vector(&other, result, "sub")
                        }
                    }
                    "xor" => self.builder.vector(result, &other, "xor"),
                    "mul" => {
                        let coefficient = if left { literal(z)? } else { literal(a)? };
                        if coefficient & 1 == 0 || e.n > 64 {
                            return None;
                        }
                        if self.compact_inverse {
                            self.builder.inverse_odd(result, coefficient)
                        } else {
                            let mut inverse = coefficient;
                            for _ in 0..6 {
                                inverse = inverse.wrapping_mul(
                                    2u64.wrapping_sub(coefficient.wrapping_mul(inverse)),
                                );
                            }
                            self.builder.vector(
                                result,
                                &crate::gadgets::constant(e.n, inverse),
                                "mul",
                            )
                        }
                    }
                    _ => return None,
                };
                self.invert(child, &reconstructed, id, guards, facts)
            }
            Kind::Cast(op, a) => {
                let mut recovered = result[..result.len().min(a.n)].to_vec();
                if op == "trunc" {
                    for i in recovered.len()..a.n {
                        recovered.push(self.save(a, i, guards));
                    }
                }
                self.invert(a, &recovered, id, guards, facts)
            }
            Kind::Select(p, a, z) => {
                if !contains(a, id) || !contains(z, id) {
                    return None;
                }
                let predicate = self.predicate(p);
                let mut true_guards = guards.to_vec();
                true_guards.push((p.clone(), true));
                let mut false_guards = guards.to_vec();
                false_guards.push((p.clone(), false));
                let mut yes = facts.clone();
                let mut no = facts.clone();
                parity_facts(p, true, &mut yes);
                parity_facts(p, false, &mut no);
                let a = self.invert(a, result, id, &true_guards, &yes)?;
                let z = self.invert(z, result, id, &false_guards, &no)?;
                Some(
                    a.into_iter()
                        .zip(z)
                        .map(|(a, z)| self.builder.mux(predicate, a, z))
                        .collect(),
                )
            }
            _ => None,
        }
    }
}
fn parity_facts(p: &E, truth: bool, facts: &mut BTreeMap<(usize, usize), bool>) {
    if let Kind::Cmp(op, a, z) = &p.kind {
        if op != "eq" && op != "ne" {
            return;
        }
        let zero = literal(z);
        if let Kind::Bin(and, v, mask) = &a.kind {
            if and == "and" && literal(mask) == Some(1) {
                if let Kind::Var(id) = v.kind {
                    if let Some(c) = zero {
                        if c <= 1 {
                            facts.insert((id, 0), (truth ^ (op == "ne")) == (c == 1));
                        }
                    }
                }
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn guarded_shift_affine_has_one_residue_bit() {
        let n = 8;
        let x = var(n, 0);
        let one = constant(Bits::from_u64(n, 1));
        let zero = constant(Bits::zero(n));
        let parity = bin("and", x.clone(), one.clone());
        let p = node(1, Kind::Cmp("eq".into(), parity, zero));
        let even = bin("lshr", x.clone(), one.clone());
        let odd = bin("add", bin("mul", x, constant(Bits::from_u64(n, 3))), one);
        let expression = node(n, Kind::Select(p, even, odd));
        let mut inv = Inverter::new(64, 32, BTreeMap::new());
        inv.solve(0, n, &[(expression, crate::gadgets::wires(0, n))]);
        assert_eq!(inv.saved.len(), 1);
    }
}
