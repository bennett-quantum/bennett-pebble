//! Weighted, context-inlined block machine. No table indexed by the budget.
use crate::{
    bits::Bits,
    source::{Budget, Outcome, Program, Result, Row},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
#[derive(Clone, Debug)]
pub enum Op {
    Row(Row),
    Enter {
        clear: Vec<usize>,
        bind: Vec<(usize, usize)>,
    },
}
#[derive(Clone, Debug)]
pub enum Exit {
    Jump(usize),
    Branch(usize, usize, usize),
    FaultIf(usize, Bits, usize),
    Fault(Bits),
    Success(usize),
    Stack { cells: u64, next: usize },
}
#[derive(Clone, Debug)]
pub struct Block {
    pub ops: Vec<Op>,
    pub exit: Exit,
    pub weight: u64,
    pub live_in: BTreeSet<usize>,
    pub live_out: BTreeSet<usize>,
}
#[derive(Clone, Debug)]
pub struct Machine {
    pub blocks: Vec<Block>,
    pub widths: Vec<usize>,
    pub inputs: Vec<usize>,
    pub constants: BTreeMap<usize, Bits>,
    pub target_width: usize,
    pub fault_width: usize,
    pub stack_limit: u64,
    pub uses_stack: bool,
    pub reach: Reachability,
    pub static_counts: Option<Vec<u64>>,
}
#[derive(Clone, Debug, Default)]
pub struct Reachability {
    pub prefix: Vec<BTreeSet<usize>>,
    pub cycle: Vec<BTreeSet<usize>>,
}
#[derive(Clone, Debug)]
struct Raw {
    ops: Vec<Op>,
    exit: Exit,
}
fn successors(e: &Exit) -> Vec<usize> {
    match e {
        Exit::Jump(n) | Exit::FaultIf(_, _, n) | Exit::Stack { next: n, .. } => vec![*n],
        Exit::Branch(_, a, b) => vec![*a, *b],
        _ => vec![],
    }
}
fn remap_row(r: &Row, map: &[usize]) -> Row {
    match r {
        Row::Const(d, v) => Row::Const(map[*d], v.clone()),
        Row::Bin(d, o, a, b) => Row::Bin(map[*d], o.clone(), map[*a], map[*b]),
        Row::Cmp(d, o, a, b) => Row::Cmp(map[*d], o.clone(), map[*a], map[*b]),
        Row::Select(d, p, a, b) => Row::Select(map[*d], map[*p], map[*a], map[*b]),
        Row::Cast(d, o, a) => Row::Cast(map[*d], o.clone(), map[*a]),
        Row::Mov(ds, ss) => Row::Mov(
            ds.iter().map(|i| map[*i]).collect(),
            ss.iter().map(|i| map[*i]).collect(),
        ),
        _ => unreachable!(),
    }
}
struct Inline<'a> {
    p: &'a Program,
    budget: Budget,
    raw: Vec<Raw>,
    widths: Vec<usize>,
    contexts: usize,
}
impl Inline<'_> {
    fn function(
        &mut self,
        fi: usize,
        depth: u64,
        return_to: Option<(usize, usize)>,
    ) -> Result<(usize, Vec<usize>)> {
        self.contexts += 1;
        if self.contexts > 4096 {
            return Err("unsupported: inlining exceeds 4096 fixed contexts".into());
        }
        let f = &self.p.functions[fi];
        let map: Vec<_> = f
            .widths
            .iter()
            .map(|n| {
                let i = self.widths.len();
                self.widths.push(*n);
                i
            })
            .collect();
        let start = self.raw.len();
        self.raw.extend((0..f.rows.len()).map(|_| Raw {
            ops: vec![],
            exit: Exit::Fault(Bits::from_u64(self.p.functions[0].fault_width, 4)),
        }));
        for (pc, row) in f.rows.iter().enumerate() {
            let next = start + pc + 1;
            let mut ops = vec![];
            let exit = match row {
                Row::Jump(n) => Exit::Jump(start + n),
                Row::Branch(p, a, b) => Exit::Branch(map[*p], start + a, start + b),
                Row::FaultIf(p, c) => Exit::FaultIf(map[*p], c.clone(), next),
                Row::Fault(c) => Exit::Fault(c.clone()),
                Row::Retval(a) => Exit::Success(map[*a]),
                Row::Ret(a) => {
                    let (dst, ret) = return_to.ok_or("return without context")?;
                    ops.push(Op::Row(Row::Mov(vec![dst], vec![map[*a]])));
                    Exit::Jump(ret)
                }
                Row::Call(d, c, args) => {
                    let callee = &self.p.functions[*c];
                    let cells = 3 + callee.locations.len() as u64;
                    if depth >= self.budget.depth || cells > self.budget.stack {
                        Exit::Fault(Bits::from_u64(self.p.functions[0].fault_width, 3))
                    } else {
                        let params = callee.params.clone();
                        let locs = callee.locations.clone();
                        let (entry, cm) = self.function(*c, depth + 1, Some((map[*d], next)))?;
                        ops.push(Op::Enter {
                            clear: locs.iter().map(|i| cm[*i]).collect(),
                            bind: params
                                .iter()
                                .zip(args)
                                .map(|(d, a)| (cm[*d], map[*a]))
                                .collect(),
                        });
                        Exit::Stack { cells, next: entry }
                    }
                }
                _ => {
                    ops.push(Op::Row(remap_row(row, &map)));
                    Exit::Jump(next)
                }
            };
            self.raw[start + pc] = Raw { ops, exit };
        }
        Ok((start, map))
    }
}
impl Machine {
    pub fn build(p: &Program, budget: Budget) -> Result<Self> {
        p.validate_budget(budget)?;
        let arguments = p.classical_values()?;
        let mut inline = Inline {
            p,
            budget,
            raw: vec![],
            widths: vec![],
            contexts: 0,
        };
        let (_, map) = inline.function(0, 0, None)?;
        let mut raw = inline.raw;
        let original_raw = raw.clone();
        // Monotonic-stack analysis. Join disagreement widens to unknown.
        let mut sp = vec![None::<Option<u64>>; raw.len()];
        sp[0] = Some(Some(0));
        let mut q = VecDeque::from([0]);
        while let Some(i) = q.pop_front() {
            let current = sp[i].unwrap();
            let value = if let Exit::Stack { cells, .. } = raw[i].exit {
                current.and_then(|n| n.checked_add(cells))
            } else {
                current
            };
            if matches!(raw[i].exit, Exit::Stack { .. }) && value.is_some_and(|n| n > budget.stack)
            {
                continue;
            }
            for n in successors(&raw[i].exit) {
                let joined = match sp[n] {
                    None => Some(value),
                    Some(old) => Some(if old == value { old } else { None }),
                };
                if sp[n] != joined {
                    sp[n] = joined;
                    q.push_back(n);
                }
            }
        }
        for (i, row) in raw.iter_mut().enumerate() {
            if let Exit::Stack { cells, next } = row.exit {
                if let Some(Some(before)) = sp[i] {
                    if before.checked_add(cells).is_some_and(|n| n <= budget.stack) {
                        row.exit = Exit::Jump(next);
                    } else {
                        row.exit = Exit::Fault(Bits::from_u64(p.functions[0].fault_width, 3));
                        row.ops.clear();
                    }
                }
            }
        }
        let uses_stack = raw.iter().any(|r| matches!(r.exit, Exit::Stack { .. }));
        if uses_stack {
            for (row, original) in raw.iter_mut().zip(&original_raw) {
                if matches!(row.exit, Exit::Jump(_)) && matches!(original.exit, Exit::Stack { .. })
                {
                    row.exit = original.exit.clone();
                }
            }
        }
        // Reachable leaders: merge maximal paths through single-predecessor rows.
        let mut reachable = BTreeSet::new();
        let mut q = vec![0];
        while let Some(i) = q.pop() {
            if reachable.insert(i) {
                q.extend(successors(&raw[i].exit));
            }
        }
        let mut pred = vec![0usize; raw.len()];
        for &i in &reachable {
            for n in successors(&raw[i].exit) {
                pred[n] += 1;
            }
        }
        let mut leaders = BTreeSet::from([0]);
        for &i in &reachable {
            match raw[i].exit.clone() {
                Exit::Jump(n) if pred[n] == 1 => {}
                _ => {
                    leaders.extend(successors(&raw[i].exit));
                }
            }
            if pred[i] != 1 {
                leaders.insert(i);
            }
        }
        let mut owner = BTreeMap::new();
        let mut blocks = vec![];
        for &leader in &leaders {
            if !reachable.contains(&leader) {
                continue;
            }
            let id = blocks.len();
            let mut pc = leader;
            let mut ops = vec![];
            let mut weight = 0;
            let exit = loop {
                owner.insert(pc, id);
                weight += 1;
                ops.extend(raw[pc].ops.clone());
                if let Exit::Jump(n) = raw[pc].exit {
                    if !leaders.contains(&n) {
                        pc = n;
                        continue;
                    }
                }
                break raw[pc].exit.clone();
            };
            blocks.push(Block {
                ops,
                exit,
                weight,
                live_in: BTreeSet::new(),
                live_out: BTreeSet::new(),
            });
        }
        for b in &mut blocks {
            b.exit = match b.exit.clone() {
                Exit::Jump(n) => Exit::Jump(owner[&n]),
                Exit::Branch(p, a, c) => Exit::Branch(p, owner[&a], owner[&c]),
                Exit::FaultIf(p, c, n) => Exit::FaultIf(p, c, owner[&n]),
                Exit::Stack { cells, next } => Exit::Stack {
                    cells,
                    next: owner[&next],
                },
                ref e => e.clone(),
            };
        }
        let f = &p.functions[0];
        let mut machine = Self {
            blocks,
            widths: inline.widths,
            inputs: f.inputs.iter().map(|i| map[*i]).collect(),
            constants: f
                .classical
                .iter()
                .zip(arguments)
                .map(|(i, v)| (map[*i], v))
                .collect(),
            target_width: f.target_width,
            fault_width: f.fault_width,
            stack_limit: budget.stack,
            uses_stack,
            reach: Reachability::default(),
            static_counts: None,
        };
        machine.liveness();
        machine.reach = machine.reachability()?;
        machine.static_counts = machine.counter_analysis();
        Ok(machine)
    }
    fn liveness(&mut self) {
        loop {
            let mut changed = false;
            for i in (0..self.blocks.len()).rev() {
                let mut live = BTreeSet::new();
                for n in successors(&self.blocks[i].exit) {
                    live.extend(self.blocks[n].live_in.iter().copied());
                }
                let out = live.clone();
                match self.blocks[i].exit.clone() {
                    Exit::Branch(p, _, _) | Exit::FaultIf(p, _, _) | Exit::Success(p) => {
                        live.insert(p);
                    }
                    _ => {}
                }
                for op in self.blocks[i].ops.iter().rev() {
                    let (writes, reads) = rw(op);
                    for d in writes {
                        live.remove(&d);
                    }
                    live.extend(reads);
                }
                if live != self.blocks[i].live_in || out != self.blocks[i].live_out {
                    self.blocks[i].live_in = live;
                    self.blocks[i].live_out = out;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
    fn reachability(&self) -> Result<Reachability> {
        let halt = self.blocks.len();
        let mut seen = BTreeMap::new();
        let mut sets = vec![];
        let mut current = BTreeSet::from([0]);
        loop {
            if let Some(&start) = seen.get(&current) {
                return Ok(Reachability {
                    prefix: sets[..start].to_vec(),
                    cycle: sets[start..].to_vec(),
                });
            }
            if sets.len() > 65536 {
                return Err("unsupported: reachability period exceeds 65536".into());
            }
            seen.insert(current.clone(), sets.len());
            sets.push(current.clone());
            let mut next = BTreeSet::new();
            for b in current {
                if b == halt {
                    next.insert(halt);
                    continue;
                }
                let e = &self.blocks[b].exit;
                next.extend(successors(e));
                if !matches!(e, Exit::Jump(_) | Exit::Branch(..)) {
                    next.insert(halt);
                }
            }
            current = next;
        }
    }
    /// Sufficient single-value analysis: a global row count at each block entry.
    /// Conflicts (including any nonzero-weight cycle) select coherent fallback.
    fn counter_analysis(&self) -> Option<Vec<u64>> {
        let mut values = vec![None; self.blocks.len()];
        values[0] = Some(0u64);
        let mut q = VecDeque::from([0]);
        while let Some(b) = q.pop_front() {
            let c = values[b]?.checked_add(self.blocks[b].weight)?;
            for n in successors(&self.blocks[b].exit) {
                match values[n] {
                    Some(old) if old != c => return None,
                    None => {
                        values[n] = Some(c);
                        q.push_back(n);
                    }
                    _ => {}
                }
            }
        }
        values.into_iter().collect()
    }
    /// Once the structural reachability sequence is permanently {HALT}, no
    /// environment can need further block steps. The row bound also stages B.
    pub fn horizon(&self, budget: u64) -> (u64, u64) {
        let halted = self
            .reach
            .cycle
            .iter()
            .all(|set| set.len() == 1 && set.contains(&self.blocks.len()));
        if halted {
            let blocks = self.reach.prefix.len() as u64;
            let rows =
                blocks.saturating_mul(self.blocks.iter().map(|b| b.weight).max().unwrap_or(1));
            (budget.min(rows), budget.min(blocks))
        } else {
            (budget, budget)
        }
    }
    pub fn state_variables(&self) -> BTreeSet<usize> {
        self.blocks
            .iter()
            .flat_map(|b| b.live_in.iter().chain(&b.live_out).copied())
            .filter(|i| !self.inputs.contains(i) && !self.constants.contains_key(i))
            .collect()
    }
    pub fn run(&self, input: &[Bits], budget: u64) -> Outcome {
        let mut values: Vec<_> = self.widths.iter().map(|n| Bits::zero(*n)).collect();
        for (i, x) in self.inputs.iter().zip(input) {
            values[*i] = x.clone();
        }
        for (i, v) in &self.constants {
            values[*i] = v.clone();
        }
        let (mut b, mut count, mut sp) = (0, 0u64, 0u64);
        let result = |payload, code, rows, stack_used| Outcome {
            payload,
            code,
            rows,
            stack_used,
            max_depth: 0,
        };
        // A block can cross B, but no later fault/success supersedes exhaustion.
        loop {
            let block = &self.blocks[b];
            if block.weight > budget.saturating_sub(count) {
                return result(
                    Bits::zero(self.target_width),
                    Bits::from_u64(self.fault_width, 1),
                    budget,
                    sp,
                );
            }
            count += block.weight;
            if let Exit::Stack { cells, .. } = block.exit {
                if cells > self.stack_limit.saturating_sub(sp) {
                    return result(
                        Bits::zero(self.target_width),
                        Bits::from_u64(self.fault_width, 3),
                        count,
                        sp,
                    );
                }
                sp += cells;
            }
            for op in &block.ops {
                apply(op, &mut values, &self.widths);
            }
            match block.exit.clone() {
                Exit::Jump(n) => b = n,
                Exit::Branch(p, a, c) => b = if values[p].0[0] { a } else { c },
                Exit::FaultIf(p, c, n) => {
                    if values[p].0[0] {
                        return result(Bits::zero(self.target_width), c, count, sp);
                    } else {
                        b = n
                    }
                }
                Exit::Fault(c) => return result(Bits::zero(self.target_width), c, count, sp),
                Exit::Success(p) => {
                    return result(values[p].clone(), Bits::zero(self.fault_width), count, sp);
                }
                Exit::Stack { next, .. } => b = next,
            }
        }
    }
}
fn rw(op: &Op) -> (Vec<usize>, Vec<usize>) {
    match op {
        Op::Enter { clear, bind } => (clear.clone(), bind.iter().map(|(_, s)| *s).collect()),
        Op::Row(r) => match r {
            Row::Const(d, _) => (vec![*d], vec![]),
            Row::Bin(d, _, a, b) | Row::Cmp(d, _, a, b) => (vec![*d], vec![*a, *b]),
            Row::Select(d, p, a, b) => (vec![*d], vec![*p, *a, *b]),
            Row::Cast(d, _, a) => (vec![*d], vec![*a]),
            Row::Mov(ds, ss) => (ds.clone(), ss.clone()),
            _ => unreachable!(),
        },
    }
}
pub fn apply(op: &Op, values: &mut [Bits], widths: &[usize]) {
    match op {
        Op::Enter { clear, bind } => {
            let args: Vec<_> = bind.iter().map(|(_, s)| values[*s].clone()).collect();
            for d in clear {
                values[*d] = Bits::zero(widths[*d]);
            }
            for ((d, _), v) in bind.iter().zip(args) {
                values[*d] = v;
            }
        }
        Op::Row(r) => match r {
            Row::Const(d, v) => values[*d] = v.clone(),
            Row::Bin(d, o, a, b) => values[*d] = values[*a].bin(&values[*b], o),
            Row::Cmp(d, o, a, b) => {
                values[*d] = Bits::from_u64(1, u64::from(values[*a].cmp(&values[*b], o)))
            }
            Row::Select(d, p, a, b) => {
                values[*d] = values[if values[*p].0[0] { *a } else { *b }].clone()
            }
            Row::Cast(d, o, a) => values[*d] = values[*a].cast(widths[*d], o == "sext"),
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
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn block_machine_matches_source() {
        for text in [
            include_str!("../../fixtures/inc8.bobj"),
            include_str!("../../fixtures/collatz.bobj"),
        ] {
            let p = Program::parse(text).unwrap();
            for (stack, depth) in if p.layout.is_some() {
                vec![(27, 1), (32, 32)]
            } else {
                vec![(0, 0)]
            } {
                let b = Budget {
                    steps: 3000,
                    heap: 0,
                    stack,
                    depth,
                };
                let m = Machine::build(&p, b).unwrap();
                for x in 0..256 {
                    for limit in [0, 1, 2, 3, 8, 9, 10, 27, 28, 29, 99, 100, 2048] {
                        let inp = [Bits::from_u64(8, x)];
                        let a = p.run(&inp, Budget { steps: limit, ..b }).unwrap();
                        let z = m.run(&inp, limit);
                        assert_eq!(
                            (&a.payload, &a.code),
                            (&z.payload, &z.code),
                            "x={x} B={limit}"
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn coherent_diamond_and_core_horizon_correction() {
        let p = Program::parse(include_str!("../../fixtures/diamond.bobj")).unwrap();
        let m = Machine::build(&p, Budget::steps(100)).unwrap();
        assert!(m.static_counts.is_none());
        let spin = include_str!("../../fixtures/inc8.bobj").replace(
            "one = lift.const.i8 1\nr = lift.add x one\nlift.retval r",
            "qjump ^entry",
        );
        let p = Program::parse(&spin).unwrap();
        let m = Machine::build(&p, Budget::steps(3)).unwrap();
        assert_eq!(m.blocks[0].weight, 1);
        assert_eq!(3 * m.blocks[0].weight, 3);
        let o = m.run(&[Bits::from_u64(8, 1)], 3);
        assert_eq!(o.code.low_u64(), 1);
    }
    #[test]
    fn liveness_and_period_are_bounded() {
        let p = Program::parse(include_str!("../../fixtures/collatz.bobj")).unwrap();
        let m = Machine::build(
            &p,
            Budget {
                steps: 1_000_000_000,
                heap: 0,
                stack: 32,
                depth: 32,
            },
        )
        .unwrap();
        assert!(
            m.state_variables()
                .iter()
                .map(|i| m.widths[*i])
                .sum::<usize>()
                < 200
        );
        assert!(m.reach.prefix.len() + m.reach.cycle.len() < 20);
        assert!(m.static_counts.is_none());
    }
}
