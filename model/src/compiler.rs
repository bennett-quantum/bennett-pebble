//! Baseline: weighted block evaluation with the entire old state as residue.
//! The budget occurs only in integer fields, counter width, and a Rep count.
use crate::{
    bits::Bits,
    block::{Exit, Machine, Op},
    circuit::{self as c, Cost, Term},
    gadgets::{self as g, Bit, Builder},
    source::{Budget, Program, Result, Row},
};
use std::collections::BTreeMap;
#[derive(Clone, Debug)]
pub struct Layout {
    pub pc: Vec<usize>,
    pub vars: BTreeMap<usize, Vec<usize>>,
    pub counter: Vec<usize>,
    pub stack: Vec<usize>,
    pub payload: Vec<usize>,
    pub code: Vec<usize>,
    pub width: usize,
}
#[derive(Clone, Debug)]
pub struct Compiled {
    pub term: Term,
    pub external: usize,
    pub input_width: usize,
    pub target_width: usize,
    pub fault_width: usize,
    pub state_width: usize,
    pub residue_width: usize,
    pub steps: u64,
    pub cost: Cost,
    pub machine: Machine,
    pub layout: Layout,
    pub step: Term,
    pub family: crate::schedule::Family,
    pub controlled: bool,
    pub checkpoints: u32,
    pub step_invocations: u128,
}
pub(crate) fn bits_needed(n: u64) -> usize {
    (64 - n.leading_zeros() as usize).max(1)
}
pub(crate) fn reserve(next: &mut usize, n: usize) -> Vec<usize> {
    let v = (*next..*next + n).collect();
    *next += n;
    v
}
pub(crate) fn select(b: &mut Builder, p: Bit, a: &[Bit], z: &[Bit]) -> Vec<Bit> {
    a.iter().zip(z).map(|(&a, &z)| b.mux(p, a, z)).collect()
}
pub(crate) fn masked_xor(b: &mut Builder, out: &mut [Bit], guard: Bit, value: &[Bit]) {
    for (d, v) in out.iter_mut().zip(value) {
        let a = b.and(guard, *v);
        *d = b.xor(*d, a);
    }
}
pub(crate) fn eval_ops(b: &mut Builder, ops: &[Op], values: &mut [Vec<Bit>], widths: &[usize]) {
    for op in ops {
        match op {
            Op::Enter { clear, bind } => {
                let args: Vec<_> = bind.iter().map(|(_, s)| values[*s].clone()).collect();
                for d in clear {
                    values[*d] = vec![Bit::Const(false); widths[*d]];
                }
                for ((d, _), v) in bind.iter().zip(args) {
                    values[*d] = v;
                }
            }
            Op::Row(r) => match r {
                Row::Const(d, v) => values[*d] = v.0.iter().map(|x| Bit::Const(*x)).collect(),
                Row::Bin(d, o, a, z) => values[*d] = b.vector(&values[*a], &values[*z], o),
                Row::Cmp(d, o, a, z) => values[*d] = vec![b.compare(&values[*a], &values[*z], o)],
                Row::Select(d, p, a, z) => {
                    values[*d] = select(b, values[*p][0], &values[*a], &values[*z])
                }
                Row::Cast(d, o, a) => {
                    values[*d] = (0..widths[*d])
                        .map(|i| {
                            values[*a].get(i).copied().unwrap_or(if o == "sext" {
                                values[*a][widths[*a] - 1]
                            } else {
                                Bit::Const(false)
                            })
                        })
                        .collect()
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
impl Layout {
    fn new(m: &Machine, budget: u64) -> Self {
        let mut width = 0;
        let pc = reserve(&mut width, bits_needed(m.blocks.len() as u64));
        let vars = m
            .state_variables()
            .into_iter()
            .map(|i| (i, reserve(&mut width, m.widths[i])))
            .collect();
        let counter = reserve(
            &mut width,
            if m.static_counts.is_some() {
                0
            } else {
                bits_needed(
                    budget.saturating_add(m.blocks.iter().map(|b| b.weight).max().unwrap_or(1)),
                ) + 1
            },
        );
        let stack = reserve(
            &mut width,
            if m.uses_stack {
                bits_needed(m.stack_limit) + 1
            } else {
                0
            },
        );
        let payload = reserve(&mut width, m.target_width);
        let code = reserve(&mut width, m.fault_width);
        Self {
            pc,
            vars,
            counter,
            stack,
            payload,
            code,
            width,
        }
    }
}
pub(crate) fn step_outputs(
    m: &Machine,
    l: &Layout,
    budget: u64,
    mut b: &mut Builder,
    old: &[Bit],
    _input_width: usize,
    freeze: bool,
    allowed: Option<&std::collections::BTreeSet<usize>>,
) -> (Vec<Bit>, Vec<Bit>) {
    let read = |indices: &[usize]| indices.iter().map(|i| old[*i]).collect::<Vec<_>>();
    let oldpc = read(&l.pc);
    let mut output = vec![Bit::Const(false); l.width];
    let mut live_guards = vec![Bit::Const(false); m.blocks.len()];
    let known = if freeze {
        Some(crate::symbolic::rematerializable(m))
    } else {
        None
    };
    for (id, block) in m.blocks.iter().enumerate() {
        if allowed.is_some_and(|s| !s.contains(&id)) {
            continue;
        }
        let at = b.compare(&oldpc, &g::constant(l.pc.len(), id as u64), "eq");
        let mut values: Vec<_> = m
            .widths
            .iter()
            .map(|n| vec![Bit::Const(false); *n])
            .collect();
        let mut offset = 0;
        for i in &m.inputs {
            values[*i] = g::wires(offset, m.widths[*i]);
            offset += m.widths[*i];
        }
        for (i, v) in &l.vars {
            values[*i] = read(v);
        }
        for (i, v) in &m.constants {
            values[*i] = v.0.iter().map(|v| Bit::Const(*v)).collect();
        }
        if let Some(known) = &known {
            let inputs: std::collections::BTreeMap<_, _> =
                m.inputs.iter().map(|i| (*i, values[*i].clone())).collect();
            for i in &block.live_in {
                if let Some(expr) = &known[id][*i] {
                    values[*i] =
                        crate::symbolic::eval(expr, b, &std::collections::BTreeMap::new(), &inputs)
                            .expect("known entry expression");
                }
            }
        }
        eval_ops(&mut b, &block.ops, &mut values, &m.widths);
        let mut next = vec![Bit::Const(false); l.width];
        for (i, indices) in &l.vars {
            if block.live_out.contains(i) {
                for (wire, value) in indices.iter().zip(&values[*i]) {
                    next[*wire] = *value;
                }
            }
        }
        let mut failed = Bit::Const(false);
        let mut next_stack = read(&l.stack);
        if let Exit::Stack { cells, .. } = block.exit {
            let added = b.vector(&next_stack, &g::constant(l.stack.len(), cells), "add");
            failed = b.compare(&g::constant(l.stack.len(), m.stack_limit), &added, "ult");
            next_stack = if freeze {
                added
            } else {
                select(&mut b, failed, &next_stack, &added)
            };
        }
        for (i, v) in l.stack.iter().zip(next_stack) {
            next[*i] = v;
        }
        let count = if let Some(counts) = &m.static_counts {
            g::constant(
                bits_needed(budget.max(counts[id].saturating_add(block.weight))) + 1,
                counts[id] + block.weight,
            )
        } else {
            let added = b.vector(
                &read(&l.counter),
                &g::constant(l.counter.len(), block.weight),
                "add",
            );
            for (i, v) in l.counter.iter().zip(&added) {
                next[*i] = *v;
            }
            added
        };
        let over = b.compare(&g::constant(count.len(), budget), &count, "ult");
        let halt = m.blocks.len() as u64;
        let (npc, payload, code) = match block.exit.clone() {
            Exit::Jump(n) => (
                g::constant(l.pc.len(), n as u64),
                vec![Bit::Const(false); m.target_width],
                g::constant(m.fault_width, 0),
            ),
            Exit::Branch(p, a, z) => (
                select(
                    &mut b,
                    values[p][0],
                    &g::constant(l.pc.len(), a as u64),
                    &g::constant(l.pc.len(), z as u64),
                ),
                vec![Bit::Const(false); m.target_width],
                g::constant(m.fault_width, 0),
            ),
            Exit::FaultIf(p, code, n) => (
                select(
                    &mut b,
                    values[p][0],
                    &g::constant(l.pc.len(), halt),
                    &g::constant(l.pc.len(), n as u64),
                ),
                vec![Bit::Const(false); m.target_width],
                select(
                    &mut b,
                    values[p][0],
                    &code.0.iter().map(|b| Bit::Const(*b)).collect::<Vec<_>>(),
                    &g::constant(m.fault_width, 0),
                ),
            ),
            Exit::Fault(code) => (
                g::constant(l.pc.len(), halt),
                vec![Bit::Const(false); m.target_width],
                code.0.iter().map(|b| Bit::Const(*b)).collect::<Vec<_>>(),
            ),
            Exit::Success(p) => (
                g::constant(l.pc.len(), halt),
                values[p].clone(),
                g::constant(m.fault_width, 0),
            ),
            Exit::Stack { next, .. } => (
                select(
                    &mut b,
                    failed,
                    &g::constant(l.pc.len(), halt),
                    &g::constant(l.pc.len(), next as u64),
                ),
                vec![Bit::Const(false); m.target_width],
                select(
                    &mut b,
                    failed,
                    &g::constant(m.fault_width, 3),
                    &g::constant(m.fault_width, 0),
                ),
            ),
        };
        let npc = select(&mut b, over, &g::constant(l.pc.len(), halt), &npc);
        let payload = select(
            &mut b,
            over,
            &vec![Bit::Const(false); m.target_width],
            &payload,
        );
        let code = select(&mut b, over, &g::constant(m.fault_width, 1), &code);
        let halting = b.compare(&npc, &g::constant(l.pc.len(), halt), "eq");
        let running = b.not(halting);
        live_guards[id] = b.and(at, running);
        if freeze {
            for (variable, indices) in &l.vars {
                if block.live_out.contains(variable) {
                    let mut allowed = Bit::Const(false);
                    for (target, target_block) in m.blocks.iter().enumerate() {
                        if target_block.live_in.contains(variable) {
                            let is_target =
                                b.compare(&npc, &g::constant(l.pc.len(), target as u64), "eq");
                            allowed = b.or(allowed, is_target);
                        }
                    }
                    for i in indices {
                        next[*i] = b.and(allowed, next[*i]);
                    }
                }
            }
            let data: std::collections::BTreeSet<_> = l.vars.values().flatten().copied().collect();
            for i in data {
                next[i] = b.mux(halting, old[i], next[i]);
            }
        }
        for (indices, data) in [(&l.pc, npc), (&l.payload, payload), (&l.code, code)] {
            for (i, v) in indices.iter().zip(data) {
                next[*i] = v;
            }
        }
        masked_xor(&mut b, &mut output, at, &next);
    }
    let athalt = b.compare(
        &oldpc,
        &g::constant(l.pc.len(), m.blocks.len() as u64),
        "eq",
    );
    masked_xor(&mut b, &mut output, athalt, &old);
    (output, live_guards)
}
pub(crate) fn step(
    m: &Machine,
    l: &Layout,
    budget: u64,
    allowed: Option<&std::collections::BTreeSet<usize>>,
) -> Term {
    let input_width: usize = m.inputs.iter().map(|i| m.widths[*i]).sum();
    let external = input_width + 2 * l.width;
    let mut b = Builder::new(external);
    let old = g::wires(input_width, l.width);
    let (output, _) = step_outputs(m, l, budget, &mut b, &old, input_width, false, allowed);
    let outputs: Vec<_> = output
        .into_iter()
        .enumerate()
        .map(|(i, v)| (input_width + l.width + i, v))
        .collect();
    let evaluator = b.finish(external, &outputs);
    let swaps = c::seq(
        (0..l.width)
            .map(|i| g::swap(input_width + i, input_width + l.width + i))
            .collect(),
    );
    c::seq(vec![evaluator, swaps])
}

impl Compiled {
    pub fn baseline(p: &Program, budget: Budget, controlled: bool) -> Result<Self> {
        let machine = Machine::build(p, budget)?;
        let (cutoff, scheduled) = machine.horizon(budget.steps);
        let layout = Layout::new(&machine, cutoff);
        let state_width = layout.width;
        let input_width: usize = machine.inputs.iter().map(|i| machine.widths[*i]).sum();
        let external =
            input_width + machine.target_width + machine.fault_width + usize::from(controlled);
        let step = step(&machine, &layout, cutoff, None);
        let family = crate::schedule::Family::build(&machine, |set| {
            self::step(&machine, &layout, cutoff, Some(set))
        });
        let history = state_width
            .checked_mul(
                usize::try_from(scheduled).map_err(|_| "step count exceeds address space")?,
            )
            .ok_or("history width exceeds address space")?;
        let arity = external
            .checked_add(state_width + history)
            .ok_or("wire count exceeds address space")?;
        let compute = family.segment(
            0,
            scheduled,
            input_width,
            state_width,
            state_width,
            external,
            external + state_width,
        );
        let commit = Self::commit(&machine, &layout, external, input_width, arity, controlled);
        let term = c::with(
            external,
            state_width + history,
            c::seq(vec![compute.clone(), commit, c::adj(compute)]),
        );
        let cost = c::cost(&term);
        Ok(Self::zero_budget(
            Self {
                term,
                external,
                input_width,
                target_width: machine.target_width,
                fault_width: machine.fault_width,
                state_width,
                residue_width: state_width,
                steps: scheduled,
                cost,
                machine,
                layout,
                step,
                family,
                controlled,
                checkpoints: 0,
                step_invocations: 2 * u128::from(scheduled),
            },
            budget,
        ))
    }
    pub fn pebbled(
        p: &Program,
        budget: Budget,
        controlled: bool,
        peak_budget: usize,
    ) -> Result<Self> {
        Self::schedule(
            Self::baseline(p, budget, controlled)?,
            budget,
            controlled,
            peak_budget,
        )
    }
    pub fn pebbled_optimized(
        p: &Program,
        budget: Budget,
        controlled: bool,
        peak_budget: usize,
    ) -> Result<Self> {
        Self::schedule(
            Self::optimized(p, budget, controlled)?,
            budget,
            controlled,
            peak_budget,
        )
    }
    pub(crate) fn schedule(
        mut out: Self,
        _budget: Budget,
        controlled: bool,
        peak_budget: usize,
    ) -> Result<Self> {
        if out.cost.peak(out.external) <= peak_budget {
            return Ok(out);
        }
        let m = out.state_width;
        let r = out.residue_width;
        let input = out.input_width;
        let (workspace, ladder, price) = out.auxiliary();
        let fixed = out.external + workspace + ladder;
        let available = peak_budget
            .checked_sub(fixed)
            .ok_or("peak budget below evaluator workspace")?;
        let plan = crate::chain::uniform(
            out.steps,
            m as u64,
            r as u64,
            price.max(1),
            0,
            available as u64,
        )
        .ok_or("no regular nested strategy fits peak budget")?;
        crate::chain::check_uniform(&plan, m as u64, r as u64, price.max(1), 0, available as u64)?;
        fn clean(
            family: &crate::schedule::Family,
            input: usize,
            m: usize,
            r: usize,
            leaf: u64,
            levels: u32,
            start: u64,
            memo: &mut std::collections::BTreeMap<(u32, usize), Term>,
        ) -> Term {
            let key = (levels, family.phase(start));
            if let Some(term) = memo.get(&key) {
                return term.clone();
            }
            let external = input + 2 * m;
            let term = if levels == 0 {
                let forward = family.segment(start, leaf, input, m, r, input, external);
                let copy = c::seq(
                    (0..m)
                        .map(|i| c::gate(&[input + i], input + m + i))
                        .collect(),
                );
                c::with(
                    external,
                    r * leaf as usize,
                    c::seq(vec![forward.clone(), copy, c::adj(forward)]),
                )
            } else {
                let left = clean(family, input, m, r, leaf, levels - 1, start, memo);
                let right = clean(
                    family,
                    input,
                    m,
                    r,
                    leaf,
                    levels - 1,
                    start + leaf * (1u64 << (levels - 1)),
                    memo,
                );
                let left = c::call(left, (0..input + m).chain(external..external + m).collect());
                let right = c::call(
                    right,
                    (0..input)
                        .chain(external..external + m)
                        .chain(input + m..input + 2 * m)
                        .collect(),
                );
                c::with(external, m, c::seq(vec![left.clone(), right, c::adj(left)]))
            };
            memo.insert(key, term.clone());
            term
        }
        let compute = if out.steps == 0 {
            c::seq(vec![])
        } else {
            clean(
                &out.family,
                input,
                m,
                r,
                plan.leaf,
                plan.levels,
                0,
                &mut std::collections::BTreeMap::new(),
            )
        };
        let map: Vec<_> = (0..input)
            .chain(out.external..out.external + 2 * m)
            .collect();
        let compute = c::call(compute, map);
        let arity = out.external + 2 * m;
        let commit = Self::commit(
            &out.machine,
            &out.layout,
            out.external + m,
            input,
            arity,
            controlled,
        );
        let term = c::with(
            out.external,
            2 * m,
            c::seq(vec![compute.clone(), commit, c::adj(compute)]),
        );
        let cost = c::cost(&term);
        if cost.peak(out.external) > peak_budget {
            return Err(format!(
                "strategy needs {} wires, budget {peak_budget}",
                cost.peak(out.external)
            ));
        }
        out.term = term;
        out.cost = cost;
        out.steps = plan.scheduled;
        out.checkpoints = plan.levels + 1;
        out.step_invocations = 2 * plan.advances;
        Ok(out)
    }
    pub(crate) fn zero_budget(mut out: Self, budget: Budget) -> Self {
        if budget.steps == 0 {
            let controls = if out.controlled {
                vec![out.external - 1]
            } else {
                vec![]
            };
            out.term = c::gate(&controls, out.input_width + out.target_width);
            out.cost = c::cost(&out.term);
            out.steps = 0;
            out.step_invocations = 0;
            out.checkpoints = 0;
        }
        out
    }
    pub fn auxiliary(&self) -> (usize, usize, u128) {
        let mut workspace = 0;
        let mut ladder = 0;
        let mut price = 0;
        for term in self.family.prefix.iter().chain(&self.family.cycle) {
            let cost = c::cost(term);
            workspace = workspace.max(cost.extra_peak);
            ladder = ladder.max(cost.ladder_ancillas());
            price = price.max(cost.toffoli());
        }
        (workspace, ladder, price)
    }
    /// Small, explicit candidate set. The optimizer is not trusted: every
    /// chosen circuit has the same whole-tuple verification interface.
    pub fn best(p: &Program, budget: Budget, controlled: bool, cap: Option<usize>) -> Result<Self> {
        let candidates = [
            Self::baseline(p, budget, controlled),
            Self::optimized(p, budget, controlled),
            Self::optimized_compact(p, budget, controlled),
        ];
        let mut best = None;
        let mut reasons = vec![];
        for candidate in candidates {
            let result = candidate.and_then(|c| {
                if let Some(cap) = cap {
                    Self::schedule(c, budget, controlled, cap)
                } else {
                    Ok(c)
                }
            });
            match result {
                Ok(c) => {
                    let price = (c.cost.toffoli(), c.cost.total(), c.cost.peak(c.external));
                    if best.as_ref().is_none_or(|old: &Self| {
                        price
                            < (
                                old.cost.toffoli(),
                                old.cost.total(),
                                old.cost.peak(old.external),
                            )
                    }) {
                        best = Some(c);
                    }
                }
                Err(e) => reasons.push(e),
            }
        }
        best.ok_or_else(|| reasons.join("; "))
    }
    pub fn commit(
        m: &Machine,
        l: &Layout,
        state_start: usize,
        input_width: usize,
        arity: usize,
        controlled: bool,
    ) -> Term {
        let old: Vec<_> = g::wires(state_start, l.width);
        let mut b = Builder::new(arity);
        let pc: Vec<_> = l.pc.iter().map(|i| old[*i]).collect();
        let halt = b.compare(&pc, &g::constant(l.pc.len(), m.blocks.len() as u64), "eq");
        let mut outputs = vec![];
        for (j, i) in l.payload.iter().enumerate() {
            let v = b.and(halt, old[*i]);
            outputs.push((input_width + j, v));
        }
        for (j, i) in l.code.iter().enumerate() {
            let v = b.mux(halt, old[*i], Bit::Const(j == 0));
            outputs.push((input_width + m.target_width + j, v));
        }
        // Only the commit gates inherit q. Predicate computation is unconditional.
        let allocated = b.next - arity;
        let compute = c::seq(b.gates);
        let mut copy = Builder::new(b.next);
        for (d, v) in outputs {
            copy.copy(v, d);
        }
        let copy = c::seq(copy.gates);
        let copy = if controlled {
            c::ctrl(vec![input_width + m.target_width + m.fault_width], copy)
        } else {
            copy
        };
        c::with(
            arity,
            allocated,
            c::seq(vec![compute.clone(), copy, c::adj(compute)]),
        )
    }
    /// Exact verification for 8-bit fixtures, including all initial target and
    /// fault values as affine symbols, and both coherent-control basis values.
    pub fn verify_truth(&self, p: &Program, budget: Budget) -> Result<u64> {
        if self.input_width > 8 || self.target_width + self.fault_width > 128 {
            return self.verify(p, budget);
        }
        let domain = 1usize << (self.input_width + usize::from(self.controlled));
        let mut initial = vec![c::Truth::default(); self.external];
        for xq in 0..512 {
            let x = xq & ((1usize << self.input_width) - 1);
            for (i, w) in initial.iter_mut().enumerate().take(self.input_width) {
                if (x >> i) & 1 != 0 {
                    w.values[xq / 64] |= 1u64 << (xq % 64);
                }
            }
            if self.controlled && ((xq >> self.input_width) & 1) != 0 {
                initial[self.external - 1].values[xq / 64] |= 1u64 << (xq % 64);
            }
        }
        for i in 0..self.target_width + self.fault_width {
            initial[self.input_width + i].symbols = 1u128 << i;
        }
        let mut expected = initial.clone();
        for xq in 0..512 {
            let x = xq & ((1usize << self.input_width) - 1);
            let q = !self.controlled || ((xq >> self.input_width) & 1) != 0;
            let mut off = 0;
            let mut inputs = vec![];
            for i in &p.functions[0].inputs {
                let n = p.functions[0].widths[*i];
                inputs.push(Bits::from_u64(n, ((x >> off) & ((1 << n) - 1)) as u64));
                off += n;
            }
            let out = p.run(&inputs, budget)?;
            if q {
                for (i, b) in out.payload.0.iter().enumerate() {
                    if *b {
                        expected[self.input_width + i].values[xq / 64] ^= 1u64 << (xq % 64);
                    }
                }
                for (i, b) in out.code.0.iter().enumerate() {
                    if *b {
                        expected[self.input_width + self.target_width + i].values[xq / 64] ^=
                            1u64 << (xq % 64);
                    }
                }
            }
        }
        let mut sim = c::TruthSimulator::new(initial);
        sim.run(&self.term).map_err(|e| e.to_string())?;
        if sim.wires != expected {
            return Err("truth simulator entire-tuple mismatch".into());
        }
        if sim.executed != self.cost.total() {
            return Err("truth simulator gate counter mismatch".into());
        }
        if sim.peak != self.external + self.cost.extra_peak {
            return Err("truth simulator native peak mismatch".into());
        }
        Ok((domain as u64)
            .checked_shl((self.target_width + self.fault_width) as u32)
            .unwrap_or(u64::MAX))
    }
    /// Exhaust all environment inputs; several arbitrary, nonzero tgt/fr states.
    /// Lane packing changes no gate semantics and checks every final interface bit.
    /// Scope release checks every scratch bit before it is deallocated.
    pub fn verify(&self, p: &Program, budget: Budget) -> Result<u64> {
        if self.input_width > 12 {
            return Err("exhaustive harness limited to 12 environment bits".into());
        }
        let mut checked = 0;
        let mask = |n: usize| if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
        for (t, f) in [
            (0, 0),
            (mask(self.target_width), 15),
            (0x55 & mask(self.target_width), 9),
        ] {
            for q in if self.controlled {
                vec![false, true]
            } else {
                vec![true]
            } {
                for base in (0..(1u64 << self.input_width)).step_by(64) {
                    let lanes = ((1u64 << self.input_width) - base).min(64);
                    let mut initial = vec![0u64; self.external];
                    let mut expected = vec![0u64; self.external];
                    for lane in 0..lanes {
                        let x = base + lane;
                        let mut inputs = vec![];
                        let mut off = 0;
                        for i in &p.functions[0].inputs {
                            let n = p.functions[0].widths[*i];
                            let v = (x >> off) & mask(n);
                            inputs.push(Bits::from_u64(n, v));
                            off += n;
                        }
                        let outcome = p.run(&inputs, budget)?;
                        for i in 0..self.input_width {
                            if (x >> i) & 1 != 0 {
                                initial[i] |= 1u64 << lane;
                            }
                        }
                        for i in 0..self.target_width {
                            if i < 64 && (t >> i) & 1 != 0 {
                                initial[self.input_width + i] |= 1u64 << lane;
                            }
                        }
                        for i in 0..self.fault_width {
                            if i < 64 && (f >> i) & 1 != 0 {
                                initial[self.input_width + self.target_width + i] |= 1u64 << lane;
                            }
                        }
                        if self.controlled && q {
                            initial[self.external - 1] |= 1u64 << lane;
                        }
                        for (i, w) in initial.iter().enumerate() {
                            if w & (1u64 << lane) != 0 {
                                expected[i] |= 1u64 << lane;
                            }
                        }
                        if q {
                            for (i, b) in outcome.payload.0.iter().enumerate() {
                                if *b {
                                    expected[self.input_width + i] ^= 1u64 << lane;
                                }
                            }
                            for i in 0..self.fault_width {
                                if outcome.code.0[i] {
                                    expected[self.input_width + self.target_width + i] ^=
                                        1u64 << lane;
                                }
                            }
                        }
                        checked += 1;
                    }
                    let mut sim = c::Lanes::new(initial);
                    sim.run(&self.term)
                        .map_err(|e| format!("scratch or simulation failure: {e}"))?;
                    let valid = if lanes == 64 {
                        !0u64
                    } else {
                        (1u64 << lanes) - 1
                    };
                    for (i, (actual, want)) in sim.wires.iter().zip(expected).enumerate() {
                        if (actual ^ want) & valid != 0 {
                            return Err(format!(
                                "entire-tuple mismatch at interface wire {i}, input batch {base}, tgt {t}, fr {f}, control {q}"
                            ));
                        }
                    }
                    if sim.executed != self.cost.total() {
                        return Err("cost recursion differs from executed gates".into());
                    }
                }
            }
        }
        Ok(checked)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fixed_classical_arguments_are_staged_and_read_only() {
        let p = crate::measure::load("add_classical").unwrap();
        assert!(
            Compiled::optimized(&p, Budget::steps(3), true)
                .unwrap_err()
                .contains("bound")
        );
        for delta in [0, 5, 129, 255] {
            let p = p.bind_classical(&[Bits::from_u64(8, delta)]).unwrap();
            for b in [0, 1, 2, 3] {
                let budget = Budget::steps(b);
                let compiled = Compiled::optimized(&p, budget, true).unwrap();
                assert_eq!(compiled.input_width, 8);
                compiled.verify_truth(&p, budget).unwrap();
                for x in [0, 1, 255] {
                    let out = p.run(&[Bits::from_u64(8, x)], budget).unwrap();
                    assert_eq!(
                        out.payload.low_u64(),
                        if b >= 2 { (x + delta) & 255 } else { 0 }
                    );
                }
            }
        }
        let text = include_str!("../../fixtures/add_classical.bobj");
        assert!(
            Program::parse(&text.replace("r = lift.add x delta", "delta = lift.mov x"))
                .unwrap_err()
                .contains("read-only")
        );
        for ty in ["ptr", "f64"] {
            let text = text
                .replace("delta:i8", &format!("delta:{ty}"))
                .replace("r = lift.add x delta", "r = lift.trunc.i8 delta");
            let p = Program::parse(&text).unwrap();
            let width = if ty == "ptr" { 32 } else { 64 };
            let p = p
                .bind_classical(&[Bits::from_u64(width, 0xdeadbeef)])
                .unwrap();
            let b = Budget::steps(2);
            Compiled::optimized(&p, b, true)
                .unwrap()
                .verify_truth(&p, b)
                .unwrap();
        }
    }
    #[test]
    fn activations_monotonic_stack_and_initial_call_faults() {
        for (name, stack, depth) in [
            ("call_loop", 10, 1),
            ("countdown", 27, 3),
            ("collatz", 27, 1),
        ] {
            let p = crate::measure::load(name).unwrap();
            for steps in [0, 1, 5, 15, 40] {
                let b = Budget {
                    steps,
                    heap: 0,
                    stack,
                    depth,
                };
                for compact in [false, true] {
                    let c = Compiled::optimized_style(&p, b, true, compact).unwrap();
                    c.verify_truth(&p, b).unwrap();
                }
            }
        }
    }
    #[test]
    fn affine_truth_verifier_agrees_with_sampled_basis_simulation() {
        for name in ["inc8", "collatz", "faultif"] {
            let p = crate::measure::load(name).unwrap();
            let b = crate::measure::budget(&p, 28);
            for control in [false, true] {
                let c = Compiled::optimized(&p, b, control).unwrap();
                c.verify(&p, b).unwrap();
                let cases = c.verify_truth(&p, b).unwrap();
                assert_eq!(cases, 256 * 4096 * if control { 2 } else { 1 });
            }
        }
    }
    #[test]
    fn baseline_inc8_all_boundary_budgets() {
        let p = Program::parse(include_str!("../../fixtures/inc8.bobj")).unwrap();
        for b in 0..=5 {
            for q in [false, true] {
                let budget = Budget::steps(b);
                let compiled = Compiled::baseline(&p, budget, q).unwrap();
                compiled.verify(&p, budget).unwrap();
            }
        }
    }
    #[test]
    fn baseline_collatz_small_budget() {
        let p = Program::parse(include_str!("../../fixtures/collatz.bobj")).unwrap();
        for b in [0, 1, 8, 9, 10, 27, 28, 29] {
            let budget = Budget {
                steps: b,
                heap: 0,
                stack: 32,
                depth: 32,
            };
            let compiled = Compiled::baseline(&p, budget, true).unwrap();
            compiled.verify(&p, budget).unwrap();
        }
    }
    #[test]
    fn pebbled_circuits_force_multiple_levels() {
        for text in [
            include_str!("../../fixtures/popcount.bobj"),
            include_str!("../../fixtures/diamond.bobj"),
        ] {
            let p = Program::parse(text).unwrap();
            let budget = Budget::steps(16);
            let baseline = Compiled::baseline(&p, budget, true).unwrap();
            let (workspace, ladder, _) = baseline.auxiliary();
            let tight = baseline.external + workspace + ladder + 7 * baseline.state_width;
            let compiled = Compiled::pebbled(&p, budget, true, tight).unwrap();
            assert!(compiled.checkpoints >= 4);
            assert!(compiled.cost.peak(compiled.external) <= tight);
            compiled.verify(&p, budget).unwrap();
        }
    }
    #[test]
    fn huge_description_is_small() {
        let p = Program::parse(include_str!("../../fixtures/collatz.bobj")).unwrap();
        let compiled = Compiled::baseline(
            &p,
            Budget {
                steps: 1_000_000_000,
                heap: 0,
                stack: 32,
                depth: 32,
            },
            true,
        )
        .unwrap();
        assert!(compiled.cost.total() > 1_000_000_000);
    }
}
