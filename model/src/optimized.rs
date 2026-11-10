//! Automatic residue synthesis for the weighted machine. Old control state is
//! retained; data residues are selected by the checked local inverse rules.
use crate::{
    bits::Bits,
    block::{Exit, Machine},
    circuit::{self as c, Term},
    compiler::{Compiled, Layout, bits_needed, masked_xor, reserve, step_outputs},
    gadgets::{self as g, Bit, Builder},
    source::{Budget, Program, Result},
    symbolic::{self as s, E, Inverter, Kind},
};
use std::collections::{BTreeMap, BTreeSet};
fn layout(m: &Machine, budget: u64) -> Layout {
    let mut next = 0;
    let pc = reserve(&mut next, bits_needed(m.blocks.len() as u64));
    let known = s::rematerializable(m);
    let vars = m.state_variables().into_iter().filter(|i| {
        m.blocks
            .iter()
            .enumerate()
            .any(|(b, block)| block.live_in.contains(i) && known[b][*i].is_none())
    });
    let mut assigned = BTreeMap::<usize, Vec<usize>>::new();
    let mut slots = Vec::<(usize, Vec<usize>, Vec<usize>)>::new();
    for id in vars {
        let n = m.widths[id];
        let compatible = slots.iter().position(|(w, _, occupants)| {
            *w == n
                && occupants.iter().all(|other| {
                    !m.blocks.iter().any(|b| {
                        (b.live_in.contains(&id) && b.live_in.contains(other))
                            || (b.live_out.contains(&id) && b.live_out.contains(other))
                    })
                })
        });
        let index = if let Some(i) = compatible {
            i
        } else {
            slots.push((n, reserve(&mut next, n), vec![]));
            slots.len() - 1
        };
        slots[index].2.push(id);
        assigned.insert(id, slots[index].1.clone());
    }
    let counter = reserve(
        &mut next,
        if m.static_counts.is_some() {
            0
        } else {
            bits_needed(budget.saturating_add(m.blocks.iter().map(|b| b.weight).max().unwrap_or(1)))
                + 1
        },
    );
    let stack = reserve(
        &mut next,
        if m.uses_stack {
            bits_needed(m.stack_limit.saturating_add(m.widths.len() as u64)) + 1
        } else {
            0
        },
    );
    let payload = reserve(&mut next, m.target_width);
    let code = reserve(&mut next, m.fault_width);
    Layout {
        pc,
        vars: assigned,
        counter,
        stack,
        payload,
        code,
        width: next,
    }
}
// Residue selection precedes physical allocation. Remove the unused logical
// frame reservation before assigning the temporary state and gadget wires.
// The block evaluator has no repetitions or calls: these belong to the outer
// schedule, whose coordinate systems are intentionally left alone.
fn close_gap(root: &Term, start: usize, end: usize) -> Term {
    fn go(t: &Term, start: usize, end: usize, memo: &mut BTreeMap<usize, Term>) -> Term {
        let key = std::rc::Rc::as_ptr(t) as usize;
        if let Some(t) = memo.get(&key) {
            return t.clone();
        }
        let wire = |w: usize| {
            assert!(
                w < start || w >= end,
                "used wire in scratch reservation gap"
            );
            if w >= end { w - (end - start) } else { w }
        };
        let out = match t.as_ref() {
            c::Node::Gate(g) => c::gate(
                &g.controls.iter().map(|w| wire(*w)).collect::<Vec<_>>(),
                wire(g.target),
            ),
            c::Node::Seq(ts) => c::seq(ts.iter().map(|t| go(t, start, end, memo)).collect()),
            c::Node::Adj(t) => c::adj(go(t, start, end, memo)),
            c::Node::Ctrl { controls, body } => c::ctrl(
                controls.iter().map(|w| wire(*w)).collect(),
                go(body, start, end, memo),
            ),
            c::Node::With {
                external,
                allocated,
                body,
            } => {
                let external = wire(*external);
                c::with(external, *allocated, go(body, start, end, memo))
            }
            _ => unreachable!("block evaluator contains schedule-level terms"),
        };
        memo.insert(key, out.clone());
        out
    }
    if start == end {
        root.clone()
    } else {
        go(root, start, end, &mut BTreeMap::new())
    }
}
fn source_guard(
    b: &mut Builder,
    source: usize,
    newpc: &[Bit],
    rank_base: usize,
    rank_width: usize,
    pred: &[Vec<usize>],
) -> Bit {
    let rank = g::wires(rank_base, rank_width);
    let mut out = Bit::Const(false);
    for (target, predecessors) in pred.iter().enumerate() {
        if let Some(r) = predecessors.iter().position(|p| *p == source) {
            let pc = b.compare(newpc, &g::constant(newpc.len(), target as u64), "eq");
            let pr = b.compare(&rank, &g::constant(rank_width, r as u64), "eq");
            let term = b.and(pc, pr);
            out = b.or(out, term);
        }
    }
    out
}
fn step(
    m: &Machine,
    l: &Layout,
    budget: u64,
    compact: bool,
    allowed: Option<&BTreeSet<usize>>,
) -> Result<(Term, usize)> {
    let input: usize = m.inputs.iter().map(|i| m.widths[*i]).sum();
    let state = l.width;
    let halt_id = m.blocks.len();
    let mut predecessors = vec![BTreeSet::new(); halt_id + 1];
    for (b, block) in m.blocks.iter().enumerate() {
        let successors = match block.exit {
            Exit::Jump(n) | Exit::Stack { next: n, .. } | Exit::FaultIf(_, _, n) => vec![n],
            Exit::Branch(_, a, z) => vec![a, z],
            _ => vec![],
        };
        for n in successors {
            predecessors[n].insert(b);
        }
        predecessors[halt_id].insert(b);
    }
    predecessors[halt_id].insert(halt_id);
    let predecessors: Vec<Vec<usize>> = predecessors
        .into_iter()
        .map(|p| p.into_iter().collect())
        .collect();
    let rank_width = bits_needed(
        predecessors
            .iter()
            .map(|p| p.len().saturating_sub(1) as u64)
            .max()
            .unwrap_or(0),
    );
    let maxframe = state + m.blocks.iter().map(|b| b.ops.len()).sum::<usize>() + 1;
    let scratch_start = input + state + maxframe + state;
    let residue_base = input + state + rank_width;
    let input_values: BTreeMap<_, _> = {
        let mut offset = 0;
        m.inputs
            .iter()
            .map(|id| {
                let v = g::wires(offset, m.widths[*id]);
                offset += m.widths[*id];
                (*id, v)
            })
            .collect()
    };
    let newvalues = g::wires(input, state);
    let newvar = |indices: &[usize]| indices.iter().map(|i| newvalues[*i]).collect::<Vec<_>>();
    let mut plans = vec![];
    let mut residues = rank_width;
    let known = s::rematerializable(m);
    for (block_id, block) in m.blocks.iter().enumerate() {
        let mut values: Vec<E> = m
            .widths
            .iter()
            .map(|n| s::constant(Bits::zero(*n)))
            .collect();
        for id in &m.inputs {
            values[*id] = s::input(m.widths[*id], *id);
        }
        for id in &block.live_in {
            if !m.inputs.contains(id) {
                values[*id] = known[block_id][*id]
                    .clone()
                    .unwrap_or_else(|| s::var(m.widths[*id], *id));
            }
        }
        s::expressions(&block.ops, &mut values, &m.widths);
        let mut inv = Inverter::new(scratch_start, residue_base, input_values.clone());
        inv.compact_inverse = compact;
        let mut outputs = vec![];
        for id in &block.live_out {
            let Some(indices) = l.vars.get(id) else {
                continue;
            };
            let expr = &values[*id];
            let mut result = newvar(indices);
            let mut usable = true;
            let successors = match block.exit {
                Exit::Jump(n) | Exit::Stack { next: n, .. } | Exit::FaultIf(_, _, n) => vec![n],
                Exit::Branch(_, a, z) => vec![a, z],
                _ => vec![],
            };
            for target in successors {
                if m.blocks[target].live_in.contains(id) {
                    continue;
                }
                let mut replacement = None;
                if let Exit::Branch(p, a, z) = block.exit {
                    if a == z {
                        usable = false;
                        break;
                    }
                    if let Kind::Cmp(op, left, right) = &values[p].kind {
                        let truth = target == a;
                        if (op == "eq" && truth) || (op == "ne" && !truth) {
                            if std::rc::Rc::ptr_eq(left, expr) {
                                if let Kind::Const(v) = &right.kind {
                                    replacement = Some(
                                        v.0.iter().map(|v| Bit::Const(*v)).collect::<Vec<_>>(),
                                    );
                                }
                            } else if std::rc::Rc::ptr_eq(right, expr) {
                                if let Kind::Const(v) = &left.kind {
                                    replacement = Some(
                                        v.0.iter().map(|v| Bit::Const(*v)).collect::<Vec<_>>(),
                                    );
                                }
                            }
                        }
                    }
                }
                if let Some(value) = replacement {
                    let at = inv.builder.compare(
                        &newvar(&l.pc),
                        &g::constant(l.pc.len(), target as u64),
                        "eq",
                    );
                    result = result
                        .iter()
                        .zip(value)
                        .map(|(a, z)| inv.builder.mux(at, z, *a))
                        .collect();
                } else {
                    usable = false;
                    break;
                }
            }
            if usable {
                outputs.push((expr.clone(), result));
            }
        }
        for (expr, v) in &outputs {
            if let Kind::Var(id) = expr.kind {
                inv.known.insert(id, v.clone());
            }
        }
        for id in &block.live_in {
            if l.vars.contains_key(id) {
                if let Some(expr) = &known[block_id][*id] {
                    let value = s::eval(expr, &mut inv.builder, &BTreeMap::new(), &input_values)
                        .ok_or("known inverse entry expression")?;
                    inv.known.insert(*id, value);
                }
                if matches!(block.exit, Exit::Success(_) | Exit::Fault(_)) {
                    inv.known
                        .insert(*id, vec![Bit::Const(false); m.widths[*id]]);
                } else {
                    inv.solve(*id, m.widths[*id], &outputs);
                }
            }
        }
        residues = residues.max(rank_width + inv.saved.len());
        plans.push(inv);
    }
    if residues > maxframe {
        return Err("residue planner exceeded conservative frame bound".into());
    }
    let external = input + state + residues;
    let intermediate = input + state + maxframe;
    let big = scratch_start;
    // Forward expressions produce both the next state and guarded residues.
    let mut f = Builder::new(big);
    let old = g::wires(input, state);
    let (output, guards) = step_outputs(m, l, budget, &mut f, &old, input, true, allowed);
    let mut assignments: Vec<_> = output
        .into_iter()
        .enumerate()
        .map(|(i, v)| (intermediate + i, v))
        .collect();
    let oldpc: Vec<_> = l.pc.iter().map(|i| old[*i]).collect();
    let newpc: Vec<_> = l.pc.iter().map(|i| Bit::Wire(intermediate + *i)).collect();
    // Rank is computed from the forward expressions before the exchange. It
    // uses expression bits, not the output slots which are still clean.
    // Reuse the original forward expression graph instead: append a separate
    // clean evaluator for rank after next-state slots have been populated.
    let mut rank_builder = Builder::new(big);
    let mut rank_bits = vec![Bit::Const(false); rank_width];
    for (target, pred) in predecessors.iter().enumerate() {
        let at_target = rank_builder.compare(&newpc, &g::constant(l.pc.len(), target as u64), "eq");
        for (rank, source) in pred.iter().enumerate() {
            if allowed.is_some_and(|s| !s.contains(source)) {
                continue;
            }
            let at_source =
                rank_builder.compare(&oldpc, &g::constant(l.pc.len(), *source as u64), "eq");
            let guard = rank_builder.and(at_target, at_source);
            for (j, bit) in rank_bits.iter_mut().enumerate() {
                if (rank >> j) & 1 != 0 {
                    *bit = rank_builder.xor(*bit, guard);
                }
            }
        }
    }
    let rank_outputs: Vec<_> = rank_bits
        .into_iter()
        .enumerate()
        .map(|(j, v)| (input + state + j, v))
        .collect();
    let rank_term = rank_builder.finish(big, &rank_outputs);
    let oldvars: BTreeMap<_, _> = l
        .vars
        .iter()
        .map(|(id, indices)| (*id, indices.iter().map(|i| old[*i]).collect::<Vec<_>>()))
        .collect();
    for (id, inv) in plans.iter().enumerate() {
        if allowed.is_some_and(|s| !s.contains(&id)) {
            continue;
        }
        for (j, saved) in inv.saved.iter().enumerate() {
            let value = s::eval(&saved.expr, &mut f, &oldvars, &input_values)
                .ok_or("cannot evaluate residue expression")?[saved.bit];
            let mut guard = guards[id];
            for (expr, positive) in &saved.guards {
                let p = s::eval(expr, &mut f, &oldvars, &input_values)
                    .ok_or("cannot evaluate residue guard")?[0];
                let p = if *positive { p } else { f.not(p) };
                guard = f.and(guard, p);
            }
            let v = f.and(guard, value);
            assignments.push((residue_base + j, v));
        }
    }
    let forward = f.finish(big, &assignments);
    let swaps = c::seq(
        (0..state)
            .map(|i| g::swap(input + i, intermediate + i))
            .collect(),
    );
    let mut recovery = vec![];
    for (id, mut inv) in plans.into_iter().enumerate() {
        if allowed.is_some_and(|s| !s.contains(&id)) {
            continue;
        }
        let at = source_guard(
            &mut inv.builder,
            id,
            &newvar(&l.pc),
            input + state,
            rank_width,
            &predecessors,
        );
        let npc = newvar(&l.pc);
        let halted =
            inv.builder
                .compare(&npc, &g::constant(l.pc.len(), m.blocks.len() as u64), "eq");
        let mut recovered = vec![Bit::Const(false); state];
        for variable in &m.blocks[id].live_in {
            if let Some(indices) = l.vars.get(variable) {
                let value = inv.known.get(variable).ok_or("unrecovered variable")?;
                for (i, v) in indices.iter().zip(value) {
                    recovered[*i] = *v;
                }
            }
        }
        let data: BTreeSet<_> = l.vars.values().flatten().copied().collect();
        for i in data {
            recovered[i] = inv.builder.mux(halted, newvalues[i], recovered[i]);
        }
        for (j, i) in l.pc.iter().enumerate() {
            recovered[*i] = Bit::Const((id >> j) & 1 != 0);
        }
        if !l.counter.is_empty() {
            let oldcount = inv.builder.vector(
                &newvar(&l.counter),
                &g::constant(l.counter.len(), m.blocks[id].weight),
                "sub",
            );
            for (i, v) in l.counter.iter().zip(oldcount) {
                recovered[*i] = v;
            }
        }
        if !l.stack.is_empty() {
            let count = if let Exit::Stack { cells, .. } = m.blocks[id].exit {
                inv.builder
                    .vector(&newvar(&l.stack), &g::constant(l.stack.len(), cells), "sub")
            } else {
                newvar(&l.stack)
            };
            for (i, v) in l.stack.iter().zip(count) {
                recovered[*i] = v;
            }
        }
        let outputs: Vec<_> = recovered
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                let v = inv.builder.and(at, v);
                (intermediate + i, v)
            })
            .collect();
        recovery.push(inv.builder.finish(big, &outputs));
    }
    let mut halt = Builder::new(big);
    let at = source_guard(
        &mut halt,
        halt_id,
        &newvar(&l.pc),
        input + state,
        rank_width,
        &predecessors,
    );
    let mut out = vec![Bit::Const(false); state];
    masked_xor(&mut halt, &mut out, at, &newvalues);
    let outputs: Vec<_> = out
        .into_iter()
        .enumerate()
        .map(|(i, v)| (intermediate + i, v))
        .collect();
    recovery.push(halt.finish(big, &outputs));
    Ok((
        c::with(
            external,
            state,
            close_gap(
                &c::seq(vec![forward, rank_term, swaps, c::seq(recovery)]),
                external,
                intermediate,
            ),
        ),
        residues,
    ))
}
impl Compiled {
    pub fn optimized(p: &Program, budget: Budget, controlled: bool) -> Result<Self> {
        Self::optimized_style(p, budget, controlled, false)
    }
    pub fn optimized_compact(p: &Program, budget: Budget, controlled: bool) -> Result<Self> {
        Self::optimized_style(p, budget, controlled, true)
    }
    pub fn optimized_style(
        p: &Program,
        budget: Budget,
        controlled: bool,
        compact: bool,
    ) -> Result<Self> {
        let machine = Machine::build(p, budget)?;
        let (cutoff, scheduled) = machine.horizon(budget.steps);
        let layout = layout(&machine, cutoff);
        let state_width = layout.width;
        let (step, residue_width) = step(&machine, &layout, cutoff, compact, None)?;
        let family = crate::schedule::Family::build(&machine, |set| {
            self::step(&machine, &layout, cutoff, compact, Some(set))
                .expect("same frame bound for restricted phase")
                .0
        });
        let input_width = machine
            .inputs
            .iter()
            .map(|i| machine.widths[*i])
            .sum::<usize>();
        let external =
            input_width + machine.target_width + machine.fault_width + usize::from(controlled);
        let history = residue_width
            .checked_mul(scheduled as usize)
            .ok_or("history address overflow")?;
        let arity = external + state_width + history;
        let compute = family.segment(
            0,
            scheduled,
            input_width,
            state_width,
            residue_width,
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
                residue_width,
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
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_frames_allow_replay_of_small_traces() {
        let p = Program::parse(include_str!("../../fixtures/collatz.bobj")).unwrap();
        let budget = Budget {
            steps: 8,
            heap: 0,
            stack: 32,
            depth: 32,
        };
        let compiled = Compiled::optimized(&p, budget, true).unwrap();
        for x in 0..4 {
            let i = compiled.input_width;
            let m = compiled.state_width;
            let r = compiled.residue_width;
            let mut init = vec![false; i + m];
            init[..i].copy_from_slice(&Bits::from_u64(i, x).0);
            let mut sim = c::Simulator::new(init);
            for t in 0..8 {
                let frame = sim.wires.len();
                sim.wires.resize(frame + r, false);
                let before = sim.wires.clone();
                let map = (0..i + m).chain(frame..frame + r).collect();
                if let Err(e) = sim.run(&c::call(compiled.step.clone(), map)) {
                    panic!(
                        "x={x} t={t} state={:?} layout={:?} blocks={:?} error={e}",
                        Bits(before[i..i + m].to_vec()),
                        compiled.layout,
                        compiled.machine.blocks
                    );
                }
            }
        }
    }
    #[test]
    fn optimized_all_additional_fixtures() {
        for name in ["gcd", "popcount", "diamond", "irreducible", "faultif"] {
            let p = crate::measure::load(name).unwrap();
            for b in [1, 9, 28, 40] {
                let budget = Budget::steps(b);
                let compiled = Compiled::optimized(&p, budget, true).unwrap();
                compiled.verify(&p, budget).unwrap();
            }
        }
    }
    #[test]
    fn optimized_checkpointing_is_correct() {
        let p = crate::measure::load("popcount").unwrap();
        let budget = Budget::steps(128);
        let baseline = Compiled::optimized(&p, budget, true).unwrap();
        let (workspace, ladder, _) = baseline.auxiliary();
        let cap = baseline.external
            + workspace
            + ladder
            + 5 * baseline.state_width
            + 16 * baseline.residue_width;
        let compiled = Compiled::pebbled_optimized(&p, budget, true, cap).unwrap();
        assert!(compiled.checkpoints >= 4);
        compiled.verify(&p, budget).unwrap();
    }
    #[test]
    fn optimized_inc8_and_fault_all_inputs() {
        for text in [
            include_str!("../../fixtures/inc8.bobj"),
            include_str!("../../fixtures/faultif.bobj"),
        ] {
            let p = Program::parse(text).unwrap();
            for b in [0, 1, 2, 3, 8, 9] {
                let budget = Budget::steps(b);
                let compiled = Compiled::optimized(&p, budget, true).unwrap();
                compiled.verify(&p, budget).unwrap();
            }
        }
    }
    #[test]
    fn optimized_collatz_all_inputs() {
        let p = Program::parse(include_str!("../../fixtures/collatz.bobj")).unwrap();
        for steps in [0, 1, 8, 9, 28, 29] {
            let budget = Budget {
                steps,
                heap: 0,
                stack: 32,
                depth: 32,
            };
            let compiled = Compiled::optimized(&p, budget, true).unwrap();
            assert!(compiled.residue_width <= 4);
            compiled.verify(&p, budget).unwrap();
        }
    }
}
