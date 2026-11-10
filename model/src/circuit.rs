//! Shared, non-flattening permutation circuit terms. All gates are positive MCX.
//! X/CX/CCX are the cases with zero/one/two controls.
use std::{
    collections::{BTreeMap, HashMap},
    io::{self, Write},
    rc::Rc,
};

#[derive(Clone, Debug)]
pub struct Gate {
    pub controls: Vec<usize>,
    pub target: usize,
}
#[derive(Clone, Debug)]
pub enum Node {
    Gate(Gate),
    Seq(Vec<Term>),
    Call {
        definition: Term,
        map: Vec<usize>,
    },
    Adj(Term),
    Ctrl {
        controls: Vec<usize>,
        body: Term,
    },
    Rep {
        count: u64,
        body: Term,
        shift: Vec<isize>,
    },
    With {
        external: usize,
        allocated: usize,
        body: Term,
    },
}
pub type Term = Rc<Node>;
pub fn gate(controls: &[usize], target: usize) -> Term {
    assert!(!controls.contains(&target), "target is a control");
    let mut controls = controls.to_vec();
    controls.sort_unstable();
    controls.dedup();
    Rc::new(Node::Gate(Gate { controls, target }))
}
pub fn seq(terms: Vec<Term>) -> Term {
    Rc::new(Node::Seq(terms))
}
pub fn adj(body: Term) -> Term {
    Rc::new(Node::Adj(body))
}
pub fn call(definition: Term, map: Vec<usize>) -> Term {
    let mut sorted = map.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), map.len(), "wire map must be injective");
    Rc::new(Node::Call { definition, map })
}
/// Fresh inherited controls are required. Checking this is independent of the
/// repetition count (conservative support intervals for affine repetitions).
pub fn ctrl(controls: Vec<usize>, body: Term) -> Term {
    let ranges = support(&body);
    for c in &controls {
        assert!(
            !ranges.iter().any(|(a, b)| a <= c && c <= b),
            "inherited control overlaps body support"
        );
    }
    let mut controls = controls;
    controls.sort_unstable();
    controls.dedup();
    Rc::new(Node::Ctrl { controls, body })
}
pub fn rep(count: u64, body: Term, shift: Vec<isize>) -> Term {
    Rc::new(Node::Rep { count, body, shift })
}
pub fn with(external: usize, allocated: usize, body: Term) -> Term {
    Rc::new(Node::With {
        external,
        allocated,
        body,
    })
}
fn support(t: &Term) -> Vec<(usize, usize)> {
    fn go(t: &Term, memo: &mut HashMap<usize, Vec<(usize, usize)>>) -> Vec<(usize, usize)> {
        let key = Rc::as_ptr(t) as usize;
        if let Some(s) = memo.get(&key) {
            return s.clone();
        }
        let mut ranges: Vec<_> = match t.as_ref() {
            Node::Gate(g) => g
                .controls
                .iter()
                .copied()
                .chain([g.target])
                .map(|w| (w, w))
                .collect(),
            Node::Seq(ts) => ts.iter().flat_map(|t| go(t, memo)).collect(),
            Node::Adj(b) => go(b, memo),
            Node::Ctrl { controls, body } => go(body, memo)
                .into_iter()
                .chain(controls.iter().map(|c| (*c, *c)))
                .collect(),
            Node::Call { definition, map } => {
                let mut out = vec![];
                for (a, b) in go(definition, memo) {
                    assert!(b < map.len(), "wire map omits a used wire");
                    out.extend(map[a..=b].iter().map(|w| (*w, *w)));
                }
                out
            }
            Node::Rep { count, body, shift } => {
                let mut out = vec![];
                if *count > 0 {
                    for (a, b) in go(body, memo) {
                        let end = b.min(shift.len().saturating_sub(1));
                        if a < shift.len() {
                            for (w, d) in shift.iter().enumerate().take(end + 1).skip(a) {
                                let finish = affine(w, *count - 1, *d);
                                out.push((w.min(finish), w.max(finish)));
                            }
                        }
                        if b >= shift.len() {
                            out.push((a.max(shift.len()), b));
                        }
                    }
                }
                out
            }
            Node::With { external, body, .. } => go(body, memo)
                .into_iter()
                .filter(|(a, _)| a < external)
                .map(|(a, b)| (a, b.min(external - 1)))
                .collect(),
        };
        ranges.sort_unstable();
        let mut merged = Vec::<(usize, usize)>::new();
        for (a, b) in ranges {
            if let Some(last) = merged.last_mut() {
                if a <= last.1.saturating_add(1) {
                    last.1 = last.1.max(b);
                    continue;
                }
            }
            merged.push((a, b));
        }
        memo.insert(key, merged.clone());
        merged
    }
    go(t, &mut HashMap::new())
}
fn affine(base: usize, i: u64, delta: isize) -> usize {
    usize::try_from(base as i128 + i128::from(i) * delta as i128)
        .expect("negative/overflowing affine wire")
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cost {
    /// Key is the number of positive controls; 0=X, 1=CX, 2=CCX.
    pub histogram: BTreeMap<usize, u128>,
    pub extra_peak: usize,
}
impl Cost {
    pub fn total(&self) -> u128 {
        self.histogram.values().sum()
    }
    /// Clean-ancilla ladder: C^kX = 2k-3 Toffolis for k>=2.
    /// The ladder's k-2 clean ancillas are separately included in peak().
    pub fn toffoli(&self) -> u128 {
        self.histogram
            .iter()
            .map(|(k, n)| {
                if *k < 2 {
                    0
                } else {
                    n * (2 * (*k as u128) - 3)
                }
            })
            .sum()
    }
    pub fn ladder_ancillas(&self) -> usize {
        self.histogram
            .keys()
            .copied()
            .max()
            .unwrap_or(0)
            .saturating_sub(2)
    }
    pub fn peak(&self, external: usize) -> usize {
        external + self.extra_peak + self.ladder_ancillas()
    }
}
pub fn cost(root: &Term) -> Cost {
    fn go(t: &Term, memo: &mut HashMap<usize, Cost>) -> Cost {
        let key = Rc::as_ptr(t) as usize;
        if let Some(c) = memo.get(&key) {
            return c.clone();
        }
        let c = match t.as_ref() {
            Node::Gate(g) => Cost {
                histogram: BTreeMap::from([(g.controls.len(), 1)]),
                extra_peak: 0,
            },
            Node::Seq(ts) => {
                let mut out = Cost::default();
                for b in ts {
                    let c = go(b, memo);
                    for (k, n) in c.histogram {
                        *out.histogram.entry(k).or_default() += n;
                    }
                    out.extra_peak = out.extra_peak.max(c.extra_peak);
                }
                out
            }
            Node::Call { definition, .. } | Node::Adj(definition) => go(definition, memo),
            Node::Ctrl { controls, body } => {
                let c = go(body, memo);
                Cost {
                    histogram: c
                        .histogram
                        .into_iter()
                        .map(|(k, n)| (k + controls.len(), n))
                        .collect(),
                    extra_peak: c.extra_peak,
                }
            }
            Node::Rep { count, body, .. } => {
                if *count == 0 {
                    Cost::default()
                } else {
                    let mut c = go(body, memo);
                    for n in c.histogram.values_mut() {
                        *n *= u128::from(*count);
                    }
                    c
                }
            }
            Node::With {
                allocated, body, ..
            } => {
                let mut c = go(body, memo);
                c.extra_peak += allocated;
                c
            }
        };
        memo.insert(key, c.clone());
        c
    }
    go(root, &mut HashMap::new())
}

trait Visitor {
    fn gate(&mut self, controls: &[usize], target: usize) -> io::Result<()>;
    fn alloc(&mut self, n: usize) -> io::Result<usize>;
    fn free(&mut self, base: usize, n: usize) -> io::Result<()>;
    fn before_call(
        &mut self,
        _definition: &Term,
        _arity: usize,
        _map: &dyn Fn(usize) -> usize,
        _inherited: &[usize],
        _reverse: bool,
    ) -> io::Result<bool> {
        Ok(false)
    }
    fn after_call(
        &mut self,
        _definition: &Term,
        _arity: usize,
        _map: &dyn Fn(usize) -> usize,
        _inherited: &[usize],
        _reverse: bool,
    ) -> io::Result<()> {
        Ok(())
    }
}
// Maps are lazy compositions. Even a scope reserving 10^12 wires needs only
// one stack record in the emitter; only the simulator materialises wire values.
fn visit<V: Visitor>(
    t: &Term,
    arity: usize,
    map: &dyn Fn(usize) -> usize,
    inherited: &[usize],
    reverse: bool,
    v: &mut V,
) -> io::Result<()> {
    match t.as_ref() {
        Node::Gate(g) => {
            let count = inherited.len() + g.controls.len();
            if count <= 4 {
                let mut cs = [0; 4];
                for (i, c) in inherited
                    .iter()
                    .copied()
                    .chain(g.controls.iter().map(|c| map(*c)))
                    .enumerate()
                {
                    cs[i] = c;
                }
                v.gate(&cs[..count], map(g.target))
            } else {
                let cs: Vec<_> = inherited
                    .iter()
                    .copied()
                    .chain(g.controls.iter().map(|c| map(*c)))
                    .collect();
                v.gate(&cs, map(g.target))
            }
        }
        Node::Seq(ts) => {
            if reverse {
                for b in ts.iter().rev() {
                    visit(b, arity, map, inherited, reverse, v)?;
                }
            } else {
                for b in ts {
                    visit(b, arity, map, inherited, reverse, v)?;
                }
            }
            Ok(())
        }
        Node::Call {
            definition,
            map: wm,
        } => {
            let next = |i: usize| map(wm[i]);
            if v.before_call(definition, wm.len(), &next, inherited, reverse)? {
                return Ok(());
            }
            visit(definition, wm.len(), &next, inherited, reverse, v)?;
            v.after_call(definition, wm.len(), &next, inherited, reverse)
        }
        Node::Adj(b) => visit(b, arity, map, inherited, !reverse, v),
        Node::Ctrl { controls, body } => {
            let cs: Vec<_> = inherited
                .iter()
                .copied()
                .chain(controls.iter().map(|i| map(*i)))
                .collect();
            visit(body, arity, map, &cs, reverse, v)
        }
        Node::Rep { count, body, shift } => {
            for j in 0..*count {
                let i = if reverse { count - 1 - j } else { j };
                let next = |w: usize| {
                    let index = affine(w, i, shift.get(w).copied().unwrap_or(0));
                    assert!(index < arity);
                    map(index)
                };
                visit(body, arity, &next, inherited, reverse, v)?;
            }
            Ok(())
        }
        Node::With {
            external,
            allocated,
            body,
        } => {
            assert_eq!(arity, *external);
            let base = v.alloc(*allocated)?;
            let next = |i: usize| {
                if i < *external {
                    map(i)
                } else {
                    assert!(i < external + allocated);
                    base + i - external
                }
            };
            visit(body, external + allocated, &next, inherited, reverse, v)?;
            v.free(base, *allocated)
        }
    }
}

#[derive(Clone, Debug)]
pub struct Simulator {
    pub wires: Vec<bool>,
    pub executed: u128,
    pub peak: usize,
}
impl Simulator {
    pub fn new(wires: Vec<bool>) -> Self {
        let peak = wires.len();
        Self {
            wires,
            executed: 0,
            peak,
        }
    }
    pub fn run(&mut self, t: &Term) -> io::Result<()> {
        visit(t, self.wires.len(), &|i| i, &[], false, self)
    }
}
impl Visitor for Simulator {
    fn gate(&mut self, cs: &[usize], target: usize) -> io::Result<()> {
        assert!(!cs.contains(&target));
        self.executed += 1;
        if cs.iter().all(|c| self.wires[*c]) {
            self.wires[target] ^= true;
        }
        Ok(())
    }
    fn alloc(&mut self, n: usize) -> io::Result<usize> {
        let old = self.wires.len();
        self.wires.resize(old + n, false);
        self.peak = self.peak.max(self.wires.len());
        Ok(old)
    }
    fn free(&mut self, base: usize, n: usize) -> io::Result<()> {
        assert_eq!(base + n, self.wires.len());
        if self.wires[base..].iter().any(|x| *x) {
            return Err(io::Error::other("releasing nonzero scratch"));
        }
        self.wires.truncate(base);
        Ok(())
    }
}
/// 64 independent basis configurations in bit lanes; same hierarchy traversal.
#[derive(Clone, Debug)]
pub struct Lanes {
    pub wires: Vec<u64>,
    pub executed: u128,
    pub peak: usize,
}
impl Lanes {
    pub fn new(wires: Vec<u64>) -> Self {
        let peak = wires.len();
        Self {
            wires,
            executed: 0,
            peak,
        }
    }
    pub fn run(&mut self, t: &Term) -> io::Result<()> {
        visit(t, self.wires.len(), &|i| i, &[], false, self)
    }
}
impl Visitor for Lanes {
    fn gate(&mut self, cs: &[usize], target: usize) -> io::Result<()> {
        assert!(!cs.contains(&target));
        self.executed += 1;
        let mask = cs.iter().fold(!0u64, |a, c| a & self.wires[*c]);
        self.wires[target] ^= mask;
        Ok(())
    }
    fn alloc(&mut self, n: usize) -> io::Result<usize> {
        let old = self.wires.len();
        self.wires.resize(old + n, 0);
        self.peak = self.peak.max(self.wires.len());
        Ok(old)
    }
    fn free(&mut self, base: usize, n: usize) -> io::Result<()> {
        assert_eq!(base + n, self.wires.len());
        if self.wires[base..].iter().any(|x| *x != 0) {
            let (offset, value) = self.wires[base..]
                .iter()
                .enumerate()
                .find(|(_, x)| **x != 0)
                .unwrap();
            return Err(io::Error::other(format!(
                "releasing nonzero scratch lanes: base={base}, size={n}, wire={}, value={value:x}",
                base + offset
            )));
        }
        self.wires.truncate(base);
        Ok(())
    }
}
/// Truth tables in up to nine environment/control bits, with arbitrary target
/// and fault contents carried as independent affine symbols. Gates are checked
/// to never read those symbols as controls. Thus one run covers ALL tgt/fr
/// basis states, not just samples. This is an exact Boolean-domain simulator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Truth {
    pub values: [u64; 8],
    pub symbols: u128,
}
type TruthKey = (usize, bool, Vec<Truth>);
pub struct TruthSimulator {
    pub wires: Vec<Truth>,
    pub executed: u128,
    pub peak: usize,
    cache: HashMap<TruthKey, Vec<Truth>>,
    pending: Vec<(TruthKey, u128)>,
    prices: HashMap<usize, (u128, usize)>,
}
impl TruthSimulator {
    pub fn new(wires: Vec<Truth>) -> Self {
        let peak = wires.len();
        Self {
            wires,
            executed: 0,
            peak,
            cache: HashMap::new(),
            pending: vec![],
            prices: HashMap::new(),
        }
    }
    pub fn run(&mut self, t: &Term) -> io::Result<()> {
        visit(t, self.wires.len(), &|i| i, &[], false, self)
    }
}
impl Visitor for TruthSimulator {
    fn before_call(
        &mut self,
        definition: &Term,
        arity: usize,
        map: &dyn Fn(usize) -> usize,
        inherited: &[usize],
        reverse: bool,
    ) -> io::Result<bool> {
        if !inherited.is_empty() {
            return Ok(false);
        }
        let id = Rc::as_ptr(definition) as usize;
        let key = (
            id,
            reverse,
            (0..arity).map(|i| self.wires[map(i)]).collect::<Vec<_>>(),
        );
        if let Some(output) = self.cache.get(&key) {
            for (i, w) in output.iter().enumerate() {
                self.wires[map(i)] = *w;
            }
            let (gates, extra) = self.prices[&id];
            self.executed += gates;
            self.peak = self.peak.max(self.wires.len() + extra);
            return Ok(true);
        }
        self.pending.push((key, self.executed));
        Ok(false)
    }
    fn after_call(
        &mut self,
        definition: &Term,
        arity: usize,
        map: &dyn Fn(usize) -> usize,
        inherited: &[usize],
        _reverse: bool,
    ) -> io::Result<()> {
        if !inherited.is_empty() {
            return Ok(());
        }
        let (key, started) = self.pending.pop().expect("cache call stack");
        let output: Vec<_> = (0..arity).map(|i| self.wires[map(i)]).collect();
        let price = self.executed - started;
        if let Some((expected, _)) = self.prices.get(&key.0) {
            assert_eq!(price, *expected);
        } else {
            let structural = cost(definition);
            assert_eq!(price, structural.total());
            self.prices.insert(key.0, (price, structural.extra_peak));
        }
        let inverse = (key.0, !key.1, output.clone());
        self.cache.insert(inverse, key.2.clone());
        self.cache.insert(key, output);
        Ok(())
    }
    fn gate(&mut self, cs: &[usize], target: usize) -> io::Result<()> {
        assert!(!cs.contains(&target));
        self.executed += 1;
        let mut mask = [!0u64; 8];
        for c in cs {
            let wire = &self.wires[*c];
            if wire.symbols != 0 {
                return Err(io::Error::other(
                    "affine interface symbol used as gate control",
                ));
            }
            for (i, v) in mask.iter_mut().enumerate() {
                *v &= wire.values[i];
            }
            if mask.iter().all(|w| *w == 0) {
                return Ok(());
            }
        }
        for (i, v) in mask.into_iter().enumerate() {
            self.wires[target].values[i] ^= v;
        }
        Ok(())
    }
    fn alloc(&mut self, n: usize) -> io::Result<usize> {
        let base = self.wires.len();
        self.wires.resize(base + n, Truth::default());
        self.peak = self.peak.max(self.wires.len());
        Ok(base)
    }
    fn free(&mut self, base: usize, n: usize) -> io::Result<()> {
        assert_eq!(base + n, self.wires.len());
        if let Some((offset, _)) = self.wires[base..]
            .iter()
            .enumerate()
            .find(|(_, w)| **w != Truth::default())
        {
            return Err(io::Error::other(format!(
                "truth simulator: dirty scratch at {}",
                base + offset
            )));
        }
        self.wires.truncate(base);
        Ok(())
    }
}

struct Emitter<W: Write> {
    out: W,
    live: usize,
}
impl<W: Write> Visitor for Emitter<W> {
    fn gate(&mut self, cs: &[usize], target: usize) -> io::Result<()> {
        write!(self.out, "mcx")?;
        for c in cs {
            write!(self.out, " {c}")?;
        }
        writeln!(self.out, " -> {target}")
    }
    fn alloc(&mut self, n: usize) -> io::Result<usize> {
        let old = self.live;
        self.live += n;
        writeln!(self.out, "alloc {old} {n}")?;
        Ok(old)
    }
    fn free(&mut self, base: usize, n: usize) -> io::Result<()> {
        self.live -= n;
        assert_eq!(self.live, base);
        writeln!(self.out, "free {base} {n}")
    }
}
/// Flat output is streamed. Expanded output and runtime may be enormous.
pub fn emit<W: Write>(t: &Term, external: usize, out: W) -> io::Result<()> {
    let mut v = Emitter {
        out,
        live: external,
    };
    visit(t, external, &|i| i, &[], false, &mut v)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn hierarchy_cost_sim_emit() {
        let d = seq(vec![gate(&[], 0), gate(&[0], 1), gate(&[0, 1], 2)]);
        let b = call(d, vec![1, 2, 3]);
        let c = ctrl(vec![0], b.clone());
        let t = seq(vec![c.clone(), adj(c)]);
        let mut sim = Simulator::new(vec![true, false, false, false]);
        sim.run(&t).unwrap();
        assert_eq!(sim.wires, vec![true, false, false, false]);
        assert_eq!(cost(&t).total(), sim.executed);
        let mut buf = vec![];
        emit(&t, 4, &mut buf).unwrap();
        assert_eq!(
            String::from_utf8(buf).unwrap().lines().count() as u128,
            sim.executed
        );
        let scratch = with(
            4,
            2,
            seq(vec![
                gate(&[0], 4),
                gate(&[4], 5),
                gate(&[4], 5),
                gate(&[0], 4),
            ]),
        );
        sim.run(&scratch).unwrap();
        assert_eq!(sim.peak, 6);
        assert_eq!(cost(&scratch).extra_peak, 2);
    }
    #[test]
    fn affine_repetition_and_adjoint() {
        let t = rep(4, gate(&[0], 1), vec![1, 1, 0, 0, 0]);
        let mut sim = Simulator::new(vec![true, false, false, false, false]);
        sim.run(&t).unwrap();
        assert_eq!(sim.wires, vec![true; 5]);
        sim.run(&adj(t.clone())).unwrap();
        assert_eq!(sim.wires, vec![true, false, false, false, false]);
        assert_eq!(cost(&t).total(), 4);
    }
    #[test]
    fn streaming_allocation_does_not_materialize_wires() {
        struct Count(usize);
        impl Write for Count {
            fn write(&mut self, b: &[u8]) -> io::Result<usize> {
                self.0 += b.len();
                Ok(b.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let t = with(
            2,
            1_000_000_000,
            seq(vec![gate(&[], 1_000_000_001), gate(&[], 1_000_000_001)]),
        );
        let mut sink = Count(0);
        emit(&t, 2, &mut sink).unwrap();
        assert!(sink.0 < 200);
        assert_eq!(cost(&t).total(), 2);
        let mut serialized = vec![];
        emit_hierarchy(&t, 2, &mut serialized).unwrap();
        assert!(serialized.len() < 300);
    }
    #[test]
    fn billion_steps_have_constant_structure() {
        let t = rep(1_000_000_000, gate(&[0, 1, 2, 3], 4), vec![]);
        let c = cost(&t);
        assert_eq!(c.total(), 1_000_000_000);
        assert_eq!(c.toffoli(), 5_000_000_000);
        assert_eq!(c.peak(5), 7);
    }
    #[test]
    #[should_panic(expected = "overlaps")]
    fn reject_control_on_body() {
        ctrl(vec![0], gate(&[0], 1));
    }
}

fn dag_nodes(root: &Term) -> (Vec<Term>, HashMap<usize, usize>) {
    fn go(t: &Term, nodes: &mut Vec<Term>, ids: &mut HashMap<usize, usize>) {
        let key = Rc::as_ptr(t) as usize;
        if ids.contains_key(&key) {
            return;
        }
        match t.as_ref() {
            Node::Seq(ts) => {
                for t in ts {
                    go(t, nodes, ids);
                }
            }
            Node::Call {
                definition: body, ..
            }
            | Node::Adj(body)
            | Node::Ctrl { body, .. }
            | Node::Rep { body, .. }
            | Node::With { body, .. } => go(body, nodes, ids),
            Node::Gate(_) => {}
        }
        ids.insert(key, nodes.len());
        nodes.push(t.clone());
    }
    let mut nodes = vec![];
    let mut ids = HashMap::new();
    go(root, &mut nodes, &mut ids);
    (nodes, ids)
}
pub fn dag_stats(root: &Term) -> (usize, usize) {
    let (nodes, _) = dag_nodes(root);
    let maps = nodes
        .iter()
        .map(|n| match n.as_ref() {
            Node::Call { map, .. } => map.len(),
            Node::Rep { shift, .. } => shift.len(),
            _ => 0,
        })
        .sum();
    (nodes.len(), maps)
}
/// A standalone shared description. Flat emission is a different, streaming API.
pub fn emit_hierarchy<W: Write>(root: &Term, external: usize, mut out: W) -> io::Result<()> {
    let (nodes, ids) = dag_nodes(root);
    let id = |t: &Term| ids[&(Rc::as_ptr(t) as usize)];
    writeln!(
        out,
        "pebble-circuit 1 external={external} root={}",
        id(root)
    )?;
    for (i, node) in nodes.iter().enumerate() {
        write!(out, "{i} ")?;
        match node.as_ref() {
            Node::Gate(g) => writeln!(out, "gate {:?} -> {}", g.controls, g.target)?,
            Node::Seq(ts) => writeln!(out, "seq {:?}", ts.iter().map(id).collect::<Vec<_>>())?,
            Node::Call { definition, map } => writeln!(out, "call {} {:?}", id(definition), map)?,
            Node::Adj(body) => writeln!(out, "adj {}", id(body))?,
            Node::Ctrl { controls, body } => writeln!(out, "ctrl {:?} {}", controls, id(body))?,
            Node::Rep { count, body, shift } => writeln!(
                out,
                "rep {count} {} shift {:?}",
                id(body),
                shift
                    .iter()
                    .enumerate()
                    .filter(|(_, d)| **d != 0)
                    .map(|(w, d)| (w, *d))
                    .collect::<Vec<_>>()
            )?,
            Node::With {
                external,
                allocated,
                body,
            } => writeln!(out, "with {external} {allocated} {}", id(body))?,
        }
    }
    Ok(())
}
