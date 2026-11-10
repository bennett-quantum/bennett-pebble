//! A periodic family of time-indexed step definitions. Segment descriptions
//! contain a finite prefix, one affine repetition, and a finite suffix.
use crate::{
    block::Machine,
    circuit::{self as c, Term},
};
#[derive(Clone, Debug)]
pub struct Family {
    pub prefix: Vec<Term>,
    pub cycle: Vec<Term>,
}
impl Family {
    pub fn build(
        m: &Machine,
        mut make: impl FnMut(&std::collections::BTreeSet<usize>) -> Term,
    ) -> Self {
        let mut phase = |s: &std::collections::BTreeSet<usize>| {
            let mut s = s.clone();
            s.insert(m.blocks.len());
            make(&s)
        };
        Self {
            prefix: m.reach.prefix.iter().map(&mut phase).collect(),
            cycle: m.reach.cycle.iter().map(&mut phase).collect(),
        }
    }
    pub fn phase(&self, start: u64) -> usize {
        if start < self.prefix.len() as u64 {
            start as usize
        } else {
            self.prefix.len()
                + ((start - self.prefix.len() as u64) % self.cycle.len() as u64) as usize
        }
    }
    pub fn term(&self, start: u64) -> Term {
        let p = self.phase(start);
        if p < self.prefix.len() {
            self.prefix[p].clone()
        } else {
            self.cycle[p - self.prefix.len()].clone()
        }
    }
    pub fn segment(
        &self,
        start: u64,
        len: u64,
        input: usize,
        m: usize,
        r: usize,
        state: usize,
        frame: usize,
    ) -> Term {
        let call = |at: u64, offset: u64| {
            c::call(
                self.term(at),
                (0..input)
                    .chain(state..state + m)
                    .chain(frame + offset as usize * r..frame + (offset as usize + 1) * r)
                    .collect(),
            )
        };
        let mut terms = vec![];
        let mut pos = 0;
        while pos < len && start + pos < self.prefix.len() as u64 {
            terms.push(call(start + pos, pos));
            pos += 1;
        }
        let period = self.cycle.len() as u64;
        let whole = (len - pos) / period;
        if whole > 0 {
            let body = c::seq(
                (0..period)
                    .map(|j| call(start + pos + j, pos + j))
                    .collect(),
            );
            let begin = frame + pos as usize * r;
            let end = frame + (pos + period) as usize * r;
            let mut shift = vec![0; end];
            for s in &mut shift[begin..end] {
                *s = period as isize * r as isize;
            }
            terms.push(c::rep(whole, body, shift));
            pos += whole * period;
        }
        while pos < len {
            terms.push(call(start + pos, pos));
            pos += 1;
        }
        c::seq(terms)
    }
}
