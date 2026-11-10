//! Independently checked local residue rules. These are not silently assumed
//! applicable to a whole control-flow graph.
use crate::{
    circuit::{self as c, Term},
    gadgets as g,
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rule {
    Add,
    Sub,
    Xor,
    OddMultiply,
    LogicalRight(usize),
    Left(usize),
    Truncate(usize),
    Extend,
    Unknown,
}
pub fn residue_width(rule: &Rule, width: usize) -> usize {
    match rule {
        Rule::Add | Rule::Sub | Rule::Xor | Rule::OddMultiply | Rule::Extend => 0,
        Rule::LogicalRight(k) | Rule::Left(k) => width.min(*k),
        Rule::Truncate(k) => width.saturating_sub(*k),
        Rule::Unknown => width,
    }
}
/// Guarded select-of-chains rule, for an even shift versus an odd affine map.
/// Stable operands are classical: odd multiplier, offset, shift=1. The parity
/// bit is retained as the entire residue; the bit shifted out is known zero
/// under the even guard. This construction works for all widths <=64 and all
/// odd constants, and does not refer to source variable or fixture names.
pub fn parity_affine_select(x: &[usize], odd: u64, offset: u64, residue: usize) -> Term {
    assert!(odd & 1 == 1);
    let odd_arm = c::seq(vec![g::multiply_odd(x, odd), g::add_constant(x, offset)]);
    // Right rotation agrees with logical right shift on the even domain.
    let even_arm = c::seq(
        (0..x.len().saturating_sub(1))
            .map(|i| g::swap(x[i], x[i + 1]))
            .collect(),
    );
    c::seq(vec![
        c::gate(&[x[0]], residue),
        c::ctrl(vec![residue], odd_arm),
        c::gate(&[], residue),
        c::ctrl(vec![residue], even_arm),
        c::gate(&[], residue),
    ])
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{bits::Bits, circuit::Simulator};
    #[test]
    fn select_rule_exhaustive_including_residue() {
        for n in 1..=4 {
            let wires: Vec<_> = (0..n).collect();
            for odd in (1..(1u64 << n)).step_by(2) {
                for offset in 0..(1u64 << n) {
                    let t = parity_affine_select(&wires, odd, offset, n);
                    for raw in 0..(1u64 << (n + 1)) {
                        let initial = Bits::from_u64(n + 1, raw).0;
                        let mut sim = Simulator::new(initial.clone());
                        sim.run(&t).unwrap();
                        if !initial[n] {
                            let x = raw & ((1 << n) - 1);
                            let expected = if x & 1 == 0 {
                                x >> 1
                            } else {
                                (x * odd + offset) & ((1 << n) - 1)
                            };
                            assert_eq!(Bits(sim.wires[..n].to_vec()).low_u64(), expected);
                            assert_eq!(sim.wires[n], x & 1 != 0);
                        }
                        sim.run(&c::adj(t.clone())).unwrap();
                        assert_eq!(sim.wires, initial);
                    }
                }
            }
        }
    }
    #[test]
    fn table_and_guarded_zero() {
        assert_eq!(residue_width(&Rule::Add, 64), 0);
        assert_eq!(residue_width(&Rule::Unknown, 64), 64);
        assert_eq!(residue_width(&Rule::LogicalRight(2), 64), 2);
        assert_eq!(residue_width(&Rule::Truncate(8), 64), 56);
    }
}
