//! Deliberately simple arbitrary-width, little-endian bit vectors.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bits(pub Vec<bool>);
impl Bits {
    pub fn zero(n: usize) -> Self {
        Self(vec![false; n])
    }
    pub fn from_u64(n: usize, x: u64) -> Self {
        Self((0..n).map(|i| i < 64 && x & (1u64 << i) != 0).collect())
    }
    pub fn width(&self) -> usize {
        self.0.len()
    }
    pub fn low_u64(&self) -> u64 {
        self.0
            .iter()
            .take(64)
            .enumerate()
            .fold(0, |x, (i, b)| x | (u64::from(*b) << i))
    }
    pub fn literal(n: usize, s: &str) -> Result<Self, String> {
        if n == 0 {
            return Err("zero-width literal".into());
        }
        let digits = s.strip_prefix('-').unwrap_or(s);
        if digits.is_empty()
            || (digits.len() > 1 && digits.starts_with('0'))
            || !digits.bytes().all(|b| b.is_ascii_digit())
        {
            return Err(format!("invalid canonical integer {s}"));
        }
        let mut v = Self::zero(n + 1);
        for b in digits.bytes() {
            let two = v.add(&v);
            let four = two.add(&two);
            let eight = four.add(&four);
            v = eight.add(&two);
            v = v.add(&Self::from_u64(n + 1, u64::from(b - b'0')));
        }
        // Constants must fit the unsigned or signed spelling of the destination.
        // Decimal range checking is done without fixed-width host integers.
        let mut limit = Self::zero(n + 1);
        if s.starts_with('-') {
            limit.0[n - 1] = true;
        } else {
            limit.0[n] = true;
        }
        let bound = decimal(limit.clone());
        let too_big = digits.len() > bound.len()
            || (digits.len() == bound.len()
                && (digits > bound.as_str() || (!s.starts_with('-') && digits == bound)));
        if too_big {
            return Err(format!("constant {s} out of range for i{n}"));
        }
        v.0.truncate(n);
        if s.starts_with('-') {
            v = Self::zero(n).sub(&v);
        }
        Ok(v)
    }
    pub fn cast(&self, n: usize, sign: bool) -> Self {
        Self(
            (0..n)
                .map(|i| {
                    self.0
                        .get(i)
                        .copied()
                        .unwrap_or(sign && self.0[self.width() - 1])
                })
                .collect(),
        )
    }
    pub fn xor(&self, b: &Self) -> Self {
        Self(self.0.iter().zip(&b.0).map(|(a, b)| *a ^ *b).collect())
    }
    pub fn add(&self, b: &Self) -> Self {
        let mut carry = false;
        Self(
            self.0
                .iter()
                .zip(&b.0)
                .map(|(&a, &b)| {
                    let z = a ^ b ^ carry;
                    carry = (a & b) | (carry & (a ^ b));
                    z
                })
                .collect(),
        )
    }
    pub fn sub(&self, b: &Self) -> Self {
        let neg = Self(b.0.iter().map(|b| !b).collect()).add(&Self::from_u64(b.width(), 1));
        self.add(&neg)
    }
    pub fn ult(&self, b: &Self) -> bool {
        self.0.iter().rev().cmp(b.0.iter().rev()).is_lt()
    }
    pub fn slt(&self, b: &Self) -> bool {
        let sa = self.0[self.width() - 1];
        let sb = b.0[b.width() - 1];
        if sa != sb { sa } else { self.ult(b) }
    }
    pub fn shift(&self, k: &Self, op: &str) -> Self {
        if k.0
            .iter()
            .enumerate()
            .any(|(i, b)| *b && i >= usize::BITS as usize)
        {
            return Self::zero(self.width());
        }
        let shift = k.low_u64() as usize;
        if shift >= self.width() {
            return Self::zero(self.width());
        }
        Self(
            (0..self.width())
                .map(|i| match op {
                    "shl" => i >= shift && self.0[i - shift],
                    "lshr" => self.0.get(i + shift).copied().unwrap_or(false),
                    "ashr" => self
                        .0
                        .get(i + shift)
                        .copied()
                        .unwrap_or(self.0[self.width() - 1]),
                    _ => unreachable!(),
                })
                .collect(),
        )
    }
    pub fn bin(&self, b: &Self, op: &str) -> Self {
        match op {
            "add" => self.add(b),
            "sub" => self.sub(b),
            "mul" => {
                let mut z = Self::zero(self.width());
                for i in 0..self.width() {
                    if b.0[i] {
                        z = z.add(&self.shift(&Self::from_u64(64, i as u64), "shl"));
                    }
                }
                z
            }
            "and" | "or" | "xor" => Self(
                self.0
                    .iter()
                    .zip(&b.0)
                    .map(|(&a, &b)| match op {
                        "and" => a & b,
                        "or" => a | b,
                        _ => a ^ b,
                    })
                    .collect(),
            ),
            "shl" | "lshr" | "ashr" => self.shift(b, op),
            _ => unreachable!(),
        }
    }
    pub fn cmp(&self, b: &Self, op: &str) -> bool {
        match op {
            "eq" => self == b,
            "ne" => self != b,
            "ult" => self.ult(b),
            "ule" => !b.ult(self),
            "slt" => self.slt(b),
            "sle" => !b.slt(self),
            _ => unreachable!(),
        }
    }
}
fn decimal(mut b: Bits) -> String {
    let mut out = Vec::new();
    while b.0.iter().any(|b| *b) {
        let mut rem = 0u8;
        for bit in b.0.iter_mut().rev() {
            let x = rem * 2 + u8::from(*bit);
            *bit = x >= 10;
            rem = x % 10;
        }
        out.push(char::from(b'0' + rem));
    }
    if out.is_empty() {
        return "0".into();
    }
    out.iter().rev().collect()
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn arithmetic() {
        for a in 0..16 {
            for b in 0..16 {
                let x = Bits::from_u64(4, a);
                let y = Bits::from_u64(4, b);
                assert_eq!(x.add(&y).low_u64(), (a + b) & 15);
                assert_eq!(x.sub(&y).low_u64(), a.wrapping_sub(b) & 15);
                assert_eq!(x.bin(&y, "mul").low_u64(), (a * b) & 15);
            }
        }
    }
    #[test]
    fn large_constants() {
        let a = Bits::literal(129, "340282366920938463463374607431768211456").unwrap();
        assert!(a.0[128]);
        assert_eq!(a.low_u64(), 0);
        assert!(Bits::literal(8, "256").is_err());
        assert!(Bits::literal(8, "-129").is_err());
        assert_eq!(Bits::literal(8, "-128").unwrap().low_u64(), 128);
        assert_eq!(Bits::literal(8, "255").unwrap().low_u64(), 255);
    }
}
