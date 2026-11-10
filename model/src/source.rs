use crate::bits::Bits;
use std::collections::{BTreeMap, BTreeSet};

pub type Result<T> = std::result::Result<T, String>;
#[derive(Clone, Debug)]
pub enum Row {
    Const(usize, Bits),
    Bin(usize, String, usize, usize),
    Cmp(usize, String, usize, usize),
    Select(usize, usize, usize, usize),
    Cast(usize, String, usize),
    Mov(Vec<usize>, Vec<usize>),
    FaultIf(usize, Bits),
    Fault(Bits),
    Retval(usize),
    Jump(usize),
    Branch(usize, usize, usize),
    Call(usize, usize, Vec<usize>),
    Ret(usize),
}
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub is_oracle: bool,
    pub names: Vec<String>,
    pub widths: Vec<usize>,
    pub inputs: Vec<usize>,
    pub locations: Vec<usize>,
    pub params: Vec<usize>,
    pub classical: Vec<usize>,
    pub labels: BTreeMap<String, usize>,
    pub rows: Vec<Row>,
    pub target_width: usize,
    pub fault_width: usize,
}
#[derive(Clone, Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub layout: Option<u32>,
    pub heap_max: u64,
    pub arguments: Vec<Option<Bits>>,
}
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    pub steps: u64,
    pub heap: u64,
    pub stack: u64,
    pub depth: u64,
}
impl Budget {
    pub fn steps(steps: u64) -> Self {
        Self {
            steps,
            heap: 0,
            stack: 0,
            depth: 0,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    pub payload: Bits,
    pub code: Bits,
    pub rows: u64,
    pub stack_used: u64,
    pub max_depth: u64,
}

fn groups(s: &str) -> Result<Vec<&str>> {
    let mut result = Vec::new();
    let mut start = None;
    for (i, b) in s.bytes().enumerate() {
        match b {
            b'(' if start.is_none() => start = Some(i + 1),
            b')' => {
                result.push(&s[start.take().ok_or("unmatched parenthesis")?..i]);
            }
            _ => {}
        }
    }
    if start.is_some() {
        return Err("unmatched parenthesis".into());
    }
    Ok(result)
}
fn list(s: &str) -> Vec<&str> {
    if s.is_empty() {
        vec![]
    } else {
        s.split(", ").collect()
    }
}
fn decl(s: &str) -> Result<(String, usize)> {
    let (name, t) = s
        .split_once(':')
        .ok_or_else(|| format!("bad declaration {s}"))?;
    let t = t.split(' ').next().unwrap();
    let width_token = t
        .strip_prefix("reg[")
        .or_else(|| t.strip_prefix("wire["))
        .and_then(|t| t.strip_suffix(']'))
        .ok_or_else(|| format!("unsupported type {t}"))?;
    let width = width_token
        .parse::<usize>()
        .map_err(|_| format!("bad width {t}"))?;
    if width.to_string() != width_token {
        return Err(format!("noncanonical width {t}"));
    }
    if width == 0 {
        return Err("zero width".into());
    }
    if name.is_empty()
        || !name.bytes().enumerate().all(|(i, c)| {
            c.is_ascii_alphabetic() || c == b'_' || (i > 0 && (c.is_ascii_digit() || c == b'.'))
        })
    {
        return Err(format!("bad name {name}"));
    }
    Ok((name.into(), width))
}
fn classical_decl(s: &str, ptr_width: usize) -> Result<(String, usize)> {
    let (name, ty) = s.split_once(':').ok_or("bad classical declaration")?;
    let width = match ty {
        "ptr" => ptr_width,
        "f64" => 64,
        _ => {
            let n = ty
                .strip_prefix('i')
                .ok_or_else(|| format!("unsupported classical type {ty}"))?;
            let parsed = n.parse::<usize>().map_err(|_| "bad classical width")?;
            if parsed.to_string() != n {
                return Err("noncanonical classical width".into());
            }
            parsed
        }
    };
    decl(&format!("{name}:reg[{width}]"))
}
fn number(s: &str, key: &str) -> Option<u64> {
    let p = s.find(&format!("\"{key}\":"))? + key.len() + 3;
    s[p..]
        .split(|c: char| !c.is_ascii_digit())
        .next()?
        .parse()
        .ok()
}

impl Program {
    /// Parses executable function text; envelope hashes and other JSON metadata
    /// are carried opaquely. This is not an object authenticator or linker.
    pub fn parse(text: &str) -> Result<Self> {
        if text.contains('\r') {
            return Err("unsupported: object must use LF line endings".into());
        }
        if !text.starts_with("bennett-object isa=0.9 ")
            && !text.starts_with("bennett-object isa=0.8 ")
        {
            return Err("unsupported object header".into());
        }
        let ptr_width = text
            .lines()
            .next()
            .unwrap()
            .split_whitespace()
            .find_map(|s| s.strip_prefix("ptr_width="))
            .ok_or("missing ptr_width")?
            .parse::<usize>()
            .map_err(|_| "bad ptr_width")?;
        let mut functions = Vec::<Function>::new();
        let mut raw = Vec::<Vec<String>>::new();
        let mut section = "";
        let mut layout = None;
        let mut heap_max = 0;
        for (line_no, line) in text.lines().enumerate().skip(1) {
            if line.is_empty() {
                continue;
            }
            if let Some(s) = line.strip_prefix("section ") {
                section = s;
                continue;
            }
            if section == "layout" {
                layout = Some(number(line, "S_cells").ok_or("layout missing S_cells")? as u32);
                heap_max = number(line, "heap_limit_max").ok_or("layout missing heap_limit_max")?;
                continue;
            }
            if section != "functions" {
                continue;
            }
            if line.trim() != line
                || line.contains('\t')
                || (line.contains("  ") && line != "regs {  }")
            {
                return Err(format!(
                    "noncanonical function whitespace at line {}",
                    line_no + 1
                ));
            }
            if line.starts_with("oracle ") || line.starts_with("lproc ") {
                let oracle = line.starts_with("oracle ");
                let name = line
                    .split_whitespace()
                    .nth(1)
                    .unwrap()
                    .trim_start_matches('@')
                    .to_string();
                let g = groups(line)?;
                if g.len() != 5 {
                    return Err(format!("line {}: expected five header groups", line_no + 1));
                }
                if (oracle && !g[3].is_empty()) || (!oracle && g[2..].iter().any(|g| !g.is_empty()))
                {
                    return Err("unsupported memory or nonempty lproc forwarding groups".into());
                }
                if functions.iter().any(|f| f.name == name) {
                    return Err(format!("duplicate function {name}"));
                }
                let mut f = Function {
                    name,
                    is_oracle: oracle,
                    names: vec![],
                    widths: vec![],
                    inputs: vec![],
                    locations: vec![],
                    params: vec![],
                    classical: vec![],
                    labels: BTreeMap::new(),
                    rows: vec![],
                    target_width: 0,
                    fault_width: 0,
                };
                for s in list(g[0]) {
                    let id = f.add(decl(s)?)?;
                    if oracle {
                        f.inputs.push(id);
                    } else {
                        f.params.push(id);
                        f.locations.push(id);
                    }
                }
                if list(g[1]).len() != 1 {
                    return Err("exactly one result required".into());
                }
                let result = decl(g[1])?;
                f.target_width = result.1;
                if oracle {
                    if list(g[2]).len() != 1 {
                        return Err("exactly one fault bundle required".into());
                    }
                    f.fault_width = decl(g[2])?.1;
                    if f.fault_width < 4 {
                        return Err("fault width < 4".into());
                    }
                } else {
                    let id = f.add(result)?;
                    f.locations.push(id);
                }
                if oracle {
                    for arg in list(g[4]) {
                        let id = f.add(classical_decl(arg, ptr_width)?)?;
                        f.classical.push(id);
                    }
                }
                functions.push(f);
                raw.push(vec![]);
                continue;
            }
            let f = functions
                .last_mut()
                .ok_or_else(|| format!("unsupported function at line {}: {line}", line_no + 1))?;
            if let Some(r) = line.strip_prefix("regs { ") {
                let r = r.strip_suffix(" }").ok_or("unsupported regs syntax")?;
                for s in list(r.trim()) {
                    let id = f.add(decl(s)?)?;
                    f.locations.push(id);
                }
                continue;
            }
            if let Some(b) = line.strip_prefix('^') {
                let label = b
                    .strip_suffix("():")
                    .ok_or("unsupported block parameters")?;
                if f.labels
                    .insert(label.into(), raw.last().unwrap().len())
                    .is_some()
                {
                    return Err(format!("duplicate label {label}"));
                }
                continue;
            }
            raw.last_mut().unwrap().push(line.into());
        }
        if functions.first().is_none_or(|f| !f.is_oracle)
            || functions.iter().skip(1).any(|f| f.is_oracle)
        {
            return Err("unsupported: exactly one oracle followed by lprocs required".into());
        }
        let names: Vec<_> = functions.iter().map(|f| f.name.clone()).collect();
        let fault_width = functions[0].fault_width;
        for (f, lines) in functions.iter_mut().zip(raw) {
            f.fault_width = fault_width;
            for (i, line) in lines.iter().enumerate() {
                let row =
                    parse_row(line, f, &names).map_err(|e| format!("@{} row {i}: {e}", f.name))?;
                f.rows.push(row);
            }
            f.validate()?;
        }
        if layout.is_none()
            && functions.iter().any(|f| {
                !f.is_oracle
                    || f.rows
                        .iter()
                        .any(|r| matches!(r, Row::Call(..) | Row::Ret(..)))
            })
        {
            return Err("lprocs and calls require layout (§7.2)".into());
        }
        for f in &functions {
            for r in &f.rows {
                if let Row::Call(d, c, args) = r {
                    let callee = &functions[*c];
                    if callee.is_oracle
                        || args.len() != callee.params.len()
                        || f.widths[*d] != callee.target_width
                        || args
                            .iter()
                            .zip(&callee.params)
                            .any(|(a, p)| f.widths[*a] != callee.widths[*p])
                    {
                        return Err("call signature mismatch".into());
                    }
                }
            }
        }
        let arguments = vec![None; functions[0].classical.len()];
        Ok(Self {
            functions,
            layout,
            heap_max,
            arguments,
        })
    }
    /// Classical arguments are fixed before compilation. Ptr/f64 use their
    /// bit readings; they never become environment or quantum input wires.
    pub fn bind_classical(&self, args: &[Bits]) -> Result<Self> {
        let f = &self.functions[0];
        if args.len() != f.classical.len()
            || args
                .iter()
                .zip(&f.classical)
                .any(|(v, i)| v.width() != f.widths[*i])
        {
            return Err("classical argument signature mismatch".into());
        }
        let mut p = self.clone();
        p.arguments = args.iter().cloned().map(Some).collect();
        Ok(p)
    }
    pub fn classical_values(&self) -> Result<Vec<Bits>> {
        self.arguments
            .iter()
            .map(|v| {
                v.clone()
                    .ok_or("classical arguments must be bound before execution/compilation".into())
            })
            .collect()
    }
    pub fn validate_budget(&self, b: Budget) -> Result<()> {
        match self.layout {
            None if b.heap != 0 || b.stack != 0 || b.depth != 0 => {
                return Err("memoryless budget requires heap=stack=depth=0".into());
            }
            Some(s) if s < 64 && b.stack > (1u64 << s) => {
                return Err("stack budget exceeds layout".into());
            }
            _ => {}
        }
        if b.heap > self.heap_max {
            return Err("heap budget exceeds layout".into());
        }
        Ok(())
    }
    pub fn run(&self, input: &[Bits], budget: Budget) -> Result<Outcome> {
        self.validate_budget(budget)?;
        let arguments = self.classical_values()?;
        let oracle = &self.functions[0];
        if input.len() != oracle.inputs.len()
            || input
                .iter()
                .zip(&oracle.inputs)
                .any(|(x, i)| x.width() != oracle.widths[*i])
        {
            return Err("input signature mismatch".into());
        }
        let mut regs: Vec<Vec<Bits>> = self
            .functions
            .iter()
            .map(|f| f.widths.iter().map(|n| Bits::zero(*n)).collect())
            .collect();
        for (v, i) in input.iter().zip(&oracle.inputs) {
            regs[0][*i] = v.clone();
        }
        for (i, v) in oracle.classical.iter().zip(arguments) {
            regs[0][*i] = v;
        }
        #[derive(Clone)]
        struct Record {
            caller: usize,
            ret: usize,
            dest: usize,
            fp: usize,
            callee: usize,
            saved: Vec<Bits>,
        }
        let mut records = Vec::<Record>::new();
        let mut active = Vec::<usize>::new();
        let (mut fi, mut pc, mut sp, mut max_depth) = (0, 0, 0u64, 0u64);
        let finish = |payload, code, rows, stack_used, max_depth| {
            Ok(Outcome {
                payload,
                code,
                rows,
                stack_used,
                max_depth,
            })
        };
        for t in 0..budget.steps {
            let f = &self.functions[fi];
            let r = f.rows.get(pc).ok_or("fell off function")?;
            pc += 1;
            let mut fault = None;
            match r {
                Row::Const(d, v) => regs[fi][*d] = v.clone(),
                Row::Bin(d, op, a, b) => regs[fi][*d] = regs[fi][*a].bin(&regs[fi][*b], op),
                Row::Cmp(d, op, a, b) => {
                    regs[fi][*d] = Bits::from_u64(1, u64::from(regs[fi][*a].cmp(&regs[fi][*b], op)))
                }
                Row::Select(d, p, a, b) => {
                    regs[fi][*d] = regs[fi][if regs[fi][*p].0[0] { *a } else { *b }].clone()
                }
                Row::Cast(d, op, a) => regs[fi][*d] = regs[fi][*a].cast(f.widths[*d], op == "sext"),
                Row::Mov(ds, ss) => {
                    let values: Vec<_> = ss.iter().map(|s| regs[fi][*s].clone()).collect();
                    for (d, v) in ds.iter().zip(values) {
                        regs[fi][*d] = v;
                    }
                }
                Row::FaultIf(p, c) => {
                    if regs[fi][*p].0[0] {
                        fault = Some(c.clone());
                    }
                }
                Row::Fault(c) => fault = Some(c.clone()),
                Row::Retval(a) => {
                    return finish(
                        regs[fi][*a].clone(),
                        Bits::zero(oracle.fault_width),
                        t + 1,
                        sp,
                        max_depth,
                    );
                }
                Row::Jump(b) => pc = *b,
                Row::Branch(p, a, b) => pc = if regs[fi][*p].0[0] { *a } else { *b },
                Row::Call(dest, callee, args) => {
                    let c = &self.functions[*callee];
                    let cells = 3 + c.locations.len() as u64;
                    if active.len() as u64 >= budget.depth
                        || cells > budget.stack.saturating_sub(sp)
                    {
                        fault = Some(Bits::from_u64(oracle.fault_width, 3));
                    } else {
                        // C1 capture precedes C2, including self-recursive calls.
                        let vals: Vec<_> = args.iter().map(|a| regs[fi][*a].clone()).collect();
                        let saved = c
                            .locations
                            .iter()
                            .map(|i| {
                                std::mem::replace(&mut regs[*callee][*i], Bits::zero(c.widths[*i]))
                            })
                            .collect();
                        let fp = active.last().copied().unwrap_or(usize::MAX);
                        records.push(Record {
                            caller: fi,
                            ret: pc,
                            dest: *dest,
                            fp,
                            callee: *callee,
                            saved,
                        });
                        active.push(records.len() - 1);
                        for (p, v) in c.params.iter().zip(vals) {
                            regs[*callee][*p] = v;
                        }
                        sp += cells;
                        max_depth = max_depth.max(active.len() as u64);
                        fi = *callee;
                        pc = 0;
                    }
                }
                Row::Ret(a) => {
                    if let Some(ri) = active.pop() {
                        let v = regs[fi][*a].clone();
                        let record = &records[ri];
                        if record.callee != fi {
                            return Err("internal activation mismatch".into());
                        }
                        for (i, old) in f.locations.iter().zip(&record.saved) {
                            regs[fi][*i] = old.clone();
                        }
                        fi = record.caller;
                        pc = record.ret;
                        regs[fi][record.dest] = v;
                        debug_assert_eq!(active.last().copied().unwrap_or(usize::MAX), record.fp);
                        // R5 changes fp/depth only. sp remains monotonic.
                    } else {
                        fault = Some(Bits::from_u64(oracle.fault_width, 4));
                    }
                }
            }
            if let Some(code) = fault {
                return finish(Bits::zero(oracle.target_width), code, t + 1, sp, max_depth);
            }
        }
        finish(
            Bits::zero(oracle.target_width),
            Bits::from_u64(oracle.fault_width, 1),
            budget.steps,
            sp,
            max_depth,
        )
    }
}
impl Function {
    fn add(&mut self, (name, width): (String, usize)) -> Result<usize> {
        if self.names.contains(&name) {
            return Err(format!("duplicate name {name}"));
        }
        let id = self.names.len();
        self.names.push(name);
        self.widths.push(width);
        Ok(id)
    }
    fn id(&self, s: &str) -> Result<usize> {
        self.names
            .iter()
            .position(|n| n == s)
            .ok_or_else(|| format!("unknown local operand {s}"))
    }
    fn label(&self, s: &str) -> Result<usize> {
        self.labels
            .get(s.strip_prefix('^').ok_or("expected label")?)
            .copied()
            .ok_or_else(|| format!("unknown label {s}"))
    }
    fn validate(&self) -> Result<()> {
        if self.rows.is_empty()
            || self.labels.values().next().is_none()
            || !self.labels.values().any(|v| *v == 0)
        {
            return Err("function requires entry block".into());
        }
        let mut starts: BTreeSet<_> = self.labels.values().copied().collect();
        starts.insert(self.rows.len());
        for end in starts.into_iter().filter(|n| *n > 0) {
            if !matches!(
                self.rows[end - 1],
                Row::Retval(_) | Row::Ret(_) | Row::Fault(_) | Row::Jump(_) | Row::Branch(..)
            ) {
                return Err("block missing terminator".into());
            }
        }
        for r in &self.rows {
            let (writes, reads): (Vec<usize>, Vec<usize>) = match r {
                Row::Const(d, v) => {
                    if self.widths[*d] != v.width() {
                        return Err("const width mismatch".into());
                    }
                    (vec![*d], vec![])
                }
                Row::Bin(d, _, a, b) => {
                    if self.widths[*d] != self.widths[*a] || self.widths[*a] != self.widths[*b] {
                        return Err("binop width mismatch".into());
                    }
                    (vec![*d], vec![*a, *b])
                }
                Row::Cmp(d, _, a, b) => {
                    if self.widths[*d] != 1 || self.widths[*a] != self.widths[*b] {
                        return Err("comparison width mismatch".into());
                    }
                    (vec![*d], vec![*a, *b])
                }
                Row::Select(d, p, a, b) => {
                    if self.widths[*p] != 1
                        || self.widths[*d] != self.widths[*a]
                        || self.widths[*a] != self.widths[*b]
                    {
                        return Err("select width mismatch".into());
                    }
                    (vec![*d], vec![*p, *a, *b])
                }
                Row::Cast(d, op, a) => {
                    if (op == "trunc" && self.widths[*d] >= self.widths[*a])
                        || (op != "trunc" && self.widths[*d] <= self.widths[*a])
                    {
                        return Err("cast width mismatch".into());
                    }
                    (vec![*d], vec![*a])
                }
                Row::Mov(ds, ss) => {
                    if ds.len() != ss.len()
                        || ds.iter().collect::<BTreeSet<_>>().len() != ds.len()
                        || ds
                            .iter()
                            .zip(ss)
                            .any(|(d, s)| self.widths[*d] != self.widths[*s])
                    {
                        return Err("parallel move width/arity/duplicate mismatch".into());
                    }
                    (ds.clone(), ss.clone())
                }
                Row::FaultIf(p, _) | Row::Branch(p, _, _) => {
                    if self.widths[*p] != 1 {
                        return Err("condition must have width 1".into());
                    }
                    (vec![], vec![*p])
                }
                Row::Retval(a) | Row::Ret(a) => {
                    if self.widths[*a] != self.target_width
                        || (matches!(r, Row::Retval(_)) != self.is_oracle)
                    {
                        return Err("invalid return".into());
                    }
                    (vec![], vec![*a])
                }
                Row::Call(d, _, args) => (vec![*d], args.clone()),
                _ => (vec![], vec![]),
            };
            if writes.iter().any(|w| !self.locations.contains(w)) {
                return Err("write to read-only operand".into());
            }
            let _ = reads;
        }
        Ok(())
    }
}
fn parse_row(line: &str, f: &Function, names: &[String]) -> Result<Row> {
    let (lhs, rhs) = line
        .split_once(" = ")
        .map_or((None, line), |(l, r)| (Some(l), r));
    let t: Vec<_> = rhs.split(' ').collect();
    let op = t[0];
    let id = |i: usize| {
        t.get(i)
            .ok_or("missing operand".to_string())
            .and_then(|s| f.id(s))
    };
    let dest = || f.id(lhs.ok_or("missing destination")?);
    let code = |i: usize| -> Result<Bits> {
        let token = t.get(i).ok_or("missing cause")?;
        if token.starts_with('-') {
            return Err("negative fault cause".into());
        }
        let value = Bits::literal(f.fault_width, token)?;
        Ok(if value.0.iter().any(|b| *b) {
            value
        } else {
            Bits::from_u64(f.fault_width, 4)
        })
    };
    let arity = |n: usize| -> Result<()> {
        if t.len() == n {
            Ok(())
        } else {
            Err(format!("wrong operand count for {op}"))
        }
    };
    let row = if let Some(n) = op.strip_prefix("lift.const.i") {
        arity(2)?;
        let n = n.parse().map_err(|_| "invalid constant width")?;
        if n == 0 {
            return Err("zero width".into());
        }
        Row::Const(dest()?, Bits::literal(n, t[1])?)
    } else if [
        "add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr",
    ]
    .iter()
    .any(|s| op == format!("lift.{s}"))
    {
        arity(3)?;
        Row::Bin(dest()?, op[5..].into(), id(1)?, id(2)?)
    } else if let Some(p) = op.strip_prefix("lift.icmp.") {
        arity(3)?;
        if !["eq", "ne", "ult", "ule", "slt", "sle"].contains(&p) {
            return Err(format!("unsupported comparison {p}"));
        }
        Row::Cmp(dest()?, p.into(), id(1)?, id(2)?)
    } else if op == "lift.select" {
        arity(4)?;
        Row::Select(dest()?, id(1)?, id(2)?, id(3)?)
    } else if ["zext", "sext", "trunc"]
        .iter()
        .any(|s| op.starts_with(&format!("lift.{s}.i")))
    {
        arity(2)?;
        let (kind, n) = op[5..].split_once(".i").unwrap();
        if n.parse::<usize>().ok() != Some(f.widths[dest()?]) {
            return Err("cast suffix mismatch".into());
        }
        Row::Cast(dest()?, kind.into(), id(1)?)
    } else {
        match op {
            "lift.mov" => {
                arity(2)?;
                Row::Mov(vec![dest()?], vec![id(1)?])
            }
            "lift.parmov" => {
                let l = lhs
                    .ok_or("missing parallel destinations")?
                    .strip_prefix('(')
                    .and_then(|s| s.strip_suffix(')'))
                    .ok_or("bad parallel destinations")?;
                let g = groups(rhs)?;
                if g.len() != 1 {
                    return Err("bad parallel sources".into());
                }
                Row::Mov(
                    list(l).iter().map(|s| f.id(s)).collect::<Result<_>>()?,
                    list(g[0]).iter().map(|s| f.id(s)).collect::<Result<_>>()?,
                )
            }
            "lift.faultif" => {
                arity(3)?;
                Row::FaultIf(id(1)?, code(2)?)
            }
            "fault" => {
                arity(2)?;
                Row::Fault(code(1)?)
            }
            "lift.retval" => {
                arity(2)?;
                Row::Retval(id(1)?)
            }
            "lift.ret" => {
                arity(2)?;
                Row::Ret(id(1)?)
            }
            "qjump" => {
                arity(2)?;
                Row::Jump(f.label(t[1])?)
            }
            "qbranch" => {
                arity(4)?;
                Row::Branch(id(1)?, f.label(t[2])?, f.label(t[3])?)
            }
            "lift.call" => {
                let g = groups(rhs)?;
                if g.len() != 1 || !rhs.ends_with(')') {
                    return Err("unsupported: only short-form lift.call".into());
                }
                let name = t
                    .get(1)
                    .ok_or("missing callee")?
                    .strip_prefix('@')
                    .ok_or("bad callee")?;
                let c = names
                    .iter()
                    .position(|n| n == name)
                    .ok_or_else(|| format!("unknown callee {name}"))?;
                Row::Call(
                    dest()?,
                    c,
                    list(g[0]).iter().map(|s| f.id(s)).collect::<Result<_>>()?,
                )
            }
            _ => return Err(format!("unsupported row {op}")),
        }
    };
    if lhs.is_some()
        && matches!(
            row,
            Row::FaultIf(..)
                | Row::Fault(_)
                | Row::Retval(_)
                | Row::Ret(_)
                | Row::Jump(_)
                | Row::Branch(..)
        )
    {
        return Err("unexpected destination".into());
    }
    Ok(row)
}

#[cfg(test)]
mod tests {
    use super::*;
    const INC: &str = include_str!("../../fixtures/inc8.bobj");
    const COL: &str = include_str!("../../fixtures/collatz.bobj");
    #[test]
    fn inc8_all_inputs_and_boundaries() {
        let p = Program::parse(INC).unwrap();
        for x in 0..256 {
            for b in 0..6 {
                let o = p.run(&[Bits::from_u64(8, x)], Budget::steps(b)).unwrap();
                assert_eq!(
                    (o.payload.low_u64(), o.code.low_u64()),
                    if b >= 3 { ((x + 1) & 255, 0) } else { (0, 1) }
                );
                assert_eq!(o.rows, b.min(3));
            }
        }
    }
    #[test]
    fn collatz_boundaries() {
        let p = Program::parse(COL).unwrap();
        assert_eq!(p.functions[1].locations.len() + 3, 28);
        for x in 1..256 {
            let mut v = x;
            let mut j = 0;
            while v != 1 {
                v = if v % 2 == 0 { v / 2 } else { v * 3 + 1 };
                j += 1;
            }
            let n = if x == 1 { 9 } else { 10 + 18 * j };
            for b in [0, n - 1, n, n + 1] {
                let o = p
                    .run(
                        &[Bits::from_u64(8, x)],
                        Budget {
                            steps: b,
                            heap: 0,
                            stack: 32,
                            depth: 32,
                        },
                    )
                    .unwrap();
                assert_eq!(
                    (o.payload.low_u64(), o.code.low_u64()),
                    if b >= n { (j & 255, 0) } else { (0, 1) },
                    "x={x} B={b}"
                );
            }
        }
        for b in [0, 1, 9, 100] {
            let o = p
                .run(
                    &[Bits::from_u64(8, 27)],
                    Budget {
                        steps: b,
                        heap: 0,
                        stack: 27,
                        depth: 1,
                    },
                )
                .unwrap();
            assert_eq!(o.code.low_u64(), if b == 0 { 1 } else { 3 });
        }
    }
    #[test]
    fn reject_memory_and_unknown_rows() {
        assert!(
            Program::parse(include_str!("../../fixtures/sum_db.bobj"))
                .unwrap_err()
                .contains("unsupported")
        );
        assert!(
            Program::parse(&INC.replace("lift.add", "lift.magic"))
                .unwrap_err()
                .contains("unsupported")
        );
        assert!(
            Program::parse(&INC.replace("r = lift.add x one", "x = lift.add x one"))
                .unwrap_err()
                .contains("read-only")
        );
    }
    #[test]
    fn recursive_capture_restore_and_fault_literal_width() {
        let p = Program::parse(include_str!("../../fixtures/countdown.bobj")).unwrap();
        for x in 0..=5 {
            let n = 6 + 8 * x;
            for b in [n - 1, n, n + 1] {
                let o = p
                    .run(
                        &[Bits::from_u64(8, x)],
                        Budget {
                            steps: b,
                            heap: 0,
                            stack: 64,
                            depth: 8,
                        },
                    )
                    .unwrap();
                assert_eq!(
                    (o.payload.low_u64(), o.code.low_u64()),
                    if b >= n { (x, 0) } else { (0, 1) }
                );
                assert_eq!(o.stack_used, 9 * (x + 1));
            }
        }
        let wide = INC.replace("f:wire[4]", "f:wire[129]").replace(
            "lift.retval r",
            "fault 340282366920938463463374607431768211456",
        );
        let p = Program::parse(&wide).unwrap();
        let o = p.run(&[Bits::from_u64(8, 1)], Budget::steps(3)).unwrap();
        assert!(o.code.0[128]);
        assert_eq!(o.code.low_u64(), 0);
        assert!(Program::parse(&INC.replace("lift.retval r", "fault 16")).is_err());
    }
    #[test]
    fn shifts_and_fault_zero() {
        let x = Bits::from_u64(8, 128);
        assert_eq!(x.shift(&Bits::from_u64(8, 1), "ashr").low_u64(), 192);
        assert_eq!(x.shift(&Bits::from_u64(8, 8), "ashr").low_u64(), 0);
        let p =
            Program::parse(&INC.replace("r = lift.add x one\nlift.retval r", "fault 0")).unwrap();
        assert_eq!(p.run(&[x], Budget::steps(2)).unwrap().code.low_u64(), 4);
    }
}
