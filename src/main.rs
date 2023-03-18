#![feature(box_patterns, box_syntax)]

use std::collections::HashMap;

type Int = usize;
#[derive(PartialEq, Clone)]
enum ITerm {
    Ann(Box<CTerm>, Box<CTerm>),
    Star,
    Pi(Box<CTerm>, Box<CTerm>),
    Bound(Int),
    Free(Name),
    At(Box<ITerm>, Box<CTerm>),
    Nat,
    NatElim(Box<CTerm>, Box<CTerm>, Box<CTerm>, Box<CTerm>),
    Zero,
    Succ(Box<CTerm>),
    Vec(Box<CTerm>, Box<CTerm>),
    Nil(Box<CTerm>),
    Cons(Box<CTerm>, Box<CTerm>, Box<CTerm>, Box<CTerm>),
    VecElim(
        Box<CTerm>,
        Box<CTerm>,
        Box<CTerm>,
        Box<CTerm>,
        Box<CTerm>,
        Box<CTerm>,
    ),
}
#[derive(PartialEq, Clone)]
enum CTerm {
    Inf(Box<ITerm>),
    Lam(Box<CTerm>),
}

#[derive(PartialEq, Eq, Hash, Clone)]
enum Name {
    Global(String),
    Local(Int),
    Quote(Int),
}

#[derive(Clone)]
struct ClonableClosure0 {
    f: fn(Value) -> Value,
}

impl ClonableClosure0 {
    fn new(f: fn(Value) -> Value) -> ClonableClosure0 {
        ClonableClosure0 { f }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(v)
    }
}

#[derive(Clone)]
struct ClonableClosure2 {
    d: Env,
    t: CTerm,
    f: fn(Value, Env, CTerm) -> Value,
}

impl ClonableClosure2 {
    fn new(d: Env, t: CTerm, f: fn(Value, Env, CTerm) -> Value) -> ClonableClosure2 {
        ClonableClosure2 { d, t, f }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(v, self.d.clone(), self.t.clone())
    }
}

#[derive(Clone)]
struct ClonableClosureV2 {
    v1: Value,
    v2: Value,
    f: fn(Value, Value, Value) -> Value,
}

impl ClonableClosureV2 {
    fn new(v1: Value, v2: Value, f: fn(Value, Value, Value) -> Value) -> ClonableClosureV2 {
        ClonableClosureV2 { v1, v2, f }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(v, self.v1.clone(), self.v2.clone())
    }
}

#[derive(Clone)]
struct ClonableClosureV1 {
    v: Value,
    f: fn(Value, Value) -> Value,
}

impl ClonableClosureV1 {
    fn new(v: Value, f: fn(Value, Value) -> Value) -> ClonableClosureV1 {
        ClonableClosureV1 { v, f }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(v, self.v.clone())
    }
}

#[derive(Clone)]
struct ClonableClosureV3 {
    v1: Value,
    v2: Value,
    v3: Value,
    f: fn(Value, Value, Value, Value) -> Value,
}

impl ClonableClosureV3 {
    fn new(
        v1: Value,
        v2: Value,
        v3: Value,
        f: fn(Value, Value, Value, Value) -> Value,
    ) -> ClonableClosureV3 {
        ClonableClosureV3 { v1, v2, v3, f }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(v, self.v1.clone(), self.v2.clone(), self.v3.clone())
    }
}

#[derive(Clone)]
struct ClonableClosureV4 {
    v1: Value,
    v2: Value,
    v3: Value,
    v4: Value,
    f: fn(Value, Value, Value, Value, Value) -> Value,
}

impl ClonableClosureV4 {
    fn new(
        v1: Value,
        v2: Value,
        v3: Value,
        v4: Value,
        f: fn(Value, Value, Value, Value, Value) -> Value,
    ) -> ClonableClosureV4 {
        ClonableClosureV4 { v1, v2, v3, v4, f }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(
            v,
            self.v1.clone(),
            self.v2.clone(),
            self.v3.clone(),
            self.v4.clone(),
        )
    }
}

#[derive(Clone)]
struct ClonableClosureV5 {
    v1: Value,
    v2: Value,
    v3: Value,
    v4: Value,
    v5: Value,
    f: fn(Value, Value, Value, Value, Value, Value) -> Value,
}

impl ClonableClosureV5 {
    fn new(
        v1: Value,
        v2: Value,
        v3: Value,
        v4: Value,
        v5: Value,
        f: fn(Value, Value, Value, Value, Value, Value) -> Value,
    ) -> ClonableClosureV5 {
        ClonableClosureV5 {
            v1,
            v2,
            v3,
            v4,
            v5,
            f,
        }
    }
    fn apply(&self, v: Value) -> Value {
        (self.f)(
            v,
            self.v1.clone(),
            self.v2.clone(),
            self.v3.clone(),
            self.v4.clone(),
            self.v5.clone(),
        )
    }
}

#[derive(Clone)]
enum ClonableClosure {
    ClonableClosure0(ClonableClosure0),
    ClonableClosure2(ClonableClosure2),
    ClonableClosureV1(ClonableClosureV1),
    ClonableClosureV2(ClonableClosureV2),
    ClonableClosureV3(ClonableClosureV3),
    ClonableClosureV4(ClonableClosureV4),
    ClonableClosureV5(ClonableClosureV5),
}

impl ClonableClosure {
    fn apply(&self, v: Value) -> Value {
        match self {
            ClonableClosure::ClonableClosure0(func) => func.apply(v),
            ClonableClosure::ClonableClosure2(func) => func.apply(v),
            ClonableClosure::ClonableClosureV1(func) => func.apply(v),
            ClonableClosure::ClonableClosureV2(func) => func.apply(v),
            ClonableClosure::ClonableClosureV3(func) => func.apply(v),
            ClonableClosure::ClonableClosureV4(func) => func.apply(v),
            ClonableClosure::ClonableClosureV5(func) => func.apply(v),
        }
    }
}

#[derive(Clone)]
enum Value {
    VLam(Box<ClonableClosure>),
    VStar,
    VPi(Box<Value>, Box<ClonableClosure>),
    VNeutral(Box<Neutral>),
    VNat,
    VZero,
    VSucc(Box<Value>),
    VNil(Box<Value>),
    VCons(Box<Value>, Box<Value>, Box<Value>, Box<Value>),
    VVec(Box<Value>, Box<Value>),
}

type Type = Value;

#[derive(Clone)]
enum Neutral {
    NFree(Name),
    NApp(Box<Neutral>, Value),
    NNatElim(Value, Value, Value, Box<Neutral>),
    NVecElim(Value, Value, Value, Value, Value, Box<Neutral>),
}

fn vfree(n: Name) -> Value {
    Value::VNeutral(box Neutral::NFree(n))
}

type Env = Vec<Value>;

fn ieval(term: ITerm, d: Env) -> Value {
    match term {
        ITerm::Ann(box cterm, _) => ceval(cterm, d),
        ITerm::Star => Value::VStar,
        ITerm::Pi(box t1, box t2) => Value::VPi(
            box ceval(t1, d.clone()),
            box ClonableClosure::ClonableClosure2(ClonableClosure2::new(
                d,
                t2,
                |x: Value, mut d: Env, t: CTerm| {
                    d.push(x);
                    ceval(t, d)
                },
            )),
        ),
        ITerm::Free(x) => vfree(x),
        ITerm::Bound(i) => d[i],
        ITerm::At(box e1, box e2) => vapp(ieval(e1, d.clone()), ceval(e2, d)),
        ITerm::Nat => Value::VNat,
        ITerm::Zero => Value::VZero,
        ITerm::Succ(box k) => Value::VSucc(box ceval(k, d)),
        ITerm::NatElim(box m, box mz, box ms, box k) => {
            let k_val = ceval(k, d.clone());
            match k_val {
                Value::VZero => ceval(mz, d),
                Value::VSucc(box l) => ceval(ms, d),
                Value::VNeutral(k) => Value::VNeutral(box Neutral::NNatElim(
                    ceval(m, d.clone()),
                    ceval(mz, d.clone()),
                    ceval(ms, d),
                    k,
                )),
                _ => panic!("Internal Error"),
            }
        }
        ITerm::VecElim(box a, box m, box mn, box mc, box k, box xs) => {
            fn rec(
                k_val: Value,
                xs_val: Value,
                d: Env,
                a: CTerm,
                m: CTerm,
                mn: CTerm,
                mc: CTerm,
            ) -> Value {
                match xs_val {
                    Value::VNil(_) => ceval(mn, d),
                    Value::VCons(_, box l, box x, box xs) => vec![
                        l.clone(),
                        x,
                        xs.clone(),
                        rec(l, xs, d.clone(), a, m, mn, mc.clone()),
                    ]
                    .iter()
                    .fold(ceval(mc, d), |v1, v2| vapp(v1, v2.clone())),
                    Value::VNeutral(n) => Value::VNeutral(box Neutral::NVecElim(
                        ceval(a, d.clone()),
                        ceval(m, d.clone()),
                        ceval(mn, d.clone()),
                        ceval(mc, d),
                        k_val,
                        n,
                    )),
                    _ => panic!("Internal Error"),
                }
            }
            rec(ceval(k, d.clone()), ceval(xs, d.clone()), d, a, m, mn, mc)
        }
    }
}

fn vapp(v1: Value, v2: Value) -> Value {
    match v1 {
        Value::VLam(box f) => f.apply(v2),
        Value::VNeutral(n) => Value::VNeutral(box Neutral::NApp(n, v2)),
        _ => panic!("Error"),
    }
}

fn ceval(term: CTerm, d: Env) -> Value {
    match term {
        CTerm::Inf(box i) => ieval(i, d),
        CTerm::Lam(box e) => Value::VLam(box ClonableClosure::ClonableClosure2(
            ClonableClosure2::new(d, e, |v, mut d, t| {
                d.push(v);
                ceval(t, d)
            }),
        )),
    }
}

enum Kind {
    Star,
}

enum Info {
    HasKind(Kind),
    HasType(Type),
}

type Context = HashMap<Name, Type>;

type StrResult<T> = Result<T, String>;

fn itype0(context: Context, term: ITerm) -> StrResult<Type> {
    itype(0, context, term)
}

fn itype(i: Int, mut context: Context, term: ITerm) -> StrResult<Type> {
    match term {
        ITerm::Ann(box e, box o) => {
            ctype(i, context.clone(), o.clone(), Value::VStar)?;
            let t = ceval(o, vec![]);
            ctype(i, context, e, t.clone())?;
            Ok(t)
        }
        ITerm::Star => Ok(Value::VStar),
        ITerm::Pi(box o1, box o2) => {
            ctype(i, context.clone(), o1.clone(), Value::VStar)?;
            let t = ceval(o1, vec![]);
            context.insert(Name::Local(i), t);
            ctype(
                i + 1,
                context,
                csubst(0, ITerm::Free(Name::Local(i)), o2),
                Value::VStar,
            )?;
            Ok(Value::VStar)
        }
        ITerm::Free(x) => match context.get(&x) {
            Some(t) => Ok(t.clone()),
            None => Err("unknown identifier".to_string()),
        },
        ITerm::At(box e1, box e2) => {
            let sigma = itype(i, context.clone(), e1)?;
            match sigma {
                Value::VPi(box t1, box t2) => {
                    ctype(i, context, e2.clone(), t1)?;
                    Ok(t2.apply(ceval(e2, vec![])))
                }
                _ => Err("illegal application".to_string()),
            }
        }
        ITerm::Nat => Ok(Value::VStar),
        ITerm::Zero => Ok(Value::VNat),
        ITerm::Succ(box k) => {
            ctype(i, context, k, Value::VNat)?;
            Ok(Value::VNat)
        }
        ITerm::NatElim(box m, box mz, box ms, box k) => {
            ctype(
                i,
                context.clone(),
                m.clone(),
                Value::VPi(
                    box Value::VNat,
                    box ClonableClosure::ClonableClosure0(ClonableClosure0::new(|_| Value::VStar)),
                ),
            )?;
            let m_val = ceval(m, vec![]);
            ctype(i, context.clone(), mz, vapp(m_val.clone(), Value::VZero))?;
            ctype(
                i,
                context.clone(),
                ms,
                Value::VPi(
                    box Value::VNat,
                    box ClonableClosure::ClonableClosureV1(ClonableClosureV1::new(
                        m_val.clone(),
                        |l, v| {
                            Value::VPi(
                                box vapp(v.clone(), l.clone()),
                                box ClonableClosure::ClonableClosureV2(ClonableClosureV2::new(
                                    v,
                                    l,
                                    |_, v1, v2| vapp(v1, Value::VSucc(box v2)),
                                )),
                            )
                        },
                    )),
                ),
            )?;
            ctype(i, context, k.clone(), Value::VNat)?;
            let k_val = ceval(k, vec![]);
            Ok(vapp(m_val, k_val))
        }
        ITerm::Vec(box a, box k) => {
            ctype(i, context.clone(), a, Value::VStar)?;
            ctype(i, context, k, Value::VNat)?;
            Ok(Value::VStar)
        }
        ITerm::Nil(box a) => {
            ctype(i, context, a.clone(), Value::VStar)?;
            let a_val = ceval(a, vec![]);
            Ok(Value::VVec(box a_val, box Value::VZero))
        }
        ITerm::Cons(box a, box k, box x, box xs) => {
            let a_val = ceval(a, vec![]);
            ctype(i, context.clone(), k.clone(), Value::VNat)?;
            let k_val = ceval(k, vec![]);
            ctype(i, context.clone(), x, a_val.clone())?;
            ctype(
                i,
                context,
                xs,
                Value::VVec(box a_val.clone(), box k_val.clone()),
            )?;
            Ok(Value::VVec(box a_val, box Value::VSucc(box k_val)))
        }
        ITerm::VecElim(box a, box m, box mn, box mc, box k, box vs) => {
            ctype(i, context.clone(), a.clone(), Value::VStar)?;
            let a_val = ceval(a, vec![]);
            ctype(
                i,
                context.clone(),
                m.clone(),
                Value::VPi(
                    box Value::VNat,
                    box ClonableClosure::ClonableClosureV1(ClonableClosureV1::new(
                        a_val.clone(),
                        |k, v| {
                            Value::VPi(
                                box Value::VVec(box v, box k),
                                box ClonableClosure::ClonableClosure0(ClonableClosure0::new(
                                    |_| Value::VStar,
                                )),
                            )
                        },
                    )),
                ),
            )?;
            let m_val = ceval(m, vec![]);
            ctype(
                i,
                context.clone(),
                mn,
                vec![Value::VZero, Value::VNil(box a_val.clone())]
                    .iter()
                    .fold(m_val.clone(), |v1, v2| vapp(v1, v2.clone())),
            )?;
            ctype(
                i,
                context.clone(),
                mc,
                Value::VPi(
                    box Value::VNat,
                    box ClonableClosure::ClonableClosureV2(ClonableClosureV2::new(
                        a_val.clone(),
                        m_val.clone(),
                        |l, v1, v2| {
                            Value::VPi(
                                box v1.clone(),
                                box ClonableClosure::ClonableClosureV3(ClonableClosureV3::new(
                                    l,
                                    v1,
                                    v2,
                                    |y, v1, v2, v3| {
                                        Value::VPi(
                                            box Value::VVec(box v2.clone(), box v1.clone()),
                                            box ClonableClosure::ClonableClosureV4(
                                                ClonableClosureV4::new(
                                                    v1,
                                                    v2,
                                                    y,
                                                    v3,
                                                    |ys, v1, v2, v3, v4| {
                                                        Value::VPi(
                                                            box vec![v1.clone(), ys.clone()]
                                                                .iter()
                                                                .fold(v4.clone(), |v1, v2| {
                                                                    vapp(v1, v2.clone())
                                                                }),
                                                            box ClonableClosure::ClonableClosureV5(
                                                                ClonableClosureV5::new(
                                                                    v1,
                                                                    v2,
                                                                    v3,
                                                                    ys,
                                                                    v4,
                                                                    |_, v1, v2, v3, v4, v5| {
                                                                        vec![
                                                                            Value::VSucc(
                                                                                box v1.clone(),
                                                                            ),
                                                                            Value::VCons(
                                                                                box v2, box v1,
                                                                                box v3, box v4,
                                                                            ),
                                                                        ]
                                                                        .iter()
                                                                        .fold(v5, |v1, v2| {
                                                                            vapp(v1, v2.clone())
                                                                        })
                                                                    },
                                                                ),
                                                            ),
                                                        )
                                                    },
                                                ),
                                            ),
                                        )
                                    },
                                )),
                            )
                        },
                    )),
                ),
            )?;
            ctype(i, context.clone(), k.clone(), Value::VNat)?;
            let k_val = ceval(k, vec![]);
            ctype(
                i,
                context,
                vs.clone(),
                Value::VVec(box a_val, box k_val.clone()),
            )?;
            let vs_val = ceval(vs, vec![]);
            Ok(vec![k_val, vs_val]
                .iter()
                .fold(m_val, |v1, v2| vapp(v1, v2.clone())))
        }
    }
}

fn ctype(i: Int, mut context: Context, term: CTerm, v1: Type) -> StrResult<()> {
    match term {
        CTerm::Inf(box e) => {
            let v2 = itype(i, context, e)?;
            if quote0(v1) == quote0(v2) {
                Ok(())
            } else {
                Err("type mismatch".to_string())
            }
        }
        CTerm::Lam(box e) => match v1 {
            Value::VPi(box t1, box t2) => {
                context.insert(Name::Local(i), t1);
                ctype(
                    i + 1,
                    context,
                    csubst(0, ITerm::Free(Name::Local(i)), e),
                    t2.apply(vfree(Name::Local(i))),
                )
            }
            _ => Err("type mismatch".to_string()),
        },
        _ => Err("type mismatch".to_string()),
    }
}

fn isubst(i: Int, r: ITerm, term: ITerm) -> ITerm {
    match term {
        ITerm::Ann(box e, box t) => ITerm::Ann(box csubst(i, r.clone(), e), box csubst(i, r, t)),
        ITerm::Star => ITerm::Star,
        ITerm::Pi(box t1, box t2) => {
            ITerm::Pi(box csubst(i, r.clone(), t1), box csubst(i + 1, r, t2))
        }
        ITerm::Bound(j) => {
            if i == j {
                r
            } else {
                ITerm::Bound(j)
            }
        }
        ITerm::Free(y) => ITerm::Free(y),
        ITerm::At(box e1, box e2) => ITerm::At(box isubst(i, r.clone(), e1), box csubst(i, r, e2)),
        ITerm::Nat => ITerm::Nat,
        ITerm::Zero => ITerm::Zero,
        ITerm::Succ(box n) => ITerm::Succ(box csubst(i, r, n)),
    }
}

fn csubst(i: Int, r: ITerm, term: CTerm) -> CTerm {
    match &term {
        CTerm::Inf(box e) => CTerm::Inf(box isubst(i, r, e.clone())),
        CTerm::Lam(box e) => CTerm::Lam(box csubst(i + 1, r, term)),
    }
}

fn quote0(v: Value) -> CTerm {
    quote(0, v)
}

fn quote(i: Int, v: Value) -> CTerm {
    match v {
        Value::VLam(box f) => CTerm::Lam(box quote(i + 1, f.apply(vfree(Name::Quote(i))))),
        Value::VStar => CTerm::Inf(box ITerm::Star),
        Value::VPi(box v, box f) => CTerm::Inf(box ITerm::Pi(
            box quote(i, v),
            box quote(i + 1, f.apply(vfree(Name::Quote(i)))),
        )),
        Value::VNeutral(box n) => CTerm::Inf(box neutral_quote(i, n)),
        Value::VNat => CTerm::Inf(box ITerm::Nat),
        Value::VZero => CTerm::Inf(box ITerm::Zero),
        Value::VSucc(box n) => CTerm::Inf(box ITerm::Succ(box quote(i, n))),
        Value::VNil(box a) => CTerm::Inf(box ITerm::Nil(box quote(i, a))),
        Value::VCons(box a, box n, box x, box xs) => CTerm::Inf(box ITerm::Cons(
            box quote(i, a),
            box quote(i, n),
            box quote(i, x),
            box quote(i, xs),
        )),
        Value::VVec(box a, box n) => CTerm::Inf(box ITerm::Vec(box quote(i, a), box quote(i, n))),
    }
}

fn neutral_quote(i: Int, n: Neutral) -> ITerm {
    match n {
        Neutral::NFree(x) => boundfree(i, x),
        Neutral::NApp(box n, v) => ITerm::At(box neutral_quote(i, n), box quote(i, v)),
        Neutral::NNatElim(m, z, s, box n) => ITerm::NatElim(
            box quote(i, m),
            box quote(i, z),
            box quote(i, s),
            box CTerm::Inf(box neutral_quote(i, n)),
        ),
        Neutral::NVecElim(a, m, mn, mc, n, box xs) => ITerm::VecElim(
            box quote(i, a),
            box quote(i, m),
            box quote(i, mn),
            box quote(i, mc),
            box quote(i, n),
            box CTerm::Inf(box neutral_quote(i, xs)),
        ),
    }
}

fn boundfree(i: Int, n: Name) -> ITerm {
    match n {
        Name::Quote(k) => ITerm::Bound(i - k - 1),
        x => ITerm::Free(x),
    }
}

fn main() {
    println!("Hello, world!");
}
