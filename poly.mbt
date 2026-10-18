// =============================================================================
// poly.mbt -- sparse multivariate polynomials over F_p with lex monomial
// order, and the multivariate division algorithm.
//
// Representation invariant (enforced by every constructor/operation):
//   * terms are sorted strictly decreasing by lex order x0 > x1 > ... ;
//   * no term has coefficient 0, no monomial occurs twice.
// Hence structural equality of the representation IS polynomial equality:
// the normal form is canonical, not an equivalence we re-check each time.
// =============================================================================

///|
fn int_array_copy(a : Array[Int32]) -> Array[Int32] {
  let r : Array[Int32] = []
  for i in 0..<a.length() {
    r.push(a[i])
  }
  r
}

///|
fn int_array_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
/// Display names for variables. Index 0 is the *largest* variable in lex.
pub fn var_name(i : Int32) -> String {
  let names = ["x", "y", "z", "w", "u", "v", "s", "t"]
  match names.get(i) {
    Some(s) => s
    None => "x\{i}"
  }
}

// -----------------------------------------------------------------------------
// Monomials x^a, stored as exponent vectors.
// -----------------------------------------------------------------------------

///|
pub struct Mono {
  exps : Array[Int32]
}

///|
pub fn Mono::one(nvars : Int32) -> Mono {
  let e : Array[Int32] = []
  for _ in 0..<nvars {
    e.push(0)
  }
  { exps: e, }
}

///|
pub fn Mono::variable(nvars : Int32, i : Int32) -> Mono {
  let m = Mono::one(nvars)
  m.exps[i] = 1
  m
}

///|
pub fn Mono::from_array(exps : Array[Int32]) -> Mono {
  { exps: int_array_copy(exps), }
}

///|
pub fn Mono::copy(self : Mono) -> Mono {
  { exps: int_array_copy(self.exps), }
}

///|
pub fn Mono::num_vars(self : Mono) -> Int32 {
  self.exps.length()
}

///|
pub fn Mono::exp_at(self : Mono, i : Int32) -> Int32 {
  self.exps[i]
}

///|
pub fn Mono::equal_to(self : Mono, other : Mono) -> Bool {
  int_array_eq(self.exps, other.exps)
}

///|
/// Lexicographic comparison with x0 > x1 > ... : returns -1, 0 or +1.
/// This is a monomial *order*: 1 is smallest and it is compatible with
/// multiplication, which is exactly what makes division terminate.
pub fn Mono::compare(self : Mono, other : Mono) -> Int32 {
  if self.exps.length() != other.exps.length() {
    abort("Mono::compare: variable count mismatch")
  }
  for i in 0..<self.exps.length() {
    if self.exps[i] > other.exps[i] {
      return 1
    }
    if self.exps[i] < other.exps[i] {
      return -1
    }
  }
  0
}

///|
pub fn Mono::mul(self : Mono, other : Mono) -> Mono {
  let e : Array[Int32] = []
  for i in 0..<self.exps.length() {
    e.push(self.exps[i] + other.exps[i])
  }
  { exps: e, }
}

///|
/// Does `self` divide `other`? (Componentwise <= on exponents.)
pub fn Mono::divides(self : Mono, other : Mono) -> Bool {
  for i in 0..<self.exps.length() {
    if self.exps[i] > other.exps[i] {
      return false
    }
  }
  true
}

///|
/// Exact quotient other/self when defined.
pub fn Mono::quotient(other : Mono, self : Mono) -> Mono {
  if !self.divides(other) {
    abort("Mono::quotient: divisor does not divide")
  }
  let e : Array[Int32] = []
  for i in 0..<self.exps.length() {
    e.push(other.exps[i] - self.exps[i])
  }
  { exps: e, }
}

///|
pub fn Mono::lcm(self : Mono, other : Mono) -> Mono {
  let e : Array[Int32] = []
  for i in 0..<self.exps.length() {
    if self.exps[i] >= other.exps[i] {
      e.push(self.exps[i])
    } else {
      e.push(other.exps[i])
    }
  }
  { exps: e, }
}

///|
pub fn Mono::total_degree(self : Mono) -> Int32 {
  let mut d = 0
  for i in 0..<self.exps.length() {
    d = d + self.exps[i]
  }
  d
}

///|
pub fn Mono::is_one(self : Mono) -> Bool {
  self.total_degree() == 0
}

///|
pub fn Mono::display(self : Mono) -> String {
  let sb = StringBuilder()
  let mut first = true
  for i in 0..<self.exps.length() {
    if self.exps[i] > 0 {
      if !first {
        sb.write_string("*")
      }
      first = false
      sb.write_string(var_name(i))
      if self.exps[i] > 1 {
        sb.write_string("^")
        sb.write_string("\{self.exps[i]}")
      }
    }
  }
  if first {
    sb.write_string("1")
  }
  sb.to_string()
}

// -----------------------------------------------------------------------------
// Terms and polynomials.
// -----------------------------------------------------------------------------

///|
pub struct Term {
  mut coeff : Fp
  mono : Mono
}

///|
pub fn Term::new(coeff : Fp, mono : Mono) -> Term {
  { coeff, mono: mono.copy(), }
}

///|
pub fn Term::copy(self : Term) -> Term {
  { coeff: self.coeff, mono: self.mono.copy(), }
}

///|
pub struct Poly {
  nvars : Int32
  terms : Array[Term]
}

///|
fn poly_normalize(nvars : Int32, raw : Array[Term]) -> Poly {
  // Combine like monomials.
  let acc : Array[Term] = []
  for t in raw {
    if t.coeff.is_zero() {
      continue
    }
    let mut found = -1
    for j in 0..<acc.length() {
      if acc[j].mono.equal_to(t.mono) {
        found = j
        break
      }
    }
    if found >= 0 {
      acc[found].coeff = acc[found].coeff + t.coeff
    } else {
      acc.push(t.copy())
    }
  }
  // Drop zeros created by cancellation.
  let kept : Array[Term] = []
  for t in acc {
    if !t.coeff.is_zero() {
      kept.push(t)
    }
  }
  // Insertion sort (lists stay small; n log n is unnecessary here, and an
  // obvious total-order sort keeps the canonicality argument transparent).
  for i in 1..<kept.length() {
    let key = kept[i]
    let mut j = i - 1
    while j >= 0 && kept[j].mono.compare(key.mono) < 0 {
      kept[j + 1] = kept[j]
      j = j - 1
    }
    kept[j + 1] = key
  }
  { nvars, terms: kept, }
}

///|
pub fn Poly::num_vars(self : Poly) -> Int32 {
  self.nvars
}

///|
pub fn Poly::num_terms(self : Poly) -> Int32 {
  self.terms.length()
}

///|
pub fn Poly::coeff_at(self : Poly, i : Int32) -> Fp {
  self.terms[i].coeff
}

///|
pub fn Poly::mono_at(self : Poly, i : Int32) -> Mono {
  self.terms[i].mono.copy()
}

///|
/// Coefficient of a given monomial (zero if absent).
pub fn Poly::coeff_of(self : Poly, m : Mono) -> Fp {
  for t in self.terms {
    if t.mono.equal_to(m) {
      return t.coeff
    }
  }
  Fp::zero()
}

///|
pub fn Poly::zero(nvars : Int32) -> Poly {
  { nvars, terms: [], }
}

///|
pub fn Poly::constant(nvars : Int32, c : Fp) -> Poly {
  poly_normalize(nvars, [Term::new(c, Mono::one(nvars))])
}

///|
pub fn Poly::one_poly(nvars : Int32) -> Poly {
  Poly::constant(nvars, Fp::one())
}

///|
pub fn Poly::variable(nvars : Int32, i : Int32) -> Poly {
  poly_normalize(nvars, [Term::new(Fp::one(), Mono::variable(nvars, i))])
}

///|
pub fn Poly::monomial(nvars : Int32, coeff : Fp, exps : Array[Int32]) -> Poly {
  poly_normalize(nvars, [Term::new(coeff, Mono::from_array(exps))])
}

///|
pub fn Poly::from_terms(nvars : Int32, terms : Array[Term]) -> Poly {
  poly_normalize(nvars, terms)
}

///|
/// Convenience constructor from (coefficient-as-int, exponents) pairs.
/// Coefficients are read modulo PRIME, so `(-1, [1,0])` means `-x`.
pub fn Poly::from_int_terms(
  nvars : Int32,
  spec : Array[(Int32, Array[Int32])],
) -> Poly {
  let ts : Array[Term] = []
  for (c, e) in spec {
    ts.push(Term::new(Fp::new(c), Mono::from_array(e)))
  }
  poly_normalize(nvars, ts)
}

///|
pub fn Poly::is_zero(self : Poly) -> Bool {
  self.terms.length() == 0
}

///|
pub fn Poly::equal_to(self : Poly, other : Poly) -> Bool {
  if self.nvars != other.nvars || self.terms.length() != other.terms.length() {
    return false
  }
  for i in 0..<self.terms.length() {
    if self.terms[i].coeff != other.terms[i].coeff {
      return false
    }
    if !self.terms[i].mono.equal_to(other.terms[i].mono) {
      return false
    }
  }
  true
}

///|
pub fn Poly::add(self : Poly, other : Poly) -> Poly {
  if self.nvars != other.nvars {
    abort("Poly::add: variable count mismatch")
  }
  let raw : Array[Term] = []
  for t in self.terms {
    raw.push(t.copy())
  }
  for t in other.terms {
    raw.push(t.copy())
  }
  poly_normalize(self.nvars, raw)
}

///|
pub fn Poly::negate(self : Poly) -> Poly {
  let raw : Array[Term] = []
  for t in self.terms {
    raw.push(Term::new(-t.coeff, t.mono))
  }
  poly_normalize(self.nvars, raw)
}

///|
pub fn Poly::sub(self : Poly, other : Poly) -> Poly {
  self.add(other.negate())
}

///|
pub fn Poly::scale(self : Poly, c : Fp) -> Poly {
  let raw : Array[Term] = []
  for t in self.terms {
    raw.push(Term::new(c * t.coeff, t.mono))
  }
  poly_normalize(self.nvars, raw)
}

///|
pub fn Poly::mul(self : Poly, other : Poly) -> Poly {
  if self.nvars != other.nvars {
    abort("Poly::mul: variable count mismatch")
  }
  let raw : Array[Term] = []
  for a in self.terms {
    for b in other.terms {
      raw.push(Term::new(a.coeff * b.coeff, a.mono.mul(b.mono)))
    }
  }
  poly_normalize(self.nvars, raw)
}

///|
pub fn Poly::pow(self : Poly, e : Int32) -> Poly {
  if e < 0 {
    abort("Poly::pow: negative exponent")
  }
  let mut r = Poly::one_poly(self.nvars)
  for _ in 0..<e {
    r = r.mul(self)
  }
  r
}

///|
pub impl Add for Poly with fn add(self, other) {
  self.add(other)
}

///|
pub impl Sub for Poly with fn sub(self, other) {
  self.sub(other)
}

///|
pub impl Mul for Poly with fn mul(self, other) {
  self.mul(other)
}

///|
pub fn Poly::lead_mono(self : Poly) -> Mono {
  if self.is_zero() {
    abort("Poly::lead_mono: zero polynomial has no leading monomial")
  }
  self.terms[0].mono.copy()
}

///|
pub fn Poly::lead_coeff(self : Poly) -> Fp {
  if self.is_zero() {
    abort("Poly::lead_coeff: zero polynomial")
  }
  self.terms[0].coeff
}

///|
pub fn Poly::lead_term(self : Poly) -> Term {
  if self.is_zero() {
    abort("Poly::lead_term: zero polynomial")
  }
  self.terms[0].copy()
}

///|
/// Evaluate at an F_p-point. This is the evaluation ring homomorphism
/// ev_a : F_p[x_1..x_n] -> F_p, whose kernel is the maximal ideal m_a.
pub fn Poly::eval(self : Poly, pt : Array[Fp]) -> Fp {
  if pt.length() != self.nvars {
    abort("Poly::eval: point dimension mismatch")
  }
  let mut acc = Fp::zero()
  for t in self.terms {
    let mut v = t.coeff
    for i in 0..<self.nvars {
      v = v * pt[i].pow(t.mono.exps[i])
    }
    acc = acc + v
  }
  acc
}

///|
/// Composition: if `self` is in m variables and `subs` gives m polynomials
/// in n variables, returns self(subs) in n variables. Algebraically this is
/// the F_p-algebra homomorphism F_p[y_1..y_m] -> F_p[x_1..x_n] determined by
/// the universal property of polynomial rings (images of the y_j freely
/// chosen) -- the algebraic shadow of a polynomial map A^n -> A^m.
pub fn Poly::compose(self : Poly, subs : Array[Poly]) -> Poly {
  if subs.length() != self.nvars {
    abort("Poly::compose: substitution count mismatch")
  }
  let n = if subs.length() == 0 { 0 } else { subs[0].nvars }
  let mut acc = Poly::zero(n)
  for t in self.terms {
    let mut prod = Poly::constant(n, t.coeff)
    for i in 0..<self.nvars {
      prod = prod.mul(subs[i].pow(t.mono.exps[i]))
    }
    acc = acc.add(prod)
  }
  acc
}

///|
/// Identity variable mapping [0, 1, ..., n-1] for Poly::relabel.
pub fn identity_mapping(n : Int32) -> Array[Int32] {
  let m : Array[Int32] = []
  for i in 0..<n {
    m.push(i)
  }
  m
}

///|
/// Shifted variable mapping i |-> i + offset for Poly::relabel.
pub fn shifted_mapping(n : Int32, offset : Int32) -> Array[Int32] {
  let m : Array[Int32] = []
  for i in 0..<n {
    m.push(i + offset)
  }
  m
}

///|
/// Relabel variables: `mapping[i]` is the new index of old variable i.
/// Used to embed polynomial rings into bigger ones (disjoint union of
/// variables = the coproduct of polynomial algebras).
pub fn Poly::relabel(
  self : Poly,
  mapping : Array[Int32],
  new_nvars : Int32,
) -> Poly {
  if mapping.length() != self.nvars {
    abort("Poly::relabel: mapping length != variable count")
  }
  for v in mapping {
    if v < 0 || v >= new_nvars {
      abort("Poly::relabel: target variable index out of range")
    }
  }
  let raw : Array[Term] = []
  for t in self.terms {
    let e : Array[Int32] = []
    for _ in 0..<new_nvars {
      e.push(0)
    }
    for i in 0..<self.nvars {
      e[mapping[i]] = e[mapping[i]] + t.mono.exps[i]
    }
    raw.push(Term::new(t.coeff, Mono::from_array(e)))
  }
  poly_normalize(new_nvars, raw)
}

///|
/// Deterministic pseudo-random polynomial (property-test utility).
pub fn Poly::pseudo_random(
  rng : Rng,
  nvars : Int32,
  max_terms : Int32,
  max_exp : Int32,
) -> Poly {
  let ts : Array[Term] = []
  let k = rng.range(0, max_terms)
  for _ in 0..<k {
    let e : Array[Int32] = []
    for _ in 0..<nvars {
      e.push(rng.range(0, max_exp))
    }
    ts.push(Term::new(rng.fp_nonzero(), Mono::from_array(e)))
  }
  poly_normalize(nvars, ts)
}

///|
pub fn Poly::display(self : Poly) -> String {
  if self.is_zero() {
    return "0"
  }
  let sb = StringBuilder()
  for i in 0..<self.terms.length() {
    if i > 0 {
      sb.write_string(" + ")
    }
    let t = self.terms[i]
    if t.mono.is_one() {
      sb.write_string(t.coeff.display())
    } else if t.coeff == Fp::one() {
      sb.write_string(t.mono.display())
    } else {
      sb.write_string(t.coeff.display())
      sb.write_string("*")
      sb.write_string(t.mono.display())
    }
  }
  sb.to_string()
}

// -----------------------------------------------------------------------------
// Multivariate division. reduce(f, G) computes a remainder r with
// f - r in the ideal (G) and no term of r divisible by any LT(g), g in G.
// If G is a Groebner basis the remainder is unique (the normal form NF(f));
// for arbitrary G it is not -- the tests demonstrate both directions.
// -----------------------------------------------------------------------------

///|
fn term_as_poly(nvars : Int32, t : Term) -> Poly {
  poly_normalize(nvars, [t.copy()])
}

///|
pub fn Poly::reduce_by(self : Poly, basis : Array[Poly]) -> Poly {
  let mut p = self
  let mut r = Poly::zero(self.nvars)
  let mut steps = 0
  while !p.is_zero() {
    steps = steps + 1
    if steps > 100000 {
      abort("Poly::reduce_by: step limit exceeded (order must be a well-order)")
    }
    let lt = p.lead_term()
    let mut reducer : Poly = Poly::zero(self.nvars)
    let mut found = false
    for g in basis {
      if g.is_zero() {
        continue
      }
      if g.lead_mono().divides(lt.mono) {
        reducer = g
        found = true
        break
      }
    }
    if found {
      let qmono = Mono::quotient(lt.mono, reducer.lead_mono())
      let qcoeff = lt.coeff.div_(reducer.lead_coeff())
      let q = term_as_poly(self.nvars, Term::new(qcoeff, qmono))
      p = p.sub(q.mul(reducer))
    } else {
      let lt_poly = term_as_poly(self.nvars, lt)
      r = r.add(lt_poly)
      p = p.sub(lt_poly)
    }
  }
  r
}

///|
/// The S-polynomial of f and g: the cancellation of their leading terms
/// along L = lcm(LM(f), LM(g)). Buchberger's criterion says a basis is a
/// Groebner basis iff every S-polynomial reduces to zero.
pub fn spoly(f : Poly, g : Poly) -> Poly {
  let l = f.lead_mono().lcm(g.lead_mono())
  let tf = Term::new(
    Fp::one().div_(f.lead_coeff()),
    Mono::quotient(l, f.lead_mono()),
  )
  let tg = Term::new(
    Fp::one().div_(g.lead_coeff()),
    Mono::quotient(l, g.lead_mono()),
  )
  term_as_poly(f.nvars, tf).mul(f).sub(term_as_poly(f.nvars, tg).mul(g))
}
