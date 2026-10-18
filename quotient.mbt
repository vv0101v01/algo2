// =============================================================================
// quotient.mbt -- quotient rings R/I with R = F_p[x_1..x_n].
//
// A coset f + I is represented *by* its normal form NF(f) w.r.t. the reduced
// Groebner basis of I. Addition/multiplication of representatives followed
// by NF is therefore well-defined by construction, and the test-suite still
// verifies representative-independence explicitly (change f by random
// multiples of the generators; the coset operations must not notice).
//
// Type honesty: I is runtime data (the user supplies generators), and
// MoonBit has no dependent types, so "element of R/I" cannot be indexed by
// I at the type level. Cosets carry a structural tag of R/I and mixing
// cosets from different quotients aborts. What *is* compile-time: a Coset
// is a different type from Poly, so a raw polynomial can never be used
// where a coset is expected without passing through the quotient map
// `of_poly` (F_p[x] -> F_p[x]/I).
// =============================================================================

///|
fn structural_tag_of_ideal(ideal : Ideal) -> Int32 {
  // Polynomial rolling hash of the reduced Groebner basis, kept small to
  // stay far from 32-bit overflow. It is a runtime guard, not a proof of
  // equality (exact ideal equality is `Ideal::equal_to`).
  let mut h = 7
  for g in ideal.groebner() {
    for i in 0..<g.num_terms() {
      h = (h * 131 + g.coeff_at(i).to_int() + 1) % 1000003
      let m = g.mono_at(i)
      for j in 0..<m.num_vars() {
        h = (h * 131 + m.exp_at(j) + 1) % 1000003
      }
    }
    h = (h * 131 + 97) % 1000003
  }
  h
}

///|
pub struct QuotientRing {
  ideal : Ideal
  tag : Int32
}

///|
pub struct Coset {
  repr : Poly
  tag : Int32
}

///|
pub fn QuotientRing::new(ideal : Ideal) -> QuotientRing {
  { ideal, tag: structural_tag_of_ideal(ideal), }
}

///|
pub fn QuotientRing::from_generators(
  nvars : Int32,
  generators : Array[Poly],
) -> QuotientRing {
  QuotientRing::new(Ideal::new(nvars, generators))
}

///|
pub fn QuotientRing::ideal(self : QuotientRing) -> Ideal {
  self.ideal
}

///|
pub fn QuotientRing::num_vars(self : QuotientRing) -> Int32 {
  self.ideal.num_vars()
}

///|
pub fn QuotientRing::tag_value(self : QuotientRing) -> Int32 {
  self.tag
}

///|
/// The quotient (projection) map pi : F_p[x] -> F_p[x]/I, f |-> f + I,
/// computed as the normal form. Kernel is exactly I (tested).
pub fn QuotientRing::of_poly(self : QuotientRing, f : Poly) -> Coset {
  { repr: self.ideal.normal_form(f), tag: self.tag, }
}

///|
fn check_coset(ring : QuotientRing, a : Coset) -> Unit {
  if a.tag != ring.tag {
    abort(
      "quotient ring mismatch: cosets of different ideals cannot be mixed " +
      "(MoonBit cannot index Coset by the runtime ideal; this guard is " +
      "the explicit runtime half of that invariant)",
    )
  }
}

///|
pub fn QuotientRing::zero_coset(self : QuotientRing) -> Coset {
  self.of_poly(Poly::zero(self.num_vars()))
}

///|
pub fn QuotientRing::one_coset(self : QuotientRing) -> Coset {
  self.of_poly(Poly::one_poly(self.num_vars()))
}

///|
/// Image of the i-th variable: x_i + I, the i-th coordinate function on the
/// (possibly non-reduced) affine scheme Spec(F_p[x]/I).
pub fn QuotientRing::variable(self : QuotientRing, i : Int32) -> Coset {
  self.of_poly(Poly::variable(self.num_vars(), i))
}

///|
pub fn QuotientRing::scalar(self : QuotientRing, c : Fp) -> Coset {
  self.of_poly(Poly::constant(self.num_vars(), c))
}

///|
pub fn QuotientRing::add(self : QuotientRing, a : Coset, b : Coset) -> Coset {
  check_coset(self, a)
  check_coset(self, b)
  { repr: self.ideal.normal_form(a.repr.add(b.repr)), tag: self.tag, }
}

///|
pub fn QuotientRing::sub(self : QuotientRing, a : Coset, b : Coset) -> Coset {
  check_coset(self, a)
  check_coset(self, b)
  { repr: self.ideal.normal_form(a.repr.sub(b.repr)), tag: self.tag, }
}

///|
pub fn QuotientRing::neg(self : QuotientRing, a : Coset) -> Coset {
  check_coset(self, a)
  { repr: a.repr.negate(), tag: self.tag, }
}

///|
pub fn QuotientRing::mul(self : QuotientRing, a : Coset, b : Coset) -> Coset {
  check_coset(self, a)
  check_coset(self, b)
  { repr: self.ideal.normal_form(a.repr.mul(b.repr)), tag: self.tag, }
}

///|
pub fn QuotientRing::pow(self : QuotientRing, a : Coset, e : Int32) -> Coset {
  let mut r = self.one_coset()
  for _ in 0..<e {
    r = self.mul(r, a)
  }
  r
}

///|
pub fn QuotientRing::scale(self : QuotientRing, c : Fp, a : Coset) -> Coset {
  check_coset(self, a)
  { repr: a.repr.scale(c), tag: self.tag, }
}

///|
/// Evaluate a polynomial expression in elements of the quotient. This is
/// the universal property in action: an assignment of the variables extends
/// uniquely to a map out of F_p[x], and it descends to the quotient iff the
/// ideal generators evaluate to zero (`respects_ideal` below).
pub fn QuotientRing::evaluate(
  self : QuotientRing,
  expr : Poly,
  args : Array[Coset],
) -> Coset {
  let subs : Array[Poly] = []
  for a in args {
    check_coset(self, a)
    subs.push(a.repr)
  }
  self.of_poly(expr.compose(subs))
}

///|
pub fn Coset::repr_poly(self : Coset) -> Poly {
  self.repr
}

///|
pub fn Coset::is_zero(self : Coset) -> Bool {
  self.repr.is_zero()
}

///|
pub fn Coset::equal_to(self : Coset, other : Coset) -> Bool {
  self.tag == other.tag && self.repr.equal_to(other.repr)
}

///|
pub fn Coset::display(self : Coset) -> String {
  "[" + self.repr.display() + "]"
}

///|
/// dim_{F_p} of this quotient when finite (zero-dimensional ideal).
pub fn QuotientRing::finite_dimension(self : QuotientRing) -> Int32? {
  self.ideal.finite_dimension()
}

///|
/// Krull dimension of this quotient ring.
pub fn QuotientRing::krull_dimension(self : QuotientRing) -> Int32 {
  self.ideal.krull_dimension()
}
