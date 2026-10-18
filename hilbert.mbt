// =============================================================================
// hilbert.mbt -- Hilbert functions, Hilbert series and Hilbert polynomials
// for homogeneous ideals in the graded polynomial ring S = F_7[x_0..x_{n-1}].
//
// Mathematical route (no interpolation guessing):
//   For homogeneous I, Macaulay's theorem says the standard monomials are a
//   basis of S/I; division of a homogeneous polynomial by the (homogeneous)
//   Groebner basis stays in its degree, so
//       HF_{S/I}(d) = #{ monomials of degree d not in in(I) }.
//   Counting those by inclusion-exclusion over the minimal monomial
//   generators L_1..L_m of in(I):
//       HF(d) = sum_{S subseteq [m]} (-1)^|S| C(d - deg lcm(S) + n - 1, n-1)
//   where the binomial is 0 when d < deg lcm(S). Replacing each counting
//   binomial by the *polynomial* (1/(n-1)!) prod_{j=1}^{n-1} (t-e+j), which
//   agrees with it for all d >= max_S deg lcm(S), yields the Hilbert
//   polynomial P_I(t) in Q[t] exactly -- this is a derivation of P_I, and
//   the tests additionally cross-check P_I(d) against independently
//   enumerated Hilbert function values, including small d where they are
//   supposed to *differ* in general.
//   The same inclusion-exclusion gives the Hilbert series
//       HS(t) = [ sum_S (-1)^|S| t^{deg lcm(S)} ] / (1-t)^n.
//
// APIs return None for non-homogeneous ideals: the Hilbert polynomial is a
// graded notion and faking it for arbitrary I (where one must first choose
// a filtration/homogenization with a graded order) is refused.
// =============================================================================

///|
/// Total degree of a polynomial (-1 for the zero polynomial).
pub fn Poly::total_degree(self : Poly) -> Int32 {
  let mut d = -1
  for i in 0..<self.num_terms() {
    let td = self.mono_at(i).total_degree()
    if td > d {
      d = td
    }
  }
  d
}

///|
pub fn Poly::is_homogeneous(self : Poly) -> Bool {
  if self.is_zero() {
    return true
  }
  let d = self.mono_at(0).total_degree()
  for i in 1..<self.num_terms() {
    if self.mono_at(i).total_degree() != d {
      return false
    }
  }
  true
}

///|
/// The degree-d homogeneous component of a polynomial.
pub fn Poly::homogeneous_component(self : Poly, d : Int32) -> Poly {
  let ts : Array[Term] = []
  for i in 0..<self.num_terms() {
    let m = self.mono_at(i)
    if m.total_degree() == d {
      ts.push(Term::new(self.coeff_at(i), m))
    }
  }
  Poly::from_terms(self.num_vars(), ts)
}

///|
/// Does this ideal come with a homogeneous presentation? Both the given
/// generators and the computed Groebner basis are checked; the Hilbert
/// machinery relies on degree-homogeneous reduction.
pub fn Ideal::is_homogeneous(self : Ideal) -> Bool {
  for g in self.gens() {
    if !g.is_homogeneous() {
      return false
    }
  }
  for g in self.groebner() {
    if !g.is_homogeneous() {
      return false
    }
  }
  true
}

///|
/// Minimal monomial generating set of the initial ideal in(I): leading
/// monomials of the reduced Groebner basis with divisibility-redundant
/// ones removed.
pub fn Ideal::initial_monomials(self : Ideal) -> Array[Mono] {
  let all : Array[Mono] = []
  for g in self.groebner() {
    all.push(g.lead_mono())
  }
  let keep : Array[Mono] = []
  for i in 0..<all.length() {
    let mut dominated = false
    for j in 0..<all.length() {
      if i != j && all[j].divides(all[i]) && (!all[j].equal_to(all[i]) || j < i) {
        dominated = true
        break
      }
    }
    if !dominated {
      keep.push(all[i])
    }
  }
  keep
}

///|
fn gen_monos_rec(
  pos : Int32,
  remaining : Int32,
  current : Array[Int32],
  out : Array[Mono],
) -> Unit {
  if pos == current.length() - 1 {
    current[pos] = remaining
    out.push(Mono::from_array(current))
    current[pos] = 0
    return
  }
  for e in 0..<(remaining + 1) {
    current[pos] = e
    gen_monos_rec(pos + 1, remaining - e, current, out)
  }
  current[pos] = 0
}

///|
/// All monomials of exact total degree d in n variables.
pub fn monomials_of_degree(nvars : Int32, d : Int32) -> Array[Mono] {
  if d < 0 {
    return []
  }
  if nvars == 0 {
    if d == 0 {
      return [Mono::one(0)]
    } else {
      return []
    }
  }
  let current : Array[Int32] = []
  for _ in 0..<nvars {
    current.push(0)
  }
  let out : Array[Mono] = []
  gen_monos_rec(0, d, current, out)
  out
}

///|
/// The Hilbert function HF_{S/I}(d) = dim_{F_7} (S/I)_d, by direct
/// enumeration of standard monomials of degree d. None if I is not
/// homogeneous.
pub fn Ideal::hilbert_function(self : Ideal, d : Int32) -> Int32? {
  if !self.is_homogeneous() {
    return None
  }
  if d < 0 {
    return Some(0)
  }
  let lms = self.initial_monomials()
  let mut count = 0
  for m in monomials_of_degree(self.num_vars(), d) {
    let mut inside = false
    for lm in lms {
      if lm.divides(m) {
        inside = true
        break
      }
    }
    if !inside {
      count = count + 1
    }
  }
  Some(count)
}

///|
/// Hilbert function values for degrees 0..=max_degree.
pub fn Ideal::hilbert_function_values(
  self : Ideal,
  max_degree : Int32,
) -> Array[Int32]? {
  let vals : Array[Int32] = []
  for d in 0..<(max_degree + 1) {
    match self.hilbert_function(d) {
      Some(v) => vals.push(v)
      None => return None
    }
  }
  Some(vals)
}

///|
const HILBERT_SUBSET_LIMIT : Int32 = 16

///|
/// Degrees of lcm(S) with signs, over all subsets S of the initial
/// monomials: the common core of the Hilbert series numerator and the
/// Hilbert polynomial. Aborts above the subset limit rather than
/// silently truncating the inclusion-exclusion.
fn hilbert_subset_data(ideal : Ideal) -> Array[(Int32, Int32)] {
  let lms = ideal.initial_monomials()
  let m = lms.length()
  if m > HILBERT_SUBSET_LIMIT {
    abort(
      "hilbert: initial ideal has too many minimal generators for " +
      "inclusion-exclusion (limit \{HILBERT_SUBSET_LIMIT}, got \{m})",
    )
  }
  let out : Array[(Int32, Int32)] = []
  for mask in 0..<(1 << m) {
    let mut lcm = Mono::one(ideal.num_vars())
    let mut bits = 0
    for i in 0..<m {
      if (mask >> i) % 2 == 1 {
        lcm = lcm.lcm(lms[i])
        bits = bits + 1
      }
    }
    out.push((if bits % 2 == 0 { 1 } else { -1 }, lcm.total_degree()))
  }
  out
}

///|
/// Numerator K(t) of the Hilbert series HS_{S/I}(t) = K(t) / (1-t)^n,
/// returned as integer coefficients in increasing degree. None if I is
/// not homogeneous.
pub fn Ideal::hilbert_series_numerator(self : Ideal) -> Array[Int32]? {
  if !self.is_homogeneous() {
    return None
  }
  if self.num_vars() == 0 {
    // S = F_7: HF = [dim quotient, 0, 0, ...]; K(t) = dim as constant
    // with the (1-t)^0 denominator convention only when quotient != 0
    // in degree 0; the series itself is the polynomial [HF(0)].
  }
  let data = hilbert_subset_data(self)
  let mut max_deg = 0
  for (_, e) in data {
    if e > max_deg {
      max_deg = e
    }
  }
  let coeffs : Array[Int32] = []
  for _ in 0..<(max_deg + 1) {
    coeffs.push(0)
  }
  for (sign, e) in data {
    coeffs[e] = coeffs[e] + sign
  }
  Some(coeffs)
}

///|
/// HF(d) recomputed from the Hilbert series numerator:
/// HF(d) = sum_e K_e * C(d - e + n - 1, n - 1). Independent route used by
/// tests to cross-check monomial enumeration.
pub fn hilbert_value_from_series(
  numerator : Array[Int32],
  nvars : Int32,
  d : Int32,
) -> Int32 {
  if nvars == 0 {
    if d == 0 && numerator.length() > 0 {
      return numerator[0]
    }
    return 0
  }
  let mut acc = 0
  for e in 0..<numerator.length() {
    acc = acc + numerator[e] * binom_int(d - e + nvars - 1, nvars - 1)
  }
  acc
}

///|
/// The polynomial C(t - e + n - 1, n - 1) in Q[t] (for n >= 1):
/// (1/(n-1)!) * prod_{j=1}^{n-1} (t - e + j).
fn binom_poly(e : Int32, n : Int32) -> RatPoly {
  let mut p = RatPoly::constant(Rat::one())
  for j in 1..<n {
    p = p.mul(RatPoly::linear(Rat::from_int(j - e)))
  }
  p.scale(Rat::new(1, factorial_int(n - 1)))
}

///|
/// The Hilbert polynomial P_I in Q[t]: sum_S (-1)^|S| C(t - deg lcm(S)
/// + n - 1, n - 1) over subsets of the initial monomials. Equals HF(d)
/// for all d >= max_S deg lcm(S) by the inclusion-exclusion identity.
/// None if I is not homogeneous.
pub fn Ideal::hilbert_polynomial(self : Ideal) -> RatPoly? {
  if !self.is_homogeneous() {
    return None
  }
  let n = self.num_vars()
  if n == 0 {
    return Some(RatPoly::zero())
  }
  let mut p = RatPoly::zero()
  for (sign, e) in hilbert_subset_data(self) {
    let term = binom_poly(e, n).scale(Rat::from_int(sign))
    p = p.add(term)
  }
  Some(p)
}

///|
/// Degree of the Hilbert polynomial = dimension of Proj(S/I) (or -1 when
/// the Hilbert polynomial is zero: empty projective scheme). None when
/// I is not homogeneous.
pub fn Ideal::projective_dimension_via_hilbert(self : Ideal) -> Int32? {
  match self.hilbert_polynomial() {
    Some(p) => Some(p.degree())
    None => None
  }
}

///|
/// The degree of Proj(S/I): if P has degree r and leading coefficient c,
/// deg = c * r!. Counts with scheme multiplicity (a double line has
/// degree 2). None for the empty projective scheme (P = 0).
pub fn Ideal::projective_degree(self : Ideal) -> Int32? {
  match self.hilbert_polynomial() {
    None => None
    Some(p) =>
      if p.is_zero() {
        None
      } else {
        Some(
          (p.leading_coefficient() * Rat::from_int(factorial_int(p.degree()))).to_int_exact(),
        )
      }
  }
}

///|
/// Arithmetic genus p_a = (-1)^r (P(0) - 1), r = dim Proj(S/I)
/// (from chi(O_X) = P(0) and p_a = (-1)^r (chi - 1)). For a smooth plane
/// curve of degree d this gives (d-1)(d-2)/2, as it should; for
/// zero-dimensional Proj of length L it gives L - 1.
pub fn Ideal::arithmetic_genus(self : Ideal) -> Int32? {
  match self.hilbert_polynomial() {
    None => None
    Some(p) =>
      if p.is_zero() {
        None
      } else {
        let r = p.degree()
        let chi_minus1 = p.eval_int_exact(0) - 1
        Some(if r % 2 == 0 { chi_minus1 } else { -chi_minus1 })
      }
  }
}

///|
/// The regularity bound coming from this construction: HF(d) = P(d) is
/// guaranteed for d >= max_S deg lcm(S). (The true Castelnuovo-Mumford
/// regularity can be smaller; this bound is what *this* proof delivers,
/// and it is returned so callers can verify agreement beyond it.)
pub fn Ideal::hilbert_agreement_bound(self : Ideal) -> Int32? {
  if !self.is_homogeneous() {
    return None
  }
  let mut bound = 0
  for (_, e) in hilbert_subset_data(self) {
    if e > bound {
      bound = e
    }
  }
  Some(bound)
}
