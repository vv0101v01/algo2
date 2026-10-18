// =============================================================================
// localization.mbt -- localizations.
//
// (1) S^{-1}(R/I) for S = {1, f, f^2, ...} and an arbitrary quotient
//     R/I of a polynomial ring. Fractions a/f^k with the *correct* equality
//     for non-domains:
//        a/f^i = b/f^j   iff   f^j*a - f^i*b ∈ (I : f^∞),
//     decided with the saturation computed once by Rabinowitsch/Groebner.
//     (Cross-multiplication in R alone would be wrong when f is a zero
//     divisor mod I -- the saturation factor is exactly the existential
//     "exists u in S, u(a t - b s) = 0" in the textbook definition.)
//
// (2) The Rabinowitsch isomorphism S^{-1}(R/I) ≅ R[t]/(I, t f - 1) with
//     both directions implemented and tested as inverse homomorphisms.
//
// (3) The local ring of A^n at a point: fractions a/s with s(a) != 0
//     (S = complement of the maximal ideal m_a, *not* of principal type).
//     Invalid denominators are refused by an Option-returning constructor.
//
// (4) Extensions to finite algebras: a map R -> B extends over R_f iff
//     the image of f is a unit in B (universal property), decided by
//     FinAlg::try_inv; when it fails we return None rather than a fake map.
// =============================================================================

///|
pub struct LocalizedRing {
  ring : QuotientRing
  denom : Poly // the f whose powers form S (as a polynomial representative)
  saturation : Ideal // (I : f^∞)
}

///|
pub struct LocElem {
  num : Poly // representative of the numerator coset
  power : Int32 // denominator is f^power
}

///|
pub fn LocalizedRing::new(ring : QuotientRing, denom : Poly) -> LocalizedRing {
  if denom.num_vars() != ring.num_vars() {
    abort("LocalizedRing::new: variable count mismatch")
  }
  { ring, denom, saturation: ring.ideal().saturate(denom), }
}

///|
/// Localization of the polynomial ring itself (I = 0, a domain): here
/// (0 : f^∞) = (0) for f != 0 and fraction equality reduces to plain
/// cross-multiplication -- as a *corollary*, verified in tests, not an
/// assumption baked into a separate implementation.
pub fn LocalizedRing::of_polynomial_ring(denom : Poly) -> LocalizedRing {
  LocalizedRing::new(
    QuotientRing::new(Ideal::zero_ideal(denom.num_vars())),
    denom,
  )
}

///|
pub fn LocalizedRing::frac(
  self : LocalizedRing,
  num : Poly,
  power : Int32,
) -> LocElem {
  if power < 0 {
    abort("LocalizedRing::frac: negative denominator power")
  }
  if num.num_vars() != self.ring.num_vars() {
    abort("LocalizedRing::frac: variable count mismatch")
  }
  { num, power, }
}

///|
pub fn LocalizedRing::of_poly(self : LocalizedRing, f : Poly) -> LocElem {
  if f.num_vars() != self.ring.num_vars() {
    abort("LocalizedRing::of_poly: variable count mismatch")
  }
  { num: f, power: 0, }
}

///|
pub fn LocalizedRing::of_coset(self : LocalizedRing, c : Coset) -> LocElem {
  check_coset(self.ring, c)
  { num: c.repr_poly(), power: 0, }
}

///|
pub fn LocalizedRing::zero_elem(self : LocalizedRing) -> LocElem {
  { num: Poly::zero(self.ring.num_vars()), power: 0, }
}

///|
pub fn LocalizedRing::one_elem(self : LocalizedRing) -> LocElem {
  { num: Poly::one_poly(self.ring.num_vars()), power: 0, }
}

///|
/// 1/f, the element whose existence is the whole point of localizing.
pub fn LocalizedRing::inv_denom(self : LocalizedRing) -> LocElem {
  { num: Poly::one_poly(self.ring.num_vars()), power: 1, }
}

///|
pub fn LocalizedRing::equal_to(
  self : LocalizedRing,
  a : LocElem,
  b : LocElem,
) -> Bool {
  let lhs = a.num.mul(self.denom.pow(b.power))
  let rhs = b.num.mul(self.denom.pow(a.power))
  self.saturation.contains(lhs.sub(rhs))
}

///|
pub fn LocalizedRing::is_zero(self : LocalizedRing, a : LocElem) -> Bool {
  self.saturation.contains(a.num)
}

///|
pub fn LocalizedRing::add(
  self : LocalizedRing,
  a : LocElem,
  b : LocElem,
) -> LocElem {
  let k = a.power
  let l = b.power
  if k >= l {
    let num = a.num.add(b.num.mul(self.denom.pow(k - l)))
    { num, power: k, }
  } else {
    let num = a.num.mul(self.denom.pow(l - k)).add(b.num)
    { num, power: l, }
  }
}

///|
pub fn LocalizedRing::neg(_self : LocalizedRing, a : LocElem) -> LocElem {
  { num: a.num.negate(), power: a.power, }
}

///|
pub fn LocalizedRing::sub(
  self : LocalizedRing,
  a : LocElem,
  b : LocElem,
) -> LocElem {
  self.add(a, self.neg(b))
}

///|
pub fn LocalizedRing::mul(
  _self : LocalizedRing,
  a : LocElem,
  b : LocElem,
) -> LocElem {
  { num: a.num.mul(b.num), power: a.power + b.power, }
}

///|
pub fn LocalizedRing::pow(
  self : LocalizedRing,
  a : LocElem,
  e : Int32,
) -> LocElem {
  let mut r = self.one_elem()
  for _ in 0..<e {
    r = self.mul(r, a)
  }
  r
}

///|
pub fn LocElem::display(self : LocElem, denom : Poly) -> String {
  "(" + self.num.display() + ")/(" + denom.display() + ")^\{self.power}"
}

///|
/// The saturation itself: kernel of R/I -> S^{-1}(R/I) is
/// (I : f^∞)/I, exposed so tests can check `of_poly(g) = 0 iff g ∈ (I:f^∞)`.
pub fn LocalizedRing::saturation_ideal(self : LocalizedRing) -> Ideal {
  self.saturation
}

///|
/// Is the localized ring the zero ring? Exactly when (I : f^∞) = (1),
/// i.e. when f is nilpotent modulo I (some power of f already lies in I):
/// inverting a nilpotent kills the ring. Geometrically D(f) ∩ V(I) = ∅.
pub fn LocalizedRing::is_zero_ring(self : LocalizedRing) -> Bool {
  self.saturation.is_unit_ideal()
}

// -----------------------------------------------------------------------------
// Rabinowitsch trick as an isomorphism of rings.
// -----------------------------------------------------------------------------

///|
pub struct RabinowitschIso {
  loc : LocalizedRing
  quot : QuotientRing // R[t]/(I, t f - 1), t = variable n (last)
}

///|
pub fn RabinowitschIso::new(loc : LocalizedRing) -> RabinowitschIso {
  let n = loc.ring.num_vars()
  let gens : Array[Poly] = []
  for g in loc.ring.ideal().gens() {
    let mapping : Array[Int32] = []
    for i in 0..<n {
      mapping.push(i)
    }
    gens.push(g.relabel(mapping, n + 1))
  }
  let mapping_f : Array[Int32] = []
  for i in 0..<n {
    mapping_f.push(i)
  }
  let f_emb = loc.denom.relabel(mapping_f, n + 1)
  let t = Poly::variable(n + 1, n)
  gens.push(t.mul(f_emb).sub(Poly::one_poly(n + 1)))
  { loc, quot: QuotientRing::from_generators(n + 1, gens), }
}

///|
pub fn RabinowitschIso::quotient_ring(self : RabinowitschIso) -> QuotientRing {
  self.quot
}

///|
/// Forward map: a/f^k |-> a·t^k.
pub fn RabinowitschIso::forward(self : RabinowitschIso, a : LocElem) -> Coset {
  let n = self.loc.ring.num_vars()
  let mapping : Array[Int32] = []
  for i in 0..<n {
    mapping.push(i)
  }
  let num_emb = a.num.relabel(mapping, n + 1)
  let t = Poly::variable(n + 1, n)
  self.quot.of_poly(num_emb.mul(t.pow(a.power)))
}

///|
/// Evaluate an (n+1)-variable polynomial in the localized ring with
/// x_i |-> x_i/1 and t |-> 1/f. Used for the backward map.
pub fn eval_poly_in_localized(loc : LocalizedRing, expr : Poly) -> LocElem {
  let n = loc.ring.num_vars()
  let images : Array[LocElem] = []
  for i in 0..<n {
    images.push(loc.of_poly(Poly::variable(n, i)))
  }
  images.push(loc.inv_denom())
  let mut acc = loc.zero_elem()
  for i in 0..<expr.num_terms() {
    let mut term = loc.of_poly(Poly::constant(n, expr.coeff_at(i)))
    let m = expr.mono_at(i)
    for v in 0..<(n + 1) {
      term = loc.mul(term, loc.pow(images[v], m.exp_at(v)))
    }
    acc = loc.add(acc, term)
  }
  acc
}

///|
/// Backward map: a coset [g(x, t)] |-> g(x, 1/f) in the localized ring.
pub fn RabinowitschIso::backward(self : RabinowitschIso, c : Coset) -> LocElem {
  eval_poly_in_localized(self.loc, c.repr_poly())
}

// -----------------------------------------------------------------------------
// Local ring at a point (S = F_7[x] \ m_a).
// -----------------------------------------------------------------------------

///|
pub struct LocalRingAtPoint {
  pt : Pt
  nvars : Int32
}

///|
pub struct LocalFrac {
  num : Poly
  den : Poly
}

///|
pub fn LocalRingAtPoint::new(pt : Pt) -> LocalRingAtPoint {
  { pt, nvars: pt.dim(), }
}

///|
/// Build a fraction a/s, legal iff s(pt) != 0. Illegal denominators yield
/// None -- the caller cannot ignore the side condition, because the value
/// it wants does not exist until the Option is destructured.
pub fn LocalRingAtPoint::frac(
  self : LocalRingAtPoint,
  num : Poly,
  den : Poly,
) -> LocalFrac? {
  if den.eval(self.pt.coords_array()).is_zero() {
    None
  } else {
    Some({ num, den, })
  }
}

///|
pub fn LocalRingAtPoint::of_poly(
  self : LocalRingAtPoint,
  f : Poly,
) -> LocalFrac {
  { num: f, den: Poly::one_poly(self.nvars), }
}

///|
/// Equality in a localization of a *domain*: cross-multiplication in the
/// polynomial ring decides it (a/t = b/s iff a s = b t when R is a domain
/// and 0 notin S).
pub fn LocalRingAtPoint::equal_to(
  _self : LocalRingAtPoint,
  a : LocalFrac,
  b : LocalFrac,
) -> Bool {
  a.num.mul(b.den).equal_to(b.num.mul(a.den))
}

///|
pub fn LocalRingAtPoint::add(
  _self : LocalRingAtPoint,
  a : LocalFrac,
  b : LocalFrac,
) -> LocalFrac {
  { num: a.num.mul(b.den).add(b.num.mul(a.den)), den: a.den.mul(b.den), }
}

///|
pub fn LocalRingAtPoint::mul(
  _self : LocalRingAtPoint,
  a : LocalFrac,
  b : LocalFrac,
) -> LocalFrac {
  { num: a.num.mul(b.num), den: a.den.mul(b.den), }
}

///|
pub fn LocalRingAtPoint::neg(
  _self : LocalRingAtPoint,
  a : LocalFrac,
) -> LocalFrac {
  { num: a.num.negate(), den: a.den, }
}

///|
pub fn LocalRingAtPoint::sub(
  self : LocalRingAtPoint,
  a : LocalFrac,
  b : LocalFrac,
) -> LocalFrac {
  self.add(a, self.neg(b))
}

///|
/// Residue field map O_{A^n,a} -> F_7, a/s |-> a(a)/s(a). Well-defined
/// exactly because denominators are units at a.
pub fn LocalRingAtPoint::residue(self : LocalRingAtPoint, a : LocalFrac) -> Fp {
  let pt = self.pt.coords_array()
  a.num.eval(pt).div_(a.den.eval(pt))
}

///|
/// The unique maximal ideal m = { a/s | a(a) = 0 }: the non-units.
pub fn LocalRingAtPoint::in_maximal_ideal(
  self : LocalRingAtPoint,
  a : LocalFrac,
) -> Bool {
  a.num.eval(self.pt.coords_array()).is_zero()
}

///|
/// Units are exactly the fractions outside the maximal ideal; inversion
/// swaps numerator and denominator, legal precisely in that case.
pub fn LocalRingAtPoint::try_inv(
  self : LocalRingAtPoint,
  a : LocalFrac,
) -> LocalFrac? {
  self.frac(a.den, a.num)
}

///|
pub fn LocalRingAtPoint::is_unit(
  self : LocalRingAtPoint,
  a : LocalFrac,
) -> Bool {
  !self.in_maximal_ideal(a)
}

// -----------------------------------------------------------------------------
// Universal property, finite target version.
// -----------------------------------------------------------------------------

///|
/// Evaluate a polynomial in a finite algebra at given variable images:
/// the unique F_7-algebra hom F_7[x_1..x_n] -> B with x_i |-> images[i]
/// (universal property of polynomial rings).
pub fn eval_poly_in_finalg(
  alg : FinAlg,
  images : Array[FinElem],
  f : Poly,
) -> FinElem {
  let mut acc = alg.zero_elem()
  for i in 0..<f.num_terms() {
    let mut term = alg.scalar_elem(f.coeff_at(i))
    let m = f.mono_at(i)
    for v in 0..<f.num_vars() {
      term = alg.mul(term, alg.pow(images[v], m.exp_at(v)))
    }
    acc = alg.add(acc, term)
  }
  acc
}

///|
/// Extend a polynomial-ring map (variable images in B) over F_7[x]_g.
/// Possible iff the image of g is a unit in B -- iff-condition implemented
/// via exact unit test; returns None otherwise (no extension exists).
pub fn extend_over_principal_localization(
  loc : LocalizedRing,
  alg : FinAlg,
  images : Array[FinElem],
  a : LocElem,
) -> FinElem? {
  let g_img = eval_poly_in_finalg(alg, images, loc.denom)
  match alg.try_inv(g_img) {
    None => None
    Some(inv) =>
      Some(
        alg.mul(eval_poly_in_finalg(alg, images, a.num), alg.pow(inv, a.power)),
      )
  }
}
