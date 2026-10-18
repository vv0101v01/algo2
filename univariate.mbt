// =============================================================================
// univariate.mbt -- dense univariate arithmetic over F_7: divmod, gcd,
// factorization into irreducibles, and minimal polynomials of elements of
// finite quotient algebras. These are the engine of zero-dimensional
// primary decomposition (splitting by coprime factors of a minimal
// polynomial) and of univariate primary decomposition.
//
// Factorization is by increasing-degree trial division over monic
// candidates -- complete (not heuristic) over a field with 7 elements,
// with an explicit candidate bound that aborts instead of running
// forever on absurd degrees:
//   a divisor found at the smallest possible degree is irreducible,
//   because a composite would contribute a smaller-degree divisor.
// =============================================================================

///|
type UniDense = Array[Fp] // coefficients low -> high, trimmed (no leading 0)

///|
fn uni_trim(a : UniDense) -> Unit {
  while a.length() > 0 && a[a.length() - 1].is_zero() {
    let _ = a.pop()
  }
}

///|
fn uni_copy(a : UniDense) -> UniDense {
  vec_copy(a)
}

///|
fn uni_degree(a : UniDense) -> Int32 {
  a.length() - 1
}

///|
fn uni_from_poly(f : Poly) -> UniDense {
  if f.num_vars() != 1 {
    abort("uni_from_poly: expected a univariate polynomial")
  }
  let deg = f.total_degree()
  let a : UniDense = []
  for d in 0..<(deg + 1) {
    a.push(f.coeff_of(Mono::from_array([d])))
  }
  uni_trim(a)
  a
}

///|
fn uni_to_poly(a : UniDense) -> Poly {
  let ts : Array[Term] = []
  for d in 0..<a.length() {
    if !a[d].is_zero() {
      ts.push(Term::new(a[d], Mono::from_array([d])))
    }
  }
  Poly::from_terms(1, ts)
}

///|
fn uni_divmod(a_in : UniDense, b : UniDense) -> (UniDense, UniDense) {
  if uni_degree(b) < 0 {
    abort("uni_divmod: division by zero")
  }
  let a = uni_copy(a_in)
  uni_trim(a)
  let db = uni_degree(b)
  let q : UniDense = []
  if uni_degree(a) >= db {
    for _ in 0..<(uni_degree(a) - db + 1) {
      q.push(Fp::zero())
    }
    let inv_lc = b[db].inv()
    while uni_degree(a) >= db && uni_degree(a) >= 0 {
      let da = uni_degree(a)
      let c = a[da] * inv_lc
      let shift = da - db
      q[shift] = c
      for j in 0..<b.length() {
        a[shift + j] = a[shift + j] - c * b[j]
      }
      uni_trim(a)
    }
  }
  uni_trim(q)
  (q, a)
}

///|
fn uni_mod(a : UniDense, b : UniDense) -> UniDense {
  let (_, r) = uni_divmod(a, b)
  r
}

///|
/// Monic gcd in F_7[x] (Euclidean algorithm). Public: it decides
/// coprimality, which the CRT/primary splitting steps rely on.
pub fn univariate_gcd(f : Poly, g : Poly) -> Poly {
  let mut a = uni_from_poly(f)
  let mut b = uni_from_poly(g)
  while uni_degree(b) >= 0 {
    let r = uni_mod(a, b)
    a = b
    b = r
  }
  if uni_degree(a) >= 0 {
    let inv = a[a.length() - 1].inv()
    for i in 0..<a.length() {
      a[i] = a[i] * inv
    }
  }
  uni_to_poly(a)
}

///|
pub struct UniFactor {
  factor : Poly
  exponent : Int32
}

///|
pub fn UniFactor::factor(self : UniFactor) -> Poly {
  self.factor
}

///|
pub fn UniFactor::exponent(self : UniFactor) -> Int32 {
  self.exponent
}

///|
const UNI_FACTOR_CANDIDATE_LIMIT : Int32 = 200000

///|
fn uni_pow7(d : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<d {
    r = r * PRIME
  }
  r
}

///|
fn uni_factor_rec(a : UniDense, out : Array[UniFactor]) -> Unit {
  let deg = uni_degree(a)
  if deg <= 0 {
    return
  }
  if deg == 1 {
    out.push({ factor: uni_to_poly(a), exponent: 1, })
    return
  }
  // Search for an irreducible divisor by increasing degree.
  let mut divisor : UniDense = []
  let mut found = false
  let mut d = 1
  while d * 2 <= deg && !found {
    let count = uni_pow7(d)
    if count > UNI_FACTOR_CANDIDATE_LIMIT {
      abort(
        "factor_univariate: candidate bound exceeded at degree \{d}; " +
        "refusing an incomplete factorization",
      )
    }
    let mut code = 0
    while code < count && !found {
      let cand : UniDense = []
      let mut c = code
      for _ in 0..<d {
        cand.push(Fp::new(c % PRIME))
        c = c / PRIME
      }
      cand.push(Fp::one()) // monic of degree d
      if uni_degree(uni_mod(a, cand)) < 0 {
        divisor = cand
        found = true
      }
      code = code + 1
    }
    d = d + 1
  }
  if !found {
    // No divisor of degree <= deg/2: a itself is irreducible.
    out.push({ factor: uni_to_poly(a), exponent: 1, })
    return
  }
  // Divide out the full power of this irreducible.
  let mut cur = a
  let mut e = 0
  while uni_degree(cur) >= uni_degree(divisor) &&
        uni_degree(uni_mod(cur, divisor)) < 0 {
    let (q, _) = uni_divmod(cur, divisor)
    cur = q
    e = e + 1
  }
  out.push({ factor: uni_to_poly(divisor), exponent: e, })
  uni_factor_rec(cur, out)
}

///|
/// Factorization of a nonzero f in F_7[x] into monic irreducibles with
/// multiplicities: f = lc(f) * prod factor^exponent (the scalar leading
/// coefficient is not part of the list, as documented).
pub fn factor_univariate(f : Poly) -> Array[UniFactor] {
  if f.num_vars() != 1 {
    abort("factor_univariate: expected a univariate polynomial")
  }
  if f.is_zero() {
    abort("factor_univariate: zero polynomial has no factorization")
  }
  let a = uni_from_poly(f)
  // Normalize to monic.
  let inv = a[a.length() - 1].inv()
  for i in 0..<a.length() {
    a[i] = a[i] * inv
  }
  let out : Array[UniFactor] = []
  uni_factor_rec(a, out)
  out
}

///|
pub fn is_irreducible_univariate(f : Poly) -> Bool {
  if f.num_vars() != 1 || f.total_degree() < 1 {
    return false
  }
  let fs = factor_univariate(f)
  fs.length() == 1 && fs[0].exponent == 1
}

///|
/// Squarefree kernel prod of distinct irreducible factors (the univariate
/// radical generator): sqrt((f)) = (radical_univariate(f)) in F_7[x].
pub fn radical_univariate(f : Poly) -> Poly {
  let mut acc = Poly::one_poly(1)
  for fc in factor_univariate(f) {
    acc = acc.mul(fc.factor)
  }
  acc
}

///|
/// Minimal polynomial of an element of a finite algebra given by a
/// QuotientModel (as a monic polynomial in one variable). Computed from
/// the first linear dependence among 1, a, a^2, ... over F_7.
pub fn minimal_polynomial_of_elem(
  model : QuotientModel,
  elem : FinElem,
) -> Poly {
  let alg = model.algebra()
  if alg.dim() == 0 {
    return Poly::one_poly(1)
  }
  let powers : Array[FinElem] = [alg.one_elem()]
  let basis_vecs : Array[Array[Fp]] = [alg.one_elem().coords()]
  let mut current = alg.one_elem()
  for d in 1..<(alg.dim() + 2) {
    current = alg.mul(current, elem)
    match coordinates_in_basis(current.coords(), basis_vecs) {
      Some(cs) => {
        // current = sum_j cs[j] * elem^j  =>  minpoly = t^d - sum cs[j] t^j,
        // provided the cs found is the unique one (previous powers are
        // independent by minimality of d) -- but coordinates_in_basis
        // also succeeds if d is not minimal with a possibly non-unique
        // answer; minimality is by construction of this loop.
        let ts : Array[Term] = []
        ts.push(Term::new(Fp::one(), Mono::from_array([d])))
        for j in 0..<cs.length() {
          if !cs[j].is_zero() {
            ts.push(Term::new(-cs[j], Mono::from_array([j])))
          }
        }
        return Poly::from_terms(1, ts)
      }
      None => {
        powers.push(current)
        basis_vecs.push(current.coords())
      }
    }
  }
  abort("minimal_polynomial_of_elem: no dependence found (impossible)")
}

///|
/// Minimal polynomial of the coset of h modulo a zero-dimensional ideal,
/// or None when the quotient is infinite-dimensional.
pub fn minimal_polynomial_mod(ideal : Ideal, h : Poly) -> Poly? {
  let ring = QuotientRing::new(ideal)
  match QuotientModel::new(ring, "minpoly-model") {
    None => None
    Some(model) =>
      Some(minimal_polynomial_of_elem(model, model.to_elem(ring.of_poly(h))))
  }
}
