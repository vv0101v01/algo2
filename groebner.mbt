// =============================================================================
// groebner.mbt -- Buchberger's algorithm, ideals in F_p[x_1..x_n], ideal
// operations (sum, product, intersection, saturation), Krull dimension and
// the monomial staircase (finite vector-space dimension of quotients).
//
// Termination is Dickson's lemma / Hilbert's basis theorem; correctness is
// Buchberger's criterion (all S-polynomials reduce to zero). A hard step
// limit converts "theoretically terminates" into an explicit resource
// contract: exceeding it aborts loudly instead of returning a wrong basis.
// =============================================================================

///|
const GROEBNER_PAIR_LIMIT : Int32 = 20000

///|
/// Buchberger's algorithm. Input: any generators. Output: a Groebner basis
/// of the same ideal (not necessarily reduced).
pub fn groebner_basis(generators : Array[Poly]) -> Array[Poly] {
  let basis : Array[Poly] = []
  for g in generators {
    if !g.is_zero() {
      basis.push(g)
    }
  }
  // Queue of critical pairs (indices into `basis`).
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<basis.length() {
    for j in (i + 1)..<basis.length() {
      pairs.push((i, j))
    }
  }
  let mut head = 0
  let mut processed = 0
  while head < pairs.length() {
    processed = processed + 1
    if processed > GROEBNER_PAIR_LIMIT {
      abort(
        "groebner_basis: critical-pair limit exceeded; refusing to return " +
        "a possibly non-Groebner basis",
      )
    }
    let (i, j) = pairs[head]
    head = head + 1
    let s = spoly(basis[i], basis[j]).reduce_by(basis)
    if !s.is_zero() {
      let new_index = basis.length()
      basis.push(s)
      for k in 0..<new_index {
        pairs.push((k, new_index))
      }
    }
  }
  basis
}

///|
/// The unique reduced Groebner basis: monic, minimal (no leading monomial
/// divides another), and fully inter-reduced tails. Uniqueness is what
/// makes ideal *equality* decidable by comparing two lists.
pub fn reduced_groebner(generators : Array[Poly]) -> Array[Poly] {
  let g = groebner_basis(generators)
  // Minimal: keep f only if no *other* basis element's LM divides LM(f).
  // (Checking only earlier elements is a bug: Buchberger appends new,
  // often smaller, leading monomials later -- e.g. from {xy-1, y^2-1} it
  // appends x-y, whose LM x divides xy, so xy-1 must be discarded.)
  // Equal leading monomials: keep only the first occurrence.
  let minimal : Array[Poly] = []
  for i in 0..<g.length() {
    let f = g[i]
    let mut dominated = false
    for j in 0..<g.length() {
      if j == i {
        continue
      }
      let h = g[j]
      if h.lead_mono().divides(f.lead_mono()) &&
        (!h.lead_mono().equal_to(f.lead_mono()) || j < i) {
        dominated = true
        break
      }
    }
    if !dominated {
      minimal.push(f)
    }
  }
  // Inter-reduce tails and normalize leading coefficients to 1.
  let reduced : Array[Poly] = []
  for i in 0..<minimal.length() {
    let others : Array[Poly] = []
    for j in 0..<minimal.length() {
      if j != i {
        others.push(minimal[j])
      }
    }
    let r = minimal[i].reduce_by(others)
    reduced.push(r.scale(r.lead_coeff().inv()))
  }
  // Canonical ordering: leading monomials decreasing (lex).
  for i in 1..<reduced.length() {
    let key = reduced[i]
    let mut j = i - 1
    while j >= 0 && reduced[j].lead_mono().compare(key.lead_mono()) < 0 {
      reduced[j + 1] = reduced[j]
      j = j - 1
    }
    reduced[j + 1] = key
  }
  reduced
}

///|
pub fn poly_list_equal(a : Array[Poly], b : Array[Poly]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !a[i].equal_to(b[i]) {
      return false
    }
  }
  true
}

///|
pub fn poly_list_display(a : Array[Poly]) -> String {
  let sb = StringBuilder()
  sb.write_string("[")
  for i in 0..<a.length() {
    if i > 0 {
      sb.write_string(", ")
    }
    sb.write_string(a[i].display())
  }
  sb.write_string("]")
  sb.to_string()
}

// -----------------------------------------------------------------------------
// Ideals. An Ideal stores the user's generators and the reduced Groebner
// basis computed once at construction; every decision procedure below is
// then a normal-form computation against that basis.
// -----------------------------------------------------------------------------

///|
pub struct Ideal {
  nvars : Int32
  generators : Array[Poly]
  gb : Array[Poly]
}

///|
pub fn Ideal::new(nvars : Int32, generators : Array[Poly]) -> Ideal {
  for g in generators {
    if g.num_vars() != nvars {
      abort("Ideal::new: generator variable count mismatch")
    }
  }
  { nvars, generators, gb: reduced_groebner(generators), }
}

///|
pub fn Ideal::zero_ideal(nvars : Int32) -> Ideal {
  Ideal::new(nvars, [])
}

///|
pub fn Ideal::unit_ideal(nvars : Int32) -> Ideal {
  Ideal::new(nvars, [Poly::one_poly(nvars)])
}

///|
pub fn Ideal::num_vars(self : Ideal) -> Int32 {
  self.nvars
}

///|
pub fn Ideal::groebner(self : Ideal) -> Array[Poly] {
  self.gb
}

///|
pub fn Ideal::gens(self : Ideal) -> Array[Poly] {
  self.generators
}

///|
/// Ideal membership, decided by the normal form: f in I iff NF(f) = 0.
/// This is *the* algorithmic content of Groebner bases (ordinary division
/// by non-Groebner generators can leave a nonzero remainder for members).
pub fn Ideal::contains(self : Ideal, f : Poly) -> Bool {
  if f.num_vars() != self.nvars {
    abort("Ideal::contains: variable count mismatch")
  }
  f.reduce_by(self.gb).is_zero()
}

///|
/// Normal form of f modulo this ideal (canonical coset representative).
pub fn Ideal::normal_form(self : Ideal, f : Poly) -> Poly {
  f.reduce_by(self.gb)
}

///|
pub fn Ideal::equal_to(self : Ideal, other : Ideal) -> Bool {
  self.nvars == other.nvars && poly_list_equal(self.gb, other.gb)
}

///|
pub fn Ideal::is_zero_ideal(self : Ideal) -> Bool {
  self.gb.length() == 0
}

///|
pub fn Ideal::is_unit_ideal(self : Ideal) -> Bool {
  self.gb.length() == 1 && self.gb[0].equal_to(Poly::one_poly(self.nvars))
}

///|
/// Sum of ideals I + J: generated by the union of generators.
/// Geometrically V(I+J) = V(I) ∩ V(J).
pub fn Ideal::sum(self : Ideal, other : Ideal) -> Ideal {
  if self.nvars != other.nvars {
    abort("Ideal::sum: variable count mismatch")
  }
  let gens : Array[Poly] = []
  for g in self.generators {
    gens.push(g)
  }
  for g in other.generators {
    gens.push(g)
  }
  Ideal::new(self.nvars, gens)
}

///|
/// Product of ideals IJ: generated by pairwise products.
/// Geometrically V(IJ) = V(I) ∪ V(J) = V(I ∩ J).
pub fn Ideal::product(self : Ideal, other : Ideal) -> Ideal {
  let gens : Array[Poly] = []
  for a in self.generators {
    for b in other.generators {
      gens.push(a.mul(b))
    }
  }
  Ideal::new(self.nvars, gens)
}

///|
/// Embed F_p[x_1..x_n] into F_p[t, x_1..x_n] (t is the new variable 0,
/// hence the largest in lex order, i.e. an elimination order for t).
fn poly_embed_t(f : Poly) -> Poly {
  let mapping : Array[Int32] = []
  for i in 0..<f.num_vars() {
    mapping.push(i + 1)
  }
  f.relabel(mapping, f.num_vars() + 1)
}

///|
/// Inverse of poly_embed_t for polynomials not mentioning t. Aborts if t
/// occurs, so misuse cannot silently drop a variable.
fn poly_drop_t(f : Poly) -> Poly {
  let ts : Array[Term] = []
  for i in 0..<f.num_terms() {
    let m = f.mono_at(i)
    if m.exp_at(0) != 0 {
      abort("poly_drop_t: polynomial still mentions the tag variable")
    }
    let e : Array[Int32] = []
    for k in 1..<m.num_vars() {
      e.push(m.exp_at(k))
    }
    ts.push(Term::new(f.coeff_at(i), Mono::from_array(e)))
  }
  Poly::from_terms(f.num_vars() - 1, ts)
}

///|
/// Intersection of ideals via the tag-variable trick:
///   I ∩ J = ( t·I + (1−t)·J ) ∩ F_p[x],
/// where the last elimination is read off a lex Groebner basis with t
/// largest. Geometrically V(I∩J) = V(I) ∪ V(J).
pub fn Ideal::intersect(self : Ideal, other : Ideal) -> Ideal {
  if self.nvars != other.nvars {
    abort("Ideal::intersect: variable count mismatch")
  }
  let n1 = self.nvars + 1
  let t = Poly::variable(n1, 0)
  let one_minus_t = Poly::one_poly(n1).sub(t)
  let gens : Array[Poly] = []
  for g in self.generators {
    gens.push(t.mul(poly_embed_t(g)))
  }
  for g in other.generators {
    gens.push(one_minus_t.mul(poly_embed_t(g)))
  }
  let big_gb = reduced_groebner(gens)
  let keep : Array[Poly] = []
  for g in big_gb {
    let mut mentions_t = false
    for i in 0..<g.num_terms() {
      if g.mono_at(i).exp_at(0) != 0 {
        mentions_t = true
        break
      }
    }
    if !mentions_t {
      keep.push(poly_drop_t(g))
    }
  }
  Ideal::new(self.nvars, keep)
}

///|
/// Saturation (I : f^∞) = { g | f^k·g ∈ I for some k ≥ 0 }, computed by the
/// Rabinowitsch trick: (I + (1 − t·f)) ∩ F_p[x] in F_p[t, x].
/// This is the algebraic operation behind restriction to the principal
/// open set D(f) = { a | f(a) ≠ 0 }.
pub fn Ideal::saturate(self : Ideal, f : Poly) -> Ideal {
  let n1 = self.nvars + 1
  let t = Poly::variable(n1, 0)
  let gens : Array[Poly] = []
  for g in self.generators {
    gens.push(poly_embed_t(g))
  }
  gens.push(Poly::one_poly(n1).sub(t.mul(poly_embed_t(f))))
  let big_gb = reduced_groebner(gens)
  let keep : Array[Poly] = []
  for g in big_gb {
    let mut mentions_t = false
    for i in 0..<g.num_terms() {
      if g.mono_at(i).exp_at(0) != 0 {
        mentions_t = true
        break
      }
    }
    if !mentions_t {
      keep.push(poly_drop_t(g))
    }
  }
  Ideal::new(self.nvars, keep)
}

///|
/// Radical membership: f ∈ √I  iff  (I : f^∞) = (1).
/// (1 ∈ (I:f^∞) iff f^k ∈ I for some k, by definition of saturation.)
pub fn Ideal::in_radical(self : Ideal, f : Poly) -> Bool {
  self.saturate(f).is_unit_ideal()
}

///|
/// The monomial staircase: monomials not divisible by any leading monomial
/// of the Groebner basis. When finite, they are a F_p-basis of the quotient
/// F_p[x]/I. Returns None iff the quotient is infinite-dimensional, which
/// happens iff some variable admits no pure power as a leading monomial.
pub fn Ideal::standard_monomials(self : Ideal) -> Array[Mono]? {
  // Unit ideal: LM(1) = 1 divides every monomial, staircase is empty and
  // the quotient is the zero ring (dimension 0), not infinite-dimensional.
  if self.is_unit_ideal() {
    return Some([])
  }
  let n = self.nvars
  // Bound b_i = smallest exponent with x_i^{b_i} a leading monomial.
  let bounds : Array[Int32] = []
  for i in 0..<n {
    let mut best = -1
    for g in self.gb {
      let lm = g.lead_mono()
      let mut pure = lm.exp_at(i) > 0
      for j in 0..<n {
        if j != i && lm.exp_at(j) != 0 {
          pure = false
          break
        }
      }
      if pure && (best < 0 || lm.exp_at(i) < best) {
        best = lm.exp_at(i)
      }
    }
    if best < 0 {
      return None
    }
    bounds.push(best)
  }
  // Enumerate the box [0,b_0) x ... x [0,b_{n-1}) by a mixed-radix counter.
  let result : Array[Mono] = []
  let mut total = 1
  for i in 0..<n {
    total = total * bounds[i]
  }
  for code in 0..<total {
    let e : Array[Int32] = []
    let mut c = code
    for i in 0..<n {
      e.push(c % bounds[i])
      c = c / bounds[i]
    }
    let m = Mono::from_array(e)
    let mut divisible = false
    for g in self.gb {
      if g.lead_mono().divides(m) {
        divisible = true
        break
      }
    }
    if !divisible {
      result.push(m)
    }
  }
  // Sort decreasing (lex) for determinism.
  for i in 1..<result.length() {
    let key = result[i]
    let mut j = i - 1
    while j >= 0 && result[j].compare(key) < 0 {
      result[j + 1] = result[j]
      j = j - 1
    }
    result[j + 1] = key
  }
  Some(result)
}

///|
/// dim_{F_p} F_p[x]/I when finite; None when infinite-dimensional.
pub fn Ideal::finite_dimension(self : Ideal) -> Int32? {
  match self.standard_monomials() {
    Some(ms) => Some(ms.length())
    None => None
  }
}

///|
/// Krull dimension of F_p[x]/I, computed from the initial monomial ideal:
///   dim = max{ |U| : U ⊆ {x_1..x_n},  in(I) ∩ F_p[U] = {0} }
/// i.e. no leading monomial is supported entirely inside U. Passing to
/// in(I) preserves Krull dimension (flat Groebner degeneration), so the
/// problem becomes hypergraph independence, brute-forced over subsets
/// (n stays small in exact computation; n ≤ 6 is the intended range).
/// Returns -1 for the unit ideal (empty variety / zero ring).
pub fn Ideal::krull_dimension(self : Ideal) -> Int32 {
  if self.is_unit_ideal() {
    return -1
  }
  let n = self.nvars
  let lms : Array[Mono] = []
  for g in self.gb {
    lms.push(g.lead_mono())
  }
  let mut best = 0
  for mask in 0..<(1 << n) {
    // popcount + independence check for U = {i : bit i set}
    let mut size = 0
    for i in 0..<n {
      if (mask >> i) % 2 == 1 {
        size = size + 1
      }
    }
    if size <= best {
      continue
    }
    let mut independent = true
    for lm in lms {
      let mut supported_in_u = true
      for i in 0..<n {
        if lm.exp_at(i) > 0 && (mask >> i) % 2 == 0 {
          supported_in_u = false
          break
        }
      }
      if supported_in_u {
        independent = false
        break
      }
    }
    if independent {
      best = size
    }
  }
  best
}
