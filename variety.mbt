// =============================================================================
// variety.mbt -- affine varieties over F_7 (as F_7-point sets with defining
// equations), coordinate rings, products, disjoint unions, polynomial
// morphisms and contravariant pullback.
//
// Two levels are kept strictly apart (collapsing them is a common fake):
//   * equation level: an ideal I in F_7[x] -- kernels, dimensions and
//     quotients F_7[x]/I live here, including non-reduced structure;
//   * point level: V_F7(I) = { a in F_7^n | f(a) = 0 for all f in I }.
// The bridge is the finite-field Nullstellenssatz
//   I(V_F7(I)) = sqrt( I + (x_1^7 - x_1, ..., x_n^7 - x_n) ),
// which the tests verify on examples *and* where the naive identity
// I(V(I)) = sqrt(I) fails (e.g. x^2+1 has no F_7-root: V empty, I(V)=(1),
// but (x^2+1) is its own radical, proper).
// =============================================================================

///|
pub struct Pt {
  coords : Array[Fp]
}

///|
pub fn Pt::new(coords : Array[Fp]) -> Pt {
  { coords: vec_copy(coords), }
}

///|
pub fn Pt::dim(self : Pt) -> Int32 {
  self.coords.length()
}

///|
pub fn Pt::coord(self : Pt, i : Int32) -> Fp {
  self.coords[i]
}

///|
pub fn Pt::coords_array(self : Pt) -> Array[Fp] {
  vec_copy(self.coords)
}

///|
pub fn Pt::equal_to(self : Pt, other : Pt) -> Bool {
  vec_eq(self.coords, other.coords)
}

///|
pub fn Pt::compare(self : Pt, other : Pt) -> Int32 {
  for i in 0..<self.coords.length() {
    if self.coords[i].to_int() > other.coords[i].to_int() {
      return 1
    }
    if self.coords[i].to_int() < other.coords[i].to_int() {
      return -1
    }
  }
  0
}

///|
pub fn Pt::display(self : Pt) -> String {
  "(" + vec_display(self.coords) + ")"
}

///|
fn sort_points(pts : Array[Pt]) -> Array[Pt] {
  let out : Array[Pt] = []
  for p in pts {
    out.push(p)
  }
  for i in 1..<out.length() {
    let key = out[i]
    let mut j = i - 1
    while j >= 0 && out[j].compare(key) > 0 {
      out[j + 1] = out[j]
      j = j - 1
    }
    out[j + 1] = key
  }
  // Deduplicate.
  let dedup : Array[Pt] = []
  for p in out {
    let mut seen = false
    for q in dedup {
      if p.equal_to(q) {
        seen = true
        break
      }
    }
    if !seen {
      dedup.push(p)
    }
  }
  dedup
}

///|
/// All 7^n points of A^n(F_7) in lexicographic order. Brute-force
/// enumeration is the decision procedure for point-level questions over a
/// finite field -- exponential in n, intended for small n (as documented).
pub fn all_points(nvars : Int32) -> Array[Pt] {
  let mut total = 1
  for _ in 0..<nvars {
    total = total * PRIME
  }
  let pts : Array[Pt] = []
  for code in 0..<total {
    let coords : Array[Fp] = []
    let mut divisor = 1
    for _ in 1..<nvars {
      divisor = divisor * PRIME
    }
    let mut rest = code
    for _ in 0..<nvars {
      coords.push(Fp::new(rest / divisor))
      rest = rest % divisor
      if divisor > 1 {
        divisor = divisor / PRIME
      }
    }
    pts.push(Pt::new(coords))
  }
  pts
}

///|
/// The maximal ideal m_a = (x_1 - a_1, ..., x_n - a_n) = ker(ev_a).
pub fn maximal_ideal_at(pt : Pt) -> Ideal {
  let n = pt.dim()
  let gens : Array[Poly] = []
  for i in 0..<n {
    gens.push(Poly::variable(n, i).sub(Poly::constant(n, pt.coord(i))))
  }
  Ideal::new(n, gens)
}

///|
/// Vanishing ideal of a finite point set: I(X) = intersection of m_a over
/// a in X, computed by iterated ideal intersection. I(empty) = (1).
pub fn vanishing_ideal_of_points(nvars : Int32, pts : Array[Pt]) -> Ideal {
  let sorted = sort_points(pts)
  if sorted.length() == 0 {
    return Ideal::unit_ideal(nvars)
  }
  let mut acc = maximal_ideal_at(sorted[0])
  for i in 1..<sorted.length() {
    acc = acc.intersect(maximal_ideal_at(sorted[i]))
  }
  acc
}

///|
/// Field equations (x_i^7 - x_i): cutting with them forces
/// algebraic-closure points to be exactly the F_7-points.
pub fn field_equations_ideal(nvars : Int32) -> Ideal {
  let gens : Array[Poly] = []
  for i in 0..<nvars {
    let xi = Poly::variable(nvars, i)
    gens.push(xi.pow(PRIME).sub(xi))
  }
  Ideal::new(nvars, gens)
}

// -----------------------------------------------------------------------------
// Varieties.
// -----------------------------------------------------------------------------

///|
pub struct Variety {
  nvars : Int32
  ideal : Ideal
  pts : Array[Pt]
}

///|
pub fn Variety::from_ideal(ideal : Ideal) -> Variety {
  let pts : Array[Pt] = []
  for pt in all_points(ideal.num_vars()) {
    let mut ok = true
    for g in ideal.gens() {
      if !g.eval(pt.coords).is_zero() {
        ok = false
        break
      }
    }
    if ok {
      pts.push(pt)
    }
  }
  { nvars: ideal.num_vars(), ideal, pts: sort_points(pts), }
}

///|
pub fn Variety::from_generators(nvars : Int32, gens : Array[Poly]) -> Variety {
  Variety::from_ideal(Ideal::new(nvars, gens))
}

///|
/// A finite point set *as* a variety: defining ideal = its vanishing ideal.
pub fn Variety::from_points(nvars : Int32, pts : Array[Pt]) -> Variety {
  let sorted = sort_points(pts)
  { nvars, ideal: vanishing_ideal_of_points(nvars, sorted), pts: sorted, }
}

///|
pub fn Variety::affine_space(nvars : Int32) -> Variety {
  Variety::from_ideal(Ideal::zero_ideal(nvars))
}

///|
pub fn Variety::empty(nvars : Int32) -> Variety {
  Variety::from_ideal(Ideal::unit_ideal(nvars))
}

///|
pub fn Variety::num_vars(self : Variety) -> Int32 {
  self.nvars
}

///|
pub fn Variety::ideal(self : Variety) -> Ideal {
  self.ideal
}

///|
pub fn Variety::points(self : Variety) -> Array[Pt] {
  self.pts
}

///|
pub fn Variety::num_points(self : Variety) -> Int32 {
  self.pts.length()
}

///|
pub fn Variety::point_index(self : Variety, pt : Pt) -> Int32? {
  for i in 0..<self.pts.length() {
    if self.pts[i].equal_to(pt) {
      return Some(i)
    }
  }
  None
}

///|
pub fn Variety::contains_point(self : Variety, pt : Pt) -> Bool {
  self.point_index(pt) is Some(_)
}

///|
/// Equality as point sets in the same ambient space.
pub fn Variety::same_point_set(self : Variety, other : Variety) -> Bool {
  if self.nvars != other.nvars || self.pts.length() != other.pts.length() {
    return false
  }
  for i in 0..<self.pts.length() {
    if !self.pts[i].equal_to(other.pts[i]) {
      return false
    }
  }
  true
}

///|
/// I(X) for the F_7-point set X of this variety. May strictly contain the
/// defining ideal (finite-field Nullstellenssatz); the tests exhibit this.
pub fn Variety::vanishing_ideal(self : Variety) -> Ideal {
  vanishing_ideal_of_points(self.nvars, self.pts)
}

///|
/// Set-theoretic union inside one ambient space: V(I) ∪ V(J) = V(I ∩ J).
pub fn Variety::union_with(self : Variety, other : Variety) -> Variety {
  Variety::from_ideal(self.ideal.intersect(other.ideal))
}

///|
/// Set-theoretic intersection: V(I) ∩ V(J) = V(I + J).
pub fn Variety::intersection_with(self : Variety, other : Variety) -> Variety {
  Variety::from_ideal(self.ideal.sum(other.ideal))
}

///|
/// The product variety X x Y ⊆ A^{n+m}: equations of X in the first block
/// of variables, of Y in the second. Points are cartesian products
/// automatically because the equation blocks are independent -- and the
/// tests also check the point list against a directly computed product.
pub fn Variety::product(self : Variety, other : Variety) -> Variety {
  let n = self.nvars
  let m = other.nvars
  let gens : Array[Poly] = []
  for g in self.ideal.gens() {
    let mapping : Array[Int32] = []
    for i in 0..<n {
      mapping.push(i)
    }
    gens.push(g.relabel(mapping, n + m))
  }
  for g in other.ideal.gens() {
    let mapping : Array[Int32] = []
    for i in 0..<m {
      mapping.push(n + i)
    }
    gens.push(g.relabel(mapping, n + m))
  }
  Variety::from_ideal(Ideal::new(n + m, gens))
}

///|
/// Disjoint union X ⊔ Y as an affine variety, via the standard tagged
/// embedding into A^{n+m+1}:
///   X -> (x, 0, 0),  Y -> (0, y, 1).
/// The defining ideal is then *computed* as the vanishing ideal of the
/// tagged point set (intersection of maximal ideals), so the result is a
/// bona fide closed subset with explicit equations, not just a list.
pub fn Variety::disjoint_union(self : Variety, other : Variety) -> Variety {
  let n = self.nvars
  let m = other.nvars
  let pts : Array[Pt] = []
  for p in self.pts {
    let coords : Array[Fp] = []
    for c in p.coords {
      coords.push(c)
    }
    for _ in 0..<m {
      coords.push(Fp::zero())
    }
    coords.push(Fp::zero())
    pts.push(Pt::new(coords))
  }
  let _ = n
  for p in other.pts {
    let coords : Array[Fp] = []
    for _ in 0..<n {
      coords.push(Fp::zero())
    }
    for c in p.coords {
      coords.push(c)
    }
    coords.push(Fp::one())
    pts.push(Pt::new(coords))
  }
  Variety::from_points(n + m + 1, pts)
}

///|
/// Points of the principal open subset D(f) ∩ X = { a in X | f(a) != 0 }.
pub fn Variety::principal_open_points(self : Variety, f : Poly) -> Array[Pt] {
  let pts : Array[Pt] = []
  for p in self.pts {
    if !f.eval(p.coords).is_zero() {
      pts.push(p)
    }
  }
  pts
}

///|
/// D(f) ∩ X realized as a *closed* subset of A^{n+1} (Rabinowitsch):
/// add a variable t and the equation t·f = 1. Projection to A^n is a
/// bijection onto D(f) ∩ X with t-coordinate 1/f(a) -- this is the geometry
/// behind k[X]_f ≅ k[x,t]/(I, tf−1).
pub fn Variety::principal_open_as_variety(self : Variety, f : Poly) -> Variety {
  let n = self.nvars
  let gens : Array[Poly] = []
  for g in self.ideal.gens() {
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
  let f_emb = f.relabel(mapping_f, n + 1)
  let t = Poly::variable(n + 1, n)
  gens.push(t.mul(f_emb).sub(Poly::one_poly(n + 1)))
  Variety::from_ideal(Ideal::new(n + 1, gens))
}

// -----------------------------------------------------------------------------
// Coordinate rings of finite varieties and interpolation.
// -----------------------------------------------------------------------------

///|
/// The indicator polynomial of a point a ∈ A^n(F_7):
///   delta_a(x) = prod_i ( 1 − (x_i − a_i)^(p−1) ).
/// By Fermat, delta_a(a) = 1 and delta_a(b) = 0 for every other F_7-point b.
/// These are the primitive idempotents behind k[X] ≅ prod_{a∈X} F_7 (CRT).
pub fn delta_poly(pt : Pt) -> Poly {
  let n = pt.dim()
  let mut acc = Poly::one_poly(n)
  for i in 0..<n {
    let factor = Poly::variable(n, i).sub(Poly::constant(n, pt.coord(i)))
    let term = Poly::one_poly(n).sub(factor.pow(PRIME - 1))
    acc = acc.mul(term)
  }
  acc
}

///|
/// Interpolation: the unique function-values-realizing polynomial
/// sum_a values[a] delta_a. Surjectivity of evaluation
/// F_7[x] -> Func(X, F_7) is exactly the existence of this polynomial.
pub fn interpolate(pts : Array[Pt], values : Array[Fp]) -> Poly {
  if pts.length() != values.length() {
    abort("interpolate: points/values length mismatch")
  }
  if pts.length() == 0 {
    abort("interpolate: empty point set has no ambient dimension here")
  }
  let n = pts[0].dim()
  let mut acc = Poly::zero(n)
  for i in 0..<pts.length() {
    acc = acc.add(delta_poly(pts[i]).scale(values[i]))
  }
  acc
}

///|
pub struct CoordRing {
  pts : Array[Pt]
  nvars : Int32
  alg : FinAlg
}

///|
/// k[X] = F_7[x]/I(X) realized as functions on the finite point set:
/// an element is its table of values. `of_poly` is evaluation; its kernel
/// is I(X) by construction, and interpolation (above) proves surjectivity
/// onto all tables, i.e. the first isomorphism theorem identification.
pub fn Variety::coordinate_ring(self : Variety) -> CoordRing {
  {
    pts: self.pts,
    nvars: self.nvars,
    alg: FinAlg::function_algebra(
      "k[X] (|X|=\{self.pts.length()})",
      self.pts.length(),
    ),
  }
}

///|
pub fn CoordRing::algebra(self : CoordRing) -> FinAlg {
  self.alg
}

///|
pub fn CoordRing::num_points(self : CoordRing) -> Int32 {
  self.pts.length()
}

///|
pub fn CoordRing::of_poly(self : CoordRing, f : Poly) -> FinElem {
  let values : Array[Fp] = []
  for p in self.pts {
    values.push(f.eval(p.coords))
  }
  self.alg.elem(values)
}

///|
/// The i-th coordinate function x_i restricted to X.
pub fn CoordRing::coordinate_function(self : CoordRing, i : Int32) -> FinElem {
  self.of_poly(Poly::variable(self.nvars, i))
}

///|
/// A polynomial representative of a function table (via interpolation);
/// `of_poly(poly_of_function(v)) == v` for every table v.
pub fn CoordRing::poly_of_function(self : CoordRing, v : FinElem) -> Poly {
  if self.pts.length() == 0 {
    return Poly::zero(self.nvars)
  }
  interpolate(self.pts, v.coords())
}

// -----------------------------------------------------------------------------
// Polynomial maps and contravariance.
// -----------------------------------------------------------------------------

///|
pub struct PolyMap {
  dom_vars : Int32
  components : Array[Poly]
}

///|
pub fn PolyMap::new(dom_vars : Int32, components : Array[Poly]) -> PolyMap {
  for c in components {
    if c.num_vars() != dom_vars {
      abort("PolyMap::new: component variable count mismatch")
    }
  }
  { dom_vars, components, }
}

///|
pub fn PolyMap::identity(nvars : Int32) -> PolyMap {
  let comps : Array[Poly] = []
  for i in 0..<nvars {
    comps.push(Poly::variable(nvars, i))
  }
  { dom_vars: nvars, components: comps, }
}

///|
pub fn PolyMap::codim(self : PolyMap) -> Int32 {
  self.components.length()
}

///|
pub fn PolyMap::apply_point(self : PolyMap, pt : Pt) -> Pt {
  let coords : Array[Fp] = []
  for c in self.components {
    coords.push(c.eval(pt.coords))
  }
  Pt::new(coords)
}

///|
/// Composition self ∘ other (other first): substitute components of other
/// into components of self.
pub fn PolyMap::compose_after(self : PolyMap, other : PolyMap) -> PolyMap {
  let comps : Array[Poly] = []
  for c in self.components {
    comps.push(c.compose(other.components))
  }
  { dom_vars: other.dom_vars, components: comps, }
}

///|
/// Pullback of a polynomial along the map: F^*(f) = f ∘ F. Note the
/// direction: maps A^n -> A^m pull functions A^m -> A^n backwards. This is
/// the contravariance of the functor X |-> k[X].
pub fn PolyMap::pullback_poly(self : PolyMap, f : Poly) -> Poly {
  f.compose(self.components)
}

///|
/// Is this polynomial map a morphism X -> Y (i.e. does it send every
/// F_7-point of X into Y)? Decided by finite inspection.
pub fn is_variety_morphism(map : PolyMap, dom : Variety, cod : Variety) -> Bool {
  if map.dom_vars != dom.nvars || map.codim() != cod.nvars {
    return false
  }
  for p in dom.pts {
    if !cod.contains_point(map.apply_point(p)) {
      return false
    }
  }
  true
}

///|
/// Pullback of a *function table* on Y along a morphism F : X -> Y:
/// F^*(phi)(a) = phi(F(a)). Aborts if some F(a) is not a point of cod,
/// i.e. the caller must first establish `is_variety_morphism`.
pub fn pullback_function(
  map : PolyMap,
  dom : Variety,
  cod : Variety,
  dom_ring : CoordRing,
  phi : FinElem,
) -> FinElem {
  let vals = phi.coords()
  let out : Array[Fp] = []
  for p in dom.pts {
    match cod.point_index(map.apply_point(p)) {
      Some(idx) => out.push(vals[idx])
      None => abort("pullback_function: image point not in codomain variety")
    }
  }
  dom_ring.alg.elem(out)
}

///|
/// Pullback as an algebra homomorphism k[Y] -> k[X] (mind the reversal!),
/// ready for verification with AlgHom::verify and for checking functor
/// laws (g∘f)^* = f^* ∘ g^* as matrices.
pub fn pullback_hom(
  map : PolyMap,
  dom : Variety,
  cod : Variety,
  dom_ring : CoordRing,
  cod_ring : CoordRing,
) -> AlgHom {
  let images : Array[FinElem] = []
  for j in 0..<cod.pts.length() {
    let delta_j = cod_ring.alg.basis_elem(j)
    images.push(pullback_function(map, dom, cod, dom_ring, delta_j))
  }
  AlgHom::from_basis_images(images)
}

///|
/// Pairing of polynomial maps with a common domain (product universal
/// property for varieties): <f, g> : A^n -> A^{m1+m2} concatenates the
/// components. Projections compose with it back to f and g on the nose
/// (polynomial equality, tested).
pub fn pair_poly_maps(f : PolyMap, g : PolyMap) -> PolyMap {
  if f.dom_vars != g.dom_vars {
    abort("pair_poly_maps: domain mismatch")
  }
  let comps : Array[Poly] = []
  for c in f.components {
    comps.push(c)
  }
  for c in g.components {
    comps.push(c)
  }
  PolyMap::new(f.dom_vars, comps)
}

///|
/// The other direction of contravariance (the "Spec" direction): from an
/// algebra hom phi : k[Y] -> k[X] between *finite point-set* coordinate
/// rings, recover the point map X -> Y that induces it. Algorithm: a point
/// a of X maps to the unique point b of Y with phi(delta_b)(a) = 1, since
/// algebra homs between products of F_7 permute/merge the primitive
/// idempotents by a function on index sets. Aborts if for some a there is
/// not exactly one such b (then phi was not a hom between these
/// function algebras in the first place).
pub fn induced_point_map(
  hom : AlgHom,
  x : Variety,
  y : Variety,
  x_ring : CoordRing,
  y_ring : CoordRing,
) -> Array[Pt] {
  // Precompute phi(delta_b) tables once.
  let images : Array[Array[Fp]] = []
  for b in 0..<y.pts.length() {
    images.push(hom.apply(x_ring.alg, y_ring.alg.basis_elem(b)).coords())
  }
  let out : Array[Pt] = []
  for a in 0..<x.pts.length() {
    let mut found = -1
    for b in 0..<y.pts.length() {
      if images[b][a] == Fp::one() {
        if found >= 0 {
          abort("induced_point_map: phi(delta_b)(a)=1 for two different b")
        }
        found = b
      } else if images[b][a] != Fp::zero() {
        abort("induced_point_map: phi(delta_b) is not a 0/1 idempotent table")
      }
    }
    if found < 0 {
      abort("induced_point_map: point has no image (phi is not unital?)")
    }
    out.push(y.pts[found])
  }
  out
}

///|
/// Projections from a product variety X x Y (ambient A^{n+m}) to factors.
pub fn product_projection_first(n : Int32, m : Int32) -> PolyMap {
  let comps : Array[Poly] = []
  for i in 0..<n {
    comps.push(Poly::variable(n + m, i))
  }
  PolyMap::new(n + m, comps)
}

///|
pub fn product_projection_second(n : Int32, m : Int32) -> PolyMap {
  let comps : Array[Poly] = []
  for i in 0..<m {
    comps.push(Poly::variable(n + m, n + i))
  }
  PolyMap::new(n + m, comps)
}

///|
/// Injections into the tagged disjoint union in A^{n+m+1}.
pub fn disjoint_injection_left(n : Int32, m : Int32) -> PolyMap {
  let comps : Array[Poly] = []
  for i in 0..<n {
    comps.push(Poly::variable(n, i))
  }
  for _ in 0..<m {
    comps.push(Poly::zero(n))
  }
  comps.push(Poly::zero(n))
  PolyMap::new(n, comps)
}

///|
pub fn disjoint_injection_right(n : Int32, m : Int32) -> PolyMap {
  let comps : Array[Poly] = []
  for _ in 0..<n {
    comps.push(Poly::zero(m))
  }
  for i in 0..<m {
    comps.push(Poly::variable(m, i))
  }
  comps.push(Poly::one_poly(m))
  PolyMap::new(m, comps)
}
