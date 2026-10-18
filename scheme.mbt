// =============================================================================
// scheme.mbt -- finite affine schemes Spec(R/I) for zero-dimensional I,
// with their structure sheaf made computational.
//
// Points are the (maximal) prime ideals from primary decomposition --
// including non-rational closed points like (x^2+1, y) with residue
// field F_49, which F_7-point enumeration cannot see. The stalk at the
// i-th point is the local Artinian factor R/Q_i from the decomposition
// (in dimension zero the Q_i are pairwise comaximal, so CRT gives
// R/I ~= prod R/Q_i, and localization at the i-th prime is projection
// to the i-th factor). The structure sheaf on this finite discrete
// space is: sections over a set U of points = product of the stalks at
// U; restrictions = projections. Global sections recover R/I (the CRT
// isomorphism is exposed as a verifiable AlgHom). Nilpotents are global
// sections vanishing in every residue field but not in stalks -- the
// exact sense in which Spec remembers more than its point set.
//
// Scope honesty: this is the zero-dimensional (finite) layer of scheme
// theory, where every prime is maximal and the topology is discrete.
// Positive-dimensional spectra have non-closed generic points and are
// not finitely enumerable; they are not represented here. What *is*
// represented with full scheme content: nonreduced local rings
// (lengths), residue field extensions, D(f) and its sections theorem
// Gamma(D(f), O) = (R/I)_f at the level of dimensions and points,
// closed/reduced subschemes, and scheme morphisms from polynomial maps
// with prime contraction computed among maximal primes.
// =============================================================================

///|
pub struct AffineScheme {
  ring : QuotientRing
  model : QuotientModel
  components : Array[Ideal] // primary components Q_i (merged by prime)
  primes : Array[Ideal] // associated (maximal) primes P_i = sqrt(Q_i)
  local_models : Array[QuotientModel]
  residue_models : Array[QuotientModel]
}

///|
fn quotient_model_of(ideal : Ideal, name : String) -> QuotientModel {
  match QuotientModel::new(QuotientRing::new(ideal), name) {
    Some(m) => m
    None => abort("scheme: expected a zero-dimensional quotient")
  }
}

///|
/// Spec(R/I) for zero-dimensional I. None outside the finite regime or
/// when primary decomposition is unavailable.
pub fn AffineScheme::spec(ideal : Ideal) -> AffineScheme? {
  let decomp = match primary_decomposition_zero_dim(ideal) {
    Some(d) => d
    None => return None
  }
  // Merge components sharing a prime (a point of Spec must occur once).
  let primes : Array[Ideal] = []
  let components : Array[Ideal] = []
  for c in decomp.components() {
    let mut idx = -1
    for i in 0..<primes.length() {
      if primes[i].equal_to(c.prime()) {
        idx = i
        break
      }
    }
    if idx < 0 {
      primes.push(c.prime())
      components.push(c.component())
    } else {
      components[idx] = components[idx].intersect(c.component())
    }
  }
  let ring = QuotientRing::new(ideal)
  let model = quotient_model_of(ideal, "Gamma(Spec)")
  let local_models : Array[QuotientModel] = []
  let residue_models : Array[QuotientModel] = []
  for i in 0..<components.length() {
    local_models.push(quotient_model_of(components[i], "stalk-\{i}"))
    residue_models.push(quotient_model_of(primes[i], "residue-\{i}"))
  }
  Some({ ring, model, components, primes, local_models, residue_models, })
}

///|
pub fn AffineScheme::num_points(self : AffineScheme) -> Int32 {
  self.primes.length()
}

///|
pub fn AffineScheme::prime_at(self : AffineScheme, i : Int32) -> Ideal {
  self.primes[i]
}

///|
pub fn AffineScheme::component_at(self : AffineScheme, i : Int32) -> Ideal {
  self.components[i]
}

///|
pub fn AffineScheme::ring(self : AffineScheme) -> QuotientRing {
  self.ring
}

///|
/// Structure-constant model of the global ring Gamma(Spec, O) = R/I.
pub fn AffineScheme::global_model(self : AffineScheme) -> QuotientModel {
  self.model
}

///|
pub fn AffineScheme::ideal(self : AffineScheme) -> Ideal {
  self.ring.ideal()
}

///|
/// The F_7-rational points only (a possibly proper subset of Spec: the
/// F_49-point (x^2+1, y) contributes no rational point). Named to make
/// the loss of information explicit at call sites.
pub fn AffineScheme::rational_points(self : AffineScheme) -> Array[Pt] {
  Variety::from_ideal(self.ring.ideal()).points()
}

///|
/// Stalk O_{X,p_i} = R/Q_i as a finite algebra model.
pub fn AffineScheme::stalk_model(
  self : AffineScheme,
  i : Int32,
) -> QuotientModel {
  self.local_models[i]
}

///|
/// Residue field kappa(p_i) = R/P_i as a finite algebra model.
pub fn AffineScheme::residue_model(
  self : AffineScheme,
  i : Int32,
) -> QuotientModel {
  self.residue_models[i]
}

///|
/// [kappa(p_i) : F_7].
pub fn AffineScheme::residue_degree(self : AffineScheme, i : Int32) -> Int32 {
  self.residue_model(i).algebra().dim()
}

///|
/// Length of the local ring at p_i: dim_{F_7} O_{p_i} / [kappa:F_7]
/// (every composition factor of an Artinian local module is kappa).
pub fn AffineScheme::length_at(self : AffineScheme, i : Int32) -> Int32 {
  let d = self.local_models[i].algebra().dim()
  let e = self.residue_degree(i)
  if d % e != 0 {
    abort("AffineScheme::length_at: dimension not divisible (bug)")
  }
  d / e
}

///|
/// Total length of the finite scheme: sum of local lengths. For a
/// zero-dimensional *variety* this counts points with residue degrees;
/// nilpotents increase it beyond any point count.
pub fn AffineScheme::total_length(self : AffineScheme) -> Int32 {
  let mut acc = 0
  for i in 0..<self.primes.length() {
    acc = acc + self.length_at(i)
  }
  acc
}

///|
pub fn AffineScheme::is_reduced(self : AffineScheme) -> Bool {
  nilradical_basis(self.model.algebra()).length() == 0
}

///|
/// The reduced subscheme Spec(R/sqrt(I)): same points, all lengths 1
/// in the sense local rings become their residue fields.
pub fn AffineScheme::reduced_scheme(self : AffineScheme) -> AffineScheme {
  let rad = match self.ring.ideal().radical_zero_dim() {
    Some(r) => r
    None => abort("AffineScheme::reduced_scheme: radical unavailable")
  }
  match AffineScheme::spec(rad) {
    Some(s) => s
    None => abort("AffineScheme::reduced_scheme: spec unavailable")
  }
}

///|
/// Closed subscheme Spec(R/J) for J containing I. None if I is not
/// contained in J (then R/J is not a quotient of R/I at all).
pub fn AffineScheme::closed_subscheme(
  self : AffineScheme,
  j : Ideal,
) -> AffineScheme? {
  if !self.ring.ideal().is_subset_of(j) {
    return None
  }
  AffineScheme::spec(j)
}

///|
/// Closed subset V(J) inside Spec(R/I): indices of primes containing J.
pub fn AffineScheme::closed_subset(
  self : AffineScheme,
  j : Ideal,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<self.primes.length() {
    if j.is_subset_of(self.primes[i]) {
      out.push(i)
    }
  }
  out
}

///|
/// Principal open subset D(f): indices of primes not containing f.
pub fn AffineScheme::principal_open_indices(
  self : AffineScheme,
  f : Poly,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<self.primes.length() {
    if !self.primes[i].contains(f) {
      out.push(i)
    }
  }
  out
}

///|
/// Specialization in this finite space: primes are maximal, hence
/// pairwise incomparable; p_i specializes only to itself. Computed by
/// actual prime containment, not assumed.
pub fn AffineScheme::specializes_to(
  self : AffineScheme,
  i : Int32,
  j : Int32,
) -> Bool {
  self.primes[i].is_subset_of(self.primes[j])
}

///|
/// Sections of the structure sheaf over the point set `indices`:
/// the product of the stalks there (zero ring for the empty open).
pub fn AffineScheme::sections_algebra(
  self : AffineScheme,
  indices : Array[Int32],
) -> FinAlg {
  if indices.length() == 0 {
    return FinAlg::function_algebra("Gamma(empty)", 0)
  }
  let mut alg = self.local_models[indices[0]].algebra()
  for k in 1..<indices.length() {
    alg = FinAlg::product(
      alg,
      self.local_models[indices[k]].algebra(),
      "Gamma(U)",
    )
  }
  alg
}

///|
/// Image of a global polynomial in the sections over `indices`
/// (its tuple of germs/classes in the local factors).
pub fn AffineScheme::section_of_poly(
  self : AffineScheme,
  indices : Array[Int32],
  f : Poly,
) -> FinElem {
  let coords : Array[Fp] = []
  for i in indices {
    let lm = self.local_models[i]
    let cos = self.local_models[i].ring().of_poly(f)
    for c in lm.to_elem(cos).coords() {
      coords.push(c)
    }
  }
  self.sections_algebra(indices).elem(coords)
}

///|
/// The canonical map Gamma(Spec) data: the CRT isomorphism from the
/// global quotient model to the product of stalks, as a verifiable
/// AlgHom. This is the finite-scheme form of "global sections of Spec A
/// recover A".
pub fn AffineScheme::global_sections_hom(self : AffineScheme) -> AlgHom {
  let all : Array[Int32] = []
  for i in 0..<self.primes.length() {
    all.push(i)
  }
  let target = self.sections_algebra(all)
  let images : Array[FinElem] = []
  let n = self.ring.num_vars()
  for m in self.model.basis_monomials() {
    let e : Array[Int32] = []
    for v in 0..<n {
      e.push(m.exp_at(v))
    }
    let mono = Poly::monomial(n, Fp::one(), e)
    let coords : Array[Fp] = []
    for i in all {
      let lm = self.local_models[i]
      let cos = self.local_models[i].ring().of_poly(mono)
      for c in lm.to_elem(cos).coords() {
        coords.push(c)
      }
    }
    images.push(target.elem(coords))
  }
  AlgHom::from_basis_images(images)
}

///|
/// Restriction of sections along an inclusion of point sets
/// (`to_indices` should be a subsequence of `from_indices`): the
/// projection of product algebras, as an AlgHom.
pub fn AffineScheme::restriction_hom(
  self : AffineScheme,
  from_indices : Array[Int32],
  to_indices : Array[Int32],
) -> AlgHom {
  let dst = self.sections_algebra(to_indices)
  // Source basis is ordered by from_indices factor blocks; only the
  // target offset of a retained factor needs computing.
  let images : Array[FinElem] = []
  for fi in from_indices {
    let d = self.local_models[fi].algebra().dim()
    // Position of this factor in the target, if retained.
    let mut dst_offset = -1
    let mut acc = 0
    for ti in to_indices {
      if ti == fi {
        dst_offset = acc
        break
      }
      acc = acc + self.local_models[ti].algebra().dim()
    }
    for j in 0..<d {
      if dst_offset < 0 {
        images.push(dst.zero_elem())
      } else {
        images.push(dst.basis_elem(dst_offset + j))
      }
    }
  }
  AlgHom::from_basis_images(images)
}

///|
/// The stalk map O_{p_i} -> kappa(p_i) as a verifiable AlgHom (images of
/// local monomial basis elements in the residue quotient).
pub fn AffineScheme::residue_hom(self : AffineScheme, i : Int32) -> AlgHom {
  let lm = self.local_models[i]
  let rm = self.residue_model(i)
  let residue_ring = rm.ring()
  let n = self.ring.num_vars()
  let images : Array[FinElem] = []
  for m in lm.basis_monomials() {
    let e : Array[Int32] = []
    for v in 0..<n {
      e.push(m.exp_at(v))
    }
    images.push(
      rm.to_elem(residue_ring.of_poly(Poly::monomial(n, Fp::one(), e))),
    )
  }
  AlgHom::from_basis_images(images)
}

///|
/// Support of the global section f: point indices where its germ in the
/// stalk is nonzero. Vanishing in every residue field is strictly
/// weaker (nilpotents) -- both predicates are exposed.
pub fn AffineScheme::support_indices(
  self : AffineScheme,
  f : Poly,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<self.primes.length() {
    let cos = self.local_models[i].ring().of_poly(f)
    if !cos.is_zero() {
      out.push(i)
    }
  }
  out
}

///|
pub fn AffineScheme::vanishes_at_all_residues(
  self : AffineScheme,
  f : Poly,
) -> Bool {
  for p in self.primes {
    if !p.contains(f) {
      return false
    }
  }
  true
}

///|
/// Is the global section f nilpotent in R/I? Decided by membership in
/// the radical (computed by the trace form).
pub fn AffineScheme::is_nilpotent_section(
  self : AffineScheme,
  f : Poly,
) -> Bool {
  match self.ring.ideal().radical_zero_dim() {
    Some(rad) => rad.contains(f)
    None => abort("AffineScheme::is_nilpotent_section: not zero-dimensional")
  }
}

// -----------------------------------------------------------------------------
// Morphisms of finite affine schemes from polynomial maps.
// -----------------------------------------------------------------------------

///|
pub struct SchemeMorphism {
  map : PolyMap
}

///|
/// Build the scheme morphism Spec(R/J) -> Spec(R/I) induced by a
/// polynomial map when it exists: precisely when pulling back every
/// equation of the target lands in J (equivalently the induced ring map
/// R/I -> R/J is well-defined). None otherwise.
pub fn scheme_morphism_from_poly_map(
  source : AffineScheme,
  target : AffineScheme,
  map : PolyMap,
) -> SchemeMorphism? {
  if map.dom_vars != source.ring.num_vars() ||
    map.codim() != target.ring.num_vars() {
    return None
  }
  let src_ideal = source.ring.ideal()
  for g in target.ring.ideal().gens() {
    if !src_ideal.contains(map.pullback_poly(g)) {
      return None
    }
  }
  Some({ map, })
}

///|
/// The ring homomorphism on global sections, target coset -> source
/// coset (contravariant, as always for Spec).
pub fn SchemeMorphism::pullback_coset(
  self : SchemeMorphism,
  source : AffineScheme,
  target_coset : Coset,
) -> Coset {
  source.ring.of_poly(self.map.pullback_poly(target_coset.repr_poly()))
}

///|
/// Image of a source prime under Spec(phi): the contraction
/// phi^{-1}(P). Among maximal target primes it is recognized as the
/// unique Q with pullback(Q) ⊆ P (maximality forces equality with the
/// contraction). Returns the target point index, or None if no target
/// prime has this property (cannot happen for a valid morphism, so a
/// None here evidences misuse/bug rather than mathematics).
pub fn SchemeMorphism::point_index_map(
  self : SchemeMorphism,
  source : AffineScheme,
  target : AffineScheme,
  source_index : Int32,
) -> Int32? {
  let p = source.primes[source_index]
  for j in 0..<target.primes.length() {
    let mut ok = true
    for g in target.primes[j].gens() {
      if !p.contains(self.map.pullback_poly(g)) {
        ok = false
        break
      }
    }
    if ok {
      return Some(j)
    }
  }
  None
}

///|
/// The polynomial map, for comparison with rational-point behavior.
pub fn SchemeMorphism::poly_map(self : SchemeMorphism) -> PolyMap {
  self.map
}

// -----------------------------------------------------------------------------
// Proj charts as affine schemes (the standard open cover), finite case.
// -----------------------------------------------------------------------------

///|
/// The coordinate ring of the affine chart U_i of a projective variety:
/// (S/I)_{(X_i)} realized as polynomials modulo the dehomogenized ideal.
pub fn ProjVariety::chart_ring(self : ProjVariety, i : Int32) -> QuotientRing {
  if i < 0 || i >= self.num_coords() {
    abort("ProjVariety::chart_ring: coordinate index out of range")
  }
  let gens : Array[Poly] = []
  for g in self.ideal().groebner() {
    gens.push(dehomogenize_poly(g, i))
  }
  QuotientRing::new(Ideal::new(self.num_coords() - 1, gens))
}

///|
/// The chart as a finite affine scheme when it is zero-dimensional
/// (e.g. charts of finite projective schemes); None for positive-
/// dimensional charts, matching AffineScheme's stated regime.
pub fn ProjVariety::chart_scheme(
  self : ProjVariety,
  i : Int32,
) -> AffineScheme? {
  AffineScheme::spec(self.chart_ring(i).ideal())
}
