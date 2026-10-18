// Finite affine scheme tests: Spec sees nilpotents and non-rational
// closed points that point-set varieties cannot; structure sheaf
// sections/restrictions, stalks, residue fields, lengths, D(f),
// subschemes, and scheme morphisms with computed prime contraction.

///|
fn spec_of(ideal : Ideal) -> AffineScheme {
  match AffineScheme::spec(ideal) {
    Some(s) => s
    None => abort("expected a finite affine scheme")
  }
}

///|
fn find_prime(s : AffineScheme, prime : Ideal) -> Int32 {
  for i in 0..<s.num_points() {
    if s.prime_at(i).equal_to(prime) {
      return i
    }
  }
  abort("prime not found in Spec")
}

///|
test "Spec remembers nilpotents: fat point has length 2, reduced has 1" {
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let fat = spec_of(Ideal::new(2, [x.pow(2), y]))
  assert_eq(fat.num_points(), 1)
  assert_eq(fat.rational_points().length(), 1)
  assert_eq(fat.length_at(0), 2)
  assert_eq(fat.total_length(), 2)
  assert_eq(fat.residue_degree(0), 1)
  assert_true(!fat.is_reduced())
  // xbar: nonzero germ, zero in the residue field, nilpotent globally.
  assert_true(fat.support_indices(x).length() == 1)
  assert_true(fat.vanishes_at_all_residues(x))
  assert_true(fat.is_nilpotent_section(x))
  assert_true(!fat.is_nilpotent_section(Poly::one_poly(2).add(x)))
  // Residue hom kills exactly the maximal ideal of the stalk.
  let res = fat.residue_hom(0)
  let stalk = fat.stalk_model(0).algebra()
  let residue = fat.residue_model(0).algebra()
  assert_true(res.verify(stalk, residue))
  let xgerm = fat
    .stalk_model(0)
    .to_elem(QuotientRing::new(fat.component_at(0)).of_poly(x))
  assert_true(res.apply(residue, xgerm).equal_to(residue.zero_elem()))
  assert_true(res.apply(residue, stalk.one_elem()).equal_to(residue.one_elem()))
  // Reduced subscheme: same point, length drops to 1.
  let red = fat.reduced_scheme()
  assert_eq(red.num_points(), 1)
  assert_eq(red.length_at(0), 1)
  assert_true(red.is_reduced())
  assert_true(red.ideal().equal_to(Ideal::new(2, [x, y])))
  // Closed subscheme by a larger ideal works; by a non-quotient, refused.
  match fat.closed_subscheme(Ideal::new(2, [x, y])) {
    Some(sub) => assert_eq(sub.total_length(), 1)
    None => assert_true(false)
  }
  assert_true(fat.closed_subscheme(Ideal::new(2, [x])) is None)
}

///|
test "structure sheaf: global sections recover the ring (CRT), restrictions project" {
  // A = k[t]/(t^2 (t-1)): fat point at 0 (length 2) + simple point at 1.
  let t = Poly::variable(1, 0)
  let one = Poly::one_poly(1)
  let ideal = Ideal::new(1, [t.pow(2).mul(t.sub(one))])
  let s = spec_of(ideal)
  assert_eq(s.num_points(), 2)
  assert_eq(s.total_length(), 3)
  let i0 = find_prime(s, Ideal::new(1, [t]))
  let i1 = find_prime(s, Ideal::new(1, [t.sub(one)]))
  assert_eq(s.length_at(i0), 2)
  assert_eq(s.length_at(i1), 1)
  // Gamma(Spec A, O) = A, via the canonical CRT map -- verified iso.
  // (Factor order in the product is the scheme's own point ordering.)
  let all_own : Array[Int32] = []
  for i in 0..<s.num_points() {
    all_own.push(i)
  }
  let gh = s.global_sections_hom()
  assert_true(
    gh.is_isomorphism(s.global_model().algebra(), s.sections_algebra(all_own)),
  )
  // Restriction to one point is a homomorphism and matches the section.
  let restr = s.restriction_hom(all_own, [i1])
  let src = s.sections_algebra(all_own)
  let dst = s.sections_algebra([i1])
  assert_true(restr.verify(src, dst))
  let f = t.pow(2).add(t.scale(Fp::new(3))).add(one)
  let global_sec = s.section_of_poly(all_own, f)
  let local_sec = s.section_of_poly([i1], f)
  assert_true(restr.apply(dst, global_sec).equal_to(local_sec))
  // f(1) = 1 + 3 + 1 = 5 in the stalk at t=1 (which is F_7).
  assert_true(local_sec.equal_to(dst.scalar_elem(Fp::new(5))))
  // Support / nilpotence distinctions.
  let nil = t.mul(t.sub(one)) // square is t^2 (t-1)^2 = 0 in A
  assert_true(s.is_nilpotent_section(nil))
  let sup = s.support_indices(nil)
  assert_eq(sup.length(), 1)
  assert_eq(sup[0], i0)
  // D(t) excludes only the fat point; sections theorem dimension check:
  // dim Gamma(D(t)) = dim of the finite localization A_t.
  let dopen = s.principal_open_indices(t)
  assert_eq(dopen.length(), 1)
  assert_eq(dopen[0], i1)
  let model = match QuotientModel::new(s.ring(), "A") {
    Some(m) => m
    None => abort("model")
  }
  let ft = model.to_elem(s.ring().of_poly(t))
  let loc = model.algebra().localize_at(ft, "A_t")
  assert_eq(loc.algebra().dim(), s.sections_algebra(dopen).dim())
  assert_eq(loc.algebra().dim(), 1)
  // Closed subset V(t) is the complementary fat point.
  let closed = s.closed_subset(Ideal::new(1, [t]))
  assert_eq(closed.length(), 1)
  assert_eq(closed[0], i0)
  // No nontrivial specializations among maximal primes.
  assert_true(s.specializes_to(i0, i0))
  assert_true(!s.specializes_to(i0, i1))
}

///|
test "Spec sees the F_49 closed point that rational points miss" {
  let y = Poly::variable(2, 1)
  let ideal = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (1, [0, 0])]),
    y,
  ])
  let s = spec_of(ideal)
  assert_eq(s.num_points(), 1)
  assert_eq(s.rational_points().length(), 0)
  assert_eq(s.residue_degree(0), 2)
  assert_eq(s.length_at(0), 1)
  assert_true(s.is_reduced())
  // Its residue field is F_49: the stalk is already a field.
  assert_true(finite_algebra_is_field(s.stalk_model(0).algebra()))
  // Frobenius on the scheme fixes the point (both conjugate roots lie
  // in the same F_7-prime), via the scheme morphism [x^7, y].
  let frob = PolyMap::new(2, [Poly::variable(2, 0).pow(7), Poly::variable(2, 1)])
  match scheme_morphism_from_poly_map(s, s, frob) {
    Some(m) => {
      assert_true(m.point_index_map(s, s, 0) is Some(0))
      // Pullback of xbar is xbar^7 = -xbar in F_49 (the conjugate root).
      let xb = s.ring().variable(0)
      let pulled = m.pullback_coset(s, xb)
      let neg = s.ring().neg(xb)
      assert_true(pulled.equal_to(neg))
    }
    None => assert_true(false)
  }
}

///|
test "scheme morphisms: well-definedness and prime contraction" {
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let one = Poly::one_poly(2)
  // Source: two points (±1, 0). Target: the point (1, 0). Squaring map.
  let source = spec_of(
    Ideal::new(2, [Poly::from_int_terms(2, [(1, [2, 0]), (-1, [0, 0])]), y]),
  )
  let target = spec_of(Ideal::new(2, [x.sub(one), y]))
  let sq = PolyMap::new(2, [x.pow(2), y])
  match scheme_morphism_from_poly_map(source, target, sq) {
    Some(m) => {
      for i in 0..<source.num_points() {
        assert_true(m.point_index_map(source, target, i) is Some(0))
      }
      // Pullback on global sections: x_target |-> x_source^2 = 1.
      let pulled = m.pullback_coset(source, target.ring().variable(0))
      assert_true(pulled.equal_to(source.ring().one_coset()))
    }
    None => assert_true(false)
  }
  // The identity map of ambient spaces does NOT descend: x-1 does not
  // pull back into (x^2-1, y). Refused, correctly.
  assert_true(
    scheme_morphism_from_poly_map(source, target, PolyMap::identity(2)) is None,
  )
  // Positive-dimensional spectra are outside the finite regime.
  let line_ideal = Ideal::new(2, [y])
  assert_true(AffineScheme::spec(line_ideal) is None)
}

///|
test "Proj charts as schemes and P^1 gluing relation t * s = 1 on overlaps" {
  // Finite projective scheme: two points in P^2.
  let two = ProjVariety::from_points(3, [
    PPoint::must([Fp::new(1), Fp::new(0), Fp::new(0)]),
    PPoint::must([Fp::new(0), Fp::new(1), Fp::new(0)]),
  ])
  // Chart U_2 (z != 0) is empty; charts U_0 and U_1 are one point each.
  match two.chart_scheme(2) {
    Some(s) => assert_eq(s.num_points(), 0)
    None => assert_true(false)
  }
  match two.chart_scheme(0) {
    Some(s) => {
      assert_eq(s.num_points(), 1)
      assert_eq(s.total_length(), 1)
    }
    None => assert_true(false)
  }
  match two.chart_scheme(1) {
    Some(s) => assert_eq(s.num_points(), 1)
    None => assert_true(false)
  }
  // P^1 charts are polynomial rings (positive-dimensional): no finite
  // AffineScheme, honestly None. The gluing data on overlaps is the
  // relation (X1/X0)*(X0/X1) = 1, checked pointwise on all overlap
  // points of P^1(F_7).
  let p1 = ProjVariety::from_ideal(Ideal::zero_ideal(2))
  assert_true(p1.chart_scheme(0) is None)
  assert_true(p1.chart_ring(0).ideal().is_zero_ideal())
  let mut overlap = 0
  for p in all_projective_points(1) {
    match (chart_point(p, 0), chart_point(p, 1)) {
      (Some(u), Some(v)) => {
        overlap = overlap + 1
        assert_true(u.coord(0) * v.coord(0) == Fp::one())
      }
      _ => ()
    }
  }
  assert_eq(overlap, 6)
  // And the same relation as localized algebra: in k[t]_t, t * (1/t) = 1.
  let t = Poly::variable(1, 0)
  let loc = LocalizedRing::new(p1.chart_ring(0), t)
  assert_true(
    loc.equal_to(loc.mul(loc.of_poly(t), loc.inv_denom()), loc.one_elem()),
  )
}
