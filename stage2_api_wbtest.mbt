// Direct tests for stage-2 public helpers that are otherwise exercised
// only internally. Every expected value below is independently known,
// so a regression in the helper itself is falsifiable.

///|
test "stage-2 helpers: rationals, homogeneous parts, monomial enumeration" {
  assert_eq(factorial_int(5), 120)
  assert_true(Rat::new(-2, 3).is_negative())
  assert_true(!Rat::new(2, 3).is_negative())
  assert_true(Rat::new(6, 3).is_integer())
  assert_true(!Rat::new(1, 2).is_integer())
  assert_eq(Rat::new(6, 3).to_int_exact(), 2)
  assert_true(Rat::new(3, 4).div_rat(Rat::new(9, 8)) == Rat::new(2, 3))
  let rp = RatPoly::from_coeffs([Rat::from_int(5), Rat::zero(), Rat::new(3, 2)])
  assert_true(rp.leading_coefficient() == Rat::new(3, 2))

  // Homogeneous components of 1 + x + x^2 + xy are visible separately.
  let f = Poly::from_int_terms(2, [
    (1, [0, 0]),
    (1, [1, 0]),
    (1, [2, 0]),
    (1, [1, 1]),
  ])
  assert_true(f.homogeneous_component(0).equal_to(Poly::one_poly(2)))
  assert_true(f.homogeneous_component(1).equal_to(Poly::variable(2, 0)))
  assert_eq(f.homogeneous_component(2).num_terms(), 2)
  assert_true(f.homogeneous_component(3).is_zero())

  // |(x^2-yz)| initial ideal is principal in degree 2.
  let conic = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [2, 0, 0]), (-1, [0, 1, 1])]),
  ])
  let inits = conic.initial_monomials()
  assert_eq(inits.length(), 1)
  assert_eq(inits[0].total_degree(), 2)

  // C(2 + 3 - 1, 3 - 1) = 6 monomials of degree 2 in 3 variables.
  let mons = monomials_of_degree(3, 2)
  assert_eq(mons.length(), 6)
  for m in mons {
    assert_eq(m.total_degree(), 2)
  }
  assert_eq(monomials_of_degree(0, 0).length(), 1)
  assert_eq(monomials_of_degree(0, 1).length(), 0)
}

///|
test "stage-2 helpers: decomposition entry points and nilradical basis" {
  let monomial = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [1, 1])]),
  ])
  assert_true(monomial.is_monomial_ideal())
  let nonmono = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  assert_true(!nonmono.is_monomial_ideal())
  let pd = match primary_decomposition(monomial) {
    Some(d) => d
    None => abort("monomial decomposition")
  }
  let primes = pd.associated_primes()
  assert_eq(primes.length(), 2)

  // Direct univariate entry point: one primary component (t^2*(t-1)).
  let uni = Ideal::new(1, [Poly::from_int_terms(1, [(1, [3]), (-1, [2])])])
  let upd = match primary_decomposition_univariate(uni) {
    Some(d) => d
    None => abort("univariate decomposition")
  }
  assert_eq(upd.num_components(), 2)
  assert_true(upd.verify(uni))

  // In F7[t]/(t^3) the nilradical is spanned by t and t^2 (dimension 2);
  // in the field F7[t]/(t^2+1) it is zero. The minimal polynomial of the
  // class of t in the latter is exactly T^2 + 1.
  let fat_model = match
    QuotientModel::new(
      QuotientRing::from_generators(1, [Poly::from_int_terms(1, [(1, [3])])]),
      "fat-line",
    ) {
    Some(m) => m
    None => abort("fat model")
  }
  assert_eq(nilradical_basis(fat_model.algebra()).length(), 2)
  let field_model = match
    QuotientModel::new(
      QuotientRing::from_generators(1, [
        Poly::from_int_terms(1, [(1, [2]), (1, [0])]),
      ]),
      "F49",
    ) {
    Some(m) => m
    None => abort("field model")
  }
  assert_eq(nilradical_basis(field_model.algebra()).length(), 0)
  let t_elem = field_model.to_elem(field_model.ring().variable(0))
  let mu = minimal_polynomial_of_elem(field_model, t_elem)
  assert_true(mu.equal_to(Poly::from_int_terms(1, [(1, [2]), (1, [0])])))
}

///|
test "stage-2 helpers: projective coordinate accessors" {
  let conic = ProjVariety::from_ideal(
    Ideal::new(3, [Poly::from_int_terms(3, [(1, [2, 0, 0]), (-1, [0, 1, 1])])]),
  )
  assert_eq(conic.num_coords(), 3)
  assert_eq(conic.ambient_dim(), 2)
  let p = PPoint::must([Fp::new(2), Fp::zero(), Fp::new(4)])
  assert_eq(p.num_coords(), 3)
}
