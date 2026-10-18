// Primary decomposition tests across all three complete regimes, with
// classical expected decompositions (including an embedded prime and a
// non-rational maximal ideal over F_7), and refusal outside scope.

///|
fn pd_of(ideal : Ideal) -> PrimaryDecomposition {
  match primary_decomposition(ideal) {
    Some(d) => d
    None => abort("expected a primary decomposition")
  }
}

///|
fn has_component(d : PrimaryDecomposition, comp : Ideal, prime : Ideal) -> Bool {
  for c in d.components() {
    if c.component().equal_to(comp) && c.prime().equal_to(prime) {
      return true
    }
  }
  false
}

///|
test "univariate factorization over F_7 is complete and exact" {
  let x = Poly::variable(1, 0)
  let one = Poly::one_poly(1)
  // x^2 - 1 = (x-1)(x+1); x^2 + 1 irreducible; x^3 - x three linear factors.
  let f1 = factor_univariate(x.pow(2).sub(one))
  assert_eq(f1.length(), 2)
  assert_true(is_irreducible_univariate(x.pow(2).add(one)))
  assert_true(!is_irreducible_univariate(x.pow(2).sub(one)))
  let f3 = factor_univariate(x.pow(3).sub(x))
  assert_eq(f3.length(), 3)
  for fc in f3 {
    assert_eq(fc.exponent(), 1)
    assert_eq(fc.factor().total_degree(), 1)
  }
  // Multiplicity: (x-1)^2 (x^2+1).
  let g = x.sub(one).pow(2).mul(x.pow(2).add(one))
  let fg = factor_univariate(g)
  assert_eq(fg.length(), 2)
  let mut saw_sq = false
  let mut saw_irred = false
  let mut rebuilt = one
  for fc in fg {
    if fc.factor().equal_to(x.sub(one)) && fc.exponent() == 2 {
      saw_sq = true
    }
    if fc.factor().equal_to(x.pow(2).add(one)) && fc.exponent() == 1 {
      saw_irred = true
    }
    rebuilt = rebuilt.mul(fc.factor().pow(fc.exponent()))
  }
  assert_true(saw_sq && saw_irred)
  assert_true(rebuilt.equal_to(g))
  // gcd and radical.
  assert_true(
    univariate_gcd(x.pow(2).sub(one), x.pow(3).sub(x)).equal_to(
      x.pow(2).sub(one),
    ),
  )
  assert_true(radical_univariate(x.sub(one).pow(3)).equal_to(x.sub(one)))
  // over F_7, x^7 - x splits completely into 7 linear factors.
  assert_eq(factor_univariate(x.pow(7).sub(x)).length(), 7)
}

///|
test "minimal polynomials and zero-dimensional radical (trace form)" {
  // minpoly of xbar in k[x,y]/(x^2-2, y-x) is t^2 - 2.
  let ideal = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-2, [0, 0])]),
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [1, 0])]),
  ])
  match minimal_polynomial_mod(ideal, Poly::variable(2, 0)) {
    Some(mu) =>
      assert_true(mu.equal_to(Poly::from_int_terms(1, [(1, [2]), (-2, [0])])))
    None => assert_true(false)
  }
  // Radical computations.
  let fat = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [1, 1])]),
    Poly::from_int_terms(2, [(1, [0, 2])]),
  ])
  match fat.radical_zero_dim() {
    Some(r) =>
      assert_true(
        r.equal_to(Ideal::new(2, [Poly::variable(2, 0), Poly::variable(2, 1)])),
      )
    None => assert_true(false)
  }
  let sq = Ideal::new(1, [Poly::from_int_terms(1, [(1, [2])])])
  match sq.radical_zero_dim() {
    Some(r) => assert_true(r.equal_to(Ideal::new(1, [Poly::variable(1, 0)])))
    None => assert_true(false)
  }
  // Field recognition: k[x]/(x^2+1) = F_49 is a field; k[x]/(x^2-1) is not.
  let f49_ideal = Ideal::new(1, [Poly::from_int_terms(1, [(1, [2]), (1, [0])])])
  assert_true(f49_ideal.is_prime_zero_dim())
  let split_ideal = Ideal::new(1, [
    Poly::from_int_terms(1, [(1, [2]), (-1, [0])]),
  ])
  assert_true(!split_ideal.is_prime_zero_dim())
  assert_true(split_ideal.is_primary_zero_dim() == false)
  // (x^2) is (x)-primary: radical prime but ideal != radical.
  assert_true(sq.is_primary_zero_dim())
  assert_true(!sq.is_prime_zero_dim())
}

///|
test "monomial primary decomposition: embedded prime example (x^2, xy)" {
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let ideal = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [1, 1])]),
  ])
  let d = pd_of(ideal)
  assert_eq(d.num_components(), 2)
  // (x^2, xy) = (x) ∩ (x^2, y), primes (x) and (x,y) -- the second is
  // embedded (strictly contains the first prime).
  assert_true(has_component(d, Ideal::new(2, [x]), Ideal::new(2, [x])))
  assert_true(
    has_component(d, Ideal::new(2, [x.pow(2), y]), Ideal::new(2, [x, y])),
  )
  assert_true(d.verify(ideal))
  let p1 = Ideal::new(2, [x])
  let p2 = Ideal::new(2, [x, y])
  assert_true(p1.is_subset_of(p2) && !p2.is_subset_of(p1))
  // sqrt(I) = (x), via decomposition and via the monomial formula.
  match ideal.radical_via_decomposition() {
    Some(r) => assert_true(r.equal_to(p1))
    None => assert_true(false)
  }
  match ideal.radical_of_monomial() {
    Some(r) => assert_true(r.equal_to(p1))
    None => assert_true(false)
  }
  // (xy) = (x) ∩ (y): two minimal primes, no embedded component.
  let axes = Ideal::new(2, [x.mul(y)])
  let d2 = pd_of(axes)
  assert_eq(d2.num_components(), 2)
  assert_true(d2.verify(axes))
  // A pure-power monomial principal ideal in 3 variables splits by
  // coprimality: (x^2 y z) = (x^2) ∩ (y) ∩ (z).
  let principal = Ideal::new(3, [Poly::from_int_terms(3, [(1, [2, 1, 1])])])
  let d3 = pd_of(principal)
  assert_eq(d3.num_components(), 3)
  assert_true(d3.verify(principal))
  // Already irreducible = already primary.
  let irr = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [0, 3])]),
  ])
  let d4 = pd_of(irr)
  assert_eq(d4.num_components(), 1)
  assert_true(has_component(d4, irr, Ideal::new(2, [x, y])))
}

///|
test "zero-dimensional primary decomposition incl. an F_49 point" {
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let one = Poly::one_poly(2)
  // Two rational points (±1, 0).
  let two = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-1, [0, 0])]),
    y,
  ])
  let d = pd_of(two)
  assert_eq(d.num_components(), 2)
  assert_true(
    has_component(
      d,
      Ideal::new(2, [x.sub(one), y]),
      Ideal::new(2, [x.sub(one), y]),
    ),
  )
  assert_true(
    has_component(
      d,
      Ideal::new(2, [x.add(one), y]),
      Ideal::new(2, [x.add(one), y]),
    ),
  )
  assert_true(d.verify(two))
  // Four rational points from (x^2-2, y^2-1): x = ±3 since 3^2 = 2.
  let four = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-2, [0, 0])]),
    Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])]),
  ])
  let d4 = pd_of(four)
  assert_eq(d4.num_components(), 4)
  assert_true(d4.verify(four))
  for c in d4.components() {
    assert_true(c.component().finite_dimension() is Some(1))
    assert_true(c.component().equal_to(c.prime()))
  }
  // A fat rational point: (x^2, y-1), radical (x, y-1), one component.
  let fat_pt = Ideal::new(2, [x.pow(2), y.sub(one)])
  let d5 = pd_of(fat_pt)
  assert_eq(d5.num_components(), 1)
  assert_true(has_component(d5, fat_pt, Ideal::new(2, [x, y.sub(one)])))
  assert_true(d5.verify(fat_pt))
  // The non-rational closed point with residue field F_49:
  // (x^2+1, y) is already prime over F_7 -- point enumeration over F_7
  // sees *no* point here, but Spec has one. Primary decomposition must
  // not (and does not) split it.
  let f49_pt = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (1, [0, 0])]),
    y,
  ])
  assert_eq(Variety::from_ideal(f49_pt).num_points(), 0)
  let d6 = pd_of(f49_pt)
  assert_eq(d6.num_components(), 1)
  assert_true(has_component(d6, f49_pt, f49_pt))
  assert_true(d6.verify(f49_pt))
  assert_true(f49_pt.finite_dimension() is Some(2))
}

///|
test "univariate primary decomposition and out-of-scope refusal" {
  let t = Poly::variable(1, 0)
  let one = Poly::one_poly(1)
  let g = t.sub(one).pow(2).mul(t.pow(2).add(one))
  let ideal = Ideal::new(1, [g])
  let d = pd_of(ideal)
  assert_eq(d.num_components(), 2)
  assert_true(
    has_component(
      d,
      Ideal::new(1, [t.sub(one).pow(2)]),
      Ideal::new(1, [t.sub(one)]),
    ),
  )
  assert_true(
    has_component(
      d,
      Ideal::new(1, [t.pow(2).add(one)]),
      Ideal::new(1, [t.pow(2).add(one)]),
    ),
  )
  assert_true(d.verify(ideal))
  // Positive-dimensional non-monomial ideals: documented refusal.
  let parabola = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  assert_true(primary_decomposition(parabola) is None)
  assert_true(primary_decomposition_monomial(parabola) is None)
  assert_true(primary_decomposition_zero_dim(parabola) is None)
}
