// Tests for localization: polynomial rings, non-domain quotients where
// the saturation subtlety decides equality, nilpotent denominators,
// the Rabinowitsch isomorphism, local rings at points, and the universal
// property as an iff (extension exists exactly when f maps to a unit).

///|
test "localization of a polynomial ring at powers of x" {
  let x = Poly::variable(2, 0)
  let loc = LocalizedRing::of_polynomial_ring(x)
  // In a domain (0 : x^infinity) = (0): kernel of R -> R_x is zero.
  assert_true(loc.saturation_ideal().is_zero_ideal())
  assert_true(!loc.is_zero_ring())
  // f/1 · 1/f = 1, the defining gain over the polynomial ring.
  let fx = loc.of_poly(x)
  assert_true(loc.equal_to(loc.mul(fx, loc.inv_denom()), loc.one_elem()))
  let rng = Rng::new(13579)
  for _ in 0..<60 {
    let a = loc.frac(Poly::pseudo_random(rng, 2, 3, 2), rng.range(0, 2))
    let b = loc.frac(Poly::pseudo_random(rng, 2, 3, 2), rng.range(0, 2))
    let c = loc.frac(Poly::pseudo_random(rng, 2, 2, 2), rng.range(0, 1))
    // Ring axioms modulo the fraction equality relation.
    assert_true(loc.equal_to(loc.add(a, b), loc.add(b, a)))
    assert_true(
      loc.equal_to(
        loc.mul(a, loc.add(b, c)),
        loc.add(loc.mul(a, b), loc.mul(a, c)),
      ),
    )
    assert_true(loc.is_zero(loc.sub(a, a)))
    // Expanding a fraction by an extra factor f does not change it.
    let expanded = loc.frac(a.num.mul(x), a.power + 1)
    assert_true(loc.equal_to(a, expanded))
    // Numerators detect zero exactly (domain case).
    assert_true(loc.is_zero(a) == a.num.is_zero())
  }
}

///|
test "non-domain quotient: equality in S^-1(R/I) needs the saturation" {
  // R = k[x,y]/(xy): x and y are zero divisors. Localize at {x^k}.
  // (xy : x^infinity) = (y), so y/1 = 0 in the localization although
  // y != 0 in R. Plain cross-multiplication in R would miss this:
  // y ∉ (xy), but x·y ∈ (xy). This is the existential factor from S.
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let ring = QuotientRing::from_generators(2, [x.mul(y)])
  assert_true(!ring.of_poly(y).is_zero())
  assert_true(ring.mul(ring.of_poly(x), ring.of_poly(y)).is_zero())
  let loc = LocalizedRing::new(ring, x)
  assert_true(loc.saturation_ideal().equal_to(Ideal::new(2, [y])))
  assert_true(loc.is_zero(loc.of_poly(y)))
  assert_true(loc.equal_to(loc.of_poly(y), loc.zero_elem()))
  // But 1 and x survive (D(x) meets the variety in the x-axis punctured).
  assert_true(!loc.is_zero(loc.one_elem()))
  assert_true(!loc.is_zero(loc.of_poly(x)))
  assert_true(
    loc.equal_to(loc.mul(loc.of_poly(x), loc.inv_denom()), loc.one_elem()),
  )
  // Kernel of R/I -> S^-1(R/I) is (I:x^∞)/I: membership test both ways
  // on samples, including y multiples that only die after one x-factor.
  let rng = Rng::new(24680)
  for _ in 0..<40 {
    let g = Poly::pseudo_random(rng, 2, 3, 2)
    assert_true(loc.is_zero(loc.of_poly(g.mul(y))))
    let h = Poly::pseudo_random(rng, 2, 2, 2)
    assert_true(
      loc.is_zero(loc.of_poly(h)) == loc.saturation_ideal().contains(h),
    )
  }
  // Geometry agrees: coordinate ring of the axes localized at the
  // x-function has dimension |D(x) ∩ axes| = 6.
  let axes = Variety::from_generators(2, [x.mul(y)])
  assert_eq(axes.num_points(), 13)
  let cr = axes.coordinate_ring()
  let ftab = cr.coordinate_function(0)
  let finloc = cr.algebra().localize_at(ftab, "k[axes]_x")
  assert_eq(finloc.algebra().dim(), axes.principal_open_points(x).length())
  assert_eq(finloc.algebra().dim(), 6)
  assert_eq(axes.principal_open_as_variety(x).num_points(), 6)
  assert_true(finloc.algebra().is_unit(finloc.project(ftab)))
}

///|
test "inverting a nilpotent gives the zero ring -- detected, not hidden" {
  // R = k[t]/(t^2), localize at t: t nilpotent => S^-1 R = 0 and 1 = 0.
  let t = Poly::variable(1, 0)
  let ring = QuotientRing::from_generators(1, [t.pow(2)])
  let loc = LocalizedRing::new(ring, t)
  assert_true(loc.is_zero_ring())
  assert_true(loc.equal_to(loc.one_elem(), loc.zero_elem()))
  let rng = Rng::new(999)
  for _ in 0..<20 {
    let a = loc.frac(Poly::pseudo_random(rng, 1, 2, 2), rng.range(0, 2))
    assert_true(loc.is_zero(a))
  }
  // The Rabinowitsch quotient k[t,s]/(t^2, s t - 1) is likewise the zero
  // ring: its ideal contains 1 = s^2 t^2 - (st-1)(st+1).
  let iso = RabinowitschIso::new(loc)
  assert_true(iso.quotient_ring().ideal().is_unit_ideal())
  assert_true(iso.forward(loc.one_elem()).is_zero())
}

///|
test "Rabinowitsch: S^-1(R/I) ≅ R[t]/(I, tf-1), both directions inverse" {
  // R = k[x,y]/(y - x^2) (parabola ring, a domain), localize at x.
  let x = Poly::variable(2, 0)
  let ring = QuotientRing::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  let loc = LocalizedRing::new(ring, x)
  let iso = RabinowitschIso::new(loc)
  let q = iso.quotient_ring()
  // The relation really holds in the quotient: t*x = 1 for t = variable 2.
  let t_cos = q.variable(2)
  let x_cos = q.variable(0)
  assert_true(q.mul(t_cos, x_cos).equal_to(q.one_coset()))
  assert_true(!t_cos.is_zero())
  let rng = Rng::new(777777)
  for _ in 0..<40 {
    let a = loc.frac(Poly::pseudo_random(rng, 2, 3, 2), rng.range(0, 2))
    let b = loc.frac(Poly::pseudo_random(rng, 2, 3, 2), rng.range(0, 2))
    // Forward is a homomorphism.
    assert_true(
      iso.forward(loc.add(a, b)).equal_to(q.add(iso.forward(a), iso.forward(b))),
    )
    assert_true(
      iso.forward(loc.mul(a, b)).equal_to(q.mul(iso.forward(a), iso.forward(b))),
    )
    // Backward after forward is the identity on the localized ring.
    assert_true(loc.equal_to(iso.backward(iso.forward(a)), a))
    // Forward respects the fraction equality relation (expansion by x).
    let expanded = loc.frac(a.num.mul(x), a.power + 1)
    assert_true(iso.forward(a).equal_to(iso.forward(expanded)))
    // Forward after backward is the identity on the quotient.
    let g = q.of_poly(Poly::pseudo_random(rng, 3, 3, 2))
    assert_true(iso.forward(iso.backward(g)).equal_to(g))
  }
}

///|
test "local ring at a point: units, maximal ideal, residue field" {
  let ring = LocalRingAtPoint::new(Pt::new([Fp::new(1), Fp::new(2)]))
  let x = Poly::variable(2, 0)
  // Denominators must not vanish at (1,2): x is fine, x-1 is refused.
  assert_true(ring.frac(Poly::one_poly(2), x) is Some(_))
  let xm1 = x.sub(Poly::one_poly(2))
  assert_true(ring.frac(Poly::one_poly(2), xm1) is None)
  let pt = [Fp::new(1), Fp::new(2)]
  let rng = Rng::new(11235)
  for _ in 0..<60 {
    // Random legal fractions: shift denominators to be nonzero at pt.
    let mk = fn() {
      let num = Poly::pseudo_random(rng, 2, 3, 2)
      let mut den = Poly::pseudo_random(rng, 2, 2, 2)
      if den.eval(pt).is_zero() {
        den = den.add(Poly::one_poly(2))
      }
      match ring.frac(num, den) {
        Some(fr) => fr
        None => abort("shifted denominator must be legal")
      }
    }
    let a = mk()
    let b = mk()
    // Residue map is a homomorphism onto F_7.
    assert_true(
      ring.residue(ring.add(a, b)) == ring.residue(a) + ring.residue(b),
    )
    assert_true(
      ring.residue(ring.mul(a, b)) == ring.residue(a) * ring.residue(b),
    )
    // Kernel of the residue map = maximal ideal = non-units.
    assert_true(ring.in_maximal_ideal(a) == ring.residue(a).is_zero())
    assert_true(ring.is_unit(a) == !ring.in_maximal_ideal(a))
    match ring.try_inv(a) {
      Some(inv) =>
        assert_true(
          ring.equal_to(ring.mul(a, inv), ring.of_poly(Poly::one_poly(2))),
        )
      None => assert_true(ring.in_maximal_ideal(a))
    }
    // The non-units form an ideal (the local ring property, on samples):
    // take a numerator vanishing at pt, viz. g - g(pt).
    let g = Poly::pseudo_random(rng, 2, 3, 2)
    let vanishing = g.sub(Poly::constant(2, g.eval(pt)))
    let m_elt = match ring.frac(vanishing, a.den) {
      Some(fr) => fr
      None => abort("denominator reuse must stay legal")
    }
    assert_true(ring.in_maximal_ideal(m_elt))
    assert_true(ring.in_maximal_ideal(ring.add(m_elt, m_elt)))
    assert_true(ring.in_maximal_ideal(ring.mul(m_elt, b)))
  }
}

///|
test "universal property of localization as an iff, finite targets" {
  let x = Poly::variable(1, 0)
  let loc = LocalizedRing::of_polynomial_ring(x)
  let frac_v = loc.frac(Poly::from_int_terms(1, [(1, [2]), (1, [0])]), 1) // (t^2+1)/t
  let ground = FinAlg::ground_field()
  // Evaluation at t=3 (x maps to a unit): extension exists, value is
  // (9+1)/3 = 10/3 = 3 * 5 = 15 = 1 in F_7? 10=3, 3^{-1}=5, so 3*5=15=1.
  let at3 = ground.elem([Fp::new(3)])
  match extend_over_principal_localization(loc, ground, [at3], frac_v) {
    Some(v) => assert_true(v.equal_to(ground.elem([Fp::new(1)])))
    None => assert_true(false)
  }
  // Evaluation at t=0 (x maps to 0, not a unit): NO extension exists.
  let at0 = ground.elem([Fp::new(0)])
  assert_true(
    extend_over_principal_localization(loc, ground, [at0], frac_v) is None,
  )
  // In F^2: image (2,0) is a zero divisor, not a unit -> no extension;
  // image (2,3) is a unit -> extension, computed componentwise.
  let f2 = FinAlg::function_algebra("F^2", 2)
  let bad = f2.elem([Fp::new(2), Fp::new(0)])
  assert_true(
    extend_over_principal_localization(loc, f2, [bad], frac_v) is None,
  )
  let good = f2.elem([Fp::new(2), Fp::new(3)])
  match extend_over_principal_localization(loc, f2, [good], frac_v) {
    Some(v) =>
      // ((4+1)/2, (9+1)/3) = (5*4, 1) = (20, 1) = (6, 1) in F_7.
      assert_true(v.equal_to(f2.elem([Fp::new(6), Fp::new(1)])))
    None => assert_true(false)
  }
}
