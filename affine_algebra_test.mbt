// Blackbox tests: public API only, imported explicitly as @affine_algebra.
// These intentionally re-derive a few headline facts from the outside, so
// the library cannot pass by exposing internals that only tests can reach.

///|
test "public API: field, ideal membership and dimensions" {
  assert_eq(@affine_algebra.PRIME, 7)
  let a = @affine_algebra.Fp::new(3)
  let b = @affine_algebra.Fp::new(5)
  assert_true(a * b == @affine_algebra.Fp::new(1))
  assert_true(a * a.inv() == @affine_algebra.Fp::one())
  let ideal = @affine_algebra.Ideal::new(2, [
    @affine_algebra.Poly::from_int_terms(2, [(1, [1, 1]), (-1, [0, 0])]),
    @affine_algebra.Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])]),
  ])
  let diff = @affine_algebra.Poly::variable(2, 0).sub(
    @affine_algebra.Poly::variable(2, 1),
  )
  assert_true(ideal.contains(diff))
  assert_true(!ideal.contains(@affine_algebra.Poly::variable(2, 0)))
  assert_true(ideal.finite_dimension() is Some(2))
  assert_eq(ideal.krull_dimension(), 0)
}

///|
test "public API: variety points and coordinate interpolation" {
  let circle = @affine_algebra.Variety::from_generators(2, [
    @affine_algebra.Poly::from_int_terms(2, [
      (1, [2, 0]),
      (1, [0, 2]),
      (-1, [0, 0]),
    ]),
  ])
  assert_eq(circle.num_points(), 8)
  let cr = circle.coordinate_ring()
  let alg = cr.algebra()
  // An arbitrary function table on the 8 points comes from a polynomial.
  let table = alg.elem([
    @affine_algebra.Fp::new(1),
    @affine_algebra.Fp::new(2),
    @affine_algebra.Fp::new(3),
    @affine_algebra.Fp::new(4),
    @affine_algebra.Fp::new(5),
    @affine_algebra.Fp::new(6),
    @affine_algebra.Fp::new(0),
    @affine_algebra.Fp::new(2),
  ])
  let p = cr.poly_of_function(table)
  assert_true(cr.of_poly(p).equal_to(table))
}

///|
test "public API: quotient nilpotent and local ring at a point" {
  let q = @affine_algebra.QuotientRing::from_generators(1, [
    @affine_algebra.Poly::from_int_terms(1, [(1, [2])]),
  ])
  let t = q.variable(0)
  assert_true(!t.is_zero())
  assert_true(q.mul(t, t).is_zero())
  let lring = @affine_algebra.LocalRingAtPoint::new(
    @affine_algebra.Pt::new([@affine_algebra.Fp::new(2)]),
  )
  // (t+1)/(t+3) at t=2 has residue 3/5 = 3*3 = 2 in F_7 (5^{-1} = 3).
  let num = @affine_algebra.Poly::from_int_terms(1, [(1, [1]), (1, [0])])
  let den = @affine_algebra.Poly::from_int_terms(1, [(1, [1]), (3, [0])])
  match lring.frac(num, den) {
    Some(fr) => {
      assert_true(lring.residue(fr) == @affine_algebra.Fp::new(2))
      assert_true(lring.is_unit(fr))
    }
    None => assert_true(false)
  }
  // Denominator t-2 vanishes at the point: refused.
  let bad = @affine_algebra.Poly::from_int_terms(1, [(1, [1]), (-2, [0])])
  assert_true(lring.frac(num, bad) is None)
}
