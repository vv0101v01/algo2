// API-completeness and checker negative-control tests. These exist because
// the coverage report flagged public functions that no theorem test had
// exercised: untested code is where decorative implementations hide.

///|
test "operator overloads and display paths agree with method paths" {
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let f = x + y
  let g = x - y
  assert_true(f.equal_to(x.add(y)))
  assert_true(g.equal_to(x.sub(y)))
  assert_true((f * g).equal_to(x.pow(2).sub(y.pow(2))))
  assert_eq(Poly::zero(2).display(), "0")
  assert_eq(x.pow(2).add(Poly::constant(2, Fp::new(3))).display(), "x^2 + 3")
  assert_eq(Fp::new(6).display(), "6")
  assert_eq(vec_display([Fp::new(1), Fp::new(2)]), "[1, 2]")
  let pt = Pt::new([Fp::new(1), Fp::new(2)])
  assert_eq(pt.display(), "([1, 2])")
  let a = FinAlg::function_algebra("F^2", 2)
  let e = a.sub(a.basis_elem(0), a.basis_elem(1))
  assert_eq(e.display(), "[1, 6]")
  let m = Matrix::from_rows([[Fp::new(1), Fp::new(2)], [Fp::new(3), Fp::new(4)]])
  assert_eq(m.display(), "[1, 2]; [3, 4]")
  assert_true(m.get(1, 0) == Fp::new(3))
  assert_true(vec_eq(m.row(0), [Fp::new(1), Fp::new(2)]))
}

///|
test "matrix transpose and coordinates_in_basis are real" {
  let a = Matrix::from_rows([[Fp::new(1), Fp::new(2)], [Fp::new(3), Fp::new(4)]])
  let b = Matrix::from_rows([[Fp::new(0), Fp::new(1)], [Fp::new(5), Fp::new(6)]])
  assert_true(a.transpose().transpose().equal_to(a))
  assert_true(a.mul(b).transpose().equal_to(b.transpose().mul(a.transpose())))
  // Coordinates: v = 2*(1,1) + 3*(1,0) = (5,2).
  let basis = [[Fp::new(1), Fp::new(1)], [Fp::new(1), Fp::new(0)]]
  match coordinates_in_basis([Fp::new(5), Fp::new(2)], basis) {
    Some(cs) => assert_true(vec_eq(cs, [Fp::new(2), Fp::new(3)]))
    None => assert_true(false)
  }
  // A vector outside a non-spanning set has no coordinates.
  assert_true(
    coordinates_in_basis([Fp::new(0), Fp::new(1)], [[Fp::new(1), Fp::new(0)]])
    is None,
  )
  assert_eq(span_basis([]).length(), 0)
}

///|
test "quotient evaluate/scale/pow and localized of_coset" {
  let q = QuotientRing::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  let xb = q.variable(0)
  // evaluate(t^2 + 1, [xbar]) where the expression is univariate over the
  // placeholder variable, must equal xbar^2 + 1 = ybar + 1 in the quotient.
  let expr = Poly::from_int_terms(1, [(1, [2]), (1, [0])])
  let value = q.evaluate(expr, [xb])
  let expected = q.of_poly(Poly::variable(2, 1).add(Poly::one_poly(2)))
  assert_true(value.equal_to(expected))
  assert_true(q.pow(xb, 2).equal_to(q.variable(1)))
  assert_true(
    q
    .scale(Fp::new(3), xb)
    .equal_to(q.of_poly(Poly::variable(2, 0).scale(Fp::new(3)))),
  )
  assert_true(
    q.scalar(Fp::new(4)).equal_to(q.of_poly(Poly::constant(2, Fp::new(4)))),
  )
  assert_true(q.zero_coset().is_zero())
  // of_coset lands in the localization as numerator class / 1.
  let loc = LocalizedRing::new(q, Poly::variable(2, 0))
  let via_coset = loc.of_coset(q.variable(1))
  assert_true(loc.equal_to(via_coset, loc.of_poly(Poly::variable(2, 1))))
  assert_eq(
    loc.frac(Poly::variable(2, 1), 2).display(Poly::variable(2, 0)),
    "(y)/(x)^2",
  )
  // Local ring subtraction.
  let lring = LocalRingAtPoint::new(Pt::new([Fp::new(1)]))
  let u = lring.of_poly(Poly::from_int_terms(1, [(1, [1]), (1, [0])]))
  let v = lring.of_poly(Poly::variable(1, 0))
  assert_true(lring.residue(lring.sub(u, v)) == Fp::new(1))
  assert_true(lring.equal_to(lring.sub(u, u), lring.of_poly(Poly::zero(1))))
}

///|
test "unit-ideal staircase is empty; zero quotient model has dimension 0" {
  let unit = Ideal::unit_ideal(2)
  assert_true(unit.standard_monomials() is Some([]))
  assert_true(unit.finite_dimension() is Some(0))
  let q = QuotientRing::new(unit)
  let model = match QuotientModel::new(q, "0-ring") {
    Some(m) => m
    None => abort("zero ring is finite-dimensional")
  }
  assert_eq(model.algebra().dim(), 0)
  assert_true(model.algebra().check_axioms())
  assert_true(q.of_poly(Poly::variable(2, 0)).is_zero())
  assert_true(
    model.to_coset(model.algebra().one_elem()).equal_to(q.zero_coset()),
  )
}

///|
test "check_axioms and is_isomorphism actually reject bad input" {
  // Fake "algebra": zero multiplication table with one = e_0. 1*e_1 = 0.
  let d = 2
  let mult : Array[Fp] = []
  for _ in 0..<(d * d * d) {
    mult.push(Fp::zero())
  }
  let fake = FinAlg::from_structure("fake", d, mult, [Fp::one(), Fp::zero()])
  assert_true(!fake.check_axioms())
  assert_eq(fake.name(), "fake")
  // A genuine homomorphism that is not invertible: evaluation k^2 -> k.
  let f2 = FinAlg::function_algebra("F^2", 2)
  let f1 = FinAlg::ground_field()
  let eval0 = AlgHom::from_basis_images([
    f1.elem([Fp::one()]),
    f1.elem([Fp::zero()]),
  ])
  assert_true(eval0.verify(f2, f1))
  assert_true(!eval0.is_isomorphism(f2, f1))
  // ideal_basis_of with two generators spans two delta ideals.
  let f3 = FinAlg::function_algebra("F^3", 3)
  let ideal = f3.ideal_basis_of([f3.basis_elem(0), f3.basis_elem(1)])
  assert_eq(ideal.length(), 2)
  let quot = f3.quotient_by_subspace(ideal, "F^3/(d0,d1)")
  assert_eq(quot.algebra().dim(), 1)
}

///|
test "point-set equality, deduplication and empty coordinate ring details" {
  let pts = [
    Pt::new([Fp::new(1), Fp::new(1)]),
    Pt::new([Fp::new(0), Fp::new(0)]),
    Pt::new([Fp::new(1), Fp::new(1)]),
  ]
  let v = Variety::from_points(2, pts)
  assert_eq(v.num_points(), 2)
  let v2 = Variety::from_points(2, [
    Pt::new([Fp::new(0), Fp::new(0)]),
    Pt::new([Fp::new(1), Fp::new(1)]),
  ])
  assert_true(v.same_point_set(v2))
  let v3 = Variety::from_points(2, [Pt::new([Fp::new(0), Fp::new(0)])])
  assert_true(!v.same_point_set(v3))
  let cr = v.coordinate_ring()
  assert_eq(cr.num_points(), 2)
  let empty_cr = Variety::empty(2).coordinate_ring()
  assert_true(
    empty_cr.poly_of_function(empty_cr.algebra().zero_elem()).is_zero(),
  )
  // Type-level leftovers flagged by coverage.
  let p = Prod::new(3, "z")
  assert_eq(p.fst, 3)
  let dist_left : Prod[Int32, Sum[Int32, String]] = { fst: 2, snd: Inl(5), }
  match distribute(dist_left) {
    Inl(pr) => assert_true(pr.fst == 2 && pr.snd == 5)
    Inr(_) => assert_true(false)
  }
}

///|
test "regression: pullback into the zero coordinate ring keeps matrix width" {
  // X empty, Y = A^1: pullback k[Y] -> k[X] = 0 is the unique hom into
  // the zero ring; its matrix is 0 x 7. Previously from_basis_images
  // collapsed this to 0x0 and verify wrongly rejected it.
  let empty_x = Variety::empty(1)
  let line = Variety::affine_space(1)
  let crx = empty_x.coordinate_ring()
  let crl = line.coordinate_ring()
  let hom = pullback_hom(PolyMap::identity(1), empty_x, line, crx, crl)
  assert_eq(hom.matrix().num_rows(), 0)
  assert_eq(hom.matrix().num_cols(), 7)
  assert_true(hom.verify(crl.algebra(), crx.algebra()))
  // FinAlg quotient edge cases: localize at 0 (zero ring) and at 1 (identity).
  let a = FinAlg::function_algebra("F^3", 3)
  let at_zero = a.localize_at(a.zero_elem(), "A_0")
  assert_eq(at_zero.algebra().dim(), 0)
  let at_one = a.localize_at(a.one_elem(), "A_1")
  assert_eq(at_one.algebra().dim(), 3)
  let qzero = a.quotient_by_subspace([], "A/0")
  assert_eq(qzero.algebra().dim(), 3)
}
