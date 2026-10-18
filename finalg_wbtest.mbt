// Tests for linear algebra, quotient rings and finite algebras.
// Conventions: claimed homomorphisms/isomorphisms are *verified* by
// AlgHom::verify / is_isomorphism (unit + all basis products + inverse),
// never merely asserted true.

///|
test "linear algebra: solve, inverse, nullspace are exact" {
  // A = [[2,1],[1,1]] over F_7, det = 1.
  let a = Matrix::from_rows([[Fp::new(2), Fp::new(1)], [Fp::new(1), Fp::new(1)]])
  match a.inverse() {
    Some(inv) => assert_true(a.mul(inv).equal_to(Matrix::identity(2)))
    None => assert_true(false)
  }
  match a.solve([Fp::new(1), Fp::new(0)]) {
    Some(x) => assert_true(vec_eq(x, [Fp::new(1), Fp::new(6)]))
    None => assert_true(false)
  }
  // Singular matrix: rows proportional.
  let s = Matrix::from_rows([[Fp::new(1), Fp::new(2)], [Fp::new(2), Fp::new(4)]])
  assert_true(s.inverse() is None)
  assert_eq(s.rank(), 1)
  let ker = s.nullspace()
  assert_eq(ker.length(), 1)
  assert_true(vec_is_zero(s.mul_vec(ker[0])))
  assert_true(!vec_is_zero(ker[0]))
  // Inconsistent system has no solution; consistent one does.
  assert_true(s.solve([Fp::new(1), Fp::new(1)]) is None)
  assert_true(s.solve([Fp::new(1), Fp::new(2)]) is Some(_))
}

///|
test "quotient ring: representative independence is real, nilpotents exist" {
  let gens = [
    Poly::from_int_terms(2, [(1, [2, 0]), (-1, [0, 0])]),
    Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])]),
  ]
  let q = QuotientRing::from_generators(2, gens)
  let xb = q.variable(0)
  let yb = q.variable(1)
  assert_true(q.mul(xb, xb).equal_to(q.one_coset()))
  assert_true(q.mul(yb, yb).equal_to(q.one_coset()))
  assert_true(!xb.equal_to(q.one_coset()))
  // Changing representatives by random ideal multiples must not change
  // any coset operation -- this is well-definedness of R/I, tested.
  let rng = Rng::new(99)
  for _ in 0..<80 {
    let f = Poly::pseudo_random(rng, 2, 3, 3)
    let g = Poly::pseudo_random(rng, 2, 3, 3)
    let h1 = Poly::pseudo_random(rng, 2, 2, 2)
    let h2 = Poly::pseudo_random(rng, 2, 2, 2)
    let f2 = f.add(h1.mul(gens[0]).add(h2.mul(gens[1])))
    assert_true(q.of_poly(f).equal_to(q.of_poly(f2)))
    assert_true(
      q
      .mul(q.of_poly(f), q.of_poly(g))
      .equal_to(q.mul(q.of_poly(f2), q.of_poly(g))),
    )
    // Ker(F_p[x] -> R/I) = I, exactly.
    assert_true(q.of_poly(f).is_zero() == q.ideal().contains(f))
  }
  // Non-reduced quotient k[t]/(t^2): tbar != 0 but tbar^2 = 0. A model
  // that only kept *points* would lose this element; quotients keep it.
  let fat = QuotientRing::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2])]),
  ])
  let t = fat.variable(0)
  assert_true(!t.is_zero())
  assert_true(fat.mul(t, t).is_zero())
  assert_true(fat.finite_dimension() is Some(2))
  assert_eq(fat.krull_dimension(), 0)
}

///|
test "quotient model: staircase basis gives the same ring" {
  let q = QuotientRing::from_generators(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-2, [0, 0])]),
    Poly::from_int_terms(2, [(1, [0, 2]), (1, [0, 1]), (1, [0, 0])]),
  ])
  let model = match QuotientModel::new(q, "Q") {
    Some(m) => m
    None => abort("expected finite-dimensional quotient")
  }
  let a = model.algebra()
  assert_eq(a.dim(), 4)
  assert_true(a.check_axioms())
  // Round trips and multiplicativity of the identification.
  let rng = Rng::new(4242)
  for _ in 0..<60 {
    let f = q.of_poly(Poly::pseudo_random(rng, 2, 3, 3))
    let g = q.of_poly(Poly::pseudo_random(rng, 2, 3, 3))
    assert_true(model.to_coset(model.to_elem(f)).equal_to(f))
    assert_true(
      model
      .to_elem(q.mul(f, g))
      .equal_to(a.mul(model.to_elem(f), model.to_elem(g))),
    )
    assert_true(
      model
      .to_elem(q.add(f, g))
      .equal_to(a.add(model.to_elem(f), model.to_elem(g))),
    )
  }
  // Infinite-dimensional quotients refuse a finite model (honest None).
  let curve = QuotientRing::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  assert_true(QuotientModel::new(curve, "curve") is None)
}

///|
fn univ_source() -> QuotientModel {
  // C = F_7[t]/(t^2-1), dim 2, basis monomials [t, 1] (lex decreasing).
  let q = QuotientRing::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (-1, [0])]),
  ])
  match QuotientModel::new(q, "C") {
    Some(m) => m
    None => abort("univ_source: expected finite")
  }
}

///|
test "direct product of algebras: universal property with negative control" {
  let cm = univ_source()
  let c = cm.algebra()
  let a = FinAlg::function_algebra("F^2", 2)
  let b = FinAlg::function_algebra("F^3", 3)
  // Homs C -> function algebras: image of t must be a function squaring to
  // 1, i.e. valued in {+1,-1}. Basis of C is [t, 1].
  let phi = AlgHom::from_basis_images([
    a.elem([Fp::new(1), Fp::new(6)]),
    a.elem([Fp::new(1), Fp::new(1)]),
  ])
  let psi = AlgHom::from_basis_images([
    b.elem([Fp::new(6), Fp::new(1), Fp::new(6)]),
    b.elem([Fp::new(1), Fp::new(1), Fp::new(1)]),
  ])
  assert_true(phi.verify(c, a))
  assert_true(psi.verify(c, b))
  // Negative control: t |-> (1,2) is NOT a homomorphism (2^2 != 1).
  let bad = AlgHom::from_basis_images([
    a.elem([Fp::new(1), Fp::new(2)]),
    a.elem([Fp::new(1), Fp::new(1)]),
  ])
  assert_true(!bad.verify(c, a))
  // Pairing into the product, and projections back: uniqueness made
  // concrete as matrix equalities proj_A ∘ pair = phi, proj_B ∘ pair = psi.
  let p = FinAlg::product(a, b, "F^2 x F^3")
  assert_eq(p.dim(), 5)
  assert_true(p.check_axioms())
  let pair = AlgHom::from_basis_images([
    p.elem([Fp::new(1), Fp::new(6), Fp::new(6), Fp::new(1), Fp::new(6)]),
    p.elem([Fp::new(1), Fp::new(1), Fp::new(1), Fp::new(1), Fp::new(1)]),
  ])
  assert_true(pair.verify(c, p))
  let proj_a = AlgHom::from_basis_images([
    a.basis_elem(0),
    a.basis_elem(1),
    a.zero_elem(),
    a.zero_elem(),
    a.zero_elem(),
  ])
  // Wait: projections must send 1_P = (1,1) to 1_A: with delta bases the
  // first two basis vectors map to e_0,e_1 and the rest to 0, and indeed
  // 1 |-> e_0 + e_1 = 1_A. Verify checks this; do not take it on faith.
  assert_true(proj_a.verify(p, a))
  let proj_b = AlgHom::from_basis_images([
    b.zero_elem(),
    b.zero_elem(),
    b.basis_elem(0),
    b.basis_elem(1),
    b.basis_elem(2),
  ])
  assert_true(proj_b.verify(p, b))
  assert_true(proj_a.compose(pair).matrix().equal_to(phi.matrix()))
  assert_true(proj_b.compose(pair).matrix().equal_to(psi.matrix()))
  // Orthogonal idempotents of the product decomposition.
  let e1 = p.elem([Fp::new(1), Fp::new(1), Fp::new(0), Fp::new(0), Fp::new(0)])
  let e2 = p.elem([Fp::new(0), Fp::new(0), Fp::new(1), Fp::new(1), Fp::new(1)])
  assert_true(p.mul(e1, e1).equal_to(e1))
  assert_true(p.mul(e1, e2).equal_to(p.zero_elem()))
  assert_true(p.add(e1, e2).equal_to(p.one_elem()))
}

///|
test "tensor product: bilinearity, inclusions, dimension multiplicativity" {
  let a = FinAlg::function_algebra("F^2", 2)
  let b = FinAlg::function_algebra("F^3", 3)
  let t = FinAlg::tensor(a, b, "F^2 (x) F^3")
  assert_eq(t.dim(), 6)
  assert_true(t.check_axioms())
  let rng = Rng::new(31337)
  for _ in 0..<60 {
    let x1 = a.random_elem(rng)
    let x2 = a.random_elem(rng)
    let y1 = b.random_elem(rng)
    let y2 = b.random_elem(rng)
    let c = rng.fp()
    // Bilinearity relations that *define* the tensor product quotient.
    assert_true(
      pure_tensor(b, t, a.add(x1, x2), y1).equal_to(
        t.add(pure_tensor(b, t, x1, y1), pure_tensor(b, t, x2, y1)),
      ),
    )
    assert_true(
      pure_tensor(b, t, a.scale(c, x1), y1).equal_to(
        pure_tensor(b, t, x1, b.scale(c, y1)),
      ),
    )
    // Algebra structure: (x⊗y)(x'⊗y') = xx' ⊗ yy'.
    assert_true(
      t
      .mul(pure_tensor(b, t, x1, y1), pure_tensor(b, t, x2, y2))
      .equal_to(pure_tensor(b, t, a.mul(x1, x2), b.mul(y1, y2))),
    )
  }
  // Inclusions A -> A⊗B, a |-> a⊗1 (coproduct injections) are homomorphisms.
  let incl = AlgHom::from_basis_images([
    pure_tensor(b, t, a.basis_elem(0), b.one_elem()),
    pure_tensor(b, t, a.basis_elem(1), b.one_elem()),
  ])
  assert_true(incl.verify(a, t))
  // Universal property instance: the bilinear map (delta_i, delta_j) |->
  // delta_{(i,j)} into F^{2x3} factors through an *algebra isomorphism*
  // F^2 ⊗ F^3 ≅ F^6. verify+inverse make this a checked proof.
  let f6 = FinAlg::function_algebra("F^6", 6)
  let lin = AlgHom::from_basis_images([
    f6.basis_elem(0),
    f6.basis_elem(1),
    f6.basis_elem(2),
    f6.basis_elem(3),
    f6.basis_elem(4),
    f6.basis_elem(5),
  ])
  assert_true(lin.is_isomorphism(t, f6))
}

///|
test "tensor of polynomial quotients = quotient in disjoint variables" {
  // A = k[x]/(x^2-2), B = k[y]/(y^2+y+1); A⊗B vs k[x,y]/(x^2-2, y^2+y+1).
  let qa = QuotientRing::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (-2, [0])]),
  ])
  let qb = QuotientRing::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (1, [1]), (1, [0])]),
  ])
  let ma = match QuotientModel::new(qa, "A") {
    Some(m) => m
    None => abort("A finite expected")
  }
  let mb = match QuotientModel::new(qb, "B") {
    Some(m) => m
    None => abort("B finite expected")
  }
  let tensor = FinAlg::tensor(ma.algebra(), mb.algebra(), "A (x) B")
  let qab = QuotientRing::from_generators(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-2, [0, 0])]),
    Poly::from_int_terms(2, [(1, [0, 2]), (1, [0, 1]), (1, [0, 0])]),
  ])
  let mab = match QuotientModel::new(qab, "AB") {
    Some(m) => m
    None => abort("AB finite expected")
  }
  assert_eq(tensor.dim(), mab.algebra().dim())
  // Candidate iso: tensor basis monomial x^i ⊗ y^j |-> coset of x^i y^j.
  let images : Array[FinElem] = []
  for mx in ma.basis_monomials() {
    for my in mb.basis_monomials() {
      let cos = qab.of_poly(
        Poly::monomial(2, Fp::one(), [mx.exp_at(0), my.exp_at(0)]),
      )
      images.push(mab.to_elem(cos))
    }
  }
  let iso = AlgHom::from_basis_images(images)
  assert_true(iso.is_isomorphism(tensor, mab.algebra()))
  // Negative control: scrambling the basis images breaks multiplicativity.
  let scrambled : Array[FinElem] = []
  for im in images {
    scrambled.push(im)
  }
  let tmp = scrambled[0]
  scrambled[0] = scrambled[1]
  scrambled[1] = tmp
  assert_true(
    !AlgHom::from_basis_images(scrambled).verify(tensor, mab.algebra()),
  )
}

///|
test "quotient of a finite algebra: kernel description + first isomorphism shape" {
  let a = FinAlg::function_algebra("F^3", 3)
  // Ideal of functions supported only at point 0: principal ideal (delta_0).
  let ideal = a.principal_ideal_basis(a.basis_elem(0))
  assert_eq(ideal.length(), 1)
  assert_true(a.is_ideal_subspace(ideal))
  // Non-ideal subspace must be detected: span{delta_0 + delta_1} in F^2.
  let a2 = FinAlg::function_algebra("F^2", 2)
  assert_true(!a2.is_ideal_subspace([[Fp::new(1), Fp::new(1)]]))
  let qt = a.quotient_by_subspace(ideal, "F^3/(delta_0)")
  let qa = qt.algebra()
  assert_eq(qa.dim(), 2)
  assert_true(qa.check_axioms())
  assert_true(qt.as_hom(a).verify(a, qa))
  // Kernel = exactly the functions vanishing at points 1 and 2.
  let rng = Rng::new(555)
  for _ in 0..<80 {
    let x = a.random_elem(rng)
    let cs = x.coords()
    let in_kernel = cs[1].is_zero() && cs[2].is_zero()
    assert_true(qt.project(x).equal_to(qa.zero_elem()) == in_kernel)
  }
  // Induced map from the quotient onto F^2 (restriction to points {1,2})
  // is an isomorphism -- first isomorphism theorem, checked.
  let f2 = FinAlg::function_algebra("F^2", 2)
  let induced = AlgHom::from_basis_images([f2.basis_elem(0), f2.basis_elem(1)])
  assert_true(induced.is_isomorphism(qa, f2))
}

///|
test "localization of a finite algebra: A_f = A / stable kernel, f becomes a unit" {
  let a = FinAlg::function_algebra("F^3", 3)
  // f vanishes at point 0, nonzero at 1, 2: D(f) = {1, 2}.
  let f = a.elem([Fp::new(0), Fp::new(2), Fp::new(3)])
  assert_true(!a.is_unit(f))
  let loc = a.localize_at(f, "(F^3)_f")
  let la = loc.algebra()
  assert_eq(la.dim(), 2)
  assert_true(la.check_axioms())
  assert_true(loc.as_hom(a).verify(a, la))
  let fbar = loc.project(f)
  match la.try_inv(fbar) {
    Some(inv) => assert_true(la.mul(fbar, inv).equal_to(la.one_elem()))
    None => assert_true(false)
  }
  // Kernel of A -> A_f: functions supported on the zero set Z(f) = {0}.
  let rng = Rng::new(8080)
  for _ in 0..<80 {
    let x = a.random_elem(rng)
    // f^1 * x = 0 already detects the stable kernel here (A reduced).
    assert_true(
      loc.project(x).equal_to(la.zero_elem()) ==
      a.mul(f, x).equal_to(a.zero_elem()),
    )
  }
  // Universal property instance: restriction rho : F^3 -> F^2 (drop point 0)
  // sends f to a unit, hence factors through A_f; the factor map here is
  // the identity matrix and factorization is checked as a matrix equality.
  let f2 = FinAlg::function_algebra("F^2", 2)
  let rho = AlgHom::from_basis_images([
    f2.zero_elem(),
    f2.basis_elem(0),
    f2.basis_elem(1),
  ])
  assert_true(rho.verify(a, f2))
  assert_true(f2.is_unit(rho.apply(f2, f)))
  let factor = AlgHom::identity(2)
  assert_true(factor.verify(la, f2))
  assert_true(factor.compose(loc.as_hom(a)).matrix().equal_to(rho.matrix()))
}
