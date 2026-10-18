// Capstone duality tests: CRT decomposition, coproduct property of the
// tensor product, pairing of variety morphisms, and the anti-equivalence
// between finite F_7-varieties (point sets) and finite products of F_7
// (coordinate rings) -- hom <-> opposite point map, in both directions.

///|
test "CRT: k[x]/(m_p ∩ m_q) ≅ k[x]/m_p x k[x]/m_q for distinct points" {
  let p = Pt::new([Fp::new(0), Fp::new(0)])
  let q = Pt::new([Fp::new(1), Fp::new(0)])
  let mp = maximal_ideal_at(p)
  let mq = maximal_ideal_at(q)
  let both = mp.intersect(mq)
  // Comaximality gives I∩J = IJ (hypothesis of CRT), here by computation.
  assert_true(both.equal_to(mp.product(mq)))
  let model = match
    QuotientModel::new(QuotientRing::new(both), "k[x]/(mp∩mq)") {
    Some(m) => m
    None => abort("finite expected")
  }
  let ground = FinAlg::ground_field()
  let prod = FinAlg::product(ground, ground, "F_7 x F_7")
  // The CRT map is evaluation at the two points, on the staircase basis.
  let images : Array[FinElem] = []
  for m in model.basis_monomials() {
    let e : Array[Int32] = []
    for i in 0..<2 {
      e.push(m.exp_at(i))
    }
    let mono = Poly::monomial(2, Fp::one(), e)
    images.push(
      prod.elem([mono.eval(p.coords_array()), mono.eval(q.coords_array())]),
    )
  }
  assert_true(
    AlgHom::from_basis_images(images).is_isomorphism(model.algebra(), prod),
  )
  // Explicit CRT inverse on values (a,b): a(1-x) + b*x hits (a at p, b at q).
  let x = Poly::variable(2, 0)
  for a in 0..<7 {
    for b in 0..<7 {
      let crt = Poly::constant(2, Fp::new(a))
        .mul(Poly::one_poly(2).sub(x))
        .add(Poly::constant(2, Fp::new(b)).mul(x))
      assert_true(crt.eval(p.coords_array()) == Fp::new(a))
      assert_true(crt.eval(q.coords_array()) == Fp::new(b))
    }
  }
}

///|
test "tensor coproduct: homs out of A⊗B are pairs of homs" {
  let a = FinAlg::function_algebra("F^2", 2)
  let b = FinAlg::function_algebra("F^3", 3)
  let c = FinAlg::function_algebra("F^6", 6)
  let t = FinAlg::tensor(a, b, "F^2 (x) F^3")
  // phi: F^2 -> F^6 (functions constant along the second factor),
  // psi: F^3 -> F^6 (constant along the first), pair index (i,j) = 3i+j.
  let z = Fp::zero()
  let o = Fp::one()
  let phi = AlgHom::from_basis_images([
    c.elem([o, o, o, z, z, z]),
    c.elem([z, z, z, o, o, o]),
  ])
  let psi = AlgHom::from_basis_images([
    c.elem([o, z, z, o, z, z]),
    c.elem([z, o, z, z, o, z]),
    c.elem([z, z, o, z, z, o]),
  ])
  assert_true(phi.verify(a, c))
  assert_true(psi.verify(b, c))
  let copair = tensor_copair_hom(a, b, c, t, phi, psi)
  assert_true(copair.is_isomorphism(t, c))
  // Triangle identities: copair ∘ (a |-> a⊗1) = phi, copair ∘ (b|->1⊗b) = psi.
  let incl_a = AlgHom::from_basis_images([
    pure_tensor(b, t, a.basis_elem(0), b.one_elem()),
    pure_tensor(b, t, a.basis_elem(1), b.one_elem()),
  ])
  let incl_b = AlgHom::from_basis_images([
    pure_tensor(b, t, a.one_elem(), b.basis_elem(0)),
    pure_tensor(b, t, a.one_elem(), b.basis_elem(1)),
    pure_tensor(b, t, a.one_elem(), b.basis_elem(2)),
  ])
  assert_true(incl_a.verify(a, t))
  assert_true(incl_b.verify(b, t))
  assert_true(copair.compose(incl_a).matrix().equal_to(phi.matrix()))
  assert_true(copair.compose(incl_b).matrix().equal_to(psi.matrix()))
}

///|
test "product of algebras: product_pair_hom satisfies projection laws" {
  let c = FinAlg::function_algebra("C=F^2", 2)
  let a = FinAlg::function_algebra("A=F^2", 2)
  let b = FinAlg::function_algebra("B=F^3", 3)
  let prod = FinAlg::product(a, b, "A x B")
  let z = Fp::zero()
  let o = Fp::one()
  let phi = AlgHom::identity(2)
  assert_true(phi.verify(c, a))
  // psi : F^2 -> F^3 from the index map b |-> [1,0,0][b]: delta_0 pulls
  // back to the table (0,1,1), delta_1 to (1,0,0).
  let psi = AlgHom::from_basis_images([b.elem([z, o, o]), b.elem([o, z, z])])
  assert_true(psi.verify(c, b))
  let pair = product_pair_hom(a, b, c, prod, phi, psi)
  assert_true(pair.verify(c, prod))
  let proj_a = AlgHom::from_basis_images([
    a.basis_elem(0),
    a.basis_elem(1),
    a.zero_elem(),
    a.zero_elem(),
    a.zero_elem(),
  ])
  let proj_b = AlgHom::from_basis_images([
    b.zero_elem(),
    b.zero_elem(),
    b.basis_elem(0),
    b.basis_elem(1),
    b.basis_elem(2),
  ])
  assert_true(proj_a.compose(pair).matrix().equal_to(phi.matrix()))
  assert_true(proj_b.compose(pair).matrix().equal_to(psi.matrix()))
}

///|
test "variety morphism pairing + product projections compose exactly" {
  let parabola = Variety::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  let line = Variety::affine_space(1)
  let fx = PolyMap::new(2, [Poly::variable(2, 0)])
  let fy = PolyMap::new(2, [Poly::variable(2, 1)])
  let paired = pair_poly_maps(fx, fy)
  let prod_v = line.product(line)
  assert_true(is_variety_morphism(paired, parabola, prod_v))
  // Component-level triangle identities (polynomial equality, not just
  // equality on points): pr1 ∘ <fx,fy> = fx as polynomial maps.
  let back1 = product_projection_first(1, 1).compose_after(paired)
  let back2 = product_projection_second(1, 1).compose_after(paired)
  assert_true(back1.components[0].equal_to(fx.components[0]))
  assert_true(back2.components[0].equal_to(fy.components[0]))
  for p in parabola.points() {
    assert_true(paired.apply_point(p).equal_to(p))
  }
}

///|
test "anti-equivalence: point maps <-> opposite algebra homs (finite case)" {
  let parabola = Variety::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  let line = Variety::affine_space(1)
  let crx = parabola.coordinate_ring()
  let crl = line.coordinate_ring()
  // Direction 1: start from the projection f, pull back, then recover f
  // from the homomorphism alone (idempotent tracking).
  let f = PolyMap::new(2, [Poly::variable(2, 0)])
  let hf = pullback_hom(f, parabola, line, crx, crl)
  let recovered = induced_point_map(hf, parabola, line, crx, crl)
  for i in 0..<parabola.points().length() {
    assert_true(recovered[i].equal_to(f.apply_point(parabola.points()[i])))
  }
  // Direction 2: start from an abstract point assignment sigma (send
  // (a,a^2) to the line point a^2 = its y-coordinate), build the hom
  // from sigma, recover sigma, then realize sigma by an interpolated
  // polynomial map whose pullback matrix equals the original hom.
  let sigma : Array[Pt] = []
  for p in parabola.points() {
    sigma.push(Pt::new([p.coord(1)]))
  }
  let images : Array[FinElem] = []
  for bpt in line.points() {
    let table : Array[Fp] = []
    for target in sigma {
      table.push(if target.equal_to(bpt) { Fp::one() } else { Fp::zero() })
    }
    images.push(crx.algebra().elem(table))
  }
  let hom = AlgHom::from_basis_images(images)
  assert_true(hom.verify(crl.algebra(), crx.algebra()))
  let sigma_back = induced_point_map(hom, parabola, line, crx, crl)
  for i in 0..<sigma.length() {
    assert_true(sigma_back[i].equal_to(sigma[i]))
  }
  let comp_values : Array[Fp] = []
  for target in sigma {
    comp_values.push(target.coord(0))
  }
  let realized = PolyMap::new(2, [interpolate(parabola.points(), comp_values)])
  assert_true(is_variety_morphism(realized, parabola, line))
  let hom2 = pullback_hom(realized, parabola, line, crx, crl)
  assert_true(hom2.matrix().equal_to(hom.matrix()))
  // Composing point maps X->Y->Z corresponds to composing homs in the
  // opposite order -- already the matrix law of contravariance, here via
  // recovered maps: induced(h2 ∘ h1) = induced(h1) after induced(h2).
  let sq = PolyMap::new(1, [Poly::variable(1, 0).pow(3)])
  let h_sq = pullback_hom(sq, line, line, crl, crl)
  let composed_hom = hf.compose(h_sq) // k[line] -sq*-> k[line] -f*-> k[X]
  let composed_pts = induced_point_map(composed_hom, parabola, line, crx, crl)
  for i in 0..<parabola.points().length() {
    let expect = sq.apply_point(f.apply_point(parabola.points()[i]))
    assert_true(composed_pts[i].equal_to(expect))
  }
}

///|
test "zero ring corners: unique hom into 0, none out of 0 into nonzero" {
  let a = FinAlg::function_algebra("F^2", 2)
  let zero_alg = FinAlg::function_algebra("0", 0)
  assert_eq(zero_alg.dim(), 0)
  assert_true(zero_alg.check_axioms())
  let into_zero = AlgHom::from_matrix(Matrix::zero(0, 2))
  assert_true(into_zero.verify(a, zero_alg))
  let out_of_zero = AlgHom::from_matrix(Matrix::zero(2, 0))
  assert_true(!out_of_zero.verify(zero_alg, a))
  // The empty variety has the zero ring as coordinate ring (dim 0):
  // 1 = 0 there, and every polynomial has the same (empty) table.
  let empty_v = Variety::empty(1)
  let cr = empty_v.coordinate_ring()
  assert_eq(cr.algebra().dim(), 0)
  assert_true(
    cr.of_poly(Poly::variable(1, 0)).equal_to(cr.algebra().one_elem()),
  )
}
