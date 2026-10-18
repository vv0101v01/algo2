// Tests for affine varieties over F_7, coordinate rings, products,
// disjoint unions, morphisms and contravariant pullback, plus type-level
// product/sum universal properties.

///|
fn pt1(a : Int32) -> Pt {
  Pt::new([Fp::new(a)])
}

///|
fn pt2(a : Int32, b : Int32) -> Pt {
  Pt::new([Fp::new(a), Fp::new(b)])
}

///|
test "affine varieties: point counts are computed, not assumed" {
  assert_eq(all_points(2).length(), 49)
  // Parabola y = x^2: graph of a function, exactly 7 F_7-points.
  let parabola = Variety::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  assert_eq(parabola.num_points(), 7)
  for p in parabola.points() {
    assert_true(p.coord(1) == p.coord(0) * p.coord(0))
  }
  // Circle x^2 + y^2 = 1 over F_7: (±1,0),(0,±1),(±2,±2) = 8 points
  // (since 2^2+2^2 = 8 = 1 in F_7). A Q-intuition count would differ.
  let circle = Variety::from_generators(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (1, [0, 2]), (-1, [0, 0])]),
  ])
  assert_eq(circle.num_points(), 8)
  assert_true(circle.contains_point(pt2(2, 2)))
  assert_true(circle.contains_point(pt2(5, 5)))
  assert_true(!circle.contains_point(pt2(1, 1)))
  // x^2 + 1 = 0 has NO F_7-solution (-1 is not a square mod 7): empty.
  let empty_v = Variety::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (1, [0])]),
  ])
  assert_eq(empty_v.num_points(), 0)
  assert_true(empty_v.vanishing_ideal().is_unit_ideal())
  // ...but its defining ideal is NOT the unit ideal, and equals its own
  // radical (irreducible polynomial): so I(V_F7(I)) != sqrt(I) here.
  // The finite-field correction is adding the field equations:
  // (x^2+1) + (x^7-x) = (1) because gcd(x^2+1, x^7-x) = 1 over F_7.
  assert_true(!empty_v.ideal().is_unit_ideal())
  let corrected = empty_v.ideal().sum(field_equations_ideal(1))
  assert_true(corrected.is_unit_ideal())
}

///|
test "finite-field Nullstellenssatz: two independent algorithms agree" {
  // For I = (y - x^2, x^2 - 1) (two points (±1, 1)) and arbitrary f:
  //   f vanishes on V_F7(I)   (brute force over points)
  //   iff f in sqrt(I + field equations)  (Rabinowitsch saturation).
  let ideal = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [2, 0]), (-1, [0, 0])]),
  ])
  let v = Variety::from_ideal(ideal)
  assert_eq(v.num_points(), 2)
  let with_field = ideal.sum(field_equations_ideal(2))
  let rng = Rng::new(2026)
  let mut saw_vanishing = false
  let mut saw_nonvanishing = false
  for _ in 0..<24 {
    let f = Poly::pseudo_random(rng, 2, 3, 2)
    let mut brute = true
    for p in v.points() {
      if !f.eval(p.coords_array()).is_zero() {
        brute = false
      }
    }
    if brute {
      saw_vanishing = true
    } else {
      saw_nonvanishing = true
    }
    assert_true(brute == with_field.in_radical(f))
  }
  // The sample must be non-trivial in both directions.
  assert_true(saw_vanishing && saw_nonvanishing)
  // f = x^7 - x vanishes on every F_7-point but is in no proper radical
  // of the zero ideal alone; with field equations it is even a member.
  let x = Poly::variable(2, 0)
  let fe = x.pow(7).sub(x)
  assert_true(field_equations_ideal(2).contains(fe))
  assert_true(!Ideal::zero_ideal(2).in_radical(fe))
}

///|
test "vanishing ideals, coordinate ring, CRT, first isomorphism theorem" {
  // X = {(0,0), (1,1)}: I(X) = (y-x ... ) intersect computation compared
  // against the directly verified ideal (x-y, x^2-x)? Check: both points
  // have y=x and x in {0,1}; the claimed ideal's variety is exactly X and
  // its quotient has dimension 2, so equality is the right expectation.
  let pts = [pt2(0, 0), pt2(1, 1), pt2(3, 2)]
  let vx = Variety::from_points(2, pts)
  let ix = vx.ideal()
  // Every generator of I(X) vanishes on the points (soundness) ...
  for g in ix.gens() {
    for p in pts {
      assert_true(g.eval(p.coords_array()).is_zero())
    }
  }
  assert_true(ix.finite_dimension() is Some(3))
  // Maximal ideals of distinct points are comaximal (CRT hypothesis).
  for i in 0..<pts.length() {
    for j in (i + 1)..<pts.length() {
      let s = maximal_ideal_at(pts[i]).sum(maximal_ideal_at(pts[j]))
      assert_true(s.is_unit_ideal())
    }
  }
  // Coordinate ring as function tables: evaluation kernel = I(X), and
  // interpolation proves every table comes from a polynomial.
  let cr = vx.coordinate_ring()
  let alg = cr.algebra()
  assert_eq(alg.dim(), 3)
  for i in 0..<pts.length() {
    // delta_poly really is the i-th primitive idempotent table.
    assert_true(cr.of_poly(delta_poly(pts[i])).equal_to(alg.basis_elem(i)))
  }
  let rng = Rng::new(60606)
  for _ in 0..<40 {
    let table = alg.random_elem(rng)
    let p = cr.poly_of_function(table)
    assert_true(cr.of_poly(p).equal_to(table))
    let f = Poly::pseudo_random(rng, 2, 3, 3)
    assert_true(cr.of_poly(f).equal_to(alg.zero_elem()) == ix.contains(f))
  }
  // First isomorphism theorem: F_7[x]/I(X) --eval--> Func(X) is an
  // isomorphism. Checked between the staircase model and function algebra.
  let model = match QuotientModel::new(QuotientRing::new(ix), "k[x]/I(X)") {
    Some(m) => m
    None => abort("finite expected")
  }
  let images : Array[FinElem] = []
  for m in model.basis_monomials() {
    let e : Array[Int32] = []
    for i in 0..<2 {
      e.push(m.exp_at(i))
    }
    images.push(cr.of_poly(Poly::monomial(2, Fp::one(), e)))
  }
  let eval_hom = AlgHom::from_basis_images(images)
  assert_true(eval_hom.is_isomorphism(model.algebra(), alg))
}

///|
test "Zariski calculus: V(I+J) = V(I)∩V(J), V(I∩J) = V(I)∪V(J)" {
  let axes_x = Variety::from_generators(2, [Poly::variable(2, 0)]) // x = 0
  let axes_y = Variety::from_generators(2, [Poly::variable(2, 1)]) // y = 0
  assert_eq(axes_x.num_points(), 7)
  let inter = axes_x.intersection_with(axes_y)
  assert_eq(inter.num_points(), 1)
  assert_true(inter.contains_point(pt2(0, 0)))
  let union = axes_x.union_with(axes_y)
  assert_eq(union.num_points(), 13)
  // Pointwise agreement with naive set operations on all 49 points.
  for p in all_points(2) {
    assert_true(
      union.contains_point(p) ==
      (axes_x.contains_point(p) || axes_y.contains_point(p)),
    )
    assert_true(
      inter.contains_point(p) ==
      (axes_x.contains_point(p) && axes_y.contains_point(p)),
    )
  }
  // Inclusion reverses: I ⊆ J implies V(J) ⊆ V(I) (Galois connection).
  let bigger_eqs = Variety::from_generators(2, [
    Poly::variable(2, 0),
    Poly::variable(2, 1),
  ])
  for p in bigger_eqs.points() {
    assert_true(axes_x.contains_point(p))
  }
}

///|
test "product of varieties: points cartesian, k[XxY] = k[X] ⊗ k[Y]" {
  // X = {1,-1} ⊆ A^1, Y = {0,-1} ⊆ A^1.
  let x = Variety::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (-1, [0])]),
  ])
  let y = Variety::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (1, [1])]),
  ])
  assert_eq(x.num_points(), 2)
  assert_eq(y.num_points(), 2)
  let prod_v = x.product(y)
  assert_eq(prod_v.num_points(), 4)
  for p in x.points() {
    for q in y.points() {
      assert_true(prod_v.contains_point(Pt::new([p.coord(0), q.coord(0)])))
    }
  }
  assert_true(!prod_v.contains_point(pt2(0, 0)))
  // Projections are morphisms; the pairing of points is a bijection
  // (checked by: every product point is recovered from its projections,
  // and there are exactly |X||Y| of them).
  let pr1 = product_projection_first(1, 1)
  let pr2 = product_projection_second(1, 1)
  assert_true(is_variety_morphism(pr1, prod_v, x))
  assert_true(is_variety_morphism(pr2, prod_v, y))
  for p in prod_v.points() {
    let paired = Pt::new([
      pr1.apply_point(p).coord(0),
      pr2.apply_point(p).coord(0),
    ])
    assert_true(paired.equal_to(p))
  }
  // Coordinate ring of product = tensor product of coordinate rings,
  // via delta_a ⊗ delta_b |-> delta_{(a,b)}. Verified isomorphism.
  let crx = x.coordinate_ring()
  let cry = y.coordinate_ring()
  let crp = prod_v.coordinate_ring()
  let tensor = FinAlg::tensor(crx.algebra(), cry.algebra(), "k[X] (x) k[Y]")
  let images : Array[FinElem] = []
  for p in x.points() {
    for q in y.points() {
      let joint = Pt::new([p.coord(0), q.coord(0)])
      let idx = match prod_v.point_index(joint) {
        Some(i) => i
        None => abort("product point missing")
      }
      images.push(crp.algebra().basis_elem(idx))
    }
  }
  assert_true(
    AlgHom::from_basis_images(images).is_isomorphism(tensor, crp.algebra()),
  )
}

///|
test "disjoint union: tagged embedding, k[X⊔Y] = k[X] x k[Y]" {
  let x = Variety::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (-1, [0])]),
  ])
  let y = Variety::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (1, [1])]),
  ])
  let u = x.disjoint_union(y)
  assert_eq(u.num_vars(), 3)
  assert_eq(u.num_points(), x.num_points() + y.num_points())
  let inl = disjoint_injection_left(1, 1)
  let inr = disjoint_injection_right(1, 1)
  assert_true(is_variety_morphism(inl, x, u))
  assert_true(is_variety_morphism(inr, y, u))
  // The two images are genuinely disjoint (the tag coordinate separates
  // them even where the underlying points would collide: -1 ∈ X ∩ Y).
  for p in x.points() {
    for q in y.points() {
      assert_true(!inl.apply_point(p).equal_to(inr.apply_point(q)))
    }
  }
  assert_true(u.contains_point(Pt::new([Fp::new(6), Fp::new(0), Fp::new(0)])))
  assert_true(u.contains_point(Pt::new([Fp::new(0), Fp::new(6), Fp::new(1)])))
  // k[X⊔Y] ≅ k[X] × k[Y]: delta of a tagged point maps to (delta, 0) or
  // (0, delta) according to its tag. Verified isomorphism.
  let crx = x.coordinate_ring()
  let cry = y.coordinate_ring()
  let cru = u.coordinate_ring()
  let prod_alg = FinAlg::product(crx.algebra(), cry.algebra(), "k[X] x k[Y]")
  let images : Array[FinElem] = []
  for p in u.points() {
    if p.coord(2).is_zero() {
      let idx = match x.point_index(pt1(p.coord(0).to_int())) {
        Some(i) => i
        None => abort("left point missing")
      }
      images.push(prod_alg.basis_elem(idx))
    } else {
      let idx = match y.point_index(pt1(p.coord(1).to_int())) {
        Some(i) => i
        None => abort("right point missing")
      }
      images.push(prod_alg.basis_elem(crx.algebra().dim() + idx))
    }
  }
  assert_true(
    AlgHom::from_basis_images(images).is_isomorphism(cru.algebra(), prod_alg),
  )
  // Coproduct universal property on points: a map out of X⊔Y to A^1 is a
  // pair of maps. Realize phi = [const 2 on X, identity on Y] as a single
  // polynomial in the tagged coordinates: phi = 2(1-t) + (coord_Y)·t.
  let phi = Poly::from_int_terms(3, [
    (2, [0, 0, 0]),
    (-2, [0, 0, 1]),
    (1, [0, 1, 1]),
  ])
  for p in x.points() {
    assert_true(phi.eval(inl.apply_point(p).coords_array()) == Fp::new(2))
  }
  for q in y.points() {
    assert_true(phi.eval(inr.apply_point(q).coords_array()) == q.coord(0))
  }
}

///|
test "contravariance: (g∘f)* = f* ∘ g* on polys, functions and matrices" {
  // f : parabola X -> A^1, projection to x; g : A^1 -> A^1, squaring.
  let x_var = Variety::from_generators(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  let line = Variety::affine_space(1)
  let f = PolyMap::new(2, [Poly::variable(2, 0)])
  let g = PolyMap::new(1, [Poly::variable(1, 0).pow(2)])
  assert_true(is_variety_morphism(f, x_var, line))
  assert_true(is_variety_morphism(g, line, line))
  let gf = g.compose_after(f)
  assert_true(is_variety_morphism(gf, x_var, line))
  // Points go forwards: (a, a^2) |-> a |-> a^2 (also directly).
  for p in x_var.points() {
    assert_true(gf.apply_point(p).equal_to(g.apply_point(f.apply_point(p))))
  }
  // Polynomials pull backwards, with composition REVERSED.
  let rng = Rng::new(112233)
  for _ in 0..<30 {
    let phi = Poly::pseudo_random(rng, 1, 3, 4)
    let direct = gf.pullback_poly(phi)
    let staged = f.pullback_poly(g.pullback_poly(phi))
    assert_true(direct.equal_to(staged))
  }
  // Same law for coordinate-ring homomorphisms k[A^1] -> k[A^1] -> k[X]:
  // pullback_hom(gf) == pullback_hom(f) ∘ pullback_hom(g) as matrices.
  let crx = x_var.coordinate_ring()
  let crl = line.coordinate_ring()
  let hf = pullback_hom(f, x_var, line, crx, crl)
  let hg = pullback_hom(g, line, line, crl, crl)
  let hgf = pullback_hom(gf, x_var, line, crx, crl)
  assert_true(hf.verify(crl.algebra(), crx.algebra()))
  assert_true(hg.verify(crl.algebra(), crl.algebra()))
  assert_true(hgf.verify(crl.algebra(), crx.algebra()))
  assert_true(hgf.matrix().equal_to(hf.compose(hg).matrix()))
  // Identity law: id^* = id.
  let id_line = pullback_hom(PolyMap::identity(1), line, line, crl, crl)
  assert_true(id_line.matrix().equal_to(Matrix::identity(7)))
  // Pullback of the coordinate function along f is the x-coordinate on X,
  // and its square relation pulls back too: f^*(t)^2 = y-coordinate table.
  let t_table = crl.coordinate_function(0)
  let fx = pullback_function(f, x_var, line, crx, t_table)
  let xs = crx.algebra()
  assert_true(fx.equal_to(crx.coordinate_function(0)))
  assert_true(xs.mul(fx, fx).equal_to(crx.coordinate_function(1)))
  // Negative control: projection does not land in {1,-1} ⊆ A^1.
  let two_pts = Variety::from_generators(1, [
    Poly::from_int_terms(1, [(1, [2]), (-1, [0])]),
  ])
  assert_true(!is_variety_morphism(f, x_var, two_pts))
}

///|
test "principal open D(f): points and the closed graph t*f = 1" {
  let line = Variety::affine_space(1)
  let fx = Poly::variable(1, 0)
  let d_pts = line.principal_open_points(fx)
  assert_eq(d_pts.length(), 6)
  let graph = line.principal_open_as_variety(fx)
  assert_eq(graph.num_points(), 6)
  for p in graph.points() {
    assert_true(p.coord(0) * p.coord(1) == Fp::one())
    assert_true(line.principal_open_points(fx).length() == 6)
  }
  // Projection of the graph to A^1 is exactly D(x) (as a set).
  let proj = product_projection_first(1, 1)
  for p in d_pts {
    let mut found = false
    for q in graph.points() {
      if proj.apply_point(q).equal_to(p) {
        found = true
      }
    }
    assert_true(found)
  }
}

///|
test "type-level product and sum: universal properties on finite samples" {
  // Pairing/projection triangle identities, checked on all of a finite
  // sample type (Int residues 0..6), i.e. function equality by enumeration.
  let f = fn(n : Int32) { n * n % 7 }
  let g = fn(n : Int32) { (n + 3) % 7 }
  let pair = pairing(f, g)
  for n in 0..<7 {
    assert_eq(pair(n).fst, f(n))
    assert_eq(pair(n).snd, g(n))
  }
  // Copairing/injection identities [h,k] ∘ inl = h, [h,k] ∘ inr = k.
  let h = fn(n : Int32) { n + 100 }
  let k = fn(s : String) { s.length() }
  for n in 0..<7 {
    assert_eq(sum_elim(Inl(n), h, k), h(n))
  }
  assert_eq(sum_elim(Inr("moonbit"), h, k), k("moonbit"))
  // Functor laws for prod_map/sum_map (identity and composition), pointwise.
  let id_int = fn(n : Int32) { n }
  for n in 0..<5 {
    let p : Prod[Int32, Int32] = { fst: n, snd: n + 10, }
    let q = prod_map(p, id_int, id_int)
    assert_true(q.fst == p.fst && q.snd == p.snd)
    let s : Sum[Int32, Int32] = if n % 2 == 0 { Inl(n) } else { Inr(n) }
    let s2 = sum_map(s, fn(v) { v + 1 }, fn(v) { v * 2 })
    match (s, s2) {
      (Inl(a), Inl(b)) => assert_eq(b, a + 1)
      (Inr(a), Inr(b)) => assert_eq(b, a * 2)
      _ => assert_true(false)
    }
  }
  // Distributivity round trip on samples (inverse built by copairing).
  let undistribute = fn(s : Sum[Prod[Int32, Int32], Prod[Int32, String]]) {
    sum_elim(s, fn(p) { { fst: p.fst, snd: Inl(p.snd), } }, fn(p) {
      { fst: p.fst, snd: Inr(p.snd), }
    })
  }
  let sample1 : Prod[Int32, Sum[Int32, String]] = { fst: 3, snd: Inr("hi"), }
  let back = undistribute(distribute(sample1))
  assert_eq(back.fst, 3)
  match back.snd {
    Inr(t) => assert_eq(t, "hi")
    Inl(_) => assert_true(false)
  }
}
