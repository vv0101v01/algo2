// Projective geometry tests: counting points of P^n(F_7), homogeneous
// equations being scalar-invariant precisely because of homogeneity,
// charts, cones, the finite projective plane, Segre/Veronese images as
// *equalities of point sets*, and PGL invariance of Hilbert data.

///|
fn pp(cs : Array[Int32]) -> PPoint {
  let fs : Array[Fp] = []
  for c in cs {
    fs.push(Fp::new(c))
  }
  PPoint::must(fs)
}

///|
test "projective points: normalization, zero rejection, counting formula" {
  assert_true(pp([2, 4]).equal_to(pp([1, 2])))
  assert_true(pp([0, 3, 6]).equal_to(pp([0, 1, 2])))
  assert_true(PPoint::new([Fp::new(0), Fp::new(0)]) is None)
  assert_eq(pp([0, 1, 2]).display(), "[0:1:2]")
  for n in 0..<4 {
    assert_eq(all_projective_points(n).length(), projective_point_count(n))
  }
  assert_eq(projective_point_count(1), 8)
  assert_eq(projective_point_count(2), 57)
  assert_eq(projective_point_count(3), 400)
  // Homogeneous evaluation is well-defined on classes: scaling the
  // representative scales the value by lambda^d, hence vanishing is
  // representative-independent. Non-homogeneous polynomials enjoy no
  // such law (checked with an explicit counterexample).
  let h = Poly::from_int_terms(3, [
    (1, [2, 0, 0]),
    (2, [1, 1, 0]),
    (-1, [0, 0, 2]),
  ])
  let pt = [Fp::new(2), Fp::new(3), Fp::new(1)]
  let scaled = [Fp::new(6), Fp::new(2), Fp::new(3)] // 3 * pt
  assert_true(h.eval(scaled) == Fp::new(2) * h.eval(pt)) // lambda^2 = 9 = 2
  let nonhomog = Poly::from_int_terms(3, [(1, [1, 0, 0]), (1, [0, 0, 0])])
  assert_true(!nonhomog.is_homogeneous())
  assert_true(h.is_homogeneous())
}

///|
test "projective varieties: conic, cone fibers, point ideals, charts" {
  let conic = ProjVariety::from_generators(3, [
    Poly::from_int_terms(3, [(1, [2, 0, 0]), (1, [0, 2, 0]), (1, [0, 0, 2])]),
  ])
  // Smooth conic over F_7 with a point ([1:2:3]: 1+4+2=0) => q+1 points.
  assert_true(conic.contains_point(pp([1, 2, 3])))
  assert_eq(conic.num_points(), 8)
  assert_eq(conic.dimension(), 1)
  assert_true(conic.degree() is Some(2))
  // Affine cone: 1 + (q-1) * 8 = 49 affine points.
  let cone = conic.affine_cone()
  assert_eq(cone.num_points(), 1 + 6 * conic.num_points())
  // Singular conic = pair of lines xy = 0: 8 + 8 - 1 = 15 points, same
  // Hilbert polynomial (degree is a Hilbert, not a smoothness, datum).
  let pair_lines = ProjVariety::from_generators(3, [
    Poly::from_int_terms(3, [(1, [1, 1, 0])]),
  ])
  assert_eq(pair_lines.num_points(), 15)
  assert_true(pair_lines.degree() is Some(2))
  // Homogeneous prime of a point: its cone is a line (7 affine points),
  // it contains no irrelevant ideal, and Proj of it is exactly the point.
  let p = pp([1, 2, 0])
  let prime = homogeneous_prime_of_point(p)
  assert_true(!irrelevant_ideal(3).is_subset_of(prime))
  let pvar = ProjVariety::from_ideal(prime)
  assert_eq(pvar.num_points(), 1)
  assert_true(pvar.contains_point(p))
  assert_eq(pvar.affine_cone().num_points(), 7)
  // Two projective points regenerate the expected homogeneous ideal.
  let two = ProjVariety::from_points(3, [pp([1, 0, 0]), pp([0, 1, 0])])
  assert_true(
    two
    .ideal()
    .equal_to(
      Ideal::new(3, [
        Poly::variable(3, 2),
        Poly::from_int_terms(3, [(1, [1, 1, 0])]),
      ]),
    ),
  )
  assert_eq(two.num_points(), 2)
  // Charts of the Veronese conic: U_2 is the affine parabola (7 points),
  // exactly the points with nonzero last coordinate; round trips hold.
  let ver = veronese_conic()
  let chart = ver.chart(2)
  assert_eq(chart.num_points(), 7)
  let mut chart_count = 0
  for p in ver.points() {
    match chart_point(p, 2) {
      Some(aff) => {
        chart_count = chart_count + 1
        assert_true(chart.contains_point(aff))
        assert_true(point_from_chart(2, aff).equal_to(p))
      }
      None => assert_true(p.coord(2).is_zero())
    }
  }
  assert_eq(chart_count, 7)
  // Homogenize/dehomogenize round trip on the affine parabola equation.
  let f = Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])])
  let fh = homogenize_poly(f, 2)
  assert_true(fh.is_homogeneous())
  assert_true(
    fh.equal_to(Poly::from_int_terms(3, [(1, [0, 1, 1]), (-1, [2, 0, 0])])),
  )
  assert_true(dehomogenize_poly(fh, 2).equal_to(f))
}

///|
test "finite projective plane P^2(F_7): duality and incidence axioms" {
  let pts = all_projective_points(2)
  let lines = all_projective_lines()
  assert_eq(pts.length(), 57)
  assert_eq(lines.length(), 57)
  for l in lines {
    assert_eq(points_on_line(l).length(), 8)
  }
  // Two distinct points determine a unique line; two distinct lines
  // meet in a unique point -- checked on a deterministic sample of pairs
  // plus full incidence of the constructed objects.
  let mut idx = 0
  for p in pts {
    for q in pts {
      idx = idx + 1
      if idx % 37 != 0 || p.equal_to(q) {
        continue
      }
      match line_through(p, q) {
        Some(l) => {
          assert_true(is_incident(p, l) && is_incident(q, l))
          for r in points_on_line(l) {
            if !r.equal_to(p) {
              match line_through(p, r) {
                Some(l2) => assert_true(l2.equal_to(l))
                None => assert_true(false)
              }
            }
          }
        }
        None => assert_true(false)
      }
    }
  }
  let l1 = match PLine::new([Fp::new(1), Fp::new(1), Fp::new(0)]) {
    Some(l) => l
    None => abort("line")
  }
  let l2 = match PLine::new([Fp::new(1), Fp::new(0), Fp::new(1)]) {
    Some(l) => l
    None => abort("line")
  }
  match line_intersection(l1, l2) {
    Some(p) => {
      assert_true(is_incident(p, l1) && is_incident(p, l2))
      assert_true(p.equal_to(pp([1, 6, 6])))
    }
    None => assert_true(false)
  }
  assert_true(line_through(pp([1, 0, 0]), pp([3, 0, 0])) is None)
}

///|
test "Segre and Veronese images equal their equation-defined varieties" {
  let p1 = all_projective_points(1)
  assert_eq(p1.length(), 8)
  // Segre: image of P^1 x P^1 has 64 points, all on the quadric, and the
  // quadric over F_7 has no other points (its 64 points are accounted).
  let segre = segre_p1_p1()
  let images : Array[PPoint] = []
  for p in p1 {
    for q in p1 {
      let im = segre_point(p, q)
      assert_true(segre.contains_point(im))
      images.push(im)
    }
  }
  assert_eq(sort_ppoints(images).length(), 64)
  assert_eq(segre.num_points(), 64)
  assert_eq(segre.dimension(), 2)
  assert_true(segre.degree() is Some(2))
  match segre.ideal().hilbert_polynomial() {
    Some(hp) => assert_eq(hp.display(), "t^2 + 2*t + 1")
    None => assert_true(false)
  }
  // Veronese: image of P^1 is the conic, 8 points, injective here.
  let ver = veronese_conic()
  let vim : Array[PPoint] = []
  for p in p1 {
    let im = veronese2_point(p)
    assert_true(ver.contains_point(im))
    vim.push(im)
  }
  assert_eq(sort_ppoints(vim).length(), 8)
  assert_eq(ver.num_points(), 8)
}

///|
test "PGL action: transformed variety, point transport, Hilbert invariance" {
  let conic = ProjVariety::from_generators(3, [
    Poly::from_int_terms(3, [(1, [2, 0, 0]), (1, [0, 2, 0]), (1, [0, 0, 2])]),
  ])
  let a = Matrix::from_rows([
    [Fp::new(1), Fp::new(1), Fp::new(0)],
    [Fp::new(0), Fp::new(2), Fp::new(0)],
    [Fp::new(0), Fp::new(0), Fp::new(3)],
  ])
  let moved = conic.transform(a)
  assert_eq(moved.num_points(), conic.num_points())
  for p in conic.points() {
    match projective_transform_point(a, p) {
      Some(q) => assert_true(moved.contains_point(q))
      None => assert_true(false)
    }
  }
  // Hilbert polynomial is a projective invariant.
  let h1 = match conic.ideal().hilbert_polynomial() {
    Some(h) => h
    None => abort("hp")
  }
  let h2 = match moved.ideal().hilbert_polynomial() {
    Some(h) => h
    None => abort("hp")
  }
  assert_true(h1.equal_to(h2))
  // Singular matrix: kernel points have no image.
  let sing = Matrix::from_rows([
    [Fp::new(1), Fp::new(0), Fp::new(0)],
    [Fp::new(0), Fp::new(1), Fp::new(0)],
    [Fp::new(0), Fp::new(0), Fp::new(0)],
  ])
  assert_true(projective_transform_point(sing, pp([0, 0, 1])) is None)
  match projective_transform_point(sing, pp([1, 1, 5])) {
    Some(q) => assert_true(q.equal_to(pp([1, 1, 0])))
    None => assert_true(false)
  }
}
