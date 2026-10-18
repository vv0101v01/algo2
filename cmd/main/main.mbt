///|
/// Executable tour of the library: every printed number below is computed
/// by the algorithms in the library (not hard-coded output), and key facts
/// are re-verified with expect(...) so a lying demo would abort loudly.
/// Run: moon run cmd/main
fn expect(cond : Bool, msg : String) -> Unit {
  if !cond {
    abort("demo check failed: " + msg)
  }
}

///|
fn main {
  println("=== Affine algebra over F_\{@lib.PRIME} -- computed tour ===")
  println("")

  // 1. Groebner basis decides ideal membership where naive division fails.
  let g1 = @lib.Poly::from_int_terms(2, [(1, [1, 1]), (-1, [0, 0])])
  let g2 = @lib.Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])])
  let ideal = @lib.Ideal::new(2, [g1, g2])
  let diff = @lib.Poly::variable(2, 0).sub(@lib.Poly::variable(2, 1))
  println("[Groebner] I = (xy-1, y^2-1)")
  println("  reduced GB      = \{@lib.poly_list_display(ideal.groebner())}")
  println(
    "  x - y in I?     = \{ideal.contains(diff)} (naive division remainder: \{diff.reduce_by([g1, g2]).display()})",
  )
  expect(ideal.contains(diff), "x-y must be in (xy-1, y^2-1)")
  expect(!diff.reduce_by([g1, g2]).is_zero(), "naive division must fail here")
  println("")

  // 2. Affine varieties: point counts over F_7.
  let parabola = @lib.Variety::from_generators(2, [
    @lib.Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  let circle = @lib.Variety::from_generators(2, [
    @lib.Poly::from_int_terms(2, [(1, [2, 0]), (1, [0, 2]), (-1, [0, 0])]),
  ])
  println("[Varieties]")
  println(
    "  |V(y-x^2)| = \{parabola.num_points()},  Krull dim = \{parabola.ideal().krull_dimension()}",
  )
  println(
    "  |V(x^2+y^2-1)| = \{circle.num_points()}  (over F_7, (±2,±2) lie on it)",
  )
  expect(parabola.num_points() == 7, "parabola has 7 points")
  expect(circle.num_points() == 8, "F_7-circle has 8 points")
  println("")

  // 3. Quotient ring and its finite model.
  let q = @lib.QuotientRing::from_generators(2, [
    @lib.Poly::from_int_terms(2, [(1, [2, 0]), (-1, [0, 0])]),
    @lib.Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])]),
  ])
  let xb = q.variable(0)
  println("[Quotient] R = F_7[x,y]/(x^2-1, y^2-1)")
  let qdim = match q.finite_dimension() {
    Some(d) => "\{d}"
    None => "infinite"
  }
  println("  dim_F7 R = \{qdim}")
  println(
    "  xbar^2 = \{q.mul(xb, xb).display()} (and xbar != 1: \{!xb.equal_to(q.one_coset())})",
  )
  expect(q.mul(xb, xb).equal_to(q.one_coset()), "xbar^2 = 1 in quotient")
  println("")

  // 4. Product / tensor / disjoint union dimensions and coordinate rings.
  let two_x = @lib.Variety::from_generators(1, [
    @lib.Poly::from_int_terms(1, [(1, [2]), (-1, [0])]),
  ])
  let two_y = @lib.Variety::from_generators(1, [
    @lib.Poly::from_int_terms(1, [(1, [2]), (1, [1])]),
  ])
  let prod_v = two_x.product(two_y)
  let tensor_alg = @lib.FinAlg::tensor(
    two_x.coordinate_ring().algebra(),
    two_y.coordinate_ring().algebra(),
    "k[X] (x) k[Y]",
  )
  println("[Product / tensor / disjoint union]")
  println(
    "  |X x Y| = \{prod_v.num_points()} = |X||Y|,  dim k[X](x)k[Y] = \{tensor_alg.dim()}",
  )
  println("  tensor axioms on basis triples: \{tensor_alg.check_axioms()}")
  let du = two_x.disjoint_union(two_y)
  let prod_alg = @lib.FinAlg::product(
    two_x.coordinate_ring().algebra(),
    two_y.coordinate_ring().algebra(),
    "k[X] x k[Y]",
  )
  println(
    "  |X ⊔ Y| = \{du.num_points()} in A^\{du.num_vars()} (tagged),  dim k[X]x k[Y] = \{prod_alg.dim()}",
  )
  expect(prod_v.num_points() == 4, "product points multiply")
  expect(du.num_points() == 4, "disjoint union points add")
  expect(tensor_alg.check_axioms(), "tensor algebra axioms")
  expect(prod_alg.check_axioms(), "product algebra axioms")
  println("")

  // 5. Localization: saturation kernel made visible.
  let x = @lib.Poly::variable(2, 0)
  let y = @lib.Poly::variable(2, 1)
  let axes_ring = @lib.QuotientRing::from_generators(2, [x.mul(y)])
  let loc = @lib.LocalizedRing::new(axes_ring, x)
  println("[Localization] R = F_7[x,y]/(xy), S = {x^k}")
  println(
    "  (xy : x^inf) GB = \{@lib.poly_list_display(loc.saturation_ideal().groebner())}",
  )
  println(
    "  y/1 = 0 in S^-1 R? \{loc.is_zero(loc.of_poly(y))}  although y != 0 in R: \{!axes_ring.of_poly(y).is_zero()}",
  )
  expect(loc.is_zero(loc.of_poly(y)), "y dies after inverting x (xy=0)")
  expect(!loc.is_zero(loc.one_elem()), "localized ring is nonzero")
  let lring = @lib.LocalRingAtPoint::new(
    @lib.Pt::new([@lib.Fp::new(1), @lib.Fp::new(2)]),
  )
  let xm1 = x.sub(@lib.Poly::one_poly(2))
  println(
    "  at (1,2): 1/(x-1) legal in O_(1,2)? \{lring.frac(@lib.Poly::one_poly(2), xm1) is Some(_)} (denominator vanishes there)",
  )
  expect(lring.frac(@lib.Poly::one_poly(2), xm1) is None, "must refuse")
  println("")

  // 6. Interpolation / CRT and the principal open graph.
  let pts = [
    @lib.Pt::new([@lib.Fp::new(0), @lib.Fp::new(0)]),
    @lib.Pt::new([@lib.Fp::new(1), @lib.Fp::new(1)]),
    @lib.Pt::new([@lib.Fp::new(3), @lib.Fp::new(2)]),
  ]
  let values = [@lib.Fp::new(5), @lib.Fp::new(1), @lib.Fp::new(4)]
  let interp = @lib.interpolate(pts, values)
  let mut ok = true
  for i in 0..<3 {
    if interp.eval(pts[i].coords_array()) != values[i] {
      ok = false
    }
  }
  println("[Interpolation] values (5,1,4) realized by one polynomial: \{ok}")
  expect(ok, "interpolation realizes prescribed values")
  let line = @lib.Variety::affine_space(1)
  let graph = line.principal_open_as_variety(@lib.Poly::variable(1, 0))
  println(
    "[D(x)] graph V(tx-1) in A^2 has \{graph.num_points()} points, each with t = 1/x",
  )
  expect(graph.num_points() == 6, "D(x) in A^1(F_7) has 6 points")
  println("")

  // 7. Hilbert polynomial of the twisted cubic and a plane cubic.
  let twisted = @lib.Ideal::new(4, [
    @lib.Poly::from_int_terms(4, [(1, [0, 2, 0, 0]), (-1, [1, 0, 1, 0])]),
    @lib.Poly::from_int_terms(4, [(1, [0, 1, 1, 0]), (-1, [1, 0, 0, 1])]),
    @lib.Poly::from_int_terms(4, [(1, [0, 0, 2, 0]), (-1, [0, 1, 0, 1])]),
  ])
  let hp_twisted = match twisted.hilbert_polynomial() {
    Some(h) => h.display()
    None => abort("twisted cubic must be homogeneous")
  }
  let elliptic = @lib.Ideal::new(3, [
    @lib.Poly::from_int_terms(3, [
      (1, [0, 2, 1]),
      (-1, [3, 0, 0]),
      (-1, [1, 0, 2]),
    ]),
  ])
  let genus = match elliptic.arithmetic_genus() {
    Some(g) => g
    None => abort("plane cubic genus")
  }
  println("[Hilbert] twisted cubic P(t) = \{hp_twisted}")
  println("  plane cubic arithmetic genus = \{genus}")
  expect(hp_twisted == "3*t + 1", "twisted cubic Hilbert polynomial")
  expect(genus == 1, "plane cubic genus")
  println("")

  // 8. Primary decomposition with an embedded prime.
  let mono_ideal = @lib.Ideal::new(2, [
    @lib.Poly::from_int_terms(2, [(1, [2, 0])]),
    @lib.Poly::from_int_terms(2, [(1, [1, 1])]),
  ])
  let pd = match @lib.primary_decomposition(mono_ideal) {
    Some(d) => d
    None => abort("monomial primary decomposition")
  }
  println(
    "[Primary decomposition] (x^2, xy) has \{pd.num_components()} components",
  )
  for c in pd.components() {
    println(
      "  Q = \{@lib.poly_list_display(c.component().groebner())},  sqrt(Q) = \{@lib.poly_list_display(c.prime().groebner())}",
    )
  }
  expect(pd.verify(mono_ideal), "primary decomposition verifies")
  println("")

  // 9. Projective geometry counts.
  let segre = @lib.segre_p1_p1()
  println(
    "[Projective] |P^2(F_7)| = \{@lib.all_projective_points(2).length()}, |Segre P^1xP^1| = \{segre.num_points()}, dim = \{segre.dimension()}",
  )
  expect(@lib.all_projective_points(2).length() == 57, "P^2 point count")
  expect(segre.num_points() == 64, "Segre point count")
  println("")

  // 10. Schemes: a fat point and the invisible F_49 point.
  let fat_spec = match
    @lib.AffineScheme::spec(@lib.Ideal::new(2, [x.pow(2), y])) {
    Some(s) => s
    None => abort("fat point spec")
  }
  let f49_ideal = @lib.Ideal::new(2, [
    @lib.Poly::from_int_terms(2, [(1, [2, 0]), (1, [0, 0])]),
    y,
  ])
  let f49_spec = match @lib.AffineScheme::spec(f49_ideal) {
    Some(s) => s
    None => abort("F49 spec")
  }
  println(
    "[Spec] fat point: points=\{fat_spec.num_points()} length=\{fat_spec.total_length()} reduced=\{fat_spec.is_reduced()}",
  )
  println(
    "[Spec] (x^2+1, y): Spec points=\{f49_spec.num_points()}, F_7-points=\{f49_spec.rational_points().length()}, residue degree=\{f49_spec.residue_degree(0)}",
  )
  expect(fat_spec.total_length() == 2, "fat point length")
  expect(f49_spec.num_points() == 1, "F49 closed point")
  println("")
  println("ALL DEMO CHECKS PASSED")
}
