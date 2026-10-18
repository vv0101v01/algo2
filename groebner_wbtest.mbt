// Whitebox tests for the field, polynomials, Buchberger and ideal calculus.
// Every test below is falsifiable: each asserts a specific mathematical
// fact (with negative controls) that a broken implementation would violate.

///|
test "F_7 is a field: exhaustive inverse and Fermat checks" {
  for a in 1..<7 {
    let x = Fp::new(a)
    assert_true(x * x.inv() == Fp::one())
    // Fermat: a^(p-1) = 1 for a != 0; a^p = a for all a (Frobenius on F_p).
    assert_true(x.pow(6) == Fp::one())
    assert_true(x.pow(7) == x)
  }
  assert_true(Fp::new(0).try_inv() is None)
  assert_true(Fp::new(-1) == Fp::new(6))
  assert_true(Fp::new(3) + Fp::new(5) == Fp::new(1))
  assert_true(Fp::new(3) * Fp::new(5) == Fp::new(1))
}

///|
test "polynomial arithmetic: ring axioms on pseudo-random samples" {
  let rng = Rng::new(12345)
  for _ in 0..<200 {
    let a = Poly::pseudo_random(rng, 2, 4, 3)
    let b = Poly::pseudo_random(rng, 2, 4, 3)
    let c = Poly::pseudo_random(rng, 2, 3, 2)
    assert_true(a.add(b).equal_to(b.add(a)))
    assert_true(a.mul(b).equal_to(b.mul(a)))
    assert_true(a.mul(b.add(c)).equal_to(a.mul(b).add(a.mul(c))))
    assert_true(a.sub(a).is_zero())
    assert_true(a.mul(Poly::one_poly(2)).equal_to(a))
    // Evaluation is a homomorphism ev : k[x,y] -> k.
    let pt = [rng.fp(), rng.fp()]
    assert_true(a.add(b).eval(pt) == a.eval(pt) + b.eval(pt))
    assert_true(a.mul(b).eval(pt) == a.eval(pt) * b.eval(pt))
  }
}

///|
test "polynomial canonicality: like terms fuse, zero drops" {
  // 2x + 5x = 7x = 0 over F_7 (a *non*zero characteristic effect).
  let f = Poly::from_int_terms(2, [(2, [1, 0]), (5, [1, 0]), (3, [0, 1])])
  assert_true(f.equal_to(Poly::from_int_terms(2, [(3, [0, 1])])))
  assert_eq(f.display(), "3*y")
  // Freshman's dream in characteristic 7: (x+y)^7 = x^7 + y^7.
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  assert_true(x.add(y).pow(7).equal_to(x.pow(7).add(y.pow(7))))
}

///|
test "division by non-Groebner generators FAILS; by the GB it decides" {
  // I = (xy-1, y^2-1). y(xy-1) - x(y^2-1) = x - y lies in I, but neither
  // xy nor y^2 divides x or y, so naive division leaves remainder x-y != 0.
  let g1 = Poly::from_int_terms(2, [(1, [1, 1]), (-1, [0, 0])])
  let g2 = Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])])
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let elt = x.sub(y)
  assert_true(!elt.reduce_by([g1, g2]).is_zero())
  let ideal = Ideal::new(2, [g1, g2])
  assert_true(elt.reduce_by(ideal.groebner()).is_zero())
  assert_true(ideal.contains(elt))
  // Negative controls: elements not in the ideal must be rejected.
  assert_true(!ideal.contains(x))
  assert_true(!ideal.contains(Poly::one_poly(2)))
  // Buchberger criterion on the *computed* basis: every S-pair reduces to 0.
  let gb = ideal.groebner()
  for i in 0..<gb.length() {
    for j in (i + 1)..<gb.length() {
      assert_true(spoly(gb[i], gb[j]).reduce_by(gb).is_zero())
    }
  }
}

///|
test "membership agrees with construction: sum h_i g_i is always in (g_i)" {
  let rng = Rng::new(777)
  let gs = [
    Poly::from_int_terms(2, [(1, [2, 0]), (1, [0, 1]), (-1, [0, 0])]),
    Poly::from_int_terms(2, [(1, [1, 1]), (-2, [0, 0])]),
  ]
  let ideal = Ideal::new(2, gs)
  for _ in 0..<60 {
    let h1 = Poly::pseudo_random(rng, 2, 3, 2)
    let h2 = Poly::pseudo_random(rng, 2, 3, 2)
    let combo = h1.mul(gs[0]).add(h2.mul(gs[1]))
    assert_true(ideal.contains(combo))
  }
  // The quotient k[x,y]/(x^2+y-1, xy-2): substituting, dimension should be
  // finite. y = 1 - x^2, x(1-x^2) = 2 => cubic => dim 3 over F_7.
  assert_true(ideal.finite_dimension() is Some(3))
}

///|
test "ideal sum/product/intersection: exact identities" {
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  let ix = Ideal::new(2, [x])
  let iy = Ideal::new(2, [y])
  // (x) ∩ (y) = (xy) since x, y coprime in a UFD.
  assert_true(ix.intersect(iy).equal_to(Ideal::new(2, [x.mul(y)])))
  // (x) + (y) = (x, y); and (x)+(1-x) = (1) (comaximality).
  assert_true(ix.sum(iy).equal_to(Ideal::new(2, [x, y])))
  let j = Ideal::new(2, [Poly::one_poly(2).sub(x)])
  assert_true(ix.sum(j).is_unit_ideal())
  // For comaximal ideals I∩J = IJ (Chinese remainder hypothesis).
  let i1 = Ideal::new(2, [x, y])
  let i2 = Ideal::new(2, [x.sub(Poly::one_poly(2)), y])
  assert_true(i1.intersect(i2).equal_to(i1.product(i2)))
  // Product vs intersection differ in general: (x,y)^2 != (x,y).
  assert_true(!i1.product(i1).equal_to(i1))
  assert_true(i1.intersect(i1).equal_to(i1))
}

///|
test "staircase and Krull dimension" {
  // F_7[x,y]/(x^2-1, y^2-1): standard monomials {1, x, y, xy}.
  let a = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-1, [0, 0])]),
    Poly::from_int_terms(2, [(1, [0, 2]), (-1, [0, 0])]),
  ])
  match a.standard_monomials() {
    Some(ms) => {
      assert_eq(ms.length(), 4)
      let mut shown = ""
      for m in ms {
        shown = shown + m.display() + ";"
      }
      assert_eq(shown, "x*y;x;y;1;")
    }
    None => assert_true(false)
  }
  assert_eq(a.krull_dimension(), 0)
  // (x^2, xy, y^2): staircase {1, x, y} -- a fat point of length 3.
  let fat = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [1, 1])]),
    Poly::from_int_terms(2, [(1, [0, 2])]),
  ])
  assert_true(fat.finite_dimension() is Some(3))
  // y - x^2 is a curve: infinite-dimensional quotient, Krull dimension 1.
  let parabola = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  assert_true(parabola.finite_dimension() is None)
  assert_eq(parabola.krull_dimension(), 1)
  assert_eq(Ideal::zero_ideal(2).krull_dimension(), 2)
  assert_eq(Ideal::unit_ideal(2).krull_dimension(), -1)
  // Twisted cubic in A^3: (y - x^2, z - x^3), dimension 1.
  let cubic = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [0, 1, 0]), (-1, [2, 0, 0])]),
    Poly::from_int_terms(3, [(1, [0, 0, 1]), (-1, [3, 0, 0])]),
  ])
  assert_eq(cubic.krull_dimension(), 1)
}

///|
test "saturation and radical membership (Rabinowitsch)" {
  // I = (x^2, xy) = x*(x,y). (I : x^infinity) = (x, y).
  let ideal = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0])]),
    Poly::from_int_terms(2, [(1, [1, 1])]),
  ])
  let x = Poly::variable(2, 0)
  let y = Poly::variable(2, 1)
  // (I : y^infinity) = (x): saturating by y kills the (x,y)-primary
  // component of I = (x) ∩ (x,y)^2, leaving the (x)-component.
  assert_true(ideal.saturate(y).equal_to(Ideal::new(2, [x])))
  // (I : x^infinity) = (1): x is nilpotent modulo I (x^2 ∈ I), and
  // inverting a nilpotent gives the zero ring / unit ideal. Geometrically
  // D(x) ∩ V(I) is empty because x vanishes on all of V(I).
  assert_true(ideal.saturate(x).is_unit_ideal())
  // x in sqrt(I) since x^2 in I; y not in sqrt(I) since I subset (x).
  assert_true(ideal.in_radical(x))
  assert_true(!ideal.in_radical(y))
  assert_true(!ideal.in_radical(Poly::one_poly(2)))
  // sqrt((x^2-2x+1)) = sqrt(((x-1)^2)) contains x-1.
  let sq = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [2, 0]), (-2, [1, 0]), (1, [0, 0])]),
  ])
  assert_true(sq.in_radical(x.sub(Poly::one_poly(2))))
  assert_true(!sq.contains(x.sub(Poly::one_poly(2))))
}
