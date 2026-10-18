// Hilbert function / series / polynomial tests. Expected values are
// classical: plane conic 2t+1, plane cubic 3t (genus 1), twisted cubic
// 3t+1, complete intersections, and Hilbert's theorem checked against
// independent enumeration (agreement only forced beyond the proven
// bound, and the small-degree behavior is pinned separately).

///|
fn hp_of(ideal : Ideal) -> RatPoly {
  match ideal.hilbert_polynomial() {
    Some(p) => p
    None => abort("expected homogeneous ideal")
  }
}

///|
fn hf_of(ideal : Ideal, d : Int32) -> Int32 {
  match ideal.hilbert_function(d) {
    Some(v) => v
    None => abort("expected homogeneous ideal")
  }
}

///|
test "rational arithmetic is exact and normalized" {
  assert_true(Rat::new(6, -8) == Rat::new(-3, 4))
  assert_true(Rat::new(1, 3) + Rat::new(1, 6) == Rat::new(1, 2))
  assert_true(Rat::new(2, 3) * Rat::new(9, 4) == Rat::new(3, 2))
  assert_eq(Rat::new(-10, 4).display(), "-5/2")
  assert_eq(binom_int(6, 2), 15)
  assert_eq(binom_int(2, 5), 0)
  // (t^2 + 3t + 2)/2 = C(t+2,2), values 1,3,6,10.
  let p = RatPoly::from_coeffs([Rat::one(), Rat::new(3, 2), Rat::new(1, 2)])
  assert_eq(p.display(), "1/2*t^2 + 3/2*t + 1")
  assert_eq(p.eval_int_exact(3), 10)
}

///|
test "Hilbert polynomial of polynomial rings and hypersurfaces" {
  // S = k[x,y,z]: P = C(t+2,2); Krull dim 3 = deg P + 1.
  let s = Ideal::zero_ideal(3)
  let p = hp_of(s)
  assert_true(
    p.equal_to(
      RatPoly::from_coeffs([Rat::one(), Rat::new(3, 2), Rat::new(1, 2)]),
    ),
  )
  assert_true(s.hilbert_function_values(3) is Some([1, 3, 6, 10]))
  assert_eq(s.krull_dimension(), p.degree() + 1)
  // Plane conic (any quadric): P = 2t + 1, degree 2, genus 0.
  let conic = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [2, 0, 0]), (1, [0, 2, 0]), (1, [0, 0, 2])]),
  ])
  let pc = hp_of(conic)
  assert_eq(pc.display(), "2*t + 1")
  assert_true(conic.projective_degree() is Some(2))
  assert_true(conic.arithmetic_genus() is Some(0))
  // HF: 1, 3, 5, 7 -- note HF(1) = 3 = P(1) here, but HF(0) = P(0) = 1.
  assert_true(conic.hilbert_function_values(3) is Some([1, 3, 5, 7]))
  // Hilbert series numerator over (1-t)^3 is 1 - t^2.
  match conic.hilbert_series_numerator() {
    Some(k) => {
      assert_eq(k.length(), 3)
      assert_true(k[0] == 1 && k[1] == 0 && k[2] == -1)
      for d in 0..<8 {
        assert_eq(hilbert_value_from_series(k, 3, d), hf_of(conic, d))
      }
    }
    None => assert_true(false)
  }
  // Plane cubic (elliptic shape y^2 z - x^3 - x z^2): P = 3t, genus 1.
  let cubic = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [0, 2, 1]), (-1, [3, 0, 0]), (-1, [1, 0, 2])]),
  ])
  assert_eq(hp_of(cubic).display(), "3*t")
  assert_true(cubic.projective_degree() is Some(3))
  assert_true(cubic.arithmetic_genus() is Some(1))
  // HF(1) = 3 != P(1) = 3 here; but HF(2) = 6 = P(2). Small degrees are
  // pinned: 1, 3, 6, 9 -- here agreement begins early (hypersurface).
  assert_true(cubic.hilbert_function_values(3) is Some([1, 3, 6, 9]))
  // General plane curve degree d genus (d-1)(d-2)/2: quartic genus 3.
  let quartic = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [4, 0, 0]), (1, [0, 4, 0]), (1, [0, 0, 4])]),
  ])
  assert_true(quartic.arithmetic_genus() is Some(3))
  assert_true(quartic.projective_degree() is Some(4))
}

///|
test "Hilbert: twisted cubic, points, complete intersections, first divergence" {
  // Twisted cubic in P^3: minors of [[x,y,z],[y,z,w]]; P = 3t + 1.
  let tc = Ideal::new(4, [
    Poly::from_int_terms(4, [(1, [0, 2, 0, 0]), (-1, [1, 0, 1, 0])]),
    Poly::from_int_terms(4, [(1, [0, 1, 1, 0]), (-1, [1, 0, 0, 1])]),
    Poly::from_int_terms(4, [(1, [0, 0, 2, 0]), (-1, [0, 1, 0, 1])]),
  ])
  let ptc = hp_of(tc)
  assert_eq(ptc.display(), "3*t + 1")
  assert_true(tc.projective_degree() is Some(3))
  assert_true(tc.arithmetic_genus() is Some(0))
  assert_eq(tc.krull_dimension(), 2)
  // Two points in P^2, ideal (z, xy): P = 2 (constant), dim Proj = 0.
  let two_pts = Ideal::new(3, [
    Poly::variable(3, 2),
    Poly::from_int_terms(3, [(1, [1, 1, 0])]),
  ])
  assert_eq(hp_of(two_pts).display(), "2")
  assert_true(two_pts.projective_dimension_via_hilbert() is Some(0))
  assert_true(two_pts.projective_degree() is Some(2))
  // HF starts 1, 2, 2, 2 -- HF(0) = 1 != P(0) = 2: Hilbert function and
  // polynomial genuinely differ in low degree. This div is asserted so
  // an implementation that just returns HF interpolation near 0 cannot
  // accidentally pass by redefining P.
  assert_true(two_pts.hilbert_function_values(3) is Some([1, 2, 2, 2]))
  assert_eq(hp_of(two_pts).eval_int_exact(0), 2)
  // Complete intersection of two quadrics in P^2: 4 points, P = 4.
  let ci = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [2, 0, 0]), (-1, [0, 0, 2])]),
    Poly::from_int_terms(3, [(1, [0, 2, 0]), (-1, [0, 0, 2])]),
  ])
  assert_eq(hp_of(ci).display(), "4")
  assert_true(ci.hilbert_function_values(4) is Some([1, 3, 4, 4, 4]))
  // Agreement theorem: beyond the certified bound, HF(d) = P(d) exactly.
  for ideal in [tc, two_pts, ci] {
    let bound = match ideal.hilbert_agreement_bound() {
      Some(b) => b
      None => abort("homogeneous expected")
    }
    let pol = hp_of(ideal)
    for d in bound..<(bound + 4) {
      assert_eq(hf_of(ideal, d), pol.eval_int_exact(d))
    }
    // And projective dimension + 1 = Krull dimension of the cone ring.
    assert_eq(ideal.krull_dimension(), pol.degree() + 1)
  }
}

///|
test "Hilbert: nonreduced schemes counted with multiplicity; refusal cases" {
  // Double line in P^2: (x^2). Its Hilbert polynomial equals the conic's:
  // degree counts the multiplicity 2. Nice scheme-theoretic content.
  let double_line = Ideal::new(3, [Poly::from_int_terms(3, [(1, [2, 0, 0])])])
  assert_eq(hp_of(double_line).display(), "2*t + 1")
  assert_true(double_line.projective_degree() is Some(2))
  // A fat point of length 3 supported at [0:0:1]: (x,y)^2 in P^2.
  // Graded pieces for d >= 1 are spanned by z^d, x z^{d-1}, y z^{d-1}.
  // (Adding z itself would make the radical the irrelevant ideal and
  // Proj empty -- that wrong example is exactly what this guards.)
  let fat = Ideal::new(3, [
    Poly::from_int_terms(3, [(1, [2, 0, 0])]),
    Poly::from_int_terms(3, [(1, [1, 1, 0])]),
    Poly::from_int_terms(3, [(1, [0, 2, 0])]),
  ])
  assert_eq(hp_of(fat).display(), "3")
  // Empty projective scheme: unit ideal has P = 0.
  assert_true(hp_of(Ideal::unit_ideal(3)).is_zero())
  assert_true(Ideal::unit_ideal(3).projective_degree() is None)
  // Non-homogeneous ideals are refused (None everywhere), not faked.
  let affine = Ideal::new(2, [
    Poly::from_int_terms(2, [(1, [0, 1]), (-1, [2, 0])]),
  ])
  assert_true(affine.hilbert_polynomial() is None)
  assert_true(affine.hilbert_function(2) is None)
  assert_true(affine.hilbert_series_numerator() is None)
}
