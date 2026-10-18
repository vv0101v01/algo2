# arena/affine_algebra

Exact affine algebraic geometry over **F_7** in MoonBit — every construction
named below is implemented as an algorithm and checked by falsifiable tests,
including the places where naive versions fail (division by a non-Groebner
basis, fraction equality in the presence of zero divisors,
$I(V(I)) \neq \sqrt{I}$ over a finite field, inverting a nilpotent).

- **Foundations**: F_7 with Fermat inverses; sparse multivariate
  polynomials in lex order; multivariate division; Buchberger's algorithm
  with the unique reduced Groebner basis.
- **Ideal calculus**: membership, equality, sum, product, intersection
  (tag-variable elimination), saturation and radical membership
  (Rabinowitsch), monomial staircase, F_7-dimension and Krull dimension.
- **Quotient rings** `R/I` by normal forms, with representative-independence,
  kernels and nilpotents tested.
- **Finite F_7-algebras** by structure constants: `check_axioms`, units by
  exact solving, homomorphisms as verified matrices, **direct products**
  (block-diagonal, pairing universal property), **tensor products**
  (Kronecker constants, bilinearity, coproduct universal property),
  quotients by ideals, localization `A_f ≅ A / {a | f^N a = 0}`.
- **Affine varieties** over F_7: point enumeration, `V`/`I`, the
  finite-field Nullstellenssatz
  `I(V(I)) = sqrt(I + (x_i^7 - x_i))` checked against brute force,
  **coordinate rings** `k[X]` as function tables with delta-polynomial
  interpolation / CRT (`k[X] ≅ prod_{a in X} F_7`, first isomorphism theorem
  verified against the staircase quotient model).
- **Products of varieties** with `k[X x Y] ≅ k[X] (x) k[Y]`;
  **disjoint unions** by the tagged embedding with computed vanishing ideal
  and `k[X ⊔ Y] ≅ k[X] x k[Y]`.
- **Contravariance**: pullback on polynomials, function tables and algebra
  homs, functor law `(g∘f)* = f* ∘ g*`, plus the Spec direction — point
  maps recovered from homs by tracking primitive idempotents (finite
  anti-equivalence).
- **Localization**: `S^{-1}(R/I)` for `S = {f^k}` with the saturation-based
  equality that is correct for non-domains; the Rabinowitsch isomorphism
  `S^{-1}(R/I) ≅ R[t]/(I, tf-1)` in both directions; the local ring at a
  point with `Option`-refused illegal denominators; extension over `R_f`
  exists iff `f` maps to a unit (decided, both directions tested).

Type-level counterparts live in `category.mbt`: `Prod`/`pairing` and
`Sum`/`sum_elim`, whose completeness is enforced by match exhaustiveness.

Theory, theorems, formulas and the theorem → algorithm → test map are in
**[THEORY.md](THEORY.md)** (in Chinese), including an explicit list of what
is *not* claimed (no compile-time Groebner bases exist in MoonBit;
ideal-indexed coset types would need dependent types; point sets are
F_7-points, with the equation level kept separate).

## Run

Requires the MoonBit toolchain (`moon` 0.1.20261012 / `moonc` v0.10.15 was
used to develop this; the official installer is
`curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash`), then
`export PATH="$HOME/.moon/bin:$PATH"`.

```bash
moon test           # full test suite
moon run cmd/main   # computed tour with self-checks
```

## Layout

| File | Contents |
|---|---|
| `fp.mbt` | F_7, vectors, deterministic RNG for property tests |
| `poly.mbt` | monomials/lex order, polynomials, division, S-polynomials |
| `groebner.mbt` | Buchberger, ideals, intersection/saturation, dimensions |
| `quotient.mbt` | quotient rings R/I via normal forms |
| `linalg.mbt` | exact linear algebra over F_7 |
| `finalg.mbt` | finite algebras, product/tensor/quotient/localization, `AlgHom` |
| `variety.mbt` | varieties, coordinate rings, morphisms & pullback |
| `localization.mbt` | `S^{-1}(R/I)`, Rabinowitsch iso, local ring at a point |
| `category.mbt` | type-level `Prod`/`Sum` universal properties |
| `*_wbtest.mbt`, `affine_algebra_test.mbt` | whitebox & public-API tests |
| `cmd/main/` | executable tour (`moon run cmd/main`) |
