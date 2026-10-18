// arena/affine_algebra: exact affine and projective algebraic geometry
// over F_7, with finite affine schemes.
//
// The library is organized by computational level:
//   fp.mbt           finite field F_7 and vectors
//   poly.mbt         sparse polynomials, lex order, division, S-polynomials
//   univariate.mbt   F_7[t]: division, gcd, irreducible factorisation
//   groebner.mbt     Buchberger, ideals, intersection/saturation, dimensions
//   quotient.mbt     quotient rings R/I by Groebner normal forms
//   linalg.mbt       exact linear algebra over F_7
//   finalg.mbt       finite F_7-algebras, product/tensor/quotient/localize
//   variety.mbt      affine varieties, coordinate rings, pullback
//   localization.mbt S^{-1}(R/I), Rabinowitsch iso, local ring at a point
//   category.mbt     type-level products/sums and universal properties
//   rat.mbt          exact rationals and rational polynomials
//   hilbert.mbt      Hilbert functions, series, polynomials and invariants
//   primary.mbt      nilradicals, splitting, primary decomposition
//   projective.mbt   projective points/varieties, embeddings, PGL action
//   scheme.mbt       finite affine schemes, stalks, sections, morphisms
//
// See THEORY.md for definitions, theorems, formulas, and the exact
// theorem -> algorithm -> test correspondence.
