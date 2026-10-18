// arena/affine_algebra: exact affine algebraic geometry over F_7.
//
// The library is organized by computational level:
//   fp.mbt          finite field F_7 and vectors
//   poly.mbt        sparse polynomials, lex order, division, S-polynomials
//   groebner.mbt    Buchberger, ideals, intersection/saturation, dimensions
//   quotient.mbt    quotient rings R/I by Groebner normal forms
//   linalg.mbt      exact linear algebra over F_7
//   finalg.mbt      finite F_7-algebras, product/tensor/quotient/localize
//   variety.mbt     affine varieties, coordinate rings, pullback (contravariant)
//   localization.mbt S^{-1}(R/I), Rabinowitsch iso, local ring at a point
//   category.mbt    type-level products/sums and their universal properties
//
// See THEORY.md for definitions, theorems, formulas, and the exact
// theorem -> algorithm -> test correspondence.
