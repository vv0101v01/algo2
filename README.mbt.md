# arena/affine_algebra

A verified computational algebra library in MoonBit, working over
$F_7$. It builds, from sparse polynomial arithmetic and Groebner bases
upwards:

- coordinate rings $F_7[x]/I$ and quotient rings with normal-form
  representatives and ideal membership as exact decision procedures;
- finite-dimensional $F_7$-algebras in structure-constant form, with
  direct products, tensor products, quotients, principal localizations
  $A_f$, matrix homomorphisms and isomorphism verification;
- affine varieties over $F_7$, products, tagged disjoint unions,
  polynomial morphisms and their contravariant pullbacks, together
  with the type-level product/coproduct duality that Spec exchanges;
- localizations by principal multiplicative sets, local rings at
  points, saturation and the Rabinowitsch isomorphism;
- exact Hilbert functions, series and polynomials, with projective
  dimension, degree and arithmetic genus derived by lcm
  inclusion–exclusion over initial monomials (never by interpolation);
- primary decomposition in the monomial (any dimension), univariate
  and zero-dimensional regimes, including embedded primes;
- projective points, varieties, charts, affine cones, line duality,
  Segre and Veronese embeddings, and projective linear transformations;
- zero-dimensional affine schemes $\mathrm{Spec}(F_7[x]/I)$ with
  stalks, residue fields, lengths/multiplicities, structure-sheaf
  sections, restriction maps, principal opens, closed/reduced
  subschemes and scheme morphisms.

Nothing here is a toy model or a tautological test: every public claim
is backed by a falsifiable white-box or black-box test, including
independent cross-checks of the same theorem by different algorithms
(for example, point enumeration against saturated vanishing ideals,
and Hilbert numerators against independently derived formulas). Full
definitions, theorems and derivations are in `THEORY.md`.

## Layout

| File | Content |
|---|---|
| `fp.mbt` | $F_7$, vectors, deterministic RNG |
| `poly.mbt`, `univariate.mbt` | sparse lex polynomials; $F_7[t]$ division, gcd, trial-division factorisation |
| `groebner.mbt` | reduced Groebner bases, ideal operations, Krull dimension |
| `linalg.mbt` | exact RREF linear algebra over $F_7$ |
| `quotient.mbt`, `finalg.mbt` | quotient rings and finite algebras, homomorphisms |
| `variety.mbt`, `category.mbt` | affine varieties; type-level products/sums |
| `localization.mbt` | principal localization, local rings, Rabinowitsch |
| `rat.mbt`, `hilbert.mbt` | exact rationals; Hilbert series/polynomials |
| `primary.mbt` | zero-dimensional algebra infrastructure; primary decomposition |
| `projective.mbt` | projective points, varieties, embeddings, PGL |
| `scheme.mbt` | finite affine schemes, stalks, sections, morphisms |

## Build and test

Install MoonBit from <https://www.moonbitlang.com/download/>, then:

```sh
moon check
moon test              # also: --target js / --target wasm
moon run cmd/main      # narrated tour; prints ALL DEMO CHECKS PASSED
```

Verified with `moon 0.1.20261012`, `moonc v0.10.15`.

## Scope (enforced, not hidden)

Constructions outside the implemented exact regimes fail loudly:
Hilbert data is `None` for non-homogeneous ideals; primary
decomposition returns `None` for positive-dimensional non-monomial
ideals; `AffineScheme::spec` returns `None` for positive-dimensional
quotients; invariant violations abort with messages. See §15 of
`THEORY.md` for the precise boundaries.
