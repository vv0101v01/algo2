# affine_algebra — contributor notes

Exact computational algebraic geometry over $\mathbb F_7$ in MoonBit.
Read `THEORY.md` before changing mathematical semantics; it is the
specification, and the tests are its falsifiable counterpart.

## Package map (single package, block style, `///|` separated)

- `fp.mbt` — $\mathbb F_7$, vectors, deterministic RNG (Schrage LCG).
- `poly.mbt`, `univariate.mbt` — sparse lex polynomials; $\mathbb F_7[t]$
  division/gcd/factorisation and minimal polynomials of algebra elements.
- `groebner.mbt` — reduced Gröbner bases, ideal operations, Krull dimension.
- `linalg.mbt`, `quotient.mbt`, `finalg.mbt` — exact linear algebra;
  quotient rings by normal form; structure-constant finite algebras,
  products/tensors/quotients/localizations and matrix homomorphisms.
- `variety.mbt`, `category.mbt`, `localization.mbt` — affine varieties,
  coordinate rings, pullbacks; type-level products/sums; principal
  localization and local rings.
- `rat.mbt`, `hilbert.mbt` — exact $\mathbb Q$, $\mathbb Q[t]$; Hilbert
  functions/series/polynomials by lcm inclusion–exclusion.
- `primary.mbt` — trace-form nilradicals, separating-element splitting,
  primary decomposition (monomial / univariate / zero-dimensional).
- `projective.mbt`, `scheme.mbt` — projective varieties and embeddings;
  finite affine schemes, stalks, sections and morphisms.

## Non-negotiable rules

- No stub mathematics. Anything outside an implemented exact regime
  returns `None` or aborts with a message; never approximate.
- Tests must be falsifiable: independent expected values or a second
  algorithm, never re-deriving the implementation's own output.
- Ring/algebra membership is guarded by structural tags
  (`check_coset`, `check_elem`); do not bypass them.

## Workflow

```sh
moon fmt
moon info
moon check
moon test                  # native; also --target js / wasm-gc
moon run cmd/main          # must print ALL DEMO CHECKS PASSED
```

Verified toolchain: `moon 0.1.20261012`, `moonc v0.10.15`.
Note: free functions must not name a typed parameter `self` (parsed as
the deprecated method shorthand), and `Array` has no `remove_at`
(rebuild the array, or `pop()` at the back).
