// =============================================================================
// category.mbt -- the same universal constructions at the level of MoonBit
// *types*, where the laws are enforced by the compiler:
//
//   * Prod[A,B] (cartesian product of types): to map INTO a product is to
//     give a pair of maps (`pairing`); projections `fst`/`snd` are part of
//     the structure. This mirrors products of rings/varieties below.
//   * Sum[A,B] (disjoint union of types): to map OUT of a sum is to give a
//     pair of maps (`sum_elim`, a.k.a. copairing [f,g]). Exhaustiveness of
//     `match` is checked at compile time: forgetting a case does not
//     compile. This is the compile-time half of "computation logic in the
//     type system" -- the eliminator IS the universal property.
//
// These are generic in A and B (statically resolved, no trait objects), so
// using them costs exactly the underlying data: a pair, or a tagged value.
// =============================================================================

///|
pub struct Prod[A, B] {
  fst : A
  snd : B
}

///|
pub fn[A, B] Prod::new(fst : A, snd : B) -> Prod[A, B] {
  { fst, snd, }
}

///|
/// Universal property of the product: maps X -> A and X -> B pair up to a
/// unique map X -> A x B with pi_1 ∘ <f,g> = f and pi_2 ∘ <f,g> = g
/// (uniqueness because a Prod value is determined by its projections).
pub fn[X, A, B] pairing(f : (X) -> A, g : (X) -> B) -> (X) -> Prod[A, B] {
  fn(x) { { fst: f(x), snd: g(x), } }
}

///|
pub enum Sum[A, B] {
  Inl(A)
  Inr(B)
}

///|
/// Universal property of the coproduct (disjoint union): maps A -> C and
/// B -> C copair to a unique map A + B -> C with [f,g] ∘ inl = f and
/// [f,g] ∘ inr = g. The MoonBit pattern-match exhaustiveness checker is
/// what enforces that both injections are handled.
pub fn[A, B, C] sum_elim(s : Sum[A, B], f : (A) -> C, g : (B) -> C) -> C {
  match s {
    Inl(a) => f(a)
    Inr(b) => g(b)
  }
}

///|
/// Bifunctoriality of the product: map each component independently.
/// prod_map(id, id) = id and prod_map(f,g) ∘ prod_map(f',g') are the
/// functor laws; both are tested pointwise (types are finite examples
/// there, so function equality is decided by enumeration).
pub fn[A, B, C, D] prod_map(
  p : Prod[A, B],
  f : (A) -> C,
  g : (B) -> D,
) -> Prod[C, D] {
  { fst: f(p.fst), snd: g(p.snd), }
}

///|
/// Bifunctoriality of the sum.
pub fn[A, B, C, D] sum_map(
  s : Sum[A, B],
  f : (A) -> C,
  g : (B) -> D,
) -> Sum[C, D] {
  match s {
    Inl(a) => Inl(f(a))
    Inr(b) => Inr(g(b))
  }
}

///|
/// Distributivity A x (B + C) -> (A x B) + (A x C) at the type level: in
/// Set (and in types) this canonical map is a bijection. The *geometric*
/// analogue is subtler and is handled separately for varieties -- the
/// contrast is discussed in THEORY.md.
pub fn[A, B, C] distribute(
  p : Prod[A, Sum[B, C]],
) -> Sum[Prod[A, B], Prod[A, C]] {
  match p.snd {
    Inl(b) => Inl({ fst: p.fst, snd: b, })
    Inr(c) => Inr({ fst: p.fst, snd: c, })
  }
}
