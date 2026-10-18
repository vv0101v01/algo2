// =============================================================================
// fp.mbt -- the ground field F_p (p = PRIME, a compile-time constant) and
// vectors over it.
//
// Zero-cost note (honest version): MoonBit v0.10.15 has no user-level
// comptime/const-generic evaluation, so "compile-time" here means exactly
// what the language can guarantee:
//   * PRIME is a `const`, folded by the compiler into every operation;
//   * Fp is a single-field concrete struct (no trait objects, no closures,
//     no dynamic dispatch anywhere in arithmetic paths);
//   * +, -, * are statically-resolved trait operators on a monomorphic type.
// Anything stronger (e.g. Groebner bases at compile time) would be fake in
// this language, so we do not claim it.
// =============================================================================

///|
/// The prime of the ground field. All computations are exact over F_7:
/// no floating point is used anywhere in this project.
pub const PRIME : Int32 = 7

///|
/// An element of the finite field F_p, stored normalized in `0 <= v < p`.
/// Smart constructor `Fp::new` is the only sanctioned way to build values
/// from raw integers; every operation re-normalizes, so equality is the
/// structural equality of representatives.
pub struct Fp {
  v : Int32
} derive(Eq)

///|
pub extend Fp with Eq::{equal, not_equal}

///|
pub fn Fp::new(v : Int32) -> Fp {
  { v: (v % PRIME + PRIME) % PRIME, }
}

///|
pub fn Fp::zero() -> Fp {
  Fp::new(0)
}

///|
pub fn Fp::one() -> Fp {
  Fp::new(1)
}

///|
pub fn Fp::is_zero(self : Fp) -> Bool {
  self.v == 0
}

///|
pub fn Fp::display(self : Fp) -> String {
  "\{self.v}"
}

///|
pub impl Add for Fp with fn add(self, other) {
  Fp::new(self.v + other.v)
}

///|
pub extend Fp with Add::{add}

///|
pub impl Sub for Fp with fn sub(self, other) {
  Fp::new(self.v - other.v)
}

///|
pub extend Fp with Sub::{sub}

///|
pub impl Mul for Fp with fn mul(self, other) {
  Fp::new(self.v * other.v)
}

///|
pub extend Fp with Mul::{mul}

///|
pub impl Neg for Fp with fn neg(self) {
  Fp::new(-self.v)
}

///|
pub extend Fp with Neg::{neg}

///|
/// Multiplicative inverse via Fermat's little theorem: a^(p-2) = a^(-1).
/// Panics (abort) on 0 -- callers that cannot rule out 0 must use
/// `Fp::try_inv` and handle `None`. This is a *partial* operation of the
/// field, made explicit in the API instead of being hidden.
pub fn Fp::inv(self : Fp) -> Fp {
  match self.try_inv() {
    Some(x) => x
    None => abort("Fp::inv: inverse of zero does not exist")
  }
}

///|
pub fn Fp::try_inv(self : Fp) -> Fp? {
  if self.v == 0 {
    None
  } else {
    Some(self.pow(PRIME - 2))
  }
}

///|
pub fn Fp::pow(self : Fp, e : Int32) -> Fp {
  if e < 0 {
    abort("Fp::pow: negative exponent")
  }
  let mut result = Fp::one()
  let mut base = self
  let mut n = e
  while n > 0 {
    if n % 2 == 1 {
      result = result * base
    }
    base = base * base
    n = n / 2
  }
  result
}

///|
/// Division, defined only for nonzero denominators.
pub fn Fp::div_(self : Fp, other : Fp) -> Fp {
  self * other.inv()
}

///|
/// Least nonnegative residue as an Int (0..p-1).
pub fn Fp::to_int(self : Fp) -> Int32 {
  self.v
}

// -----------------------------------------------------------------------------
// Vectors over F_p (elements of F_p^d). Plain Arrays with explicit length
// checks: mixing vectors of different dimensions aborts instead of silently
// truncating.
// -----------------------------------------------------------------------------

///|
pub fn vec_zero(d : Int32) -> Array[Fp] {
  let r : Array[Fp] = []
  for _ in 0..<d {
    r.push(Fp::zero())
  }
  r
}

///|
pub fn vec_basis(d : Int32, i : Int32) -> Array[Fp] {
  let r = vec_zero(d)
  r[i] = Fp::one()
  r
}

///|
pub fn vec_eq(a : Array[Fp], b : Array[Fp]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
pub fn vec_add(a : Array[Fp], b : Array[Fp]) -> Array[Fp] {
  if a.length() != b.length() {
    abort("vec_add: dimension mismatch")
  }
  let r : Array[Fp] = []
  for i in 0..<a.length() {
    r.push(a[i] + b[i])
  }
  r
}

///|
pub fn vec_sub(a : Array[Fp], b : Array[Fp]) -> Array[Fp] {
  if a.length() != b.length() {
    abort("vec_sub: dimension mismatch")
  }
  let r : Array[Fp] = []
  for i in 0..<a.length() {
    r.push(a[i] - b[i])
  }
  r
}

///|
pub fn vec_scale(c : Fp, a : Array[Fp]) -> Array[Fp] {
  let r : Array[Fp] = []
  for i in 0..<a.length() {
    r.push(c * a[i])
  }
  r
}

///|
pub fn vec_is_zero(a : Array[Fp]) -> Bool {
  for i in 0..<a.length() {
    if a[i] != Fp::zero() {
      return false
    }
  }
  true
}

///|
pub fn vec_copy(a : Array[Fp]) -> Array[Fp] {
  let r : Array[Fp] = []
  for i in 0..<a.length() {
    r.push(a[i])
  }
  r
}

///|
pub fn vec_display(a : Array[Fp]) -> String {
  let sb = StringBuilder()
  sb.write_string("[")
  for i in 0..<a.length() {
    if i > 0 {
      sb.write_string(", ")
    }
    sb.write_string(a[i].display())
  }
  sb.write_string("]")
  sb.to_string()
}

// -----------------------------------------------------------------------------
// Deterministic pseudo-random generator (linear congruential) used ONLY by
// property tests, so that test runs are reproducible and failures are
// replayable from the seed. Returns values in [0, 2^31).
// -----------------------------------------------------------------------------

///|
pub struct Rng {
  mut state : Int32
}

///|
pub fn Rng::new(seed : Int32) -> Rng {
  { state: (seed % 2147483647 + 2147483647) % 2147483647 + 1, }
}

///|
pub fn Rng::next_int(self : Rng) -> Int32 {
  // Lehmer RNG modulo the Mersenne prime m = 2^31-1 with multiplier
  // a = 48271, evaluated by Schrage's method (q = m div a = 44488,
  // r = m mod a = 3399) so no intermediate exceeds 32-bit Int range:
  // a*(s mod q) <= 48271*44487 < 2^31-1 and r*(s div q) is far smaller.
  let s = self.state
  let hi = s / 44488
  let lo = s % 44488
  let mut t = 48271 * lo - 3399 * hi
  if t <= 0 {
    t = t + 2147483647
  }
  self.state = t
  t
}

///|
/// Uniform-ish element of F_p.
pub fn Rng::fp(self : Rng) -> Fp {
  Fp::new(self.next_int() % PRIME)
}

///|
/// Nonzero element of F_p.
pub fn Rng::fp_nonzero(self : Rng) -> Fp {
  Fp::new(1 + self.next_int() % (PRIME - 1))
}

///|
/// Integer in [lo, hi] inclusive (requires lo <= hi).
pub fn Rng::range(self : Rng, lo : Int32, hi : Int32) -> Int32 {
  if hi < lo {
    abort("Rng::range: empty range")
  }
  lo + self.next_int() % (hi - lo + 1)
}
