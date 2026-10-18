// =============================================================================
// rat.mbt -- exact rational numbers and univariate polynomials over Q.
//
// Hilbert polynomials live in Q[t] (integer-valued but not in Z[t] in),
//  so the library needs one exact rational type. Int is 32-bit; the
//  rational arithmetic below is used for low-degree Hilbert polynomials
//  with small coefficients, and normalizing by gcd at every step keeps
//  intermediates small. No floating point is introduced.
// =============================================================================

///|
fn gcd_int(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let r = x % y
    x = y
    y = r
  }
  x
}

///|
/// Factorial as Int. Only used with tiny inputs (variable counts).
pub fn factorial_int(n : Int32) -> Int32 {
  if n < 0 {
    abort("factorial_int: negative input")
  }
  let mut r = 1
  for i in 2..<(n + 1) {
    r = r * i
  }
  r
}

///|
/// Binomial coefficient C(n, k) for n >= 0 as an exact Int; 0 when
/// k < 0 or k > n. This is the *counting* convention used in Hilbert
/// functions (not the polynomial continuation to negative n).
pub fn binom_int(n : Int32, k : Int32) -> Int32 {
  if k < 0 || n < 0 || k > n {
    return 0
  }
  let kk = if k > n - k { n - k } else { k }
  let mut r = 1
  for i in 0..<kk {
    // Divide at each step: the partial product C(n, i+1) stays integral.
    r = r * (n - i) / (i + 1)
  }
  r
}

///|
pub struct Rat {
  num : Int32
  den : Int32 // invariant: den > 0, gcd(|num|, den) = 1, zero is 0/1
} derive(Eq)

///|
pub extend Rat with Eq::{equal, not_equal}

///|
pub fn Rat::new(num : Int32, den : Int32) -> Rat {
  if den == 0 {
    abort("Rat::new: zero denominator")
  }
  if num == 0 {
    return { num: 0, den: 1, }
  }
  let g = gcd_int(num, den)
  let mut n = num / g
  let mut d = den / g
  if d < 0 {
    n = -n
    d = -d
  }
  { num: n, den: d, }
}

///|
pub fn Rat::from_int(n : Int32) -> Rat {
  { num: n, den: 1, }
}

///|
pub fn Rat::zero() -> Rat {
  Rat::from_int(0)
}

///|
pub fn Rat::one() -> Rat {
  Rat::from_int(1)
}

///|
pub fn Rat::is_zero(self : Rat) -> Bool {
  self.num == 0
}

///|
pub fn Rat::is_negative(self : Rat) -> Bool {
  self.num < 0
}

///|
pub fn Rat::abs(self : Rat) -> Rat {
  if self.num < 0 {
    { num: -self.num, den: self.den, }
  } else {
    self
  }
}

///|
pub fn Rat::is_integer(self : Rat) -> Bool {
  self.den == 1
}

///|
pub fn Rat::to_int_exact(self : Rat) -> Int32 {
  if self.den != 1 {
    abort("Rat::to_int_exact: not an integer")
  }
  self.num
}

///|
pub fn Rat::display(self : Rat) -> String {
  if self.den == 1 {
    "\{self.num}"
  } else {
    "\{self.num}/\{self.den}"
  }
}

///|
pub impl Add for Rat with fn add(self, other) {
  Rat::new(self.num * other.den + other.num * self.den, self.den * other.den)
}

///|
pub extend Rat with Add::{add}

///|
pub impl Sub for Rat with fn sub(self, other) {
  Rat::new(self.num * other.den - other.num * self.den, self.den * other.den)
}

///|
pub extend Rat with Sub::{sub}

///|
pub impl Mul for Rat with fn mul(self, other) {
  Rat::new(self.num * other.num, self.den * other.den)
}

///|
pub extend Rat with Mul::{mul}

///|
pub impl Neg for Rat with fn neg(self) {
  { num: -self.num, den: self.den, }
}

///|
pub extend Rat with Neg::{neg}

///|
pub fn Rat::div_rat(self : Rat, other : Rat) -> Rat {
  if other.num == 0 {
    abort("Rat::div_rat: division by zero")
  }
  Rat::new(self.num * other.den, self.den * other.num)
}

// -----------------------------------------------------------------------------
// Univariate polynomials over Q (coefficients low -> high, trimmed).
// -----------------------------------------------------------------------------

///|
pub struct RatPoly {
  coeffs : Array[Rat]
}

///|
pub fn RatPoly::from_coeffs(coeffs : Array[Rat]) -> RatPoly {
  let cs : Array[Rat] = []
  for c in coeffs {
    cs.push(c)
  }
  while cs.length() > 0 && cs[cs.length() - 1].is_zero() {
    let _ = cs.pop()
  }
  { coeffs: cs, }
}

///|
pub fn RatPoly::zero() -> RatPoly {
  { coeffs: [], }
}

///|
pub fn RatPoly::constant(c : Rat) -> RatPoly {
  RatPoly::from_coeffs([c])
}

///|
/// The polynomial (t + a).
pub fn RatPoly::linear(a : Rat) -> RatPoly {
  RatPoly::from_coeffs([a, Rat::one()])
}

///|
pub fn RatPoly::degree(self : RatPoly) -> Int32 {
  self.coeffs.length() - 1
}

///|
pub fn RatPoly::is_zero(self : RatPoly) -> Bool {
  self.coeffs.length() == 0
}

///|
pub fn RatPoly::coeff(self : RatPoly, i : Int32) -> Rat {
  match self.coeffs.get(i) {
    Some(c) => c
    None => Rat::zero()
  }
}

///|
pub fn RatPoly::leading_coefficient(self : RatPoly) -> Rat {
  if self.is_zero() {
    abort("RatPoly::leading_coefficient: zero polynomial")
  }
  self.coeffs[self.coeffs.length() - 1]
}

///|
pub fn RatPoly::equal_to(self : RatPoly, other : RatPoly) -> Bool {
  if self.coeffs.length() != other.coeffs.length() {
    return false
  }
  for i in 0..<self.coeffs.length() {
    if self.coeffs[i] != other.coeffs[i] {
      return false
    }
  }
  true
}

///|
pub fn RatPoly::add(self : RatPoly, other : RatPoly) -> RatPoly {
  let n = if self.coeffs.length() > other.coeffs.length() {
    self.coeffs.length()
  } else {
    other.coeffs.length()
  }
  let cs : Array[Rat] = []
  for i in 0..<n {
    cs.push(self.coeff(i) + other.coeff(i))
  }
  RatPoly::from_coeffs(cs)
}

///|
pub fn RatPoly::sub(self : RatPoly, other : RatPoly) -> RatPoly {
  let n = if self.coeffs.length() > other.coeffs.length() {
    self.coeffs.length()
  } else {
    other.coeffs.length()
  }
  let cs : Array[Rat] = []
  for i in 0..<n {
    cs.push(self.coeff(i) - other.coeff(i))
  }
  RatPoly::from_coeffs(cs)
}

///|
pub fn RatPoly::mul(self : RatPoly, other : RatPoly) -> RatPoly {
  if self.is_zero() || other.is_zero() {
    return RatPoly::zero()
  }
  let cs : Array[Rat] = []
  for _ in 0..<(self.coeffs.length() + other.coeffs.length() - 1) {
    cs.push(Rat::zero())
  }
  for i in 0..<self.coeffs.length() {
    for j in 0..<other.coeffs.length() {
      cs[i + j] = cs[i + j] + self.coeffs[i] * other.coeffs[j]
    }
  }
  RatPoly::from_coeffs(cs)
}

///|
pub fn RatPoly::scale(self : RatPoly, c : Rat) -> RatPoly {
  let cs : Array[Rat] = []
  for x in self.coeffs {
    cs.push(x * c)
  }
  RatPoly::from_coeffs(cs)
}

///|
/// Evaluate at an integer (Horner over Q).
pub fn RatPoly::eval_int(self : RatPoly, t : Int32) -> Rat {
  let tt = Rat::from_int(t)
  let mut acc = Rat::zero()
  let mut i = self.coeffs.length() - 1
  while i >= 0 {
    acc = acc * tt + self.coeffs[i]
    i = i - 1
  }
  acc
}

///|
/// Evaluate at an integer and require an integer result (Hilbert
/// polynomials are integer-valued; a non-integer here means a bug).
pub fn RatPoly::eval_int_exact(self : RatPoly, t : Int32) -> Int32 {
  self.eval_int(t).to_int_exact()
}

///|
pub fn RatPoly::display(self : RatPoly) -> String {
  if self.is_zero() {
    return "0"
  }
  let sb = StringBuilder()
  let mut first = true
  let mut i = self.coeffs.length() - 1
  while i >= 0 {
    let c = self.coeffs[i]
    if !c.is_zero() {
      if first {
        if c.is_negative() {
          sb.write_string("-")
        }
      } else if c.is_negative() {
        sb.write_string(" - ")
      } else {
        sb.write_string(" + ")
      }
      first = false
      let a = c.abs()
      if i == 0 {
        sb.write_string(a.display())
      } else {
        if a != Rat::one() {
          sb.write_string(a.display())
          sb.write_string("*")
        }
        sb.write_string("t")
        if i > 1 {
          sb.write_string("^")
          sb.write_string("\{i}")
        }
      }
    }
    i = i - 1
  }
  sb.to_string()
}
