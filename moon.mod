// Learn more about moon.mod configuration:
// https://docs.moonbitlang.com/en/latest/toolchain/moon/module.html
//
// To add a dependency, run this command in your terminal:
//   moon add moonbitlang/x
//
// Or manually declare it in `import`, for example:
// import {
//   "moonbitlang/x@0.4.6",
// }

name = "arena/affine_algebra"

version = "0.1.0"

readme = "README.mbt.md"

repository = ""

license = "Apache-2.0"

keywords = [
  "algebraic-geometry",
  "commutative-algebra",
  "groebner",
  "finite-fields",
]

preferred_target = "wasm"

description = "Exact affine algebraic geometry over F_7: Groebner bases, quotients, tensor/direct products, varieties, contravariant pullback, disjoint unions and localizations."
