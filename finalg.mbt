// =============================================================================
// finalg.mbt -- finite-dimensional commutative F_p-algebras by structure
// constants, their elements, homomorphisms (as matrices), and the closure
// operations: direct product, tensor product, quotient by an ideal, and
// localization at one element.
//
// An algebra A is (dim d, constants c_{ij}^k with e_i e_j = sum_k c_{ij}^k e_k,
// coordinates of 1). Every construction is a theorem turned into linear
// algebra:
//   * product   A x B      : block-diagonal constants
//   * tensor    A (x) B    : Kronecker product of constants
//   * quotient  A / I      : choose a vector-space complement of I, project
//   * localize  A_f (A finite): A / { a | f^N a = 0 for some N } -- valid
//     because in a finite ring an element whose multiplication map is
//     injective is a unit (injective => surjective on a finite set).
// Homomorphisms are matrices; being a homomorphism is *checked*
// (unit + all basis products), so claimed isomorphisms in the tests are
// verified, not asserted.
// =============================================================================

///|
pub struct FinAlg {
  name : String
  dim : Int32
  mult : Array[Fp] // flat, index ((i*dim)+j)*dim + k
  one_vec : Array[Fp]
  tag : Int32
}

///|
pub struct FinElem {
  coords : Array[Fp]
  tag : Int32
}

///|
fn structural_tag_of_algebra(
  dim : Int32,
  mult : Array[Fp],
  one_vec : Array[Fp],
) -> Int32 {
  let mut h = (dim * 31 + 11) % 1000003
  for c in mult {
    h = (h * 131 + c.to_int() + 1) % 1000003
  }
  for c in one_vec {
    h = (h * 131 + c.to_int() + 3) % 1000003
  }
  h
}

///|
pub fn FinAlg::from_structure(
  name : String,
  dim : Int32,
  mult : Array[Fp],
  one_vec : Array[Fp],
) -> FinAlg {
  if mult.length() != dim * dim * dim || one_vec.length() != dim {
    abort("FinAlg::from_structure: shape mismatch")
  }
  let mc : Array[Fp] = []
  for c in mult {
    mc.push(c)
  }
  {
    name,
    dim,
    mult: mc,
    one_vec: vec_copy(one_vec),
    tag: structural_tag_of_algebra(dim, mult, one_vec),
  }
}

///|
pub fn FinAlg::name(self : FinAlg) -> String {
  self.name
}

///|
pub fn FinAlg::dim(self : FinAlg) -> Int32 {
  self.dim
}

///|
pub fn FinAlg::elem(self : FinAlg, coords : Array[Fp]) -> FinElem {
  if coords.length() != self.dim {
    abort("FinAlg::elem: coordinate length != dimension")
  }
  { coords: vec_copy(coords), tag: self.tag, }
}

///|
pub fn FinAlg::zero_elem(self : FinAlg) -> FinElem {
  { coords: vec_zero(self.dim), tag: self.tag, }
}

///|
pub fn FinAlg::one_elem(self : FinAlg) -> FinElem {
  { coords: vec_copy(self.one_vec), tag: self.tag, }
}

///|
pub fn FinAlg::basis_elem(self : FinAlg, i : Int32) -> FinElem {
  { coords: vec_basis(self.dim, i), tag: self.tag, }
}

///|
pub fn FinAlg::scalar_elem(self : FinAlg, c : Fp) -> FinElem {
  { coords: vec_scale(c, self.one_vec), tag: self.tag, }
}

///|
fn check_elem(a : FinAlg, x : FinElem) -> Unit {
  if x.tag != a.tag || x.coords.length() != a.dim {
    abort("FinAlg: element does not belong to this algebra")
  }
}

///|
pub fn FinAlg::add(self : FinAlg, x : FinElem, y : FinElem) -> FinElem {
  check_elem(self, x)
  check_elem(self, y)
  { coords: vec_add(x.coords, y.coords), tag: self.tag, }
}

///|
pub fn FinAlg::sub(self : FinAlg, x : FinElem, y : FinElem) -> FinElem {
  check_elem(self, x)
  check_elem(self, y)
  { coords: vec_sub(x.coords, y.coords), tag: self.tag, }
}

///|
pub fn FinAlg::scale(self : FinAlg, c : Fp, x : FinElem) -> FinElem {
  check_elem(self, x)
  { coords: vec_scale(c, x.coords), tag: self.tag, }
}

///|
pub fn FinAlg::mul(self : FinAlg, x : FinElem, y : FinElem) -> FinElem {
  check_elem(self, x)
  check_elem(self, y)
  let d = self.dim
  let out = vec_zero(d)
  for i in 0..<d {
    if x.coords[i].is_zero() {
      continue
    }
    for j in 0..<d {
      if y.coords[j].is_zero() {
        continue
      }
      let c = x.coords[i] * y.coords[j]
      let base = (i * d + j) * d
      for k in 0..<d {
        out[k] = out[k] + c * self.mult[base + k]
      }
    }
  }
  { coords: out, tag: self.tag, }
}

///|
pub fn FinAlg::pow(self : FinAlg, x : FinElem, e : Int32) -> FinElem {
  let mut r = self.one_elem()
  for _ in 0..<e {
    r = self.mul(r, x)
  }
  r
}

///|
pub fn FinElem::coords(self : FinElem) -> Array[Fp] {
  vec_copy(self.coords)
}

///|
pub fn FinElem::equal_to(self : FinElem, other : FinElem) -> Bool {
  self.tag == other.tag && vec_eq(self.coords, other.coords)
}

///|
pub fn FinElem::display(self : FinElem) -> String {
  vec_display(self.coords)
}

///|
/// Verify the commutative-algebra axioms on basis elements:
/// commutativity and associativity on basis pairs/triples, two-sided unit.
/// (Distributivity is automatic: multiplication is extended bilinearly from
/// the constants -- and the tests also check full ring axioms on arbitrary
/// pseudo-random elements.)
pub fn FinAlg::check_axioms(self : FinAlg) -> Bool {
  let one = self.one_elem()
  for i in 0..<self.dim {
    let ei = self.basis_elem(i)
    if !self.mul(one, ei).equal_to(ei) {
      return false
    }
    for j in 0..<self.dim {
      let ej = self.basis_elem(j)
      if !self.mul(ei, ej).equal_to(self.mul(ej, ei)) {
        return false
      }
      for k in 0..<self.dim {
        let ek = self.basis_elem(k)
        let lhs = self.mul(self.mul(ei, ej), ek)
        let rhs = self.mul(ei, self.mul(ej, ek))
        if !lhs.equal_to(rhs) {
          return false
        }
      }
    }
  }
  true
}

///|
pub fn FinAlg::random_elem(self : FinAlg, rng : Rng) -> FinElem {
  let c : Array[Fp] = []
  for _ in 0..<self.dim {
    c.push(rng.fp())
  }
  { coords: c, tag: self.tag, }
}

///|
/// Matrix of the F_p-linear map "multiply by x", acting on column vectors.
pub fn FinAlg::mult_matrix(self : FinAlg, x : FinElem) -> Matrix {
  check_elem(self, x)
  let d = self.dim
  // Column j is x * e_j; assemble row by row.
  let cols : Array[Array[Fp]] = []
  for j in 0..<d {
    cols.push(self.mul(x, self.basis_elem(j)).coords)
  }
  let rows : Array[Array[Fp]] = []
  for k in 0..<d {
    let row : Array[Fp] = []
    for j in 0..<d {
      row.push(cols[j][k])
    }
    rows.push(row)
  }
  Matrix::from_rows(rows)
}

///|
/// Inverse of x if it is a unit, found by solving m_x(y) = 1 exactly.
pub fn FinAlg::try_inv(self : FinAlg, x : FinElem) -> FinElem? {
  match self.mult_matrix(x).solve(vec_copy(self.one_vec)) {
    Some(coords) => Some({ coords, tag: self.tag, })
    None => None
  }
}

///|
pub fn FinAlg::is_unit(self : FinAlg, x : FinElem) -> Bool {
  self.try_inv(x) is Some(_)
}

// -----------------------------------------------------------------------------
// Constructors: field, function algebra, product, tensor, from quotient.
// -----------------------------------------------------------------------------

///|
/// The ground field itself as a 1-dimensional algebra.
pub fn FinAlg::ground_field() -> FinAlg {
  FinAlg::from_structure("F_7", 1, [Fp::one()], [Fp::one()])
}

///|
/// The algebra of F_p-valued functions on a finite set of `npoints` points:
/// basis of delta-functions delta_a with delta_a * delta_b = delta_{ab}
/// delta_a, unit = constant 1 = (1,...,1). This is simultaneously the
/// direct product F_p^n and (proved in the tests via interpolation) the
/// coordinate ring of any n-point affine variety.
pub fn FinAlg::function_algebra(name : String, npoints : Int32) -> FinAlg {
  let d = npoints
  let mult : Array[Fp] = []
  for _ in 0..<(d * d * d) {
    mult.push(Fp::zero())
  }
  for i in 0..<d {
    mult[(i * d + i) * d + i] = Fp::one()
  }
  let one_vec : Array[Fp] = []
  for _ in 0..<d {
    one_vec.push(Fp::one())
  }
  FinAlg::from_structure(name, d, mult, one_vec)
}

///|
/// Direct product A x B of algebras (componentwise operations): basis is
/// the disjoint union of bases, constants are block diagonal. Universal
/// property (product in F_p-Alg): homs C -> A x B are pairs of homs.
pub fn FinAlg::product(a : FinAlg, b : FinAlg, name : String) -> FinAlg {
  let (da, db) = (a.dim, b.dim)
  let d = da + db
  let mult : Array[Fp] = []
  for _ in 0..<(d * d * d) {
    mult.push(Fp::zero())
  }
  for i in 0..<da {
    for j in 0..<da {
      for k in 0..<da {
        mult[(i * d + j) * d + k] = a.mult[(i * da + j) * da + k]
      }
    }
  }
  for i in 0..<db {
    for j in 0..<db {
      for k in 0..<db {
        mult[((da + i) * d + (da + j)) * d + (da + k)] = b.mult[(i * db + j) *
          db +
          k]
      }
    }
  }
  let one_vec : Array[Fp] = []
  for c in a.one_vec {
    one_vec.push(c)
  }
  for c in b.one_vec {
    one_vec.push(c)
  }
  FinAlg::from_structure(name, d, mult, one_vec)
}

///|
/// Pair embedding: (x, y) in A x B from x in A, y in B.
pub fn product_elem(prod : FinAlg, x : FinElem, y : FinElem) -> FinElem {
  let coords : Array[Fp] = []
  for c in x.coords {
    coords.push(c)
  }
  for c in y.coords {
    coords.push(c)
  }
  prod.elem(coords)
}

///|
/// Tensor product A ⊗_{F_p} B: basis e_i ⊗ f_j (index i*dimB + j),
/// constants are the Kronecker product c^A c^B. Universal property:
/// F_p-bilinear maps A x B -> C correspond to linear maps A⊗B -> C, and
/// for algebras it is the coproduct: homs A⊗B -> C are pairs of homs.
pub fn FinAlg::tensor(a : FinAlg, b : FinAlg, name : String) -> FinAlg {
  let (da, db) = (a.dim, b.dim)
  let d = da * db
  let mult : Array[Fp] = []
  for _ in 0..<(d * d * d) {
    mult.push(Fp::zero())
  }
  for i in 0..<da {
    for j in 0..<db {
      for i2 in 0..<da {
        for j2 in 0..<db {
          for i3 in 0..<da {
            for j3 in 0..<db {
              let ca = a.mult[(i * da + i2) * da + i3]
              let cb = b.mult[(j * db + j2) * db + j3]
              if !ca.is_zero() && !cb.is_zero() {
                mult[((i * db + j) * d + (i2 * db + j2)) * d + (i3 * db + j3)] = ca *
                  cb
              }
            }
          }
        }
      }
    }
  }
  let one_vec = vec_zero(d)
  for i in 0..<da {
    for j in 0..<db {
      one_vec[i * db + j] = a.one_vec[i] * b.one_vec[j]
    }
  }
  FinAlg::from_structure(name, d, mult, one_vec)
}

///|
/// Pure tensor x ⊗ y inside `t = A ⊗ B`.
pub fn pure_tensor(b : FinAlg, t : FinAlg, x : FinElem, y : FinElem) -> FinElem {
  let coords = vec_zero(t.dim)
  for i in 0..<x.coords.length() {
    for j in 0..<y.coords.length() {
      coords[i * b.dim + j] = x.coords[i] * y.coords[j]
    }
  }
  t.elem(coords)
}

// -----------------------------------------------------------------------------
// From polynomial quotients: the monomial staircase is an explicit basis.
// -----------------------------------------------------------------------------

///|
pub struct QuotientModel {
  ring : QuotientRing
  alg : FinAlg
  basis : Array[Mono]
}

///|
/// Build the structure-constant model of a zero-dimensional quotient.
/// None when the quotient is infinite-dimensional -- there, structure
/// constants do not exist and we say so instead of truncating silently.
pub fn QuotientModel::new(ring : QuotientRing, name : String) -> QuotientModel? {
  match ring.ideal().standard_monomials() {
    None => None
    Some(basis) => {
      let d = basis.length()
      let n = ring.num_vars()
      let basis_polys : Array[Poly] = []
      for m in basis {
        let e : Array[Int32] = []
        for i in 0..<n {
          e.push(m.exp_at(i))
        }
        basis_polys.push(Poly::monomial(n, Fp::one(), e))
      }
      let mult : Array[Fp] = []
      for _ in 0..<(d * d * d) {
        mult.push(Fp::zero())
      }
      for i in 0..<d {
        for j in 0..<d {
          let nf = ring.ideal().normal_form(basis_polys[i].mul(basis_polys[j]))
          for k in 0..<d {
            mult[(i * d + j) * d + k] = nf.coeff_of(basis[k])
          }
        }
      }
      let one_vec : Array[Fp] = []
      let one_nf = ring.ideal().normal_form(Poly::one_poly(n))
      for k in 0..<d {
        one_vec.push(one_nf.coeff_of(basis[k]))
      }
      Some({ ring, alg: FinAlg::from_structure(name, d, mult, one_vec), basis, })
    }
  }
}

///|
pub fn QuotientModel::algebra(self : QuotientModel) -> FinAlg {
  self.alg
}

///|
pub fn QuotientModel::basis_monomials(self : QuotientModel) -> Array[Mono] {
  self.basis
}

///|
pub fn QuotientModel::ring(self : QuotientModel) -> QuotientRing {
  self.ring
}

///|
pub fn QuotientModel::to_elem(self : QuotientModel, c : Coset) -> FinElem {
  check_coset(self.ring, c)
  let coords : Array[Fp] = []
  for m in self.basis {
    coords.push(c.repr_poly().coeff_of(m))
  }
  self.alg.elem(coords)
}

///|
pub fn QuotientModel::to_coset(self : QuotientModel, x : FinElem) -> Coset {
  check_elem(self.alg, x)
  let n = self.ring.num_vars()
  let mut acc = Poly::zero(n)
  for k in 0..<self.basis.length() {
    let m = self.basis[k]
    let e : Array[Int32] = []
    for i in 0..<n {
      e.push(m.exp_at(i))
    }
    acc = acc.add(Poly::monomial(n, x.coords[k], e))
  }
  self.ring.of_poly(acc)
}

// -----------------------------------------------------------------------------
// Homomorphisms as matrices, with verification.
// -----------------------------------------------------------------------------

///|
pub struct AlgHom {
  mat : Matrix // (codim x domdim), acting on column coordinate vectors
}

///|
pub fn AlgHom::from_basis_images(images : Array[FinElem]) -> AlgHom {
  let domdim = images.length()
  let coddim = if domdim == 0 { 0 } else { images[0].coords.length() }
  if coddim == 0 && domdim > 0 {
    // Zero codomain: the matrix has no rows, but its width must still
    // record the domain dimension (from_rows([]) would lose it).
    return { mat: Matrix::zero(0, domdim), }
  }
  let rows : Array[Array[Fp]] = []
  for r in 0..<coddim {
    let row : Array[Fp] = []
    for c in 0..<domdim {
      row.push(images[c].coords[r])
    }
    rows.push(row)
  }
  { mat: Matrix::from_rows(rows), }
}

///|
pub fn AlgHom::from_matrix(mat : Matrix) -> AlgHom {
  { mat, }
}

///|
pub fn AlgHom::matrix(self : AlgHom) -> Matrix {
  self.mat
}

///|
pub fn AlgHom::identity(dim : Int32) -> AlgHom {
  { mat: Matrix::identity(dim), }
}

///|
pub fn AlgHom::apply(self : AlgHom, cod : FinAlg, x : FinElem) -> FinElem {
  cod.elem(self.mat.mul_vec(x.coords))
}

///|
/// Decide whether this linear map is an F_p-algebra homomorphism dom -> cod
/// by checking 1 |-> 1 and all d^2 basis products. Linearity + scalar
/// compatibility are automatic for a matrix, so this check is complete.
pub fn AlgHom::verify(self : AlgHom, dom : FinAlg, cod : FinAlg) -> Bool {
  if self.mat.num_rows() != cod.dim || self.mat.num_cols() != dom.dim {
    // Zero-algebra corner: a 0x0 matrix between zero algebras verifies.
    if dom.dim != 0 || cod.dim != 0 {
      return false
    }
  }
  if dom.dim == 0 || cod.dim == 0 {
    // Zero ring corner cases, by the universal properties:
    //  * into the zero ring: a unique hom always exists (zero ring is the
    //    terminal ring; 1 maps to 1 = 0 there) -- any 0-row matrix of the
    //    right width represents it;
    //  * out of the zero ring into a nonzero ring: none, since it would
    //    force 1_cod = 0_cod.
    if cod.dim == 0 {
      return self.mat.num_rows() == 0 && self.mat.num_cols() == dom.dim
    }
    return false
  }
  if !self.apply(cod, dom.one_elem()).equal_to(cod.one_elem()) {
    return false
  }
  for i in 0..<dom.dim {
    for j in 0..<dom.dim {
      let lhs = self.apply(cod, dom.mul(dom.basis_elem(i), dom.basis_elem(j)))
      let rhs = cod.mul(
        self.apply(cod, dom.basis_elem(i)),
        self.apply(cod, dom.basis_elem(j)),
      )
      if !lhs.equal_to(rhs) {
        return false
      }
    }
  }
  true
}

///|
/// Composition self ∘ other (other applied first).
pub fn AlgHom::compose(self : AlgHom, other : AlgHom) -> AlgHom {
  { mat: self.mat.mul(other.mat), }
}

///|
/// Decide isomorphism: homomorphism both ways with inverse matrices.
pub fn AlgHom::is_isomorphism(
  self : AlgHom,
  dom : FinAlg,
  cod : FinAlg,
) -> Bool {
  if !self.verify(dom, cod) {
    return false
  }
  match self.mat.inverse() {
    None => false
    Some(inv) => AlgHom::from_matrix(inv).verify(cod, dom)
  }
}

///|
/// Coproduct universal property of the tensor product: algebra homs
/// phi : A -> C and psi : B -> C induce a unique hom A ⊗ B -> C with
/// e_i ⊗ f_j |-> phi(e_i)·psi(f_j) (well-defined because images commute in
/// the commutative ring C; uniqueness because pure tensors span A ⊗ B).
/// The returned matrix is the hom out of FinAlg::tensor(a, b, _); caller
/// verifies with AlgHom::verify, including that phi/psi are homs.
pub fn tensor_copair_hom(
  a : FinAlg,
  b : FinAlg,
  c : FinAlg,
  phi : AlgHom,
  psi : AlgHom,
) -> AlgHom {
  let images : Array[FinElem] = []
  for i in 0..<a.dim {
    for j in 0..<b.dim {
      images.push(
        c.mul(phi.apply(c, a.basis_elem(i)), psi.apply(c, b.basis_elem(j))),
      )
    }
  }
  AlgHom::from_basis_images(images)
}

///|
/// Product universal property, matrix form: homs phi : C -> A, psi : C -> B
/// pair to a hom C -> A x B by stacking coordinates. `prod` must be
/// FinAlg::product(a, b, _).
pub fn product_pair_hom(
  a : FinAlg,
  b : FinAlg,
  c : FinAlg,
  prod : FinAlg,
  phi : AlgHom,
  psi : AlgHom,
) -> AlgHom {
  let images : Array[FinElem] = []
  for i in 0..<c.dim {
    let x = phi.apply(a, c.basis_elem(i))
    let y = psi.apply(b, c.basis_elem(i))
    images.push(product_elem(prod, x, y))
  }
  AlgHom::from_basis_images(images)
}

// -----------------------------------------------------------------------------
// Ideals of a FinAlg, quotients by them, localization at one element.
// -----------------------------------------------------------------------------

///|
/// Basis of the ideal generated by `g`: span of { g * e_i }.
pub fn FinAlg::principal_ideal_basis(
  self : FinAlg,
  g : FinElem,
) -> Array[Array[Fp]] {
  let gens : Array[Array[Fp]] = []
  for i in 0..<self.dim {
    gens.push(self.mul(g, self.basis_elem(i)).coords)
  }
  span_basis(gens)
}

///|
/// Basis of the ideal generated by a list of elements.
pub fn FinAlg::ideal_basis_of(
  self : FinAlg,
  generators : Array[FinElem],
) -> Array[Array[Fp]] {
  let gens : Array[Array[Fp]] = []
  for g in generators {
    for i in 0..<self.dim {
      gens.push(self.mul(g, self.basis_elem(i)).coords)
    }
  }
  span_basis(gens)
}

///|
/// Test whether a subspace (given by a basis) is an ideal: closed under
/// multiplication by every basis element of the algebra.
pub fn FinAlg::is_ideal_subspace(
  self : FinAlg,
  basis : Array[Array[Fp]],
) -> Bool {
  for v in basis {
    let x = self.elem(v)
    for i in 0..<self.dim {
      if !vec_in_span(self.mul(x, self.basis_elem(i)).coords, basis) {
        return false
      }
    }
  }
  true
}

///|
pub struct FinQuotient {
  quotient : FinAlg
  cob_inv : Matrix // inverse of [ideal basis | lifts] change-of-basis (columns)
  ideal_dim : Int32
  source_tag : Int32
}

///|
/// Quotient of a finite algebra by an ideal subspace. A complement of the
/// ideal is chosen greedily from the standard basis; multiplication of
/// cosets is lifted, multiplied, and projected. Aborts if the subspace is
/// not actually an ideal -- otherwise the "quotient" would not be a ring
/// and pretending otherwise is exactly the kind of fake we refuse.
pub fn FinAlg::quotient_by_subspace(
  self : FinAlg,
  subspace : Array[Array[Fp]],
  name : String,
) -> FinQuotient {
  let ideal_basis = span_basis(subspace)
  if !self.is_ideal_subspace(ideal_basis) {
    abort("FinAlg::quotient_by_subspace: subspace is not an ideal")
  }
  let d = self.dim
  // Greedy complement from standard basis vectors.
  let lifts : Array[Array[Fp]] = []
  let current : Array[Array[Fp]] = []
  for v in ideal_basis {
    current.push(v)
  }
  let mut cur_rank = span_basis(current).length()
  for i in 0..<d {
    if cur_rank == d {
      break
    }
    let e = vec_basis(d, i)
    let trial : Array[Array[Fp]] = []
    for v in current {
      trial.push(v)
    }
    trial.push(e)
    let r = span_basis(trial).length()
    if r > cur_rank {
      lifts.push(e)
      current.push(e)
      cur_rank = r
    }
  }
  let qd = lifts.length()
  // Change-of-basis matrix P: columns = ideal basis followed by lifts.
  let cols_all : Array[Array[Fp]] = []
  for v in ideal_basis {
    cols_all.push(v)
  }
  for v in lifts {
    cols_all.push(v)
  }
  let p_rows : Array[Array[Fp]] = []
  for r in 0..<d {
    let row : Array[Fp] = []
    for c in 0..<d {
      row.push(cols_all[c][r])
    }
    p_rows.push(row)
  }
  let p = Matrix::from_rows(p_rows)
  let pinv = match p.inverse() {
    Some(inv) => inv
    None => abort("FinAlg::quotient_by_subspace: basis change singular (bug)")
  }
  let project_coords = fn(v : Array[Fp]) -> Array[Fp] {
    if d == 0 {
      return []
    }
    let all = pinv.mul_vec(v)
    let out : Array[Fp] = []
    for k in 0..<qd {
      out.push(all[ideal_basis.length() + k])
    }
    out
  }
  let mult : Array[Fp] = []
  for _ in 0..<(qd * qd * qd) {
    mult.push(Fp::zero())
  }
  for i in 0..<qd {
    for j in 0..<qd {
      let prod = self.mul(self.elem(lifts[i]), self.elem(lifts[j]))
      let pc = project_coords(prod.coords)
      for k in 0..<qd {
        mult[(i * qd + j) * qd + k] = pc[k]
      }
    }
  }
  let one_q = project_coords(self.one_vec)
  {
    quotient: FinAlg::from_structure(name, qd, mult, one_q),
    cob_inv: pinv,
    ideal_dim: ideal_basis.length(),
    source_tag: self.tag,
  }
}

///|
pub fn FinQuotient::algebra(self : FinQuotient) -> FinAlg {
  self.quotient
}

///|
/// The quotient map A -> A/I on elements.
pub fn FinQuotient::project(self : FinQuotient, x : FinElem) -> FinElem {
  if x.tag != self.source_tag {
    abort("FinQuotient::project: element from a different algebra")
  }
  if x.coords.length() == 0 {
    return self.quotient.zero_elem()
  }
  let all = self.cob_inv.mul_vec(x.coords)
  let out : Array[Fp] = []
  for k in 0..<self.quotient.dim {
    out.push(all[self.ideal_dim + k])
  }
  self.quotient.elem(out)
}

///|
/// The quotient map as an AlgHom (for verification with `AlgHom::verify`).
pub fn FinQuotient::as_hom(self : FinQuotient, source : FinAlg) -> AlgHom {
  let images : Array[FinElem] = []
  for i in 0..<source.dim {
    images.push(self.project(source.basis_elem(i)))
  }
  AlgHom::from_basis_images(images)
}

///|
/// Localization A_f of a *finite* algebra A at the multiplicative set
/// {1, f, f^2, ...}. Algorithm (theorem): let K = { a | f^N a = 0, some N }
/// be the stable kernel of multiplication-by-f. Then A_f ≅ A/K, because
/// the kernel of A -> A_f is exactly K, and in A/K the map m_fbar is
/// injective, hence (finite-dimensionality!) surjective, so fbar is
/// already a unit and A/K has the universal property of A_f.
/// Returns the quotient data for A/K together with its projection map.
pub fn FinAlg::localize_at(
  self : FinAlg,
  f : FinElem,
  name : String,
) -> FinQuotient {
  let m = self.mult_matrix(f)
  let mut power = m
  let mut kernel = m.nullspace()
  let mut prev_dim = -1
  let mut rounds = 0
  while kernel.length() != prev_dim {
    rounds = rounds + 1
    if rounds > self.dim + 2 {
      abort("FinAlg::localize_at: kernel chain did not stabilize (bug)")
    }
    prev_dim = kernel.length()
    power = power.mul(m)
    kernel = power.nullspace()
  }
  self.quotient_by_subspace(kernel, name)
}
