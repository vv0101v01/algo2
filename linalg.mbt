// =============================================================================
// linalg.mbt -- exact linear algebra over F_p: Gauss-Jordan (RREF), rank,
// nullspace, solving, inversion, spans and coordinates.
// Matrices are row-major Array[Array[Fp]]; a matrix acts on column vectors.
// =============================================================================

///|
pub struct Matrix {
  rows : Int32
  cols : Int32
  data : Array[Array[Fp]]
}

///|
pub fn Matrix::zero(rows : Int32, cols : Int32) -> Matrix {
  let data : Array[Array[Fp]] = []
  for _ in 0..<rows {
    data.push(vec_zero(cols))
  }
  { rows, cols, data, }
}

///|
pub fn Matrix::identity(n : Int32) -> Matrix {
  let m = Matrix::zero(n, n)
  for i in 0..<n {
    m.data[i][i] = Fp::one()
  }
  m
}

///|
pub fn Matrix::from_rows(data : Array[Array[Fp]]) -> Matrix {
  let rows = data.length()
  let cols = if rows == 0 { 0 } else { data[0].length() }
  for r in data {
    if r.length() != cols {
      abort("Matrix::from_rows: ragged rows")
    }
  }
  let copy : Array[Array[Fp]] = []
  for r in data {
    copy.push(vec_copy(r))
  }
  { rows, cols, data: copy, }
}

///|
pub fn Matrix::num_rows(self : Matrix) -> Int32 {
  self.rows
}

///|
pub fn Matrix::num_cols(self : Matrix) -> Int32 {
  self.cols
}

///|
pub fn Matrix::get(self : Matrix, i : Int32, j : Int32) -> Fp {
  self.data[i][j]
}

///|
pub fn Matrix::row(self : Matrix, i : Int32) -> Array[Fp] {
  vec_copy(self.data[i])
}

///|
pub fn Matrix::equal_to(self : Matrix, other : Matrix) -> Bool {
  if self.rows != other.rows || self.cols != other.cols {
    return false
  }
  for i in 0..<self.rows {
    if !vec_eq(self.data[i], other.data[i]) {
      return false
    }
  }
  true
}

///|
pub fn Matrix::mul(self : Matrix, other : Matrix) -> Matrix {
  if self.cols != other.rows {
    abort("Matrix::mul: shape mismatch")
  }
  let r = Matrix::zero(self.rows, other.cols)
  for i in 0..<self.rows {
    for k in 0..<self.cols {
      if self.data[i][k].is_zero() {
        continue
      }
      for j in 0..<other.cols {
        r.data[i][j] = r.data[i][j] + self.data[i][k] * other.data[k][j]
      }
    }
  }
  r
}

///|
pub fn Matrix::mul_vec(self : Matrix, v : Array[Fp]) -> Array[Fp] {
  if self.cols != v.length() {
    // A 0x0 matrix acting on the zero vector is legitimate (zero ring).
    if !(self.rows == 0 && v.length() == 0) {
      abort("Matrix::mul_vec: shape mismatch")
    }
  }
  let r : Array[Fp] = []
  for i in 0..<self.rows {
    let mut acc = Fp::zero()
    for j in 0..<self.cols {
      acc = acc + self.data[i][j] * v[j]
    }
    r.push(acc)
  }
  r
}

///|
/// Reduced row echelon form plus the list of pivot columns, in row order.
pub fn Matrix::rref(self : Matrix) -> (Matrix, Array[Int32]) {
  let a = Matrix::from_rows(self.data)
  let pivots : Array[Int32] = []
  let mut row = 0
  for col in 0..<self.cols {
    if row >= self.rows {
      break
    }
    // Find a pivot.
    let mut pivot_row = -1
    for r in row..<self.rows {
      if !a.data[r][col].is_zero() {
        pivot_row = r
        break
      }
    }
    if pivot_row < 0 {
      continue
    }
    if pivot_row != row {
      let tmp = a.data[row]
      a.data[row] = a.data[pivot_row]
      a.data[pivot_row] = tmp
    }
    let inv = a.data[row][col].inv()
    for j in 0..<self.cols {
      a.data[row][j] = a.data[row][j] * inv
    }
    // Eliminate this column from every other row (Gauss-Jordan).
    for r in 0..<self.rows {
      if r != row && !a.data[r][col].is_zero() {
        let factor = a.data[r][col]
        for j in 0..<self.cols {
          a.data[r][j] = a.data[r][j] - factor * a.data[row][j]
        }
      }
    }
    pivots.push(col)
    row = row + 1
  }
  (a, pivots)
}

///|
pub fn Matrix::rank(self : Matrix) -> Int32 {
  let (_, pivots) = self.rref()
  pivots.length()
}

///|
/// Basis of { x | A x = 0 } (right nullspace), one vector per free column.
pub fn Matrix::nullspace(self : Matrix) -> Array[Array[Fp]] {
  let (r, pivots) = self.rref()
  let is_pivot : Array[Bool] = []
  for _ in 0..<self.cols {
    is_pivot.push(false)
  }
  for p in pivots {
    is_pivot[p] = true
  }
  let basis : Array[Array[Fp]] = []
  for free in 0..<self.cols {
    if is_pivot[free] {
      continue
    }
    let v = vec_zero(self.cols)
    v[free] = Fp::one()
    for ri in 0..<pivots.length() {
      v[pivots[ri]] = -r.data[ri][free]
    }
    basis.push(v)
  }
  basis
}

///|
/// Solve A x = b. Some particular solution (free variables = 0), or None
/// if the system is inconsistent. Solvability is decided exactly: this is
/// the test behind "is this element a unit?" and "is this vector in the
/// span?" in finite algebras.
pub fn Matrix::solve(self : Matrix, b : Array[Fp]) -> Array[Fp]? {
  if b.length() != self.rows {
    if self.rows == 0 && b.length() == 0 {
      return Some([])
    }
    abort("Matrix::solve: shape mismatch")
  }
  let aug_rows : Array[Array[Fp]] = []
  for i in 0..<self.rows {
    let r = vec_copy(self.data[i])
    r.push(b[i])
    aug_rows.push(r)
  }
  let aug = Matrix::from_rows(aug_rows)
  let (r, pivots) = aug.rref()
  for p in pivots {
    if p == self.cols {
      return None
    }
  }
  let x = vec_zero(self.cols)
  for ri in 0..<pivots.length() {
    x[pivots[ri]] = r.data[ri][self.cols]
  }
  Some(x)
}

///|
pub fn Matrix::inverse(self : Matrix) -> Matrix? {
  if self.rows != self.cols {
    return None
  }
  let n = self.rows
  if n == 0 {
    return Some(Matrix::zero(0, 0))
  }
  let aug_rows : Array[Array[Fp]] = []
  for i in 0..<n {
    let r = vec_copy(self.data[i])
    for j in 0..<n {
      r.push(if i == j { Fp::one() } else { Fp::zero() })
    }
    aug_rows.push(r)
  }
  let aug = Matrix::from_rows(aug_rows)
  let (r, _) = aug.rref()
  // Counting pivots is NOT enough: for singular A a pivot can land in the
  // augmented half (e.g. [[1,2],[2,4]] gives pivots [0,2]). Invertible
  // iff the left half of the RREF is exactly the identity.
  for i in 0..<n {
    for j in 0..<n {
      let expected = if i == j { Fp::one() } else { Fp::zero() }
      if r.data[i][j] != expected {
        return None
      }
    }
  }
  let inv_rows : Array[Array[Fp]] = []
  for i in 0..<n {
    let row : Array[Fp] = []
    for j in 0..<n {
      row.push(r.data[i][n + j])
    }
    inv_rows.push(row)
  }
  Some(Matrix::from_rows(inv_rows))
}

///|
/// A basis (RREF rows) of the span of the given vectors.
pub fn span_basis(vectors : Array[Array[Fp]]) -> Array[Array[Fp]] {
  if vectors.length() == 0 {
    return []
  }
  let m = Matrix::from_rows(vectors)
  let (r, _) = m.rref()
  let basis : Array[Array[Fp]] = []
  for i in 0..<r.rows {
    if !vec_is_zero(r.data[i]) {
      basis.push(vec_copy(r.data[i]))
    }
  }
  basis
}

///|
pub fn vec_in_span(v : Array[Fp], basis : Array[Array[Fp]]) -> Bool {
  if vec_is_zero(v) {
    return true
  }
  let extended : Array[Array[Fp]] = []
  for b in basis {
    extended.push(b)
  }
  extended.push(v)
  span_basis(extended).length() == span_basis(basis).length()
}

///|
/// Coordinates of v in the given basis (basis vectors as columns), if v is
/// in their span and they are linearly independent.
pub fn coordinates_in_basis(
  v : Array[Fp],
  basis : Array[Array[Fp]],
) -> Array[Fp]? {
  let d = v.length()
  let cols = basis.length()
  let m = Matrix::zero(d, cols)
  for j in 0..<cols {
    if basis[j].length() != d {
      abort("coordinates_in_basis: dimension mismatch")
    }
    for i in 0..<d {
      m.data[i][j] = basis[j][i]
    }
  }
  m.solve(v)
}

///|
pub fn Matrix::transpose(self : Matrix) -> Matrix {
  let rows : Array[Array[Fp]] = []
  for j in 0..<self.cols {
    let row : Array[Fp] = []
    for i in 0..<self.rows {
      row.push(self.data[i][j])
    }
    rows.push(row)
  }
  Matrix::from_rows(rows)
}

///|
pub fn Matrix::display(self : Matrix) -> String {
  let sb = StringBuilder()
  for i in 0..<self.rows {
    sb.write_string(vec_display(self.data[i]))
    if i + 1 < self.rows {
      sb.write_string("; ")
    }
  }
  sb.to_string()
}
