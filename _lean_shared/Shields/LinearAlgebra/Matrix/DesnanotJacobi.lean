/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Data.Fin.SuccPred

/-!
# Desnanot--Jacobi condensation

Dodgson condensation: for a square matrix of size `m + 2`, the determinant times the doubly-deleted
interior minor equals the difference of the two products of corner minors.

## Main results

* `Shields.desnanot_jacobi`: the classical corner-minor form,
  `det A * det A^{0,last}_{0,last} = det A^0_0 * det A^{last}_{last} - det A^{last}_0 * det
  A^0_{last}`, over an arbitrary commutative ring and **with no hypothesis on `det A`**.
* `Shields.desnanot_jacobi_adjugate`: Jacobi's classical adjugate form, the `2 × 2` corner minor
  of `adjugate A` equal to `det A` times the interior minor of `A`.
* `Shields.desnanot_jacobi_adjugate_mul_det`: the same adjugate form, premultiplied by `det A`.
* `Shields.det_auxN`: the auxiliary-matrix determinant that drives both.

## Implementation notes

The auxiliary matrix `auxN A` agrees with the identity off two columns, so Weinstein--Aronszajn
(`Matrix.det_one_add_mul_comm`) reduces its `(m + 2) × (m + 2)` determinant to a `2 × 2` one in a
single move -- no induction over the `m` standard-basis columns is required.

Canceling the extra `det A` is the only step that could cost hypotheses, and it does not: the
cancellation is performed once in the generic matrix `Matrix.mvPolynomialX`, whose entries are
independent indeterminates over `ℤ`, so the coefficient ring is a domain and the determinant is
nonzero there. Every `A` is an evaluation of that matrix, and adjugate, determinant and
`cornerCleared` all commute with the evaluation homomorphism.

Mathlib has no condensation identity at the pinned revision. One is in flight as
`feat(LinearAlgebra/Matrix/Determinant): Desnanot-Jacobi identity` (#37716).

## Tags

determinant, Desnanot-Jacobi, Dodgson condensation, adjugate, minor
-/

namespace Shields

open Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

/-! ### The auxiliary matrix

Jacobi's identity runs through an auxiliary matrix whose columns `0` and `last`
are the corresponding columns of `adjugate A` and whose other columns are
standard basis vectors. -/

/-- The auxiliary matrix: columns `0` and `last` are the corresponding columns of
`adjugate A`, the rest are standard basis vectors. -/
noncomputable def auxN (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  Matrix.of fun i j =>
    if j = 0 then adjugate A i 0
    else if j = Fin.last (m + 1) then adjugate A i (Fin.last (m + 1))
    else if i = j then 1 else 0

/-- **The construction's key identity.**  `A · N` has `det A` in the two corners,
zeros elsewhere in those columns, and `A`'s own columns in between.

Taking determinants, `det A · det N = det(A·N)`, and the right side expands to
`det A ² · det(interior)` by clearing the two corner columns.  Canceling one
`det A` leaves `det N = det A · det(interior)`, and `det N` is exactly the `2×2`
minor of `adjugate A` at the corners. -/
theorem mul_auxN_apply (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (i j : Fin (m + 2)) :
    (A * auxN A) i j =
      if j = 0 then (if i = 0 then A.det else 0)
      else if j = Fin.last (m + 1) then (if i = Fin.last (m + 1) then A.det else 0)
      else A i j := by
  rw [Matrix.mul_apply]
  by_cases h0 : j = 0
  · subst h0
    simp only [auxN, Matrix.of_apply, if_true]
    have := Matrix.mul_adjugate A
    have hij := congrFun (congrFun this i) 0
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hij
    rw [hij]
    by_cases hi : i = 0 <;> simp [hi]
  · by_cases hl : j = Fin.last (m + 1)
    · subst hl
      simp only [auxN, Matrix.of_apply, if_neg h0, if_true]
      have := Matrix.mul_adjugate A
      have hij := congrFun (congrFun this i) (Fin.last (m + 1))
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hij
      rw [hij]
      by_cases hi : i = Fin.last (m + 1) <;> simp [hi]
    · simp only [auxN, Matrix.of_apply, if_neg h0, if_neg hl]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; rw [if_neg hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h

/-- **Expansion along a basis-vector column.**  If column `c` of `M` is the
standard basis vector `e_r`, the determinant collapses to the single signed minor
obtained by deleting row `r` and column `c`.

This is the workhorse of the first determinant reduction: `det (A · auxN A)` has
two such columns after `det A` is factored out. -/
theorem det_of_basis_column (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (r c : Fin (m + 1))
    (hcol : ∀ i, M i c = if i = r then 1 else 0) :
    M.det = (-1) ^ ((r : ℕ) + (c : ℕ)) * (M.submatrix r.succAbove c.succAbove).det := by
  rw [Matrix.det_succ_column _ c, Finset.sum_eq_single r]
  · rw [hcol r, if_pos rfl, mul_one]
  · intro i _ hi
    rw [hcol i, if_neg hi, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- The matrix left after `det A` is factored out of both corner columns: columns
`0` and `last` are standard basis vectors, the rest are `A`'s. -/
noncomputable def cornerCleared (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  Matrix.of fun i j =>
    if j = 0 then (if i = 0 then 1 else 0)
    else if j = Fin.last (m + 1) then (if i = Fin.last (m + 1) then 1 else 0)
    else A i j

/-- **`det (A · auxN A) = (det A)² · det (cornerCleared A)`.**  Each corner column
of `A · auxN A` carries a factor `det A`; pulling both out leaves
`cornerCleared A`. -/
theorem det_mul_auxN (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    (A * auxN A).det = A.det * A.det * (cornerCleared A).det := by
  have hfact : A * auxN A
      = Matrix.of fun i j =>
          (if j = 0 then A.det else if j = Fin.last (m + 1) then A.det else 1)
            * cornerCleared A i j := by
    ext i j
    rw [mul_auxN_apply, Matrix.of_apply, cornerCleared, Matrix.of_apply]
    by_cases h0 : j = 0
    · subst h0; by_cases hi : i = 0 <;> simp [hi]
    · by_cases hl : j = Fin.last (m + 1)
      · subst hl; by_cases hi : i = Fin.last (m + 1) <;> simp [h0, hi]
      · simp [h0, hl]
  rw [hfact, Matrix.det_mul_row]
  congr 1
  -- The scaling product is `det A` twice: every other column carries `1`.
  have hne : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    simp [Fin.ext_iff]
  rw [← Finset.prod_subset (Finset.subset_univ ({0, Fin.last (m + 1)} : Finset (Fin (m + 2))))]
  · rw [Finset.prod_pair hne]
    simp
  · intro c _ hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [if_neg hc.1, if_neg hc.2]

/-- Clearing column `0` of `cornerCleared A`, which is the basis vector `e_0`. -/
theorem det_cornerCleared_step (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    (cornerCleared A).det
      = ((cornerCleared A).submatrix
          (0 : Fin (m + 2)).succAbove (0 : Fin (m + 2)).succAbove).det := by
  rw [det_of_basis_column _ (0 : Fin (m + 2)) (0 : Fin (m + 2))
    (fun i => by simp [cornerCleared])]
  simp

/-- After deleting row and column `0`, the last column of what remains is again a
basis vector — the second corner of `cornerCleared A`. -/
theorem cornerCleared_last_col (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (k : Fin (m + 1)) :
    ((cornerCleared A).submatrix (0 : Fin (m + 2)).succAbove (0 : Fin (m + 2)).succAbove)
        k (Fin.last m)
      = if k = Fin.last m then (1 : R) else 0 := by
  have hl : ((Fin.last m).succ : Fin (m + 2)) = Fin.last (m + 1) := rfl
  have hiff : (k.succ = Fin.last (m + 1)) ↔ (k = Fin.last m) := by
    constructor
    · intro h; exact Fin.succ_injective _ (by rw [h, ← hl])
    · intro h; rw [h, hl]
  simp only [Matrix.submatrix_apply, Fin.zero_succAbove, cornerCleared, Matrix.of_apply, hl,
    if_neg (show ¬ (Fin.last (m + 1) : Fin (m + 2)) = 0 by simp [Fin.ext_iff])]
  by_cases hk : k = Fin.last m
  · rw [if_pos (hiff.mpr hk), if_pos hk]; simp
  · rw [if_neg (fun hc => hk (hiff.mp hc)), if_neg hk]; simp

/-- **The first determinant reduction, complete.**
`det (A · auxN A) = (det A)² · det(interior of A)`, where the interior deletes rows
and columns `0` and `last`. -/
theorem det_mul_auxN_eq_interior (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    (A * auxN A).det
      = A.det * A.det *
        (((cornerCleared A).submatrix
            (0 : Fin (m + 2)).succAbove (0 : Fin (m + 2)).succAbove).submatrix
          (Fin.last m).succAbove (Fin.last m).succAbove).det := by
  rw [det_mul_auxN, det_cornerCleared_step,
    det_of_basis_column _ (Fin.last m) (Fin.last m) (cornerCleared_last_col A)]
  simp

/-! ### The second reduction, by Weinstein--Aronszajn

`auxN A` differs from the identity in exactly two columns, so it is `1 + UV` with
`U` of width `2` and `V` of height `2`.  `Matrix.det_one_add_mul_comm` then trades
the `(m + 2) × (m + 2)` determinant for a `2 × 2` one, which *is* the corner minor of
the adjugate. -/

/-- The two column corrections of `auxN A` against the identity. -/
noncomputable def auxU (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    Matrix (Fin (m + 2)) (Fin 2) R :=
  Matrix.of fun i b =>
    if b = 0 then adjugate A i 0 - (if i = 0 then 1 else 0)
    else adjugate A i (Fin.last (m + 1)) - (if i = Fin.last (m + 1) then 1 else 0)

/-- Selection of the coordinates `0` and `last`. -/
def auxV (m : ℕ) : Matrix (Fin 2) (Fin (m + 2)) R :=
  Matrix.of fun b i =>
    if b = 0 then (if i = 0 then 1 else 0) else (if i = Fin.last (m + 1) then 1 else 0)

/-- `auxN A` is a rank-`≤2` correction of the identity. -/
theorem auxN_eq_one_add (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    auxN A = 1 + auxU A * auxV (R := R) m := by
  have hne : ¬ (0 : Fin (m + 2)) = Fin.last (m + 1) := by simp [Fin.ext_iff]
  ext i j
  have hmul : (auxU A * auxV (R := R) m) i j
      = (adjugate A i 0 - (if i = 0 then 1 else 0)) * (if j = 0 then 1 else 0)
        + (adjugate A i (Fin.last (m + 1)) - (if i = Fin.last (m + 1) then 1 else 0))
          * (if j = Fin.last (m + 1) then 1 else 0) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, auxU, auxV]
  rw [auxN, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, hmul]
  by_cases h0 : j = 0
  · subst h0; by_cases hi : i = 0 <;> simp [hi, hne]
  · by_cases hl : j = Fin.last (m + 1)
    · subst hl; by_cases hi : i = Fin.last (m + 1) <;> simp [hi, h0]
    · simp [h0, hl]

/-- **The second determinant reduction.**  `det (auxN A)` is the `2×2` corner minor
of `adjugate A`, by Weinstein--Aronszajn. -/
theorem det_auxN (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    (auxN A).det
      = adjugate A 0 0 * adjugate A (Fin.last (m + 1)) (Fin.last (m + 1))
        - adjugate A 0 (Fin.last (m + 1)) * adjugate A (Fin.last (m + 1)) 0 := by
  have hne : ¬ (0 : Fin (m + 2)) = Fin.last (m + 1) := by simp [Fin.ext_iff]
  rw [auxN_eq_one_add, Matrix.det_one_add_mul_comm]
  have hentry : ∀ a b : Fin 2,
      ((1 : Matrix (Fin 2) (Fin 2) R) + auxV (R := R) m * auxU A) a b
      = if a = 0 then (if b = 0 then adjugate A 0 0 else adjugate A 0 (Fin.last (m + 1)))
        else (if b = 0 then adjugate A (Fin.last (m + 1)) 0
              else adjugate A (Fin.last (m + 1)) (Fin.last (m + 1))) := by
    intro a b
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply]
    simp only [auxU, auxV, Matrix.of_apply]
    fin_cases a <;> fin_cases b <;> simp [hne, Ne.symm hne]
  rw [Matrix.det_fin_two, hentry, hentry, hentry, hentry]
  simp

/-- **Desnanot--Jacobi, multiplied through by `det A`, in adjugate form.**
Combining the two reductions:
\[
  \det A\cdot\bigl(\operatorname{adj}A_{00}\operatorname{adj}A_{ll}
    -\operatorname{adj}A_{0l}\operatorname{adj}A_{l0}\bigr)
  = (\det A)^2\,\det(\text{interior}),
\]
unconditionally, for every commutative ring. -/
theorem desnanot_jacobi_adjugate_mul_det (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    A.det * (adjugate A 0 0 * adjugate A (Fin.last (m + 1)) (Fin.last (m + 1))
        - adjugate A 0 (Fin.last (m + 1)) * adjugate A (Fin.last (m + 1)) 0)
      = A.det * A.det *
        (((cornerCleared A).submatrix
            (0 : Fin (m + 2)).succAbove (0 : Fin (m + 2)).succAbove).submatrix
          (Fin.last m).succAbove (Fin.last m).succAbove).det := by
  rw [← det_auxN, ← Matrix.det_mul, det_mul_auxN_eq_interior]

/-! ### From adjugate entries to submatrix determinants

The four adjugate entries at the corners are the four deleted-row-and-column
minors, and the two off-diagonal signs cancel against one another in the product.
The interior of `cornerCleared A` is the interior of `A`, because
`cornerCleared` alters only columns `0` and `last`. -/

/-- Deleting row and column `0` — the top-left corner minor. -/
theorem adjugate_corner_zero_zero (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    adjugate A 0 0 = (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix A 0 0]
  simp

/-- Deleting the last row and the last column — the bottom-right corner minor.
The sign `(-1)^{2(m + 1)}` is `1`. -/
theorem adjugate_corner_last_last (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    adjugate A (Fin.last (m + 1)) (Fin.last (m + 1))
      = (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix A (Fin.last (m + 1)) (Fin.last (m + 1)),
    Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨m + 1, rfl⟩, one_mul]

/-- The two off-diagonal corners each carry the sign `(-1)^{m + 1}`, so their product
is the plain product of the two anti-diagonal minors: deleting row `0` with column
`last`, and row `last` with column `0`. -/
theorem adjugate_corner_offdiag_mul (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    adjugate A 0 (Fin.last (m + 1)) * adjugate A (Fin.last (m + 1)) 0
      = (A.submatrix Fin.succ Fin.castSucc).det
        * (A.submatrix Fin.castSucc Fin.succ).det := by
  have hsq : (-1 : R) ^ (m + 1) * (-1 : R) ^ (m + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, rfl⟩
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix A 0 (Fin.last (m + 1)),
    Matrix.adjugate_fin_succ_eq_det_submatrix A (Fin.last (m + 1)) 0, Fin.succAbove_last,
    Fin.succAbove_zero,
    Fin.val_last, Fin.val_zero, add_zero, zero_add, mul_mul_mul_comm, hsq, one_mul]
  exact mul_comm _ _

/-- The interior of `cornerCleared A` is the interior of `A`: `cornerCleared`
alters only columns `0` and `last`, and the interior index map `i ↦ i.castSucc.succ`
lands on neither. -/
theorem cornerCleared_interior (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    ((cornerCleared A).submatrix
        (0 : Fin (m + 2)).succAbove (0 : Fin (m + 2)).succAbove).submatrix
      (Fin.last m).succAbove (Fin.last m).succAbove
      = A.submatrix (fun i : Fin m => i.castSucc.succ) fun j : Fin m => j.castSucc.succ := by
  ext i j
  have hne0 : (j.castSucc.succ : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero _
  have hnel : (j.castSucc.succ : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last, cornerCleared,
    Matrix.of_apply, if_neg hne0, if_neg hnel]

/-! ### Desnanot--Jacobi -/

/-- **Desnanot--Jacobi, multiplied through by `det A`.**  Holds for every
commutative ring and every matrix. -/
theorem desnanot_jacobi_mul_det (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    A.det *
        (A.det * (A.submatrix (fun i : Fin m => i.castSucc.succ)
          fun j : Fin m => j.castSucc.succ).det)
      = A.det *
        ((A.submatrix Fin.succ Fin.succ).det * (A.submatrix Fin.castSucc Fin.castSucc).det
          - (A.submatrix Fin.succ Fin.castSucc).det
            * (A.submatrix Fin.castSucc Fin.succ).det) := by
  have h := desnanot_jacobi_adjugate_mul_det A
  rw [adjugate_corner_zero_zero, adjugate_corner_last_last, adjugate_corner_offdiag_mul,
    cornerCleared_interior] at h
  exact (mul_assoc A.det A.det _).symm.trans h.symm

/-- **Desnanot--Jacobi condensation over a domain.**  With `det A ≠ 0` the factor
`det A` cancels from `desnanot_jacobi_mul_det`. -/
theorem desnanot_jacobi_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (hA : A.det ≠ 0) :
    A.det * (A.submatrix (fun i : Fin m => i.castSucc.succ)
        fun j : Fin m => j.castSucc.succ).det
      = (A.submatrix Fin.succ Fin.succ).det * (A.submatrix Fin.castSucc Fin.castSucc).det
        - (A.submatrix Fin.succ Fin.castSucc).det
          * (A.submatrix Fin.castSucc Fin.succ).det :=
  mul_left_cancel₀ hA (desnanot_jacobi_mul_det A)

/-- A ring homomorphism carries a determinant to the determinant of the mapped
matrix. -/
private theorem map_det_map {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] {n : ℕ}
    (f : S₁ →+* S₂) (M : Matrix (Fin n) (Fin n) S₁) : f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

/-- A ring homomorphism carries the determinant of a submatrix to the determinant
of the corresponding submatrix of the mapped matrix. -/
private theorem map_submatrix_det {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] {n p : ℕ}
    (f : S₁ →+* S₂) (M : Matrix (Fin n) (Fin n) S₁) (e₁ e₂ : Fin p → Fin n) :
    f (M.submatrix e₁ e₂).det = ((M.map f).submatrix e₁ e₂).det := by
  rw [RingHom.map_det]; rfl

/-- **Desnanot--Jacobi condensation.**  For every commutative ring `R` and every
`(m + 2) × (m + 2)` matrix `A` over `R`,
\[
  \det A\cdot\det A^{0,l}_{0,l}
    = \det A^{0}_{0}\cdot\det A^{l}_{l} - \det A^{0}_{l}\cdot\det A^{l}_{0}.
\]
Both sides are polynomials with integer coefficients in the entries of `A`, so
the identity is settled on the generic matrix over
`MvPolynomial (Fin (m + 2) × Fin (m + 2)) ℤ` — a domain whose generic determinant is
nonzero, where `desnanot_jacobi_of_det_ne_zero` applies — and transported to `A`
along the evaluation homomorphism carrying the generic matrix to `A`. -/
theorem desnanot_jacobi (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    A.det * (A.submatrix (fun i : Fin m => i.castSucc.succ)
        fun j : Fin m => j.castSucc.succ).det
      = (A.submatrix Fin.succ Fin.succ).det * (A.submatrix Fin.castSucc Fin.castSucc).det
        - (A.submatrix Fin.succ Fin.castSucc).det
          * (A.submatrix Fin.castSucc Fin.succ).det := by
  have hgen := desnanot_jacobi_of_det_ne_zero
    (Matrix.mvPolynomialX (Fin (m + 2)) (Fin (m + 2)) ℤ)
    (Matrix.det_mvPolynomialX_ne_zero _ _)
  have hX : (Matrix.mvPolynomialX (Fin (m + 2)) (Fin (m + 2)) ℤ).map
      ⇑(MvPolynomial.eval₂Hom (Int.castRingHom R)
        fun p : Fin (m + 2) × Fin (m + 2) => A p.1 p.2) = A := by
    rw [MvPolynomial.coe_eval₂Hom]
    exact Matrix.mvPolynomialX_map_eval₂ _ A
  have h1 : (MvPolynomial.eval₂Hom (Int.castRingHom R)
        fun p : Fin (m + 2) × Fin (m + 2) => A p.1 p.2)
      (Matrix.mvPolynomialX (Fin (m + 2)) (Fin (m + 2)) ℤ).det = A.det := by
    rw [map_det_map, hX]
  have h2 : ∀ (p : ℕ) (e₁ e₂ : Fin p → Fin (m + 2)),
      (MvPolynomial.eval₂Hom (Int.castRingHom R)
          fun q : Fin (m + 2) × Fin (m + 2) => A q.1 q.2)
        ((Matrix.mvPolynomialX (Fin (m + 2)) (Fin (m + 2)) ℤ).submatrix e₁ e₂).det
        = (A.submatrix e₁ e₂).det := by
    intro p e₁ e₂
    rw [map_submatrix_det, hX]
  have himg := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R)
    fun p : Fin (m + 2) × Fin (m + 2) => A p.1 p.2) hgen
  simp only [map_mul, map_sub, h1, h2] at himg
  exact himg

/-- **Jacobi's identity in adjugate form.**  The `2 × 2` corner minor of `adjugate A` is `det A`
times the interior minor, over every commutative ring and with no condition on `det A`.

This is `desnanot_jacobi` read backwards through the bridging lemmas: the four corner entries of
the adjugate are the four corner minors, and `cornerCleared` leaves the interior alone. -/
theorem desnanot_jacobi_adjugate (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    adjugate A 0 0 * adjugate A (Fin.last (m + 1)) (Fin.last (m + 1))
        - adjugate A 0 (Fin.last (m + 1)) * adjugate A (Fin.last (m + 1)) 0
      = A.det *
        (((cornerCleared A).submatrix
            (0 : Fin (m + 2)).succAbove (0 : Fin (m + 2)).succAbove).submatrix
          (Fin.last m).succAbove (Fin.last m).succAbove).det := by
  rw [adjugate_corner_zero_zero, adjugate_corner_last_last, adjugate_corner_offdiag_mul,
    cornerCleared_interior]
  exact (desnanot_jacobi A).symm


/-! ### Axiom footprint -/

/-- info: 'Shields.desnanot_jacobi_adjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms desnanot_jacobi_adjugate

end Shields
