-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/Determinant.lean
import GluingCore.OlsonHarris.Plan.Defs

/-!
# Differentiating a Jacobi–Trudi determinant

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the first step of the derivation form of thesis Cor. 5.1.15
(`OlsonHarris2024HopfApplications`), carried out on determinants `det (h_{a_i - b_j})` with
arbitrary integer lists `a`, `b`.

* `jtDet a b`: the determinant `det (h_{a_i - b_j})_{i, j < M}`.
* `pDeriv_hh`: `∂_m h_k = h_{k - m}` for every integer `k` and `m > 0`.
* `derivation_det`, `pDeriv_jtDet`: the derivation of a determinant is the sum over the columns
  of the determinants with that column differentiated; `∂_m jtDet a b = ∑_j jtDet a (b + m e_j)`.
* `jtDet_swap`, `jtDet_perm`, `jtDet_eq_zero_of_eq`: the determinant is alternating in `b`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace MN

open MvPolynomial

/-- `∂_m h_k = h_{k - m}` for every integer `k`, when `m > 0`. -/
theorem pDeriv_hh {m : ℕ} (hm : 0 < m) (k : ℤ) : pDeriv m (hh k) = hh (k - m) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [hh_of_neg hk, hh_of_neg (by omega : k - m < 0), map_zero]
  · subst hk
    rw [hh_zero, hh_of_neg (by omega : (0 : ℤ) - m < 0), Derivation.map_one_eq_zero]
  · set p : ℕ+ := ⟨k.toNat, by omega⟩ with hpdef
    have hp : (p : ℤ) = k := by simp [hpdef]; omega
    have e : hh k = X p := by rw [← hp]; exact hh_pnat p
    rw [e, pDeriv_X, hp]

/-- The derivative of a finite product. -/
theorem derivation_prod {ι : Type*} [DecidableEq ι] (D : Derivation ℚ Lambda Lambda)
    (s : Finset ι) (f : ι → Lambda) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ k ∈ s.erase i, f k) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, Finset.sum_insert ha, Finset.erase_insert ha]
    simp only [smul_eq_mul]
    rw [ih, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/-- **The derivative of a determinant**: the sum over the columns of the determinants with that
column differentiated. -/
theorem derivation_det {M : ℕ} (D : Derivation ℚ Lambda Lambda)
    (A : Matrix (Fin M) (Fin M) Lambda) :
    D A.det = ∑ j : Fin M, (A.updateCol j fun i => D (A i j)).det := by
  simp only [Matrix.det_apply]
  rw [map_sum]
  simp only [Units.smul_def, zsmul_eq_mul]
  have hz : ∀ (z : ℤ) (x : Lambda), D ((z : Lambda) * x) = (z : Lambda) * D x := by
    intro z x
    rw [Derivation.leibniz]
    simp [Derivation.map_intCast]
  simp only [hz, derivation_prod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Matrix.updateCol_self]
  rw [Finset.prod_congr rfl (fun i hi => Matrix.updateCol_ne (Finset.ne_of_mem_erase hi))]
  ring

/-- The Jacobi–Trudi type determinant `det (h_{a_i - b_j})_{i, j < M}` of two integer lists. -/
noncomputable def jtDet {M : ℕ} (a b : Fin M → ℤ) : Lambda :=
  (Matrix.of fun i j : Fin M => hh (a i - b j)).det

/-- **Differentiating the determinant** column by column: `∂_m` raises one `b_j` by `m`. -/
theorem pDeriv_jtDet {M m : ℕ} (hm : 0 < m) (a b : Fin M → ℤ) :
    pDeriv m (jtDet a b) = ∑ j : Fin M, jtDet a (Function.update b j (b j + m)) := by
  unfold jtDet
  rw [derivation_det]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ext i k
  by_cases hk : k = j
  · subst hk
    simp only [Matrix.updateCol_self, Matrix.of_apply, Function.update_self]
    rw [pDeriv_hh hm, sub_sub]
  · simp [Matrix.updateCol_ne hk, Function.update_of_ne hk]

/-- Swapping two columns changes the sign. -/
theorem jtDet_swap {M : ℕ} (a b : Fin M → ℤ) {p q : Fin M} (hpq : p ≠ q) :
    jtDet a (b ∘ Equiv.swap p q) = - jtDet a b := by
  unfold jtDet
  have : (Matrix.of fun i j : Fin M => hh (a i - (b ∘ Equiv.swap p q) j)) =
      (Matrix.of fun i j : Fin M => hh (a i - b j)).submatrix id (Equiv.swap p q) := by
    ext i j; simp
  rw [this, Matrix.det_permute', Equiv.Perm.sign_swap hpq]
  simp

/-- Two equal columns give a zero determinant. -/
theorem jtDet_eq_zero_of_eq {M : ℕ} (a b : Fin M → ℤ) {p q : Fin M} (hpq : p ≠ q)
    (h : b p = b q) : jtDet a b = 0 :=
  Matrix.det_zero_of_column_eq hpq fun i => by simp [h]

/-- Permuting the columns multiplies the determinant by the sign. -/
theorem jtDet_perm {M : ℕ} (a b : Fin M → ℤ) (σ : Equiv.Perm (Fin M)) :
    jtDet a (b ∘ σ) = (Equiv.Perm.sign σ : ℤ) * jtDet a b := by
  unfold jtDet
  have : (Matrix.of fun i j : Fin M => hh (a i - (b ∘ σ) j)) =
      (Matrix.of fun i j : Fin M => hh (a i - b j)).submatrix id σ := by
    ext i j; simp
  rw [this, Matrix.det_permute']

/-- Permuting the rows multiplies the determinant by the sign. -/
theorem jtDet_rows_perm {M : ℕ} (a b : Fin M → ℤ) (σ : Equiv.Perm (Fin M)) :
    jtDet (a ∘ σ) b = (Equiv.Perm.sign σ : ℤ) * jtDet a b := by
  unfold jtDet
  have : (Matrix.of fun i j : Fin M => hh ((a ∘ σ) i - b j)) =
      (Matrix.of fun i j : Fin M => hh (a i - b j)).submatrix σ id := by
    ext i j; simp
  rw [this, Matrix.det_permute]

/-- Two equal rows give a zero determinant. -/
theorem jtDet_rows_eq_zero_of_eq {M : ℕ} (a b : Fin M → ℤ) {p q : Fin M} (hpq : p ≠ q)
    (h : a p = a q) : jtDet a b = 0 :=
  Matrix.det_zero_of_row_eq hpq (by ext j; simp [h])

end MN

end Plan

end GluingCore
