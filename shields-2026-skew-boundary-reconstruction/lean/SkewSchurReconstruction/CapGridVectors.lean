/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.EqualityNormalization
import SkewSchurReconstruction.CappedExtensions

/-!
# Cofactor vectors on the union of cap grids

Formalizes `eq:defect`, `eq:Pk`, and `eq:P0-vanishes` in
"Capped cofactors and admissible convex weights" (`sec:coordinates`).
Finite grid vectors retain their actual integer shifts, including parents with
unequal row counts or origins.  Their responses are the actual cap polynomials.
Coefficient and shift bounds come from the actual determinant matrices.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- Shifted response of a finite integer-grid vector. -/
noncomputable def gridResponse (G : ℤ →₀ CompleteRing) (k : ℤ) : CompleteRing :=
  G.sum fun d c => c * complete (k + d)

private noncomputable def gridResponseHom (k : ℤ) : (ℤ →₀ CompleteRing) →+ CompleteRing :=
  Finsupp.liftAddHom fun d =>
    { toFun := fun c => c * complete (k + d)
      map_zero' := zero_mul _
      map_add' := fun c e => add_mul c e _ }

theorem gridResponse_sub (G H : ℤ →₀ CompleteRing) (k : ℤ) :
    gridResponse (G - H) k = gridResponse G k - gridResponse H k :=
  (gridResponseHom k).map_sub G H

theorem gridResponse_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ →₀ CompleteRing) (k : ℤ) :
    gridResponse (∑ i ∈ s, f i) k = ∑ i ∈ s, gridResponse (f i) k :=
  map_sum (gridResponseHom k) f s

@[simp] theorem gridResponse_single (d : ℤ) (c : CompleteRing) (k : ℤ) :
    gridResponse (Finsupp.single d c) k = c * complete (k + d) := by
  unfold gridResponse
  exact Finsupp.sum_single_index (zero_mul _)

namespace Diagram

variable {n m : ℕ}

/-- The actual signed cofactor vector, indexed by its integer cap shifts. -/
noncomputable def cofactorGridVector (X : Diagram n) : ℤ →₀ CompleteRing :=
  ∑ j, Finsupp.single (X.capShift j) (X.cofactor j)

theorem cofactorGridVector_response (X : Diagram n) (k : ℤ) :
    gridResponse X.cofactorGridVector k = X.capPolynomial k := by
  rw [cofactorGridVector, gridResponse_sum]
  simp only [gridResponse_single, capPolynomial]

/-- Strict grid order prevents cofactor coefficients from being merged. -/
theorem cofactorGridVector_apply_capShift (X : Diagram n) (j : Fin (n + 1)) :
    X.cofactorGridVector (X.capShift j) = X.cofactor j := by
  classical
  simp [cofactorGridVector, Finsupp.single_apply,
    X.capShift_strictMono.injective.eq_iff]

theorem cofactorGridVector_apply_of_not_grid (X : Diagram n) (d : ℤ)
    (hd : ∀ j, X.capShift j ≠ d) : X.cofactorGridVector d = 0 := by
  classical
  simp [cofactorGridVector, hd]

theorem exists_capShift_of_gridVector_ne_zero (X : Diagram n) (d : ℤ)
    (hd : X.cofactorGridVector d ≠ 0) : ∃ j, X.capShift j = d := by
  by_contra h
  push Not at h
  exact hd (X.cofactorGridVector_apply_of_not_grid d h)

theorem cofactorGridVector_shift_bounds (X : Diagram n) (d : ℤ)
    (hd : X.cofactorGridVector d ≠ 0) : 0 ≤ d ∧ d ≤ X.capShift (Fin.last n) := by
  obtain ⟨j, rfl⟩ := X.exists_capShift_of_gridVector_ne_zero d hd
  exact ⟨X.capShift_nonneg j, X.capShift_strictMono.monotone (Fin.le_last j)⟩

theorem cofactorGridVector_response_zero (X : Diagram n) (hn : 0 < n) :
    gridResponse X.cofactorGridVector 0 = 0 := by
  rw [cofactorGridVector_response]
  exact X.capPolynomial_zero hn

/-- Every generator in a cofactor is bounded by the terminal parent cap shift. -/
theorem cofactor_vars_bound (X : Diagram n) (j : Fin (n + 1)) (k : ℕ+)
    (hk : k ∈ (X.cofactor j).vars) : (k.val : ℤ) ≤ X.capShift (Fin.last n) := by
  have he : (-1 : CompleteRing) ^ j.val = MvPolynomial.C ((-1 : ℤ) ^ j.val) := by simp
  unfold cofactor signedMaximalCofactor at hk
  rw [he, MvPolynomial.vars_C_mul _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
    capMatrix_minor_eq_staircase] at hk
  apply staircase_vars_bound _ _ _ ?_ k hk
  intro i l
  have hd := X.capShift_strictMono.monotone (Fin.le_last (j.succAbove l))
  have ha := X.rowParam_nonneg i
  omega

theorem cofactorGridVector_coefficient_vars_bound (X : Diagram n) (d : ℤ) (k : ℕ+)
    (hk : k ∈ (X.cofactorGridVector d).vars) : (k.val : ℤ) ≤ X.capShift (Fin.last n) := by
  by_cases hd : X.cofactorGridVector d = 0
  · rw [hd] at hk
    simp at hk
  · obtain ⟨j, rfl⟩ := X.exists_capShift_of_gridVector_ne_zero d hd
    rw [cofactorGridVector_apply_capShift] at hk
    exact X.cofactor_vars_bound j k hk

end Diagram

/-- Actual heterogeneous cofactor defect on the union of the parent cap grids. -/
noncomputable def gridDefect {n m : ℕ} (X : Diagram n) (Y : Diagram m) : ℤ →₀ CompleteRing :=
  X.cofactorGridVector - Y.cofactorGridVector

theorem gridDefect_response {n m : ℕ} (X : Diagram n) (Y : Diagram m) (k : ℤ) :
    gridResponse (gridDefect X Y) k = X.capPolynomial k - Y.capPolynomial k := by
  rw [gridDefect, gridResponse_sub, Diagram.cofactorGridVector_response,
    Diagram.cofactorGridVector_response]

theorem gridDefect_response_zero {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hn : 0 < n) (hm : 0 < m) : gridResponse (gridDefect X Y) 0 = 0 := by
  rw [gridDefect_response, X.capPolynomial_zero hn, Y.capPolynomial_zero hm, sub_self]

/-- The largest cap shift of either parent. -/
def terminalBound {n m : ℕ} (X : Diagram n) (Y : Diagram m) : ℤ :=
  max (X.capShift (Fin.last n)) (Y.capShift (Fin.last m))

theorem gridDefect_shift_bounds {n m : ℕ} (X : Diagram n) (Y : Diagram m) (d : ℤ)
    (hd : gridDefect X Y d ≠ 0) : 0 ≤ d ∧ d ≤ terminalBound X Y := by
  by_cases hx : X.cofactorGridVector d = 0
  · have hy : Y.cofactorGridVector d ≠ 0 := by
      intro hy
      simp [gridDefect, hx, hy] at hd
    obtain ⟨h0, hD⟩ := Y.cofactorGridVector_shift_bounds d hy
    exact ⟨h0, hD.trans (le_max_right _ _)⟩
  · obtain ⟨h0, hD⟩ := X.cofactorGridVector_shift_bounds d hx
    exact ⟨h0, hD.trans (le_max_left _ _)⟩

theorem gridDefect_coefficient_vars_bound {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (d : ℤ) (k : ℕ+) (hk : k ∈ (gridDefect X Y d).vars) :
    (k.val : ℤ) ≤ terminalBound X Y := by
  have h := MvPolynomial.vars_sub_subset
    (p := X.cofactorGridVector d) (q := Y.cofactorGridVector d) hk
  rcases Finset.mem_union.mp h with hx | hy
  · exact (X.cofactorGridVector_coefficient_vars_bound d k hx).trans (le_max_left _ _)
  · exact (Y.cofactorGridVector_coefficient_vars_bound d k hy).trans (le_max_right _ _)

end SkewSchurReconstruction
