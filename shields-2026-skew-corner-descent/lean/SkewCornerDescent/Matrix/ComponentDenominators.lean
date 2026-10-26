/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ComponentIntervals
import SkewCornerDescent.Matrix.ComponentRegularity

/-!
# Denominators of complete actual component inverses

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Every entry of a nonselected complete
component inverse has its actual Schur determinant as a denominator. Distinct connected
functions make this denominator regular at the selected divisor, even at span ties.
The complementary selected minor inverse uses strictly lower generators. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The entire complementary selected inverse belongs to the strictly lower rational field. -/
theorem componentInterval_inverse_lower {n : ℕ} (P : Profile n) (i j : Fin n) :
    letI := componentIntervalInverse P
    (⅟(intervalMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc))) i j ∈
      lowerGeneratorField P.topVar := by
  let := componentIntervalInverse P
  apply inverse_entries_mem_subfield
  intro i j
  apply hh_mem_lowerGeneratorField
  change P.xi i.succ - P.zeta j.castSucc < (P.topVar : ℤ)
  have hx := P.xi_strictAnti (Fin.succ_pos i)
  have hz := P.zeta_nonneg j.castSucc
  rw [P.topVar_coe]
  omega

/-- Each entry of the full original inverse is an actual adjugate numerator divided by
its original determinant. No normal-dependent inverse entry is discarded. -/
theorem original_inverse_entry {n : ℕ} (P : Profile n) (i j : Fin (n + 1)) :
    (originalMatrix P)⁻¹ i j =
      originalMap ((Matrix.of (fun i j : Fin (n + 1) => hh (P.xi i - P.zeta j))).adjugate i j) /
        originalMap P.schur := by
  have hm : originalMatrix P = originalMap.mapMatrix
      (Matrix.of (fun i j : Fin (n + 1) => hh (P.xi i - P.zeta j))) := rfl
  have ha : (originalMatrix P).adjugate = originalMap.mapMatrix
      (Matrix.of (fun i j : Fin (n + 1) => hh (P.xi i - P.zeta j))).adjugate := by
    rw [hm, RingHom.map_adjugate]
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    det_originalMatrix, ha]
  change (originalMap P.schur)⁻¹ * originalMap _ = _
  rw [div_eq_mul_inv, mul_comm]

/-- A distinct connected component supplies regular denominators for every complete
inverse entry. The denominator is the actual component function, not a surrogate unit. -/
theorem original_inverse_regular_denominator {D : Diagram} (hD : IsConnectedSkew D)
    {n : ℕ} (P : Profile n) (hne : cellSchur D hD.1 ≠ P.schur)
    (i j : Fin (n + 1)) :
    ∃ a b : Lambda, (originalMatrix P)⁻¹ i j = originalMap a / originalMap b ∧
      b = P.schur ∧ b ≠ 0 ∧ ¬ cellSchur D hD.1 ∣ b := by
  have hp : P.schur ≠ 0 := by
    rw [← cellSchur_cells]
    exact (irreducible_cellSchur P.isConnectedSkew_cells).ne_zero
  refine ⟨_, P.schur, original_inverse_entry P i j, rfl, hp, ?_⟩
  have hne' : cellSchur D hD.1 ≠ cellSchur P.cells P.isSkew_cells := by
    rwa [cellSchur_cells]
  simpa only [cellSchur_cells] using
    not_dvd_distinct_component hD P.isConnectedSkew_cells hne'

/-- A complete connected original matrix is invertible from its actual Schur function. -/
@[instance_reducible]
noncomputable def originalMatrixInverse {n : ℕ} (P : Profile n) :
    Invertible (originalMatrix P) :=
  Matrix.invertibleOfIsUnitDet _ (by
    apply isUnit_iff_ne_zero.mpr
    rw [det_originalMatrix]
    intro hz
    have hp := (originalMap_eq_zero _).mp hz
    rw [← cellSchur_cells] at hp
    exact (irreducible_cellSchur P.isConnectedSkew_cells).ne_zero hp)

/-- The full inverse of any component of span at most `N` uses only indices at most `N`.
This retains maximal-span ties and every normal-dependent entry. -/
theorem original_inverse_span_bound {n : ℕ} (P : Profile n) (N : ℕ+)
    (hN : P.topVar ≤ N) (i j : Fin (n + 1)) :
    (originalMatrix P)⁻¹ i j ∈ lowerGeneratorField (N + 1) := by
  let := originalMatrixInverse P
  rw [← Matrix.invOf_eq_nonsing_inv]
  apply inverse_entries_mem_subfield
  intro i j
  apply hh_mem_lowerGeneratorField
  have hx := P.xi_strictAnti.antitone (Fin.zero_le i)
  have hz := P.zeta_nonneg j
  have hNz : (P.topVar : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have htop := P.topVar_coe
  change P.xi i - P.zeta j < (((N + 1 : ℕ+) : ℕ) : ℤ)
  simp only [PNat.add_coe, PNat.val_ofNat]
  omega

end SkewCornerDescent.Matrix
