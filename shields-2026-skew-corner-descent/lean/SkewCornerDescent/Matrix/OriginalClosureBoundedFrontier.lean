/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalBoundedSchurFrontier
import SkewCornerDescent.Matrix.OriginalVirtualClosureTransfer
import SkewCornerDescent.Matrix.NormalRationalAffineJets

/-!
# The original virtual closure coefficient without a gap period

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Literal
closure geometry transfers each complete source gap window to the closure.
Both full original Schur summands remain in the virtual difference. Its unit,
earlier independence, exact filtered coefficient, and affine fresh jet are
produced from the source bound. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual closure gap window is a source gap window, with the same start
under the literal cyclic projection; no source period is required. -/
theorem originalHorizontalClosure_completed_gap_window_at {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)]
    (j : ℕ) (z : ZMod (originalSelectedCount (hD := hD) Q)) :
    windowSum (fun s => c.originalCompletedGap Q ((ZMod.finEquiv _).symm s)) 1 j z =
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j
        (ZMod.castHom (show originalSelectedCount (hD := hD) P ∣
          originalSelectedCount (hD := hD) Q by
            rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
            exact dvd_mul_left _ _) (ZMod (originalSelectedCount (hD := hD) P)) z) := by
  unfold windowSum
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [c.originalHorizontalClosure_completed_gap_projection P Q v hQ]
  simp only [map_add, map_nsmul, map_one]

/-- The full original virtual closure has its exact filtered logarithmic
coefficient on a bounded nonperiodic gap cycle. All response and factor units are
supplied by the actual closure geometry and transcendental quotient. -/
theorem originalVirtualClosure_normalized_log_from_gap_bound {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P)
    (M : ℤ)
    (hbound : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 j s ≤ M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M) (α : ℚ) :
    let f := c.normalPolynomialSeries P.schur
    let β := c.normalPolynomialSeries Q.schur
    let T := β - PowerSeries.C (α : OtherField c.top) * f ^ 2
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l T) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1)
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff T)⁻¹ * T))) =
      ((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
        (c.residueMap Q.schur * c.originalFilteredIntervalInventory Q j K -
          2 * (α : OtherField c.top) * c.residueMap P.schur ^ 2 *
            c.originalFilteredIntervalInventory P j K) /
        (c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2) ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      T (j - 1) := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  have hboundQ : ∀ s : ZMod (originalSelectedCount (hD := hD) Q),
      windowSum (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z)) 1 j s ≤ M := by
    intro z
    rw [c.originalHorizontalClosure_completed_gap_window_at P Q v hQ]
    exact hbound _
  have htP := c.originalSchur_normalized_log_from_gap_bound P hB hmax j hj hjB
    M hbound K hK hKeq
  have htQ := c.originalSchur_normalized_log_from_gap_bound Q hBQ hmaxQ j hj (by omega)
    M hboundQ K hK hKeq
  have hunit := c.originalVirtualClosure_residue_ne_zero P Q v hQ hB hmax α
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let β := c.normalPolynomialSeries Q.schur
  have hf0 : PowerSeries.constantCoeff f ≠ 0 := by
    simpa only [f, c.normalPolynomialSeries_constant] using
      c.originalSchur_residue_ne_zero P hB hmax
  have hβ0 : PowerSeries.constantCoeff β ≠ 0 := by
    simpa only [β, c.normalPolynomialSeries_constant] using
      c.originalSchur_residue_ne_zero Q hBQ hmaxQ
  have hα : δ (α : OtherField c.top) = 0 := by
    apply residueGeneratorDeriv_lower
    exact SubfieldClass.ratCast_mem (residueLowerField c.top K) α
  have hsquare : ∀ l, l < j - 1 → δ (PowerSeries.coeff l (f ^ 2)) = 0 :=
    fun l hl => coeff_deriv_pow_zero δ f l (fun z hz => htP.1 z (hz.trans_lt hl)) 2
  have hsquare0 : PowerSeries.constantCoeff (f ^ 2) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hf0
  have he := coeff_deriv_normalized_difference_first δ β (f ^ 2) (α : OtherField c.top)
    hα (j - 1) (by omega) hβ0 hsquare0
    (by simpa only [map_pow, f, β, c.normalPolynomialSeries_constant] using hunit)
    htQ.1 hsquare
  rw [coeff_deriv_normalized_pow_log_first δ f (j - 1) (by omega) hf0 htP.1 2] at he
  dsimp only at htP htQ ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    rw [map_sub, PowerSeries.coeff_C_mul, map_sub, Derivation.leibniz,
      htQ.1 l hl, hsquare l hl, hα, smul_zero, smul_zero, add_zero, sub_zero]
  · dsimp only [δ, f, β] at he
    rw [htP.2.1, htQ.2.1, map_pow, c.normalPolynomialSeries_constant,
      c.normalPolynomialSeries_constant] at he
    rw [he]
    simp only [div_eq_mul_inv]
    ring
  · apply jetsAffineOver_sub _ _ htQ.2.2
    apply jetsAffineOver_mul _ _ (by omega)
    · exact jetsAffineOver_C _ _ (SubfieldClass.ratCast_mem _ α) _
    · exact jetsAffineOver_pow _ _ (by omega) htP.2.2 2

end SkewCornerDescent.Matrix.SelectedCoordinate
