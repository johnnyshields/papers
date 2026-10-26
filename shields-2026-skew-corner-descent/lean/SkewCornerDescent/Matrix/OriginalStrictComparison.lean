/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationStrictFrontier
import SkewCornerDescent.Matrix.OriginalClosureMaximalInventory
import SkewCornerDescent.Matrix.OriginalMaximalBinReciprocal
import SkewCornerDescent.Matrix.NormalComparisonCoefficient

/-!
# A nonperiodic strict-bin detector for the original comparison germ

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Literal
geometry excludes the source and amalgamation contributions. The actual closure
has an inhabited nonzero filtered context on one monic-positive chamber. Its
signed reciprocal multiplier cannot vanish. No periodic gap premise is used.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The whole original comparison logarithm detects every attained strict bin at
full internal-period length, for arbitrary signed classes of nonzero total degree. -/
theorem originalComparison_strict_bin_ne_zero {n m k t : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u w z : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate w W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate z Q.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hstrict : q < M)
    (hbound : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j s ≤ M)
    (hretain : ∃ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j s = M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M)
    (classes : Finset ℚ) (e : ℚ → ℤ) (hdegree : (∑ α ∈ classes, e α) ≠ 0)
    (b a : ℕ) :
    let f := c.normalPolynomialSeries P.schur
    let E := c.normalPolynomialSeries A.schur
    let T := fun α : ℚ => c.normalPolynomialSeries Q.schur -
      PowerSeries.C (α : OtherField c.top) * f ^ 2
    let R := normalComparisonSeries classes E f T e b a
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l R) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1)
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff R)⁻¹ * R))) ≠ 0 := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by omega
  have htP := c.originalSchur_normalized_log_from_gap_bound P hB hmax j hj hjB
    M hbound K hK hKeq
  have hzP := c.originalWindow_strict_filtered_inventory_zero P W q w v hv hW.symm
    hwindow hcutq hcutLq hB j hj hjB hjlen M hstrict hbound K hKeq
  have htA := c.originalAmalgamation_strict_normalized_log_zero P W A q v u w hq hv
    hwindow hW hA hcutq hcutLq hC hmax j hj hjlen M hstrict hbound K hK hKeq
  have htT (α : ℚ) := c.originalVirtualClosure_normalized_log_from_gap_bound P Q z hQ
    hB hmax j hj hjB M hbound K hK hKeq α
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u w
    hv hwindow hW hA
  have hmaxA := originalAmalgamation_component_span P W A q v u w hv hwindow hW hA
    (c.top : ℕ) hmax
  have hE0 := c.originalSchur_residue_ne_zero A (by omega) hmaxA
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  have hcQ := originalHorizontalClosure_profile_selected_count (hD := hD) P Q z hQ
  have hβ0 := c.originalSchur_residue_ne_zero Q (by omega)
    (c.originalHorizontalClosure_profile_component_span P Q z hQ hmax)
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let E := c.normalPolynomialSeries A.schur
  let T := fun α : ℚ => c.normalPolynomialSeries Q.schur -
    PowerSeries.C (α : OtherField c.top) * f ^ 2
  have hTc : ∀ α ∈ classes, PowerSeries.constantCoeff (T α) ≠ 0 := by
    intro α _
    simpa only [T, f, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C,
      c.normalPolynomialSeries_constant] using
      c.originalVirtualClosure_residue_ne_zero P Q z hQ hB hmax α
  dsimp only at htP htA ⊢
  constructor
  · intro l hl
    exact coeff_deriv_normal_comparison_zero δ classes E f T e b a l
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
      (fun k hk => htA.1 k (hk.trans_lt hl))
      (fun k hk => htP.1 k (hk.trans_lt hl))
      (fun α _ k hk => (htT α).1 k (hk.trans_lt hl))
  · have he := coeff_deriv_normal_comparison_log_first δ classes E f T e b a
      (j - 1) (by omega)
      (by simpa only [E, c.normalPolynomialSeries_constant] using hE0)
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
      htA.1 htP.1 (fun α _ => (htT α).1)
    dsimp only [δ, E, f, T] at he
    rw [he, htA.2.1, htP.2.1, hzP, mul_zero, mul_zero, mul_zero, zero_sub]
    have hsum : (∑ α ∈ classes, (e α : OtherField c.top) *
        residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
          (PowerSeries.coeff (j - 1) (PowerSeries.logOf
            (PowerSeries.C (PowerSeries.constantCoeff (T α))⁻¹ * T α)))) =
        ((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
          c.residueMap Q.schur * c.originalFilteredIntervalInventory Q j K *
          ∑ α ∈ classes, (e α : OtherField c.top) /
            (c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      have ht := (htT α).2.1
      rw [ht, hzP]
      simp only [mul_zero, sub_zero, div_eq_mul_inv]
      ring
    rw [hsum]
    simp only [neg_zero, zero_sub]
    apply neg_ne_zero.mpr
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero
          (mul_ne_zero (pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (inv_ne_zero c.normalCoefficient_ne_zero))) hβ0
      · exact c.originalHorizontalClosure_filtered_inventory_ne_zero P Q z hQ hB hmax
          j (by omega) hjB M hretain K hKeq
    · exact c.originalVirtualResidue_signed_reciprocal_ne_zero P Q z hQ hB hmax
        classes e hdegree

end SkewCornerDescent.Matrix.SelectedCoordinate
