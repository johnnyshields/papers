/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationFilteredInventory
import SkewCornerDescent.Matrix.OriginalVirtualFilteredCycle
import SkewCornerDescent.Matrix.OriginalComparisonLogTransfer

/-!
# The complete original logarithmic coefficient in a filtered span bin

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The original
source, amalgamation, and virtual closure germs have the same actual gap mask.
Signed class balance cancels their complete linear source inventories. The two
remaining cyclic inventories retain every start and both true cap completions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full-period coefficient is the exact signed difference of the actual
filtered period and virtual closure inventories, without a cyclic gap period. -/
theorem originalComparison_normalized_log_filtered_bin {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) [NeZero j] (hj : 2 ≤ j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hqM : q ≤ M)
    (hbound : ∀ x : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j x ≤ M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M)
    (classes : Finset ℚ) (e : ℚ → ℤ) (b a : ℕ)
    (hbalance : (∑ α ∈ classes, e α) = (b : ℤ) - (a : ℤ)) :
    let f := c.normalPolynomialSeries P.schur
    let E := c.normalPolynomialSeries A.schur
    let T := fun α : ℚ => c.normalPolynomialSeries Q.schur -
      PowerSeries.C (α : OtherField c.top) * f ^ 2
    let R := normalComparisonSeries classes E f T e b a
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l R) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1)
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff R)⁻¹ * R))) =
      ((-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1)) *
        ((b : OtherField c.top) * filteredInverseWindowSum
          (finiteWordCycle (n := j) (c.originalInternalResidue P) (by omega))
          (finiteWordCycle (n := j) (c.originalCompletedGap P) (by omega)) j M -
          ∑ α ∈ classes, (e α : OtherField c.top) * filteredInverseWindowSum
            (completeResponseCycle (c.originalInternalResidue P)
              (c.originalVirtualCentralResponse P Q middle α))
            (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) j M) := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by omega
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u z
    hv hwindow hW hA
  have hBA : 0 < originalSelectedCount (hD := hD) A := by omega
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨by omega⟩
  have hboundA := c.originalAmalgamation_completed_gap_bound P W A q v u z hq hv hwindow
    hW hA hcutq' hcutLq' hC j (by omega) hjlen M hqM hbound
  have hmaxA := originalAmalgamation_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  have htE := c.originalSchur_normalized_log_from_gap_bound A hBA hmaxA j hj (by omega)
    M hboundA K hK hKeq
  have htf := c.originalSchur_normalized_log_from_gap_bound P hB hmax j hj hjB
    M hbound K hK hKeq
  have htT (α : ℚ) := c.originalVirtualClosure_normalized_log_filtered_cycle P Q w hQ
    hB hmax j hj hjB M hbound K hK hKeq α
  have hEI := c.originalAmalgamation_filtered_interval_inventory P W A q v u z hq hv
    hwindow hW hA hcutq hcutLq hC j hj hjlen M hqM hbound K hKeq
  have hE0 := c.originalSchur_residue_ne_zero A hBA hmaxA
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let E := c.normalPolynomialSeries A.schur
  let T := fun α : ℚ => c.normalPolynomialSeries Q.schur -
    PowerSeries.C (α : OtherField c.top) * f ^ 2
  have hTc : ∀ α ∈ classes, PowerSeries.constantCoeff (T α) ≠ 0 := by
    intro α _
    simpa only [T, f, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C,
      c.normalPolynomialSeries_constant] using
      c.originalVirtualClosure_residue_ne_zero P Q w hQ hB hmax α
  dsimp only at htE htf ⊢
  constructor
  · intro l hl
    exact coeff_deriv_normal_comparison_zero δ classes E f T e b a l
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
      (fun k hk => htE.1 k (hk.trans_lt hl))
      (fun k hk => htf.1 k (hk.trans_lt hl))
      (fun α _ k hk => (htT α).1 k (hk.trans_lt hl))
  · have he := coeff_deriv_normal_comparison_log_first δ classes E f T e b a
      (j - 1) (by omega)
      (by simpa only [E, c.normalPolynomialSeries_constant] using hE0)
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
      htE.1 htf.1 (fun α _ => (htT α).1)
    dsimp only [δ, E, f, T] at he
    rw [he, htE.2.1, htf.2.1, hEI]
    have hs := Finset.sum_congr (s₁ := classes) (s₂ := classes) rfl (fun α _ =>
      congrArg (fun x => (e α : OtherField c.top) * x) (htT α).2.1)
    rw [hs]
    exact scaled_signed_linear_inventory_cancel classes e b a _ _ _ _ hbalance

end SkewCornerDescent.Matrix.SelectedCoordinate
