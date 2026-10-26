/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMaximalGapPeriod
import SkewCornerDescent.Matrix.OriginalSchurAffine

/-!
# Actual maximal-gap coefficient of the whole original Schur germ

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The complete
cyclic gap maximum and an attaining start are constructed. Actual interval bounds
then produce the full filtered logarithmic coefficient, lower earlier jets, and
an affine fresh coefficient without assuming a completed-gap period. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The maximum of the complete actual gap windows supplies its own protected
generator and the exact whole-source filtered coefficient. No period is assumed. -/
theorem originalSchur_maximal_gap_frontier {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P) :
    ∃ M : ℤ, ∃ K : ℕ+, ∃ hK : c.top < K,
      (K : ℤ) = (c.top : ℤ) + M ∧
      (∀ s : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 j s ≤ M) ∧
      (∃ s : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 j s = M) ∧
      let f := c.normalPolynomialSeries P.schur
      (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff l f) = 0) ∧
      (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff (j - 1)
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) =
        ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
          ∑ k : Fin (originalSelectedCount (hD := hD) P + 1),
            if i.val ≤ k.val ∧ k.val - i.val = j - 1 ∧
                originalHessenbergDistance (hD := hD) P i k = (K : ℤ) then
              (-1 : OtherField c.top) ^ (j - 1) * (c.normalCoefficient)⁻¹ ^ (j - 1) *
                (∏ l ∈ Finset.Icc i k, (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹)
            else 0) ∧
      jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
        f (j - 1) := by
  classical
  let g := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
  let fwindow := fun s : ZMod (originalSelectedCount (hD := hD) P) => windowSum g 1 j s
  have hne : (Finset.univ : Finset (ZMod (originalSelectedCount (hD := hD) P))).Nonempty :=
    ⟨0, Finset.mem_univ _⟩
  let M := Finset.univ.sup' hne fwindow
  have hbnd : ∀ s, fwindow s ≤ M := fun s => Finset.le_sup' fwindow (Finset.mem_univ s)
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' hne fwindow
  have hwinpos : 0 < fwindow 0 := by
    unfold fwindow windowSum
    apply Finset.sum_pos
    · intro i _
      exact c.originalCompletedGap_pos P hB _
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hM : 0 < M := hwinpos.trans_le (hbnd 0)
  let K : ℕ+ := ⟨(c.top : ℕ) + M.toNat, by have := c.top.pos; omega⟩
  have hKco : (K : ℤ) = (c.top : ℤ) + M := by
    change (((c.top : ℕ) + M.toNat : ℕ) : ℤ) = _
    rw [Nat.cast_add, Int.toNat_of_nonneg hM.le]
  have hK : c.top < K := by
    exact_mod_cast (show (c.top : ℤ) < (K : ℤ) by omega)
  have hbound : ∀ i k : Fin (originalSelectedCount (hD := hD) P + 1), i ≤ k →
      k.val - i.val = j - 1 → originalHessenbergDistance (hD := hD) P i k ≤ (K : ℤ) := by
    intro i k hik hcost
    rw [hKco]
    apply c.originalHessenbergDistance_bound_of_cyclic_gaps P hB (j - 1) (by omega)
      (by omega) M _ i k hik hcost
    intro z
    have he : j - 1 + 1 = j := by omega
    simpa only [he] using hbnd z
  have he := c.originalHessenberg_normalized_log_from_length_bound P hB hmax K hK
    (j - 1) (by omega) (by omega) hbound
  have hf := c.originalSchur_normalized_log_from_response P hB hmax K hK
    (j - 1) (by omega) he.1
  dsimp only at he hf ⊢
  refine ⟨M, K, hK, hKco, hbnd, ⟨s, hs.symm⟩, hf.1, ?_, ?_⟩
  · rw [hf.2]
    exact he.2
  · exact c.originalSchur_jets_affine_from_length_bound P hB hmax K hK
      (j - 1) (by omega) (by omega) hbound

end SkewCornerDescent.Matrix.SelectedCoordinate
