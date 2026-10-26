/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalComparisonPrefixes
import SkewCornerDescent.Matrix.NormalPrefixCycles
import SkewCornerDescent.Matrix.OriginalInternalWordPeriods

/-!
# Original first logarithmic coefficient on the actual cycles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original corner powers produce the exact cycle lengths; complete removed
factors and true caps cancel through their proved suppliers. The result uses
full normal onsite jets and genuine boundary pair entries, without requiring
a smaller residue response period or an assumed coefficient formula. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete original first logarithmic coefficient, as the weighted cyclic
onsite-minus-pair charge of the actual full normal words. -/
theorem originalCompleted_first_log_cyclic {n m an qn : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an) (Q : Profile qn)
    (q : ℤ) (u v w z : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hn : 2 ≤ (b - a) * r)
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    let d := b - a
    let n := d * r
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    letI : NeZero n := ⟨by have hn' : 2 ≤ n := hn; omega⟩
    let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
    let MQ := (c.originalInternalResponseMatrix Q).map c.normalSeries
    let fP := normalDiagonalCycle MA (show n ≤ originalSelectedCount (hD := hD) A - 1 by omega)
    let qP := normalAdjacentCycle MA (show n ≤ originalSelectedCount (hD := hD) A - 1 - 1 by omega)
    let fQ := normalDiagonalCycle MQ (show originalSelectedCount (hD := hD) P ≤
      originalSelectedCount (hD := hD) Q - 1 by omega)
    let qQ := normalAdjacentCycle MQ (show originalSelectedCount (hD := hD) P ≤
      originalSelectedCount (hD := hD) Q - 1 - 1 by have hn' : 2 ≤ n := hn; omega)
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))) =
      b • normalCyclicFirstCharge fP qP c.normalCoefficient⁻¹ -
        d • normalCyclicFirstCharge fQ qQ c.normalCoefficient⁻¹ := by
  let d := b - a
  let n := d * r
  have hn2 : 2 ≤ n := hn
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hCW : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  have hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = n := by
    dsimp only [n, d]
    rw [hcountP, hcountW, ← Nat.mul_sub_left_distrib, Nat.mul_comm]
  have hWP : originalSelectedCount (hD := hD) W ≤ originalSelectedCount (hD := hD) P := by
    rw [hcountW, hcountP]
    exact Nat.mul_le_mul_left r hab.le
  have hshort : n < originalSelectedCount (hD := hD) P := by omega
  have hinv := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v w u hv hwindow hW.symm hA
  have hcountA : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := by omega
  have hshift : originalSelectedCount (hD := hD) A -
      originalSelectedCount (hD := hD) P = n := by omega
  have hb : a + d = b := by dsimp only [d]; omega
  obtain ⟨_, hcountQ, hfirst⟩ := c.originalOrdinaryComparison_first_defect_prefixes
    P W A Q q v w u z hq0 hv hwindow hW.symm hA hQ
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) (by omega) hmax a d κ Λ
    (by rw [hb]; exact hKU) hKW (by rw [hb]; exact hmatch)
  have hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ) :=
    originalAmalgamation_component_span P W A q v w u hv hwindow hW.symm hA _ hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q z hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hQ hmax
  let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
  have hunit {k : ℕ} (X : Profile k) (hX : 0 < originalSelectedCount (hD := hD) X)
      (hmaxX : ∀ C ∈ edgeComponents (diagramInterior X.cells), span C ≤ (c.top : ℕ)) :
      PowerSeries.constantCoeff (full X) ≠ 0 := by
    rw [c.normalPolynomialSeries_constant]
    exact c.originalSchur_residue_ne_zero X hX hmaxX
  have hE := hunit A (by omega) hmaxA
  have hf := hunit P (by omega) hmax
  have hT := hunit Q (by omega) hmaxQ
  have hlog := residue_matched_ratio_log (full A) (full P) (full Q) κ b a d hE hf hT hmatch
  have hflog := one_active_comparison_first_log
    (full A) (full P) (full Q) κ b a d hE hf hT hmatch
  have hlogfirst := (congrArg (PowerSeries.coeff 1) hlog).trans hflog.symm
  let : NeZero n := ⟨by omega⟩
  obtain ⟨_, _, hwordA⟩ := c.originalAmalgamation_internal_word_periods
    P W A q v w u hq0 hv hwindow hW.symm hA
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  obtain ⟨_, hwordQ⟩ := c.originalClosure_internal_word_periods P Q z hQ
  dsimp only at hwordA hwordQ
  rw [hshift] at hwordA
  have hcycA := normalFirstPrefixCharge_cyclic
    ((c.originalInternalResponseMatrix A).map c.normalSeries) c.normalCoefficient⁻¹
    (show n ≤ originalSelectedCount (hD := hD) A - 1 - 1 by omega) hwordA.1
  have hcycQ := normalFirstPrefixCharge_cyclic
    ((c.originalInternalResponseMatrix Q).map c.normalSeries) c.normalCoefficient⁻¹
    (show originalSelectedCount (hD := hD) P ≤
      originalSelectedCount (hD := hD) Q - 1 - 1 by omega) hwordQ.1
  dsimp only at hcycA hcycQ
  simp only [hb, hshift] at hfirst
  refine ⟨hshort, hcountA, hcountQ, ?_⟩
  exact (hlogfirst.trans hfirst).trans (by rw [hcycA, hcycQ])

end SkewCornerDescent.Matrix.SelectedCoordinate
