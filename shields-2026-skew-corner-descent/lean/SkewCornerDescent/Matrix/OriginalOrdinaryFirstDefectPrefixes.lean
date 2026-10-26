/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOrdinaryRemovedLogComparison
import SkewCornerDescent.Matrix.OriginalRetainedFirstDefectPrefixes

/-!
# The complete original Schur first defect as actual prefix charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original corner powers and actual ordinary closure geometry cancel all
removed factors and both full true caps. The complete original Schur ratio,
not a retained or partition surrogate, supplies the first normal coefficient.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The residue-normalized ratio of the three original Schur functions has its
complete first defect given by the two full actual prefix charges. Every removed
power balance, determinant unit, and true-cap cancellation is produced. -/
theorem originalOrdinaryComparison_first_defect_prefixes {n m k qn : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (Q : Profile qn)
    (q : ℤ) (v u z w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells ∨
      originalVerticalClosure P = translate w Q.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hP2 : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (a d : ℕ) (κ : OtherField c.top)
    (Λ : Lambda)
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ (a + d))
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (hmatch : (PowerSeries.constantCoeff
      (c.normalPolynomialSeries A.schur)) ^ (a + d) =
      κ * ((PowerSeries.constantCoeff
        (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ d)) :
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      let full := fun {k : ℕ} (X : Profile k) =>
        c.normalPolynomialSeries X.schur
      PowerSeries.coeff 1
        (PowerSeries.C κ⁻¹ * (full A ^ (a + d) * (full P ^ a * full Q ^ d)⁻¹) - 1) =
      (a + d) • normalFirstPrefixCharge
        ((c.originalInternalResponseMatrix A).map c.normalSeries) c.normalCoefficient⁻¹
        (originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P) (by omega) -
      d • normalFirstPrefixCharge
        ((c.originalInternalResponseMatrix Q).map c.normalSeries) c.normalCoefficient⁻¹
        (originalSelectedCount (hD := hD) P) (by omega) := by
  obtain ⟨hAP, hCQ, hpref⟩ := c.originalComparison_first_log_prefixes P W A Q
    q v u z w hq hv hwindow hW hA hQ hcutq hcutLq hP2 hmax
  let full := fun {k : ℕ} (X : Profile k) =>
    c.normalPolynomialSeries X.schur
  let fullFirst := fun {k : ℕ} (X : Profile k) =>
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff (full X))⁻¹ * full X))
  let midFirst := fun {k : ℕ} (X : Profile k) =>
    let M := (c.originalInternalResponseMatrix X).map c.normalSeries
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det))
  let retFirst := fun {k : ℕ} (X : Profile k) =>
    let p := c.normalSeries (c.originalHessenbergResponse X).det
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))
  have hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ) :=
    originalAmalgamation_component_span P W A q v u z hv hwindow hW hA _ hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q w hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q w hQ hmax
  have hunit {k : ℕ} (X : Profile k) (hX : 0 < originalSelectedCount (hD := hD) X)
      (hmaxX : ∀ C ∈ edgeComponents (diagramInterior X.cells), span C ≤ (c.top : ℕ)) :
      PowerSeries.constantCoeff (c.normalPolynomialSeries X.schur) ≠ 0 := by
    rw [c.normalPolynomialSeries_constant]
    exact c.originalSchur_residue_ne_zero X hX hmaxX
  have hE := hunit A (by omega) hmaxA
  have hf := hunit P (by omega) hmax
  have hT := hunit Q (by omega) hmaxQ
  have hfirst : PowerSeries.coeff 1
      (PowerSeries.C κ⁻¹ * (full A ^ (a + d) * (full P ^ a * full Q ^ d)⁻¹) - 1) =
      ((a + d : ℕ) : OtherField c.top) * fullFirst A -
        (a : OtherField c.top) * fullFirst P - (d : OtherField c.top) * fullFirst Q := by
    have h := one_active_comparison_first_log
      (full A) (full P) (full Q) κ (a + d) a d hE hf hT hmatch
    simp only [map_sub, map_nsmul] at h
    simpa only [fullFirst, full, map_sub, nsmul_eq_mul] using h
  have hmid {k : ℕ} (X : Profile k) :
      c.normalSeries (c.originalInternalResponseMatrix X).det =
        ((c.originalInternalResponseMatrix X).map c.normalSeries).det := by
    rw [RingHom.map_det]
    congr 1
  have hcapsRet : ((a + d : ℕ) : OtherField c.top) * retFirst A -
      (a : OtherField c.top) * retFirst P - (d : OtherField c.top) * retFirst Q =
      ((a + d : ℕ) : OtherField c.top) * midFirst A -
      (a : OtherField c.top) * midFirst P - (d : OtherField c.top) * midFirst Q := by
    rcases hQ with hQ | hQ
    · have h := c.originalHorizontalComparison_internal_log_balance P W A Q q v u z w
        hq hv hwindow hW hA hQ hcutq hcutLq hmax (a + d) a d (by omega) 1 (by omega)
      simpa only [retFirst, midFirst, hmid] using h
    · have h := c.originalVerticalComparison_internal_log_balance P W A Q q v u z w
        hq hv hwindow hW hA hQ hcutq hcutLq hmax (a + d) a d (by omega) 1 (by omega)
      simpa only [retFirst, midFirst, hmid] using h
  have hraw := c.originalOrdinary_normal_log_comparison P W A Q q v u z w hq hv
    hwindow hW hA hQ hcutq hcutLq Λ (a + d) a d (by omega) (by omega) hKP hKW (by omega) hmax
  have hraw1 := congrArg (PowerSeries.coeff 1) hraw
  simp only [map_sub, map_nsmul] at hraw1
  have hrawFirst : ((a + d : ℕ) : OtherField c.top) * fullFirst A -
      (a : OtherField c.top) * fullFirst P - (d : OtherField c.top) * fullFirst Q =
      ((a + d : ℕ) : OtherField c.top) * retFirst A -
      (a : OtherField c.top) * retFirst P - (d : OtherField c.top) * retFirst Q := by
    simpa only [fullFirst, retFirst, full, nsmul_eq_mul] using hraw1
  have hcaps := hrawFirst.trans hcapsRet
  have hpre : ((a + d : ℕ) : OtherField c.top) * midFirst A -
      (a : OtherField c.top) * midFirst P - (d : OtherField c.top) * midFirst Q =
      (a + d) • normalFirstPrefixCharge
        ((c.originalInternalResponseMatrix A).map c.normalSeries) c.normalCoefficient⁻¹
        (originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P) (by omega) -
      d • normalFirstPrefixCharge
        ((c.originalInternalResponseMatrix Q).map c.normalSeries) c.normalCoefficient⁻¹
        (originalSelectedCount (hD := hD) P) (by omega) := by
    have h := hpref a d
    simp only [map_sub, map_nsmul] at h
    simpa only [midFirst, nsmul_eq_mul] using h
  exact ⟨hAP, hCQ, hfirst.trans (hcaps.trans hpre)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
