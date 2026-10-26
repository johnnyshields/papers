/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSchurOpenPrefixComparison
import SkewCornerDescent.Matrix.OriginalOrdinaryFirstDefectPrefixes

/-!
# Actual original logarithmic defect coefficients as complete prefix charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The defect is the logarithm of the residue-normalized original Schur ratio.
Its complete first coefficient and its higher generator derivative retain all
removed factors, true caps, onsite jets, and exterior overlapping pairs through
their proved cancellations.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual logarithmic defect has both its complete first coefficient and
its higher resolving derivative given by the genuine finite prefix charges.
The constant residue equation fixes normalization, not either coefficient. -/
theorem originalCompleted_normal_comparison_prefixes {n m an qn : ℕ}
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
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hn : 2 ≤ (b - a) * r) (J H : ℕ+)
    (hH : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ))
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    let d := b - a
    let n := d * r
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      (PowerSeries.coeff 1 logDefect =
        b • normalFirstPrefixCharge ((c.originalInternalResponseMatrix A).map c.normalSeries)
          c.normalCoefficient⁻¹ n (by omega) -
        d • normalFirstPrefixCharge ((c.originalInternalResponseMatrix Q).map c.normalSeries)
          c.normalCoefficient⁻¹ (originalSelectedCount (hD := hD) P)
          (by have hn' : 2 ≤ n := hn; omega)) ∧
      (δ₀ (PowerSeries.coeff n logDefect) =
        b • normalOpenOverlapPrefixCharge
          ((c.originalInternalResponseMatrix A).map c.normalSeries) δ
          c.normalCoefficient⁻¹ γ (n - 1) n (by omega) -
        d • normalOpenOverlapPrefixCharge
          ((c.originalInternalResponseMatrix Q).map c.normalSeries) δ
          c.normalCoefficient⁻¹ γ (n - 1) (originalSelectedCount (hD := hD) P)
          (by have hn' : 2 ≤ n := hn; omega)) := by
  let d := b - a
  let n := d * r
  let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
  let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
  let wordLog := fun {k : ℕ} (X : Profile k) =>
    let p := full X
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
  let logDefect := PowerSeries.logOf
    (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
  obtain ⟨hshort, hcountA, hcountQ, hhigher⟩ :=
    c.originalCompleted_schur_open_prefix_comparison P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW
      active hresponse hgap hmax hn J H hH
  have hn2 : 2 ≤ n := hn
  have hshort' : n < originalSelectedCount (hD := hD) P := hshort
  have hcountA' : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := hcountA
  have hP2 : 2 ≤ originalSelectedCount (hD := hD) P := by omega
  have hb : a + d = b := by dsimp only [d]; omega
  have hshift : originalSelectedCount (hD := hD) A -
      originalSelectedCount (hD := hD) P = n := by omega
  have hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ) :=
    originalAmalgamation_component_span P W A q v w u hv hwindow hW.symm hA _ hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q z hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hQ hmax
  have hunit {k : ℕ} (X : Profile k) (hX : 0 < originalSelectedCount (hD := hD) X)
      (hmaxX : ∀ C ∈ edgeComponents (diagramInterior X.cells), span C ≤ (c.top : ℕ)) :
      PowerSeries.constantCoeff (full X) ≠ 0 := by
    rw [c.normalPolynomialSeries_constant]
    exact c.originalSchur_residue_ne_zero X hX hmaxX
  have hE := hunit A (by omega) hmaxA
  have hf := hunit P (by omega) hmax
  have hT := hunit Q (by omega) hmaxQ
  have hlog := residue_matched_ratio_log (full A) (full P) (full Q) κ b a d hE hf hT hmatch
  change logDefect = b • wordLog A - a • wordLog P - d • wordLog Q at hlog
  have hKP' := hKU
  rw [← hb] at hKP'
  have hmatch' : PowerSeries.constantCoeff (full A) ^ (a + d) =
      κ * (PowerSeries.constantCoeff (full P) ^ a * PowerSeries.constantCoeff (full Q) ^ d) := by
    rw [hb]
    exact hmatch
  obtain ⟨_, _, hfirst⟩ := c.originalOrdinaryComparison_first_defect_prefixes P W A Q
    q v w u z hq0 hv hwindow hW.symm hA hQ
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) hP2 hmax a d κ Λ hKP' hKW hmatch'
  simp only [hb, hshift] at hfirst
  have hratioFirst := one_active_comparison_first_log
    (full A) (full P) (full Q) κ b a d hE hf hT hmatch
  change PowerSeries.coeff 1
    (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹) - 1) =
      PowerSeries.coeff 1 (b • wordLog A - a • wordLog P - d • wordLog Q) at hratioFirst
  have hlow := (congrArg (PowerSeries.coeff 1) hlog).trans hratioFirst.symm
  have hhigh := congrArg (fun p : PowerSeries (OtherField c.top) => δ₀ (PowerSeries.coeff n p)) hlog
  exact ⟨hshort, hcountA, hcountQ, hlow.trans hfirst, hhigh.trans hhigher⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
