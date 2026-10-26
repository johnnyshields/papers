/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOrdinaryRemovedLogComparison
import SkewCornerDescent.Matrix.OriginalOpenPrefixComparison

/-!
# Original Schur logarithmic derivative as two complete actual prefixes

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact ordinary removed-power balance cancels every removed normal jet.
Both full true-cap logarithms cancel below the original selected cost. The
remaining original Schur logarithmic derivative is the exact full two-prefix
charge expression, before cyclic charge simplification.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original Schur comparison, not a retained or partition
surrogate, has its higher normalized-logarithm derivative given by the two
actual finite prefix charges in either ordinary closure direction. -/
theorem originalCompleted_schur_open_prefix_comparison {n m an qn : ℕ}
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
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let d := b - a
    let n := d * r
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
    let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
      let p := c.normalPolynomialSeries X.schur
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      δ₀ (PowerSeries.coeff n (b • wordLog A - a • wordLog P - d • wordLog Q)) =
        b • normalOpenOverlapPrefixCharge
          ((c.originalInternalResponseMatrix A).map c.normalSeries) δ
          c.normalCoefficient⁻¹ γ (n - 1) n (by omega) -
        d • normalOpenOverlapPrefixCharge
          ((c.originalInternalResponseMatrix Q).map c.normalSeries) δ
          c.normalCoefficient⁻¹ γ (n - 1) (originalSelectedCount (hD := hD) P)
          (by have hn' : 2 ≤ n := hn; omega) := by
  let d := b - a
  let n := d * r
  let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
  let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
    let p := c.normalPolynomialSeries X.schur
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
  let internalLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
    let M := (c.originalInternalResponseMatrix X).map c.normalSeries
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
  let retainedLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
    let p := c.normalSeries (c.originalHessenbergResponse X).det
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
  obtain ⟨hshort, hcountA, hcountQ, hinter⟩ :=
    c.originalCompleted_open_prefix_comparison P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW
      active hresponse hgap hmax hn J H hH
  have hd : d + a = b := by dsimp only [d]; omega
  have hraw := c.originalOrdinary_normal_log_comparison P W A Q q v w u z hq0 hv
    hwindow hW.symm hA hQ (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) Λ b a d hab.le hd hKU hKW
    (NeZero.pos _) hmax
  change b • wordLog A - a • wordLog P - d • wordLog Q =
    b • retainedLog A - a • retainedLog P - d • retainedLog Q at hraw
  have hrawCoeff := congrArg (PowerSeries.coeff n) hraw
  have hmid {k : ℕ} (X : Profile k) :
      c.normalSeries (c.originalInternalResponseMatrix X).det =
        ((c.originalInternalResponseMatrix X).map c.normalSeries).det := by
    rw [RingHom.map_det]
    congr 1
  have hcap : PowerSeries.coeff n
      (b • retainedLog A - a • retainedLog P - d • retainedLog Q) =
      PowerSeries.coeff n (b • internalLog A - a • internalLog P - d • internalLog Q) := by
    simp only [map_sub, map_nsmul]
    simp only [nsmul_eq_mul]
    rcases hQ with hQ | hQ
    · have h := c.originalHorizontalComparison_internal_log_balance P W A Q q v w u z
        hq0 hv hwindow hW.symm hA hQ (fun x hx => privateDiagonal_avoids_interior hq hx)
        (fun x hx => privateDiagonal_avoids_interior hLq hx) hmax b a d hd n hshort
      simpa only [retainedLog, internalLog, hmid] using h
    · have h := c.originalVerticalComparison_internal_log_balance P W A Q q v w u z
        hq0 hv hwindow hW.symm hA hQ (fun x hx => privateDiagonal_avoids_interior hq hx)
        (fun x hx => privateDiagonal_avoids_interior hLq hx) hmax b a d hd n hshort
      simpa only [retainedLog, internalLog, hmid] using h
  have heq := congrArg δ₀ (hrawCoeff.trans hcap)
  exact ⟨hshort, hcountA, hcountQ, heq.trans hinter⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
