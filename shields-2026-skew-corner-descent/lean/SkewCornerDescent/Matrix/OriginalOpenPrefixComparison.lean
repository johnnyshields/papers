/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOpenOverlapComparison
import SkewCornerDescent.Matrix.OriginalNormalOpenPrefixes

/-!
# Closed actual logarithmic derivative as two complete prefix charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original corner powers and literal geometry produce all counts and copied
matrices. The complete marked logarithm comparison then reduces to its two
actual finite prefixes in both ordinary closure directions.
Cyclic charge simplification is a separate identity.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual three-word logarithmic derivative equals its two complete normal
prefix charges. No entry gradient, copied inverse, or finite charge match is
an extra premise; every supplier is invoked in the proof. -/
theorem originalCompleted_open_prefix_comparison {n m an qn : ℕ}
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
      let M := (c.originalInternalResponseMatrix X).map c.normalSeries
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
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
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
  let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
    let M := (c.originalInternalResponseMatrix X).map c.normalSeries
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
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
  have hn2 : 2 ≤ n := hn
  have hshort : n < originalSelectedCount (hD := hD) P := by omega
  have hinv := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v w u hv hwindow hW.symm hA
  have hcountA : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := by omega
  have hshift : originalSelectedCount (hD := hD) A -
      originalSelectedCount (hD := hD) P = n := by omega
  obtain ⟨_, hcountQ, hpref⟩ := c.originalComparison_normal_open_prefixes P W A Q
    q v w u z hq0 hv hwindow hW.symm hA hQ
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) (n - 1) (by omega) (by omega)
  have hpre := hpref δ c.normalCoefficient⁻¹ γ a d
  have hb : a + d = b := by dsimp only [d]; omega
  have hlen : n - 1 + 1 = n := by omega
  simp only [hb, hlen, hshift] at hpre
  have hopen := c.originalCompleted_open_overlap_comparison P W A Q q u v w z hq0 hv
    hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap hmax hn J H hH
  change δ₀ (PowerSeries.coeff n (b • wordLog A - a • wordLog P - d • wordLog Q)) =
    b • normalOpenOverlapCharge ((c.originalInternalResponseMatrix A).map c.normalSeries)
      δ c.normalCoefficient⁻¹ γ n -
    a • normalOpenOverlapCharge ((c.originalInternalResponseMatrix P).map c.normalSeries)
      δ c.normalCoefficient⁻¹ γ n -
    d • normalOpenOverlapCharge ((c.originalInternalResponseMatrix Q).map c.normalSeries)
      δ c.normalCoefficient⁻¹ γ n at hopen
  exact ⟨hshort, hcountA, hcountQ, hopen.trans hpre⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
