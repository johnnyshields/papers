/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalLogOverlap
import SkewCornerDescent.Matrix.OriginalAmalgamationPeriodGradient
import SkewCornerDescent.Matrix.OriginalClosurePeriodGradient
import SkewCornerDescent.Matrix.OriginalVerticalPeriodGradient
import SkewCornerDescent.Matrix.OriginalComparisonInternalLogs
import SkewCornerDescent.Matrix.OriginalInternalPeriodEntryGradient

/-!
# Closed actual three-word open overlap comparison

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original corner powers and literal windows supply every actual word's
constant period-entry gradient, gap period, and diagonal regularity. The
open-word expression retains all long, vertex, and overlapping-pair terms.
Passing from these finite open sums to cyclic charges is a separate identity.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The exact actual source comparison has its complete finite open overlap
formula in both ordinary closure directions. Every period gradient is produced
inside the proof; none is an additional hypothesis. -/
theorem originalCompleted_open_overlap_comparison {n m an qn : ℕ}
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
    let m := d * r
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
      let M := (c.originalInternalResponseMatrix X).map c.normalSeries
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
    let openCharge : {k : ℕ} → Profile k → OtherField c.top := fun X =>
      let A := (c.originalInternalResponseMatrix X).map c.normalSeries
      let w₀ := fun i => (PowerSeries.constantCoeff (A i i))⁻¹
      let ν := fun i => PowerSeries.coeff 1 (A i i) * w₀ i
      let m := d * r
      let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
      let long := ∑ i : Fin (originalSelectedCount (hD := hD) X - 1), ∑ j,
        if i.val ≤ j.val ∧ j.val - i.val = m then
          δ (A i j) * ∏ k ∈ Finset.Icc i j, (A k k)⁻¹ else 0
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m * PowerSeries.constantCoeff long -
      (-1 : OtherField c.top) ^ (m - 1) * c.normalCoefficient⁻¹ ^ (m - 1) * γ *
        (∑ i : Fin (originalSelectedCount (hD := hD) X - 1), ∑ j,
          if j.val - i.val = m - 1 then
            (∏ k ∈ Finset.Icc i j, w₀ k) * ∑ k ∈ Finset.Icc i j, ν k else 0) -
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m * γ *
        (∑ i : Fin (originalSelectedCount (hD := hD) X - 1), ∑ j, ∑ k, ∑ l,
          if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
            ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
              (∏ s ∈ Finset.Icc i j, w₀ s) *
                (PowerSeries.constantCoeff (A k l) * ∏ s ∈ Finset.Icc k l, w₀ s) else 0)
    δ₀ (PowerSeries.coeff m (b • wordLog A - a • wordLog P - d • wordLog Q)) =
      b • openCharge A - a • openCharge P - d • openCharge Q := by
  let d := b - a
  let m := d * r
  let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
  let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
  let wordLog : {k : ℕ} → Profile k → PowerSeries (OtherField c.top) := fun X =>
    let M := (c.originalInternalResponseMatrix X).map c.normalSeries
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)
  let openCharge : {k : ℕ} → Profile k → OtherField c.top := fun X =>
      let A := (c.originalInternalResponseMatrix X).map c.normalSeries
      let w₀ := fun i => (PowerSeries.constantCoeff (A i i))⁻¹
      let ν := fun i => PowerSeries.coeff 1 (A i i) * w₀ i
      let m := d * r
      let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
      let long := ∑ i : Fin (originalSelectedCount (hD := hD) X - 1), ∑ j,
        if i.val ≤ j.val ∧ j.val - i.val = m then
          δ (A i j) * ∏ k ∈ Finset.Icc i j, (A k k)⁻¹ else 0
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m * PowerSeries.constantCoeff long -
      (-1 : OtherField c.top) ^ (m - 1) * c.normalCoefficient⁻¹ ^ (m - 1) * γ *
        (∑ i : Fin (originalSelectedCount (hD := hD) X - 1), ∑ j,
          if j.val - i.val = m - 1 then
            (∏ k ∈ Finset.Icc i j, w₀ k) * ∑ k ∈ Finset.Icc i j, ν k else 0) -
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m * γ *
        (∑ i : Fin (originalSelectedCount (hD := hD) X - 1), ∑ j, ∑ k, ∑ l,
          if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
            ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
              (∏ s ∈ Finset.Icc i j, w₀ s) *
                (PowerSeries.constantCoeff (A k l) * ∏ s ∈ Finset.Icc k l, w₀ s) else 0)
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
      originalSelectedCount (hD := hD) W = r * d := by
    dsimp only [d]
    rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  have hrd : r * d = d * r := Nat.mul_comm _ _
  have hm2 : 2 ≤ d * r := hn
  have hWP : originalSelectedCount (hD := hD) W <
      originalSelectedCount (hD := hD) P := by omega
  have hP2 : 2 ≤ originalSelectedCount (hD := hD) P := by omega
  have hres (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val = i.val + r) : c.originalInternalResidue P i = c.originalInternalResidue P j :=
    completeResponseCycle_internal_period (c.originalInternalResidue P) active r hresponse i j hij
  have hinv := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v w u hv hwindow hW.symm hA
  have hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A := by omega
  have hA2 : 2 ≤ originalSelectedCount (hD := hD) A := hP2.trans hAP
  obtain ⟨hApos, hdata⟩ := c.originalCompleted_amalgamation_gap_period_data P W A q u v w
    hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW hgap
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hApos⟩
  obtain ⟨hpA, hsumA⟩ := hdata
  have hmaxA : ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ (c.top : ℕ) :=
    originalAmalgamation_component_span P W A q v w u hv hwindow hW.symm hA _ hmax
  have hcountQ : originalSelectedCount (hD := hD) Q =
      2 * originalSelectedCount (hD := hD) P := by
    rcases hQ with hQ | hQ
    · exact originalHorizontalClosure_profile_selected_count P Q z hQ
    · exact originalVerticalClosure_profile_selected_count P Q z hQ
  have hQ2 : 2 ≤ originalSelectedCount (hD := hD) Q := by omega
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hpQ : Function.Periodic
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) Q)) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_period P Q z hQ r hgap
    · exact c.originalVerticalClosure_completed_gap_period P Q z hQ r hgap
  have hsumQ : windowSum (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 =
      windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_window P Q z hQ r
    · exact c.originalVerticalClosure_completed_gap_window P Q z hQ r
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q z hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hQ hmax
  have hHA : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap A ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ) := by
    rw [hsumA]
    exact hH
  have hHQ : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ) := by
    rw [hsumQ]
    exact hH
  have hGP (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val + 1 = i.val + d * r) :
      δ (c.normalSeries (c.originalInternalResponseMatrix P i j)) = PowerSeries.C γ :=
    c.originalInternal_period_entry_gradient P W q u v hv hW hwindow hq hLq hCW
      r d hn hdiff hres hgap i j hij J H hH
  have hGA (i j : Fin (originalSelectedCount (hD := hD) A - 1))
      (hij : j.val + 1 = i.val + d * r) :
      δ (c.normalSeries (c.originalInternalResponseMatrix A i j)) = PowerSeries.C γ := by
    rw [c.originalInternalResponseMatrix_selected_entry A i j]
    exact c.originalCompleted_amalgamation_period_gradient P W A q u v w hq0 hv
      hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap
      d hn _ _ hij J H hH
  have hGQ (i j : Fin (originalSelectedCount (hD := hD) Q - 1))
      (hij : j.val + 1 = i.val + d * r) :
      δ (c.normalSeries (c.originalInternalResponseMatrix Q i j)) = PowerSeries.C γ := by
    rw [c.originalInternalResponseMatrix_selected_entry Q i j]
    rcases hQ with hQ | hQ
    · exact c.originalCompleted_closure_period_gradient P W Q z hQ q u v hv hW hwindow hq hLq
        Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap d hn _ _ hij J H hH
    · exact c.originalCompleted_vertical_period_gradient P W Q z hQ q u v hv hW hwindow hq hLq
        Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap d hn _ _ hij J H hH
  have hPlog : δ₀ (PowerSeries.coeff m (wordLog P)) = openCharge P :=
    c.originalInternal_marked_log_overlap P hP2 hmax r d hn hgap J H hH hGP
  have hAlog : δ₀ (PowerSeries.coeff m (wordLog A)) = openCharge A :=
    c.originalInternal_marked_log_overlap A hA2 hmaxA r d hn hpA J H hHA hGA
  have hQlog : δ₀ (PowerSeries.coeff m (wordLog Q)) = openCharge Q :=
    c.originalInternal_marked_log_overlap Q hQ2 hmaxQ r d hn hpQ J H hHQ hGQ
  dsimp only
  change δ₀ (PowerSeries.coeff m (b • wordLog A - a • wordLog P - d • wordLog Q)) =
    b • openCharge A - a • openCharge P - d • openCharge Q
  simp only [map_sub, map_nsmul, hAlog, hPlog, hQlog]

end SkewCornerDescent.Matrix.SelectedCoordinate
