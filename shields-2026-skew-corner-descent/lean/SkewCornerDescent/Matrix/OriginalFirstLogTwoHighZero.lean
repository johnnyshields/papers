/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalCrossSelfIdentity
import SkewCornerDescent.Matrix.OriginalFirstLogHighZero
import SkewCornerDescent.Matrix.NormalCyclicBalancedDerivative
import SkewCornerDescent.Matrix.NormalCyclicPairProduct
import SkewCornerDescent.CyclicPeriodicProducts

/-!
# Exact two-state cancellation in the whole original first logarithm

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
All genuine adjacent-entry gradients are produced on both actual diagrams.
Complete overlap words transport their inverse pair products, and the exact
weighted occurrence counts cancel the high derivative. No coprimality or
frozen inverse jet is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual two-state first-normal independence from exact occurrence balance. -/
theorem originalCompleted_first_log_two_high_zero {n m an qn : ℕ}
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
    (hn : (b - a) * r = 2) (J H : ℕ+)
    (hH : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ))
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    let d := b - a
    let K := c.originalInternalPeriodHigherIndex P r d
      (show 2 ≤ d * r by dsimp only [d]; omega) hgap J H hH
    let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = active) → δ (PowerSeries.coeff 1 logDefect) = 0 := by
  let d := b - a
  let n := d * r
  have hnEq : n = 2 := hn
  have hn2 : 2 ≤ n := by omega
  have hd : 0 < d := by dsimp only [d]; omega
  let : NeZero n := ⟨by omega⟩
  let K := c.originalInternalPeriodHigherIndex P r d hn2 hgap J H hH
  let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let Δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let γ := c.normalCoefficient⁻¹ * c.residueMap (pderiv J (cellSchur D hD.1))
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    change (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ)
    rw [hH]
    have hj := J.pos
    omega
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hcountW : originalSelectedCount (hD := hD) W = a * r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hCW : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos ha hrpos
  have hproper : originalSelectedCount (hD := hD) W < originalSelectedCount (hD := hD) P := by
    rw [hcountW, hcountP]
    exact Nat.mul_lt_mul_of_pos_right hab hrpos
  have hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = d * r := by
    rw [hcountP, hcountW, ← Nat.sub_mul]
  obtain ⟨hshort, hcountA, hcountQ, hfirst⟩ := c.originalCompleted_first_log_cyclic
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
    hKU hKW hmax hn2 κ hmatch
  have hshort' : n < originalSelectedCount (hD := hD) P := hshort
  have hcountA' : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n :=
    hcountA
  obtain ⟨hposA, hpA, hsumA⟩ := c.originalCompleted_amalgamation_gap_period_data
    P W A q u v w hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW hgap
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hposA⟩
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega⟩
  have hpQ : Function.Periodic
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) Q)) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_period P Q z hQ r hgap
    · exact c.originalVerticalClosure_completed_gap_period P Q z hQ r hgap
  have hsumQ : windowSum
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 =
      windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_window P Q z hQ r
    · exact c.originalVerticalClosure_completed_gap_window P Q z hQ r
  have hmaxA := originalAmalgamation_component_span P W A q v w u hv hwindow hW.symm hA
    (c.top : ℕ) hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q z hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hQ hmax
  have hdA (i : Fin (originalSelectedCount (hD := hD) A - 1)) (k : ℕ) :
      δ (PowerSeries.coeff k (c.normalSeries (c.originalInternalResponseMatrix A i i))) = 0 := by
    have he := c.originalInternal_normal_diagonal_high_zero A hmaxA r d hn2 hpA K.val K.property
      (by rw [hsumA]; exact hheight) i
    simpa only [residueSeriesGeneratorDeriv_coeff, map_zero] using congrArg (PowerSeries.coeff k) he
  have hdQ (i : Fin (originalSelectedCount (hD := hD) Q - 1)) (k : ℕ) :
      δ (PowerSeries.coeff k (c.normalSeries (c.originalInternalResponseMatrix Q i i))) = 0 := by
    have he := c.originalInternal_normal_diagonal_high_zero Q hmaxQ r d hn2 hpQ K.val K.property
      (by rw [hsumQ]; exact hheight) i
    simpa only [residueSeriesGeneratorDeriv_coeff, map_zero] using congrArg (PowerSeries.coeff k) he
  have hGA (i j : Fin (originalSelectedCount (hD := hD) A - 1))
      (hij : j.val + 1 = i.val + n) :
      Δ (c.normalSeries (c.originalInternalResponseMatrix A i j)) = PowerSeries.C γ := by
    rw [c.originalInternalResponseMatrix_selected_entry A i j]
    exact c.originalCompleted_amalgamation_period_gradient P W A q u v w hq0 hv
      hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap
      d hn2 _ _ hij J H hH
  have hGQ (i j : Fin (originalSelectedCount (hD := hD) Q - 1))
      (hij : j.val + 1 = i.val + n) :
      Δ (c.normalSeries (c.originalInternalResponseMatrix Q i j)) = PowerSeries.C γ := by
    rw [c.originalInternalResponseMatrix_selected_entry Q i j]
    rcases hQ with hQ | hQ
    · exact c.originalCompleted_closure_period_gradient P W Q z hQ q u v hv hW hwindow hq hLq
        Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap d hn2 _ _ hij J H hH
    · exact c.originalCompleted_vertical_period_gradient P W Q z hQ q u v hv hW hwindow hq hLq
        Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap d hn2 _ _ hij J H hH
  have hresA := c.originalAmalgamation_normal_residue_cycle P W A q v w u hq0 hv hwindow
    hW.symm hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) hCW hproper r d hrpos hd hdiff
    active hresponse
  obtain ⟨_, hresQ⟩ := c.originalClosure_normal_residue_cycle P Q z hQ active
  obtain ⟨_, _, hwordA⟩ := c.originalAmalgamation_internal_word_periods P W A q v w u hq0 hv
    hwindow hW.symm hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  obtain ⟨_, hwordQ⟩ := c.originalClosure_internal_word_periods P Q z hQ
  have hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P = n := by
    omega
  dsimp only at hwordA hwordQ
  rw [hshift] at hwordA
  let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
  let MQ := (c.originalInternalResponseMatrix Q).map c.normalSeries
  let g := completeResponseCycle (c.originalInternalResidue P) active
  have hper2 : Function.Periodic (fun s => (g s)⁻¹)
      (2 : ZMod (originalSelectedCount (hD := hD) P)) := by
    intro s
    have he := (hresponse.nsmul d) s
    have hc : d • (r : ZMod (originalSelectedCount (hD := hD) P)) = 2 := by
      rw [nsmul_eq_mul, ← Nat.cast_mul]
      exact congrArg (fun k : ℕ => (k : ZMod (originalSelectedCount (hD := hD) P))) hnEq
    rw [hc] at he
    exact congrArg Inv.inv he
  let Z := (g 0)⁻¹ * (g 1)⁻¹
  have hZ (s : ZMod (originalSelectedCount (hD := hD) P)) : (g s)⁻¹ * (g (s + 1))⁻¹ = Z := by
    have he := windowProduct_of_zmod_period (fun s => (g s)⁻¹) 2 hper2 s
    simpa only [windowProduct, Finset.prod_range_succ, Finset.prod_range_zero,
      zero_nsmul, one_nsmul, add_zero, zero_add, one_mul, Z] using he
  have hα : δ c.normalCoefficient⁻¹ = 0 := by
    apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono K.property.le c.normalCoordinate_mem_lower.1)
  refine ⟨hcountQ, ?_⟩
  intro hactive
  have hresQ' := hresQ hactive
  dsimp only at hfirst ⊢
  rw [hfirst]
  apply normalCyclicFirstCharge_balanced_deriv (N := n)
    (M := originalSelectedCount (hD := hD) P) δ _ _ _ _ c.normalCoefficient⁻¹ γ Z b d
  · rw [hcountP]
    dsimp only [n]
    ring
  · exact hα
  · intro s
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hdA ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩ 0
  · intro s
    exact hdA ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩ 1
  · intro s
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hdQ ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩ 0
  · intro s
    exact hdQ ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩ 1
  · intro s
    have he := hGA ⟨s.val, by have := ZMod.val_lt s; omega⟩
      ⟨s.val + 1, by have := ZMod.val_lt s; omega⟩ (by dsimp only; omega)
    have hh := congrArg (PowerSeries.coeff 0) he
    rw [residueSeriesGeneratorDeriv_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C] at hh
    exact hh
  · intro s
    have he := hGQ ⟨s.val, by have := ZMod.val_lt s; omega⟩
      ⟨s.val + 1, by have := ZMod.val_lt s; omega⟩ (by dsimp only; omega)
    have hh := congrArg (PowerSeries.coeff 0) he
    rw [residueSeriesGeneratorDeriv_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C] at hh
    exact hh
  · intro s
    exact normalDiagonalCycle_inverse_pair MA (by omega) hwordA.1 g hresA Z hZ s
  · intro s
    exact normalDiagonalCycle_inverse_pair MQ (by omega) hwordQ.1 g hresQ' Z hZ s

end SkewCornerDescent.Matrix.SelectedCoordinate
