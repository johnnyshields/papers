/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergTwoFrontiers
import SkewCornerDescent.Matrix.OriginalCompletedGaps
import SkewCornerDescent.Matrix.OriginalNormalFrontier
import SkewCornerDescent.CyclicGapPeriod

/-!
# The two frontiers of the actual internal normal matrix

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete actual gap geometry supplies every short-entry independence premise.
The full internal matrix retains normal-dependent inverse jets and both cost
frontiers. Its indices omit the two exterior cap states, not any internal
occurrence. End-cap cancellation belongs to the complete comparison assembly.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual retained internal state at each finite source-word position. -/
def originalInternalStateIndex {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    Fin (originalSelectedCount (hD := hD) P + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The complete actual response matrix on the internal retained states. -/
noncomputable def originalInternalResponseMatrix {n : ℕ} (P : Profile n) :
    Matrix (Fin (originalSelectedCount (hD := hD) P - 1))
      (Fin (originalSelectedCount (hD := hD) P - 1)) c.RegularRing :=
  (c.originalHessenbergResponse P).submatrix
    (originalInternalStateIndex (hD := hD) P) (originalInternalStateIndex (hD := hD) P)

/-- Every actual internal interval shorter than a complete period total lies
strictly below that total. All gap lower bounds come from actual source cells. -/
theorem originalInternalDistance_short_period {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r k : ℕ)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) (hij : i ≤ j)
    (hlen : j.val - i.val + 1 < k * r) :
    originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex (hD := hD) P i) (originalInternalStateIndex (hD := hD) P j) <
      k • windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
  let ii : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let jj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  have hij' : ii ≤ jj := hij
  have hsum := c.originalCompletedGap_internal_window P ii jj hij' (by
    have := j.isLt
    dsimp only [jj]
    omega)
  have hwindow := windowSum_finite_interval (c.originalCompletedGap P) ii jj hij'
  have hbound := windowSum_short_period_lt
    (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) (c.top : ℕ) r k
    (jj.val - ii.val + 1) hp (fun x => c.originalCompletedGap_gt_top P _)
    hlen (ii.val : ZMod (originalSelectedCount (hD := hD) P))
  rw [hwindow, ← hsum] at hbound
  exact hbound

/-- The full actual internal determinant has both exact normal frontiers.
No short-entry derivative, gap floor, subdiagonal unit, or first inverse jet
is supplied as an extra hypothesis. The fresh generator is above the period sum. -/
theorem originalInternal_normal_two_frontiers {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k : ℕ)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hheight : k • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K : ℤ)) :
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
    δ (PowerSeries.coeff (k*r) (c.normalSeries (c.originalInternalResponseMatrix P).det)) =
      ∑ σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)),
        if (∀ i : Fin (originalSelectedCount (hD := hD) P - 1), (i : ℕ) ≤ (σ i : ℕ) + 1) then
          let lower := Finset.univ.filter (fun i => (σ i : ℕ) < (i : ℕ))
          let upper := Finset.univ.filter (fun i => ¬ (σ i : ℕ) < (i : ℕ))
          (Equiv.Perm.sign σ : ℤ) •
            (if lower.card = k*r then
              (c.normalCoefficient)⁻¹ ^ (k*r) *
                δ (∏ i ∈ upper, PowerSeries.constantCoeff (A i (σ i)))
            else if lower.card + 1 = k*r then
              (c.normalCoefficient)⁻¹ ^ (k*r-1) *
                δ (PowerSeries.coeff 1 (∏ i ∈ upper, A i (σ i)))
            else 0)
        else 0 := by
  intro A δ
  rw [RingHom.map_det]
  change δ (PowerSeries.coeff (k*r) A.det) = _
  have hshape : IsUpperHessenberg A := by
    intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P
      (originalInternalStateIndex (hD := hD) P i)
      (originalInternalStateIndex (hD := hD) P j)) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P _ _ (by
      dsimp only [originalInternalStateIndex]
      omega), map_zero]
  have ha : δ (c.normalCoefficient)⁻¹ = 0 := by
    apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)
  have hsub : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      (i : ℕ) = (j : ℕ) + 1 → A i j = PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹ := by
    intro i j hij
    let b : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by
      have := j.isLt
      omega⟩
    have hi : originalInternalStateIndex (hD := hD) P i = b.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [originalInternalStateIndex, b]
      omega
    have hj : originalInternalStateIndex (hD := hD) P j = b.castSucc := rfl
    change c.normalSeries (c.originalHessenbergResponse P
      (originalInternalStateIndex (hD := hD) P i)
      (originalInternalStateIndex (hD := hD) P j)) = _
    rw [hi, hj]
    exact c.originalHessenberg_normalSeries_subdiagonal P b
  have hshort : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) + 1 < k*r →
      ∀ l, δ (PowerSeries.coeff l (A i j)) = 0 := by
    intro i j hij hlen l
    change δ (PowerSeries.coeff l (c.normalSeries (c.originalHessenbergResponse P
      (originalInternalStateIndex (hD := hD) P i)
      (originalInternalStateIndex (hD := hD) P j)))) = 0
    exact c.originalHessenberg_normalSeries_derivative_below P (NeZero.pos _) hmax K hK _ _
      (by change i.val + 1 ≤ j.val + 1; omega)
      ((c.originalInternalDistance_short_period P r k hp i j hij hlen).trans hheight) l
  simpa only [smul_eq_mul, zsmul_eq_mul] using
    hessenberg_coeff_deriv_two_frontiers δ A hshape (c.normalCoefficient)⁻¹ ha hsub (k*r) hshort

end SkewCornerDescent.Matrix.SelectedCoordinate
