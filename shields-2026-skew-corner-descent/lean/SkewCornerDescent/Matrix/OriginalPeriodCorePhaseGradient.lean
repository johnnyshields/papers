/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPeriodGradient

/-!
# Period-length gradients from the actual proper-core phase

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The required right-core phase is explicit. Original literal windows produce it
through `originalSelectedCore_multiple_phase_jets`; literal closure transport
allows that same producer to be used on the actual completed words.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact source period heights and the actual right-core phase supply the full
normal gradient. The phase premise is DERIVED and must be produced by the caller. -/
theorem original_period_response_normal_gradient_of_core_phase {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + d * r)
    (hphase : ∀ k < (c.top : ℕ), (c.originalSelectedCoreRight P t).coeff k =
      (c.originalSelectedCoreRight P i).coeff k)
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    residueSeriesGeneratorDeriv c.top
      ⟨H, by
        have h := c.originalInternal_period_total_gt_top P r d hr hd hp
        have hpos := J.pos
        have hlt : (c.top : ℤ) < (H : ℤ) := by omega
        exact ne_of_gt (show c.top < H by exact_mod_cast hlt)⟩
      (c.normalSeries (c.originalLocalResponse P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))) =
      PowerSeries.C (c.normalCoefficient⁻¹ *
        c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))) := by
  by_cases hJ : J ≤ c.top
  · have htotal := c.originalInternal_period_total_gt_top P r d hr hd hp
    have hHH : c.top < H := by
      have hpos := J.pos
      have hlt : (c.top : ℤ) < (H : ℤ) := by omega
      exact_mod_cast hlt
    let E := originalSelectedEnumeration (hD := hD) P
    let A := interiorBlockProfile P (E i).val.val
      (originalBlockSelected_nonempty P (E i).val (E i).property)
    let B := interiorBlockProfile P (E t).val.val
      (originalBlockSelected_nonempty P (E t).val (E t).property)
    have hA : cellSchur D hD.1 = A.schur := (originalSelectedProfile_schur P (E i)).symm
    have hB : cellSchur D hD.1 = B.schur := (originalSelectedProfile_schur P (E t)).symm
    let k := (c.top : ℕ) - (J : ℕ)
    have hk : k < (c.top : ℕ) := by
      have := J.pos
      change (J : ℕ) ≤ (c.top : ℕ) at hJ
      dsimp only [k]
      omega
    have hdegree : (c.top : ℤ) - (J : ℤ) = (k : ℤ) := by
      change (J : ℕ) ≤ (c.top : ℕ) at hJ
      dsimp only [k]
      omega
    have hright (j : ℕ) (hj : j ≤ k) :
        (c.selectedCoreRightPolynomial B hB).coeff j =
          (c.selectedCoreRightPolynomial A hA).coeff j := by
      exact hphase j (hj.trans_lt hk)
    have horder : interiorBlock P (E i).val.val ≤ interiorBlock P (E t).val.val :=
      interiorBlock_mono P (show (E i).val.val ≤ (E t).val.val from
        E.monotone (show i ≤ t from by change i.val ≤ t.val; omega))
    have hspan := c.originalInternal_period_endpoint_height P r d hr hd hp i t ht
    have hdeg : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i)))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E t)))) - (H : ℤ) = (k : ℤ) := by
      change P.xi (originalRowSplitEquiv P (.inl (some (E i)))) -
        P.zeta (originalColSplitEquiv P (.inl (some (E t)))) = _ at hspan
      omega
    rw [c.originalLocalResponse_normal_low_core_gradient P (E i) (E t) horder H hHH k hk.le hdeg]
    rw [c.selected_core_cross_polynomial_gradient A B hA hB J k hdegree hright]
  · have hgt : c.top < J := lt_of_not_ge hJ
    have hps : polynomialSpan (cellSchur D hD.1) = (c.top : ℕ) := by
      rw [polynomialSpan_cellSchur hD, ← c.span_eq]
    have hnot : J ∉ (cellSchur D hD.1).vars := by
      intro hj
      have hle : (J : ℕ) ≤ polynomialSpan (cellSchur D hD.1) := Finset.le_sup hj
      rw [hps] at hle
      exact (not_le_of_gt hgt) hle
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot, map_zero, mul_zero, map_zero]
    have htotal := c.originalInternal_period_total_gt_top P r d hr hd hp
    have hHH : c.top < H := by
      have hpos := J.pos
      have hlt : (c.top : ℤ) < (H : ℤ) := by omega
      exact_mod_cast hlt
    apply c.originalLocalResponse_normal_gradient_above_span P _ _ H hHH
    have hspan := c.originalInternal_period_endpoint_height P r d hr hd hp i t ht
    have hgtI : (c.top : ℤ) < (J : ℤ) := by exact_mod_cast hgt
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
