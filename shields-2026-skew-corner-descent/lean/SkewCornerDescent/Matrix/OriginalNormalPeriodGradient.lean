/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalProfileGradient
import SkewCornerDescent.Matrix.SelectedCoreCrossPolynomialGradient
import SkewCornerDescent.Matrix.OriginalSelectedCoreMultiplePhase
import SkewCornerDescent.Matrix.OriginalInternalPeriodHeight

/-!
# Complete high coefficient of an actual period-length internal response

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual period-height calculation and source-produced proper-core phases
identify the full high response gradient with the raw selected-function gradient.
Every positive normal jet vanishes by proof, without a frozen-unit substitution.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- On the actual periodic source, a complete period-length internal response has
exactly the raw lower selected-function high coefficient as a constant normal series.
The height, high-index inequality and all proper-core phase matches are produced. -/
theorem original_period_response_normal_gradient_of_le {n m : ℕ} (P : Profile n) (W : Profile m)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = r * d)
    (hresponse : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + d * r)
    (J H : ℕ+) (hJ : J ≤ c.top)
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
  have htotal := c.originalInternal_period_total_gt_top P r d hr hd hp
  have hHH : c.top < H := by
    have hpos := J.pos
    have hlt : (c.top : ℤ) < (H : ℤ) := by omega
    exact_mod_cast hlt
  have hgap (a b : Fin (originalSelectedCount (hD := hD) P)) (hab : b.val = a.val + r)
      (_hb : b.val + 1 < originalSelectedCount (hD := hD) P) :
      c.originalCompletedGap P a = c.originalCompletedGap P b := by
    have he : ZMod.finEquiv _ a + (r : ZMod (originalSelectedCount (hD := hD) P)) =
        ZMod.finEquiv _ b := by
      rw [finEquiv_eq_natCast, finEquiv_eq_natCast, hab, Nat.cast_add]
    have h := hp (ZMod.finEquiv _ a)
    rw [he] at h
    simpa only [RingEquiv.symm_apply_apply] using h.symm
  have hphase := c.originalSelectedCore_multiple_phase_jets P W q u v hv hW hwindow hq hLq hC
    r d hr hd hdiff hresponse hgap
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
    exact (hphase d i t ht j (hj.trans_lt hk)).2
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

/-- The complete actual period-length response has the raw selected-function high
coefficient at every normal order. Indices above the selected span give zero by
actual generator support, so there is no separate frozen or unsupported regime. -/
theorem original_period_response_normal_gradient {n m : ℕ} (P : Profile n) (W : Profile m)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = r * d)
    (hresponse : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + d * r)
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
  · exact c.original_period_response_normal_gradient_of_le P W q u v hv hW hwindow hq hLq hC
      r d hr hd hdiff hresponse hp i t ht J H hJ hH
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
