/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalPeriodEntryGradient
import SkewCornerDescent.Matrix.OriginalSelectedProfileLocality

/-!
# Actual next-length entry gradients from full local profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Two exact period-height identities supply both full local-height bounds.
Integer Laurent offsets preserve the zero regime above each local height.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A next-length actual internal entry has its full local cross-profile gradient.
Both proper selected strips and every nonselected inverse coupling remain; offsets
below zero vanish as Laurent coefficients rather than becoming constant terms. -/
theorem originalInternal_long_entry_local_gradient {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hlen : j.val = i.val + d * r) (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let a : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨i.val, by have := i.isLt; omega⟩
    let b : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨i.val + 1, by have := i.isLt; omega⟩
    let e : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨j.val, by have := j.isLt; omega⟩
    let t : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨j.val + 1, by have := j.isLt; omega⟩
    let E := originalSelectedEnumeration (hD := hD) P
    residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (c.regularResidue (c.originalInternalResponseMatrix P i j)) =
    ((c.originalResidueLeftEndpointPolynomial P (some (E a)) (some (E b)) *
      c.originalResidueRightEndpointPolynomial P (some (E e)) (some (E t))).toLaurent).coeff
        (P.xi (originalRowSplitEquiv P (.inl (some (E a)))) -
          P.zeta (originalColSplitEquiv P (.inl (some (E b)))) - (J : ℤ)) := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let a : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨i.val + 1, by have := i.isLt; omega⟩
  let e : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨j.val, by have := j.isLt; omega⟩
  let t : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨j.val + 1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let x := fun k => P.xi (originalRowSplitEquiv P (.inl (some (E k))))
  let y := fun k => P.zeta (originalColSplitEquiv P (.inl (some (E k))))
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, zero_mul] at hn
    omega
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := by omega
    rw [hz, mul_zero] at hn
    omega
  have hdiag (k) : x k - y k = (c.top : ℤ) := by
    dsimp only [x, y]
    rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
    exact c.originalSelected_endpoint_distance P (E k)
  have hleftperiod := c.originalInternal_period_endpoint_height P r d hr hd hp b t
    (by change j.val + 1 = i.val + 1 + d * r; omega)
  have hrightperiod := c.originalInternal_period_endpoint_height P r d hr hd hp a e hlen
  change x b - y t = _ at hleftperiod
  change x a - y e = _ at hrightperiod
  have hdegree : x a - y t - (H : ℤ) = x a - y b - (J : ℤ) := by
    have hb := hdiag b
    omega
  have hboundleft : x a - y b - (J : ℤ) ≤ x a - y b := by have := J.pos; omega
  have hboundright : x a - y b - (J : ℤ) ≤ x e - y t := by
    have he := hdiag e
    have := J.pos
    omega
  have hle (u v : Fin (originalSelectedCount (hD := hD) P)) (h : u.val ≤ v.val) :
      (E u).val ≤ (E v).val := E.monotone h
  have hab : a.val ≤ b.val := by change i.val ≤ i.val + 1; omega
  have hbt : b.val ≤ t.val := by change i.val + 1 ≤ j.val + 1; omega
  have hae : a.val ≤ e.val := by change i.val ≤ j.val; omega
  have het : e.val ≤ t.val := by change j.val ≤ j.val + 1; omega
  dsimp only
  rw [c.originalInternalResponseMatrix_selected_entry P i j]
  exact c.original_long_response_local_gradient_laurent P (E a) (E b) (E e) (E t)
    ⟨hle a b hab, hle b t hbt⟩ ⟨hle a e hae, hle e t het⟩ H K.property
    (x a - y b - (J : ℤ)) hdegree hboundleft hboundright

end SkewCornerDescent.Matrix.SelectedCoordinate
