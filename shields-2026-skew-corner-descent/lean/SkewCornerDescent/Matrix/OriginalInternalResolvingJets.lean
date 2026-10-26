/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalProfileGradient
import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# Resolving-generator independence of actual positive onsite normal jets

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Every actual internal interval supplies its full normal inverse and ordered
selected endpoints. A resolving generator above the endpoint span minus
the core span therefore has zero derivative on every positive normal jet,
including the regime where it is above the whole local endpoint span.
The residue response itself is not asserted independent. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full onsite normal jet, not a frozen residue representative,
is independent of the resolving generator at every positive normal order. -/
theorem originalInternal_positive_normal_resolving_derivative {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (H : ℕ+) (hH : c.top < H)
    (hspan : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (H : ℤ) ≤
        (c.top : ℤ)) (m : ℕ) (hm : 0 < m) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalInternalResponseMatrix P i i))) = 0 := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let K := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E a)))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E b))))
  have hheight : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) = K := by
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) = K
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hentry := c.originalInternalResponseMatrix_selected_entry P i i
  rw [hentry]
  change residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
    (PowerSeries.coeff m (c.normalSeries
      (c.originalLocalResponse P (some (E a)) (some (E b))))) = 0
  by_cases hk : 0 ≤ K - (H : ℤ)
  · let k := (K-(H : ℤ)).toNat
    have hdegree : K-(H : ℤ) = (k : ℤ) := (Int.toNat_of_nonneg hk).symm
    have hbound : k ≤ (c.top : ℕ) := by rw [hheight] at hspan; omega
    have hab : a < b := by change i.val < i.val+1; omega
    have horder : interiorBlock P (E a).val.val ≤ interiorBlock P (E b).val.val :=
      (originalSelectedEnumeration_label_strictMono P hab).le
    have he := c.originalLocalResponse_normal_low_core_jets P (E a) (E b)
      horder H hH k hbound hdegree m
    simpa only [ne_of_gt hm, ↓reduceIte] using he
  · have hfull := c.originalLocalResponse_normal_gradient_above_span
      P (some (E a)) (some (E b)) H hH (by change K < (H : ℤ); omega)
    rw [← residueSeriesGeneratorDeriv_coeff, hfull, map_zero]

end SkewCornerDescent.Matrix.SelectedCoordinate
