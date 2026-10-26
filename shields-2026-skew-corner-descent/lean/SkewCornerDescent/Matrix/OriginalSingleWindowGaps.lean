/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalHessenbergInventory

/-!
# Literal selected gaps from a common actual response top

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:residue-classifier`). The common-top premise is the remaining output
of the full-window classifier assembly, not an assumed geometric gap equality. The conclusions
use the complete original endpoints, including both true exterior caps. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Summing a response family with two exterior entries and a constant internal top. -/
theorem sum_two_caps_internal {B : ℕ} (hB : 0 < B) (f : Fin (B + 1) → ℤ) (K : ℤ)
    (h : ∀ i, 0 < i.val → i.val < B → f i = K) :
    ∑ i, f i = f 0 + f (Fin.last B) + ((B - 1 : ℕ) : ℤ) * K := by
  cases B with
  | zero => omega
  | succ m =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have hi (i : Fin m) : f i.castSucc.succ = K :=
      h _ (by simp) (by change i.val + 1 < m + 1; omega)
    simp only [hi, Fin.succ_last, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.add_sub_cancel]
    ring

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A common actual internal top fixes every literal consecutive selected gap. -/
theorem originalSelected_gap_of_common_top {n : ℕ} (P : Profile n) (K : ℤ)
    (hsame : ∀ i : Fin (originalSelectedCount (hD := hD) P + 1),
      0 < i.val → i.val < originalSelectedCount (hD := hD) P →
        originalHessenbergDistance (hD := hD) P i i = K)
    (a k : Fin (originalSelectedCount (hD := hD) P)) (hnext : a.val + 1 = k.val) :
    P.zeta (interiorBlockLast P
        (originalSelectedEnumeration (hD := hD) P a).val.val).castSucc -
      P.zeta (interiorBlockLast P
        (originalSelectedEnumeration (hD := hD) P k).val.val).castSucc = K - (c.top : ℤ) := by
  have he := c.originalHessenbergDistance_between P a k hnext
  have ht := hsame a.succ (by simp)
    (by change a.val + 1 < originalSelectedCount (hD := hD) P; omega)
  omega

/-- Once the full-window assembly identifies the two cap sum with the closure top, the actual
parent endpoint span is the number of selected occurrences times the common gap. -/
theorem originalSpan_of_common_top {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) (K : ℤ)
    (hsame : ∀ i : Fin (originalSelectedCount (hD := hD) P + 1),
      0 < i.val → i.val < originalSelectedCount (hD := hD) P →
        originalHessenbergDistance (hD := hD) P i i = K)
    (hcaps : originalHessenbergDistance (hD := hD) P 0 0 +
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) = K) :
    P.xi 0 - P.zeta (Fin.last n) =
      (originalSelectedCount (hD := hD) P : ℤ) * (K - (c.top : ℤ)) := by
  have hs := sum_two_caps_internal hB
    (fun i => originalHessenbergDistance (hD := hD) P i i) K hsame
  rw [c.originalHessenbergDistance_sum P, hcaps] at hs
  have hcount : ((originalSelectedCount (hD := hD) P - 1 : ℕ) : ℤ) =
      (originalSelectedCount (hD := hD) P : ℤ) - 1 := by omega
  rw [hcount] at hs
  linear_combination hs

end SelectedCoordinate
end SkewCornerDescent.Matrix
