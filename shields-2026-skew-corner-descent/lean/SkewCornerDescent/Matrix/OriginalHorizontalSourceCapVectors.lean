/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalHorizontalCapVectors

/-!
# Complete source-cap lists in canonical horizontal private bounds

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The source-to-copy equivalence retains both complete beta lists and uses the
actual canonical private-window endpoints. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Complete source caps match their canonical private-window copies in the
actual horizontal reference, with every row and column transported. -/
theorem originalHorizontalClosure_source_cap_vectors {n m : ℕ}
    (P : Profile n) (H : Profile m) (v : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate v H.cells) (copy upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let shift : ℤ := if copy then P.xi 0 else 0
    let hi : ℤ := if copy then H.xi 0 else P.xi 0
    let d := originalHorizontalClosureSelectedCopy P H v hH copy b
    ∃ e : OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      {i : OriginalWholeWindowRemaining (hD := hD) H shift hi //
        originalCapBlockSide upper d i.1.val},
      ∀ i, originalResponseRows H ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows P i.1.1 + shift ∧
        originalResponseCols H ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols P i.1.1 + shift := by
  intro shift hi d
  have htop : H.xi 0 = 2 * P.xi 0 := by
    have h := originalHorizontalClosure_xi_upper P H v hH 0
    change H.xi 0 = P.xi 0 + P.xi 0 at h
    omega
  have hbound : P.xi 0 + shift = hi := by
    cases copy <;> simp only [shift, hi, Bool.false_eq_true, ↓reduceIte, add_zero,
      htop, two_mul]
  obtain ⟨e, he⟩ := originalHorizontalClosure_half_cap_vectors P H v hH copy upper b
  obtain ⟨t, ht⟩ := originalWindow_cap_bound_vectors H shift (P.xi 0 + shift)
    shift hi rfl hbound upper d
  refine ⟨e.trans t, ?_⟩
  intro i
  have hsource := he i
  have htarget := ht (e i)
  exact ⟨htarget.1.trans hsource.1, htarget.2.trans hsource.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
