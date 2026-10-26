/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassDefects

/-!
# Exact transport between literal response classes and rational plane support

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`). The
finite support of signed multiplicities is transported by actual response equality.
The class values remain in the unchanged original field; inactive classes contribute
zero and no original word position is deleted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A faithful finite support parameterization preserves every signed class sum,
including negative multiplicities and arbitrary functions of the complete responses. -/
theorem originalResponseClass_sum_support {n m : ℕ} (P : Profile n) (W : Profile m)
    (a b : ℕ) (s : Finset ℚ) (e : ℚ → ℤ) (value : ℚ → OtherField c.top)
    (hinj : Function.Injective value) (hsupport : ∀ α, α ∈ s ↔ e α ≠ 0)
    (hweight : ∀ α ∈ s, e α = c.originalResponseValueExponent P W a b (value α))
    (hmem : ∀ α ∈ s, ∃ X : c.OriginalResponseClass P, X.val = value α)
    (hcover : ∀ X : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b X ≠ 0 → ∃ α ∈ s, X.val = value α)
    (H : OtherField c.top → OtherField c.top) :
    (∑ X : c.OriginalResponseClass P,
      (c.originalResponseClassExponent P W a b X : OtherField c.top) * H X.val) =
      ∑ α ∈ s, (e α : OtherField c.top) * H (value α) := by
  classical
  let active := Finset.univ.filter
    (fun X : c.OriginalResponseClass P => c.originalResponseClassExponent P W a b X ≠ 0)
  have hcollapse : (∑ X : c.OriginalResponseClass P,
      (c.originalResponseClassExponent P W a b X : OtherField c.top) * H X.val) =
      ∑ X ∈ active, (c.originalResponseClassExponent P W a b X : OtherField c.top) * H X.val := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro X _
    by_cases he : c.originalResponseClassExponent P W a b X = 0
    · simp only [he, ne_eq, not_true_eq_false, ite_false, Int.cast_zero, zero_mul]
    · rw [ite_eq_left he]
  have hchosen (α : ℚ) (hα : α ∈ s) :
      (Classical.choose (hmem α hα)).val = value α := Classical.choose_spec (hmem α hα)
  have hchosenWeight (α : ℚ) (hα : α ∈ s) :
      c.originalResponseClassExponent P W a b (Classical.choose (hmem α hα)) = e α := by
    change c.originalResponseValueExponent P W a b (Classical.choose (hmem α hα)).val = _
    rw [hchosen α hα]
    exact (hweight α hα).symm
  rw [hcollapse]
  symm
  apply Finset.sum_bij (fun α hα => Classical.choose (hmem α hα))
  · intro α hα
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hchosenWeight α hα]
    exact (hsupport α).mp hα
  · intro α hα β hβ he
    apply hinj
    exact (hchosen α hα).symm.trans ((congrArg Subtype.val he).trans (hchosen β hβ))
  · intro X hX
    have hne := (Finset.mem_filter.mp hX).2
    obtain ⟨α, hα, he⟩ := hcover X hne
    exact ⟨α, hα, Subtype.ext ((hchosen α hα).trans he.symm)⟩
  · intro α hα
    rw [hchosen α hα, hchosenWeight α hα]

end SkewCornerDescent.Matrix.SelectedCoordinate
