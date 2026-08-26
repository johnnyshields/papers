/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Assembling one bound out of several

`eq:phase-derivative-bound` is needed at **one** constant over an arbitrary
ordered family of blocks anywhere in the arc, while it is proved region by region
— a collar at each end and the interior, and inside the interior one collar per
amplitude zero.  Both steps that put those together are here, and neither is
about the amplitude: they are statements about bounding a real function.

They are separated from `EndpointCofactorBound` because they are, and because
that module had grown past the file-length limit carrying them.  This module is
**imported by** it rather than importing it, so the declarations stay reachable
from the root re-export and the guard file through the import they already have
— a module hung downstream of a guarded one would be reachable from neither, and
`lake build` on the module alone cannot see that.

## Main statements

* `abs_le_of_cover_three` — one bound from three, with the cover carried as a
  hypothesis so a seam cannot be skipped.
* `Icc_subset_cover_three` — that cover at the sets the regions are.
* `exists_bound_of_finite_exceptional` — bounded off a finite exceptional set,
  which is the several-amplitude-zero mechanism.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `lem:amplitude-divisor`,
`eq:amplitude-zero-count`, `eq:phase-derivative-bound`).

## Tags

covering, uniformity, amplitude divisor, phase derivative
-/

namespace ForgacsTran

open Set

/-! ### One `κ` from the three regions -/

/-- **A pointwise bound from a three-set cover, with the cover as a hypothesis.**
`AngularDiscrepancyFT.FTPhaseSupply` needs `|Im(W'/W)| ≤ κ` at one `κ` over an
arbitrary ordered family of blocks anywhere in the arc, and the bound is
assembled from three regions — a collar at each end and the interior.  Taking
`max` of the three constants is the whole of it, but it is stated here rather
than performed inline, because the two ways it goes wrong are both silent.

**The cover must have no seam.**  A point in none of the three regions has no
bound, and nothing downstream would notice: the composed statement would still
typecheck and still be provable on each region separately.  `hcov` is that
hypothesis, and it is the reason this is a lemma.

**A block straddling two regions is not a separate case.**  `hbranch` quantifies
over blocks positioned arbitrarily, so a block spanning the interior and a collar
is admissible, and one might expect the assembly to need care there.  It does
not, and the reason is worth stating: the bound is *pointwise*, and the `max` is
taken once over the regions rather than per block, so every point of a straddling
block is covered by whichever region contains it and the same `max` serves.  What
would break under straddling is a bound stated per block or a constant depending
on the family — which is (ii)'s failure mode one level down. -/
theorem abs_le_of_cover_three {f : ℝ → ℝ} {S A B C : Set ℝ} {κ₁ κ₂ κ₃ : ℝ}
    (hcov : S ⊆ A ∪ B ∪ C)
    (hA : ∀ x ∈ A, |f x| ≤ κ₁) (hB : ∀ x ∈ B, |f x| ≤ κ₂)
    (hC : ∀ x ∈ C, |f x| ≤ κ₃) :
    ∀ x ∈ S, |f x| ≤ max κ₁ (max κ₂ κ₃) := by
  intro x hx
  rcases hcov hx with (hx' | hx') | hx'
  · exact le_trans (hA x hx') (le_max_left _ _)
  · exact le_trans (hB x hx') (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact le_trans (hC x hx') (le_trans (le_max_right _ _) (le_max_right _ _))

/-- **The arc is covered by two collars and the interior, with no seam.**  The
covering hypothesis `abs_le_of_cover_three` asks for, at the sets the three
regions actually are: `[0,b₁]`, `[b₁,b₂]`, `[b₂,L]`.  The endpoints are shared
rather than excluded, which is what makes the union exact — a cover written with
half-open middle pieces leaves the two seam points uncovered, and that is the
gap the lemma above exists to make impossible to skip.

**No ordering of `b₁`, `b₂`, `L` is required**, which was not obvious: the
statement was first written with `b₁ ≤ b₂ ≤ L` and neither hypothesis was used.
Every `x ∈ [0,L]` lands in the first piece it is below, and the last piece
catches the rest because `x ≤ L` is already given. -/
theorem Icc_subset_cover_three (b₁ b₂ : ℝ) {L : ℝ} :
    Icc (0 : ℝ) L ⊆ Icc (0 : ℝ) b₁ ∪ Icc b₁ b₂ ∪ Icc b₂ L := by
  intro x hx
  rcases le_or_gt x b₁ with h | h
  · exact Or.inl (Or.inl ⟨hx.1, h⟩)
  · rcases le_or_gt x b₂ with h' | h'
    · exact Or.inl (Or.inr ⟨h.le, h'⟩)
    · exact Or.inr ⟨h'.le, hx.2⟩


/-! ### The interior, across several amplitude zeros -/

/-- **Bounded off a finite exceptional set.**  `eq:phase-derivative-bound` on the
interior has to hold across *all* the amplitude zeros at once, and
`Amplitude.exists_phase_derivative_bound` reaches one.  What makes the several-zero
case work is not a harder estimate but the shape of the argument: each zero
contributes a bound on a collar around it, the complement of those collars is
compact and the function is continuous there, and one `max` finishes.

The exceptional set is a `Finset` because the amplitude divisor is —
`eq:amplitude-zero-count` bounds it by `deg B`.  **The collars need not be
disjoint**, which is the same economy `Amplitude.exists_amplitude_divisor_lower_bound`
takes for the modulus: a point inside two collars is bounded by either.

`hloc` is stated over all of `ℝ` with the membership as a hypothesis rather than
over `S`, so the chosen radius and constant are total functions and no dependent
choice is needed — the tree's own idiom, and the reason is that
`choose` over a `∀ z ∈ S` produces functions of the membership proof. -/
theorem exists_bound_of_finite_exceptional {g : ℝ → ℝ} {a b : ℝ} {S : Finset ℝ}
    (hcont : ContinuousOn g (Icc a b \ ↑S))
    (hloc : ∀ z : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      z ∈ S → ∀ θ ∈ Icc a b, θ ∉ S → |θ - z| < δ → |g θ| ≤ C) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc a b, θ ∉ S → |g θ| ≤ κ := by
  classical
  choose δ hδ C hC using hloc
  set K : Set ℝ := Icc a b \ ⋃ z ∈ S, Metric.ball z (δ z) with hKdef
  have hKcpt : IsCompact K :=
    isCompact_Icc.diff (isOpen_biUnion fun z _ => Metric.isOpen_ball)
  have hKsub : K ⊆ Icc a b \ ↑S := fun x hx =>
    ⟨hx.1, fun hxS => hx.2 (Set.mem_biUnion hxS (Metric.mem_ball_self (hδ x)))⟩
  obtain ⟨C₀, hC₀⟩ := hKcpt.exists_bound_of_continuousOn (hcont.mono hKsub)
  -- a point off the exceptional set is either in the compact part or in a collar
  have hsplit : ∀ θ ∈ Icc a b, θ ∉ S →
      |g θ| ≤ C₀ ∨ ∃ z ∈ S, |g θ| ≤ C z := by
    intro θ hθ hθS
    by_cases hK : θ ∈ K
    · exact Or.inl (by simpa [Real.norm_eq_abs] using hC₀ θ hK)
    · rw [hKdef] at hK
      simp only [Set.mem_sdiff, not_and, not_not] at hK
      obtain ⟨z, hzS, hzb⟩ := Set.mem_iUnion₂.1 (hK hθ)
      rw [Metric.mem_ball, Real.dist_eq] at hzb
      exact Or.inr ⟨z, hzS, hC z hzS θ hθ hθS hzb⟩
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · refine ⟨max C₀ 0, le_max_right _ _, fun θ hθ hθS => ?_⟩
    rcases hsplit θ hθ hθS with h | ⟨z, hz, -⟩
    · exact le_trans h (le_max_left _ _)
    · simp at hz
  · obtain ⟨z₀, hz₀S, hz₀⟩ := S.exists_max_image C hSne
    refine ⟨max (max C₀ (C z₀)) 0, le_max_right _ _, fun θ hθ hθS => ?_⟩
    rcases hsplit θ hθ hθS with h | ⟨z, hzS, hz⟩
    · exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans (le_trans hz (hz₀ z hzS))
        (le_trans (le_max_right _ _) (le_max_left _ _))

end ForgacsTran
