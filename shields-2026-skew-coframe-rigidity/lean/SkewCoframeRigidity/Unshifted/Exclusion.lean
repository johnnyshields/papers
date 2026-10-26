/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Connected
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected

/-!
# Assembly of the unshifted exclusion

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`sec:unshifted`, `ph:unshifted-exclusion`).  An actual nonself board satisfying the unshifted
identity has both extreme ports, and its proper corner is either a single positive strict
component, handled in `Exclusion.Connected`, or has two or more strict components, handled in
`Exclusion.Disconnected`; a corner that is a single unit is excluded by the span bound.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial

variable {n : ℕ}

/-- The cases of the proper corner exhaust: two or more strict components, a single positive
strict component, or a single unit, and the last is excluded by `3 ≤ M`. -/
theorem exclusion_false {V W : BetaDiagram (n + 1)} {p : ℕ} (H : ExclusionHyp V W p) :
    False := by
  classical
  by_cases hdisc : ∃ i j : Fin n, blockIdx V i ≠ blockIdx V j
  · exact exclusion_disconnected'' H hdisc
  push Not at hdisc
  have hcut : ∀ c, ¬ IsCut V c := fun c hc => by
    obtain ⟨j, hj, hlt⟩ := hc
    have hjc : j < c := by rw [Fin.lt_def]; omega
    exact absurd (hdisc j c) (ne_of_lt (blockIdx_lt_of_cut V hjc le_rfl ⟨j, hj, hlt⟩))
  by_cases hunit : ∃ i, IsUnit' V i
  · obtain ⟨i, hi⟩ := hunit
    obtain ⟨⟨i0, hi0⟩, ⟨j0, hj0⟩⟩ := exclusion_ports H
    have h1 : i0 = i := blockIdx_eq_imp_of_unit hi (hdisc i0 i)
    have h2 : j0 = i := blockIdx_eq_imp_of_unit hi (hdisc j0 i)
    rw [h1] at hi0
    rw [h2] at hj0
    have e1 := rowPos_cast V i
    have e2 := colPos_cast V i
    unfold IsUnit' at hi
    have := H.span3
    omega
  · push Not at hunit
    exact exclusion_connected H ⟨hcut, hunit⟩

/-- `ph:unshifted-exclusion`: for a connected normalized board of span `M ≥ 3`, its rotation `W`
and an exponent `p ≥ 2`, the unshifted identity `𝒯_{G,C}(H^p) = p [H^{p-1} D]_{<2M}` at
precision `2M` forces `V = W`. -/
theorem unshifted_exclusion {V W : BetaDiagram (n + 1)} (hV : V.Connected)
    (hVn : V.col (Fin.last n) = 0) (hWn : W.col (Fin.last n) = 0) (hrot : V.RotationEquivalent W)
    (hM : 3 ≤ span V) (p : ℕ) (hp : 2 ≤ p)
    (h : ∀ k < 2 * span V,
      (clippedOp (span V) (coframe V) (coframe W) (letterSeries ^ p)).coeff k =
        (p : CohField) * PowerSeries.coeff k (letterSeries ^ (p - 1) *
          (defect V W : PowerSeries CohField))) : V = W := by
  by_contra hne
  exact exclusion_false ⟨hV, hVn, hWn, hrot, hM, hp, h, hne⟩

end SkewCoframeRigidity.Unshifted
