/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorInnerInventory
import SkewClassInflation.RibbonFactorReversal

/-!
# Factor-reversal completeness under actual composition

The induction assembly for the ribbon factor-reversal classification cited after
`thm:sharp-inflation` in `shields-2026-skew-class-inflation.tex`.
Reconstructible leaves and complete factors supply complete products.
A failure of the full classification would therefore have an actual
nonreconstructible source with no proper ordinary factorization.
Sorry-free.
-/

namespace SkewClassInflation

/-- Every actual same-inventory mate is reached by finite factor reversals. -/
def ribbonFactorComplete {N : ℕ} (α : Composition N) : Prop :=
  ∀ β : Composition N, coarseningInventory β = coarseningInventory α →
    RibbonFactorReversal α β

/-- A reconstructible source is complete, including the empty-weight boundary. -/
theorem ribbonFactorComplete_of_reconstructible {N : ℕ} (α : Composition N)
    (hr : ribbonReconstructible α) : ribbonFactorComplete α := by
  intro β he
  rcases hr β he with he | he
  · rw [he]
    exact RibbonFactorReversal.refl α
  · rw [he]
    exact RibbonFactorReversal.reverse α

/-- Exact actual words transport completeness independently of the presentation of total weight. -/
theorem ribbonFactorComplete_congr {M N : ℕ} (α : Composition M) (β : Composition N)
    (he : α.blocks = β.blocks) : ribbonFactorComplete α ↔ ribbonFactorComplete β := by
  have hh : (⟨M, α⟩ : (K : ℕ) × Composition K) = ⟨N, β⟩ :=
    Composition.sigma_eq_iff_blocks_eq.mpr he
  cases hh
  rfl

/-- Complete actual factors give a complete ordinary product, with no mate-factor premises. -/
theorem ribbonFactorComplete_compose {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (hM : 2 ≤ M) (hN : 0 < N) (hδ : ribbonFactorComplete δ)
    (hε : ribbonFactorComplete ε) : ribbonFactorComplete (compositionProduct δ ε) := by
  intro θ hInv
  obtain ⟨hfactor, houter, hinner⟩ := inventory_mate_factor_transport δ ε hM hN θ hInv
  rw [← hfactor]
  exact RibbonFactorReversal.compose δ (periodicOuter θ) ε (periodicInner θ)
    (by omega) hN (hδ _ houter) (hε _ hinner)

/-- A failure of full generation has an actual nonreconstructible source with no proper factors. -/
theorem exists_minimal_factor_counterexample
    (hbad : ∃ N : ℕ, ∃ α : Composition N, ¬ ribbonFactorComplete α) :
    ∃ N : ℕ, ∃ α : Composition N, ¬ ribbonFactorComplete α ∧ ¬ ribbonReconstructible α ∧
      ∀ M K : ℕ, ∀ δ : Composition M, ∀ ε : Composition K,
        2 ≤ M → 2 ≤ K → α.blocks ≠ (compositionProduct δ ε).blocks := by
  classical
  let N := Nat.find hbad
  obtain ⟨α, hα⟩ := Nat.find_spec hbad
  refine ⟨N, α, hα, ?_, ?_⟩
  · exact fun hr => hα (ribbonFactorComplete_of_reconstructible α hr)
  · intro M K δ ε hM hK he
    have hweight := congrArg List.sum he
    rw [α.blocks_sum, (compositionProduct δ ε).blocks_sum] at hweight
    have hMlt : M < N := by nlinarith
    have hKlt : K < N := by nlinarith
    have hδ : ribbonFactorComplete δ := by
      by_contra hh
      exact Nat.find_min hbad hMlt ⟨δ, hh⟩
    have hε : ribbonFactorComplete ε := by
      by_contra hh
      exact Nat.find_min hbad hKlt ⟨ε, hh⟩
    exact hα ((ribbonFactorComplete_congr α (compositionProduct δ ε) he).mpr
      (ribbonFactorComplete_compose δ ε hM (by omega) hδ hε))

end SkewClassInflation
