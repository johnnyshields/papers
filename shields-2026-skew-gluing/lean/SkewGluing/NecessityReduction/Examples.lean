import SkewGluing.NecessityReduction.Reduction

/-!
# Checked examples for the reduction of composition necessity

Formalizes `shields-2026-skew-gluing.tex`, «Source-minimal fibers» (`eq:chart-score`,
`eq:component-key`, the row example after `cor:least-root-period`) and «Reduction of composition
necessity» (`thm:necessity-reduction`).

Non-vacuity witnesses for the definitions of this development, checked on the paper's worked
examples: the chart score agrees with `(N_F mod p, p + N_F mod p)`; the ordinary gauge identifies
the keys of the two charts of `(4, 4, 2)/(2)`; presentations, correspondence and legality on the
row `(7) = (3) ∘ (3)` and on the pair of hooks, whose one-factor presentation is the reason the
rotation quotient identifies them.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

/-! ### The chart score -/

/-- The chart figure `F = D ∘_ω E`, with `D` a domino: width two, inner span five, which is
`(N_F mod p, p + N_F mod p)` for `N_F = 8`, `p = 3`. -/
example : (⟨domino, chartFigureInner⟩ : Chart).score = score 8 3 := by decide +kernel

/-- The two presentations `(7) = (3) ∘ (3) = (2) ∘ (4)` have scores `(1, 3)` and `(1, 4)`, those
of `score 7 2` and `score 7 3`: the least proper period two is source-minimal, the period three
is not. -/
example : (⟨skewOf [3] [], rowInnerThree⟩ : Chart).score = score 7 2 := by decide +kernel

example : (⟨skewOf [2] [], rowInnerFour⟩ : Chart).score = score 7 3 := by decide +kernel

example : (⟨skewOf [3] [], rowInnerThree⟩ : Chart).score <
    (⟨skewOf [2] [], rowInnerFour⟩ : Chart).score := by decide +kernel

/-! ### The ordinary gauge in the key -/

theorem skewOf_two_antitranspose :
    skewOf [1, 1] [] = translate (1, 0) (antitranspose (skewOf [2] [])) := by
  decide +kernel

/-- The gauge example `(2) ∘_{ω_a} E = (1, 1) ∘_{ω_b} E`, `E = (4, 4, 2)/(2)`: the keys of the two
charts agree, because the key identifies `(ω_a, h₂)` with `(ω_b, ι(h₂)) = (ω_b, e₂)`. -/
theorem gauge_example_key_eq :
    (⟨skewOf [2] [], gaugeInnerA⟩ : Chart).key = (⟨skewOf [1, 1] [], gaugeInnerB⟩ : Chart).key := by
  have h : cellSchur (skewOf [1, 1] []) = schurInvolution (cellSchur (skewOf [2] [])) := by
    rw [skewOf_two_antitranspose, cellSchur_translate, cellSchur_antitranspose]
  have step : KeyStep (gaugeInnerA, cellSchur (skewOf [2] []))
      (gaugeInnerB, schurInvolution (cellSchur (skewOf [2] []))) :=
    KeyStep.gauge _ rfl rfl rfl (by decide) (by decide +kernel) (by decide +kernel)
  change Quot.mk KeyStep (gaugeInnerA, cellSchur (skewOf [2] [])) =
    Quot.mk KeyStep (gaugeInnerB, cellSchur (skewOf [1, 1] []))
  rw [h]
  exact Quot.sound step

/-! ### Presentations -/

/-- `(7) = (3) ∘ (3)` as a two-factor presentation, with its legal marked inner. -/
theorem row_presentation :
    (Presentation.step (.first (skewOf [3] [])) rowInnerThree).value = skewOf [7] [] ∧
      (Presentation.step (.first (skewOf [3] [])) rowInnerThree).IsLegal := by
  refine ⟨by decide +kernel, ?_⟩
  exact ⟨(by decide : IsConnectedSkew (skewOf [3] [])), by decide⟩

/-- The two hooks are rotation mates, so they form a one-factor reversal presentation
(`sec:minimal-fibers`: the pair is not a counterexample to composition-and-reversal
necessity). -/
theorem hook_pair_corresponds :
    (Presentation.first (skewOf [2, 1] [])).Corresponds (.first (skewOf [2, 2] [1])) :=
  Or.inr ⟨(1, 1), hookRotated_eq_rotate_hook⟩

/-- The two hooks as the first factors of two presentations with the same marked inner:
corresponding legal presentations of the diagrams `(3) ∘ H` and `(3) ∘ H*`-type composites. -/
theorem hook_pair_extended_corresponds :
    (Presentation.step (.first (skewOf [2, 1] [])) rowInnerThree).Corresponds
      (.step (.first (skewOf [2, 2] [1])) rowInnerThree) ∧
    (Presentation.step (.first (skewOf [2, 1] [])) rowInnerThree).IsLegal :=
  ⟨⟨hook_pair_corresponds, Or.inl (MarkedInner.EquivTranslate.refl _)⟩,
    ⟨isConnectedSkew_hook, by decide⟩⟩

end SkewGluing
