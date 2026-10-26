/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MarkFacts/Translate.lean
import SkewMarkedFactor.Gluing.Invariance
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Defs

/-!
# The modified composition under translation of the outer diagram

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`): translating the outer diagram `D` by `t` translates the
composite `D ∘_ω E` (`MarkedInner.compose_translate_outer`), so everything that is translation
invariant (the Schur function, the number of cells, rows, columns and diagonals, the northbound
count) is unchanged.  This gives the translation invariance of `componentT` and
`northbound`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan.MarkFacts

theorem card_translate (t : ℤ × ℤ) (D : Diagram) : (translate t D).card = D.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

theorem numRows_translate (t : ℤ × ℤ) (D : Diagram) : numRows (translate t D) = numRows D := by
  unfold numRows rowSet translate
  rw [Finset.image_image]
  have : (Prod.fst ∘ fun x : ℤ × ℤ => x + t) = (· + t.1) ∘ Prod.fst := by
    funext x; simp only [Function.comp, Prod.fst_add]
  rw [this, ← Finset.image_image,
    Finset.card_image_of_injective _ (add_left_injective t.1)]

theorem numCols_translate (t : ℤ × ℤ) (D : Diagram) : numCols (translate t D) = numCols D := by
  unfold numCols
  have : transpose (translate t D) = translate t.swap (transpose D) := by
    ext y
    simp only [transpose, translate, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x.swap, ⟨x, hx, rfl⟩, by simp [add_comm]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x + t, ⟨x, hx, rfl⟩, by simp⟩
  rw [this, numRows_translate]

end Plan.MarkFacts

open Plan.MarkFacts

namespace MarkedInner

theorem northbound_translate (ω : MarkedInner) (t : ℤ × ℤ) (C : Diagram) :
    Plan.northbound ω (SkewMarkedFactor.Gluing.translate t C) = Plan.northbound ω C := by
  unfold Plan.northbound
  symm
  refine Finset.card_bij (fun d _ => d + t) ?_ (fun a _ b _ h => add_right_cancel h) ?_
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨SkewMarkedFactor.Gluing.mem_translate.mpr (by simpa using hd.1),
      (sameRibbon_translate_outer hd.1 t ω).mpr hd.2⟩
  · intro d' hd'
    rw [Finset.mem_filter] at hd'
    have hd : d' - t ∈ C := SkewMarkedFactor.Gluing.mem_translate.mp hd'.1
    refine ⟨d' - t, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨hd, ?_⟩
    rw [← sameRibbon_translate_outer hd t ω]
    simpa using hd'.2

theorem componentT_translate (ω : MarkedInner) {C : Diagram} (hC : C.Nonempty) (t : ℤ × ℤ) :
    Plan.componentT ω (SkewMarkedFactor.Gluing.translate t C) = Plan.componentT ω C := by
  unfold Plan.componentT
  rw [card_translate, numRows_translate, numCols_translate, span_translate,
    compose_translate_outer t hC ω, cellSchur_translate]

/-! ### Checks -/

/-- The northbound count of a case-(d) mark, on a translated outer. -/
example : Plan.northbound hookInner (SkewMarkedFactor.Gluing.translate (2, 1) (skewOf [3,
    2] [])) =
    Plan.northbound hookInner (skewOf [3, 2] []) := by decide +kernel

/-- The number of northbound cells is positive on the outer `(2, 2)`: the check is not vacuous. -/
example : 0 < Plan.northbound hookInner (skewOf [2, 2] []) := by decide +kernel

end MarkedInner

end SkewMarkedFactor.Gluing
