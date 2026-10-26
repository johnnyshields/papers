/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicPositiveNullPeriod
import SkewCornerDescent.RegularWindowDefectSpecialization

/-!
# Faithful field period from one-active positive null inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`). Any
unequal actual response pair has one common positive regular separating assignment.
The complete detector identity transfers to that assignment, where literal-count
log balance and mean rigidity contradict the separation. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- Positive separating assignments lift scalar one-active rigidity to the
unchanged original response field. No global specialization of that field is used. -/
theorem field_one_active_null_period {α R F : Type*}
    [Fintype α] [DecidableEq α] [CommRing R] [Field F]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (ι : R →+* F) (hι : Function.Injective ι) (response : α → F)
    (hsep : ∀ a b, response a ≠ response b →
      ∃ num den : α → R, ∃ φ : R →+* ℝ,
        (∀ X, response X = ι (num X) / ι (den X)) ∧
        (∀ X, ι (num X) ≠ 0) ∧ (∀ X, φ (num X) ≠ 0) ∧
        (∀ X, 0 < φ (num X) / φ (den X)) ∧
        φ (num a) / φ (den a) ≠ φ (num b) / φ (den b))
    (hr : 0 < r) (hs : 0 < s) (word : ZMod (r * d) → α) (active : α)
    (hsingle : ∀ a, classDefect word 1 d s (r * s - 1) 0 a =
      if a = active then (d : ℤ) else 0)
    (hzero : windowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * d) = 0) :
    Function.Periodic (closureWord (response ∘ word) (response active)
      (k * (r * d) + r * s)) (r * d : ℕ) := by
  intro i
  by_contra hne
  let letter := closureWord word active (k * (r * d) + r * s)
  have hmap (j) : response (letter j) =
      closureWord (response ∘ word) (response active) (k * (r * d) + r * s) j := by
    unfold letter closureWord
    split_ifs <;> rfl
  have hdiff : response (letter (i + (r * d : ℕ))) ≠ response (letter i) := by
    rw [hmap, hmap]
    exact hne
  obtain ⟨num, den, φ, hrep, hnF, hnφ, hpos, hdistinct⟩ :=
    hsep (letter (i + (r * d : ℕ))) (letter i) hdiff
  have hfun : response = fun X => ι (num X) / ι (den X) := funext hrep
  have hz := hzero
  rw [hfun] at hz
  have hreal := windowDefect_zero_specialize ι φ hι num den hnF hnφ word
    (classDefect word 1 d s (r * s - 1) 0) (k * d + s) (r * d) hz
  have hp := one_active_positive_null_period hr hs word
    (fun X => φ (num X) / φ (den X)) hpos active hsingle hreal
  have he := hp i
  have hleft : φ (num (letter (i + (r * d : ℕ)))) / φ (den (letter (i + (r * d : ℕ)))) =
      closureWord ((fun X => φ (num X) / φ (den X)) ∘ word)
        (φ (num active) / φ (den active)) (k * (r * d) + r * s) (i + (r * d : ℕ)) := by
    unfold letter closureWord
    split_ifs <;> rfl
  have hright : φ (num (letter i)) / φ (den (letter i)) =
      closureWord ((fun X => φ (num X) / φ (den X)) ∘ word)
        (φ (num active) / φ (den active)) (k * (r * d) + r * s) i := by
    unfold letter closureWord
    split_ifs <;> rfl
  exact hdistinct (hleft.trans (he.trans hright.symm))

end SkewCornerDescent.CyclicWindows
