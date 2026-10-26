/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonWordComposition
import SkewClassInflation.RibbonReversal

/-!
# Ribbon functions under the ordinary composition product

The forward factor-reversal construction used with
`eq:ribbon-composition` in `shields-2026-skew-class-inflation.tex`.
The actual ribbon recurrence produces the substitution; no ribbon
classification theorem is assumed.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The defining ribbon recurrence, expressed through the actual ordinary endpoint merger. -/
theorem ribbon_cons_near (a : ℕ) (w : List ℕ) (hw : w ≠ []) :
    ribbonWord (a :: w) = complete a * ribbonWord w - ribbonWord (wordNear [a] w) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons b w => rfl

/-- Cutting a literal boundary gives product minus the actual ordinary endpoint merger. -/
theorem ribbon_concat_near (a : ℕ) (u v : List ℕ) (hv : v ≠ []) :
    ribbonWord ((a :: u) ++ v) =
      ribbonWord (a :: u) * ribbonWord v - ribbonWord (wordNear (a :: u) v) := by
  induction u generalizing a with
  | nil =>
    cases v with
    | nil => exact (hv rfl).elim
    | cons b v => rfl
  | cons b u ih =>
    change complete a * ribbonWord ((b :: u) ++ v) -
      ribbonWord (((a + b) :: u) ++ v) = _
    rw [ih b, ih (a + b)]
    have hn := wordNear_ne_nil (b :: u) v (by simp) hv
    rw [wordNear_cons a (b :: u) v (by simp), ribbon_cons_near a _ hn]
    have he := wordNear_assoc [a] (b :: u) v
    change wordNear ((a + b) :: u) v = wordNear [a] (wordNear (b :: u) v) at he
    rw [he]
    change complete a * (ribbonWord (b :: u) * ribbonWord v -
        ribbonWord (wordNear (b :: u) v)) -
      (ribbonWord ((a + b) :: u) * ribbonWord v -
        ribbonWord (wordNear [a] (wordNear (b :: u) v))) =
      (complete a * ribbonWord (b :: u) - ribbonWord ((a + b) :: u)) * ribbonWord v -
        (complete a * ribbonWord (wordNear (b :: u) v) -
          ribbonWord (wordNear [a] (wordNear (b :: u) v)))
    ring

/-- Merging adjacent outer parts merges exactly the corresponding ordinary near powers. -/
theorem wordCompose_near_head (inner : List ℕ) (hi : 0 < inner.sum)
    (a b : ℕ) (hb : 0 < b) (l : List ℕ) :
    wordNear (wordNearPower inner a) (wordCompose inner (b :: l)) =
      wordCompose inner ((a + b) :: l) := by
  have hn := word_ne_nil_of_sum_pos (wordNearPower inner b)
    (by rw [wordNearPower_sum]; exact Nat.mul_pos hb hi)
  rw [wordCompose, wordNear_append_right _ _ _ hn, ← wordNearPower_add]
  rfl

/-- The ribbon boundary identity for any two genuine nonempty row words. -/
theorem ribbon_append_near (u v : List ℕ) (hu : u ≠ []) (hv : v ≠ []) :
    ribbonWord (u ++ v) = ribbonWord u * ribbonWord v - ribbonWord (wordNear u v) := by
  cases u with
  | nil => exact (hu rfl).elim
  | cons a u => exact ribbon_concat_near a u v hv

/-- Substitute the actual ordinary near-power ribbon for each positive complete generator. -/
noncomputable def ribbonProductSubstitution (inner : List ℕ) : CompleteRing →+* CompleteRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j : ℕ+ => ribbonWord (wordNearPower inner j.val))

/-- The zeroth generator is the unit; every positive generator is the stated actual near power. -/
theorem ribbonProductSubstitution_complete (inner : List ℕ) (a : ℕ) :
    ribbonProductSubstitution inner (complete a) = ribbonWord (wordNearPower inner a) := by
  cases a with
  | zero => simp only [Nat.cast_zero, complete_zero, map_one, wordNearPower, ribbonWord]
  | succ a =>
    let j : ℕ+ := ⟨a + 1, by omega⟩
    have he : complete ((a + 1 : ℕ) : ℤ) = MvPolynomial.X j := complete_nat j
    rw [he, ribbonProductSubstitution, MvPolynomial.eval₂Hom_X']
    rfl

private theorem ribbonProductSubstitution_tail (inner : List ℕ) (hi : 0 < inner.sum)
    (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    ribbonProductSubstitution inner (ribbonWord (a :: l)) =
      ribbonWord (wordCompose inner (a :: l)) := by
  induction l generalizing a with
  | nil =>
    change ribbonProductSubstitution inner (complete a) =
      ribbonWord (wordNearPower inner a ++ [])
    rw [List.append_nil, ribbonProductSubstitution_complete]
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    have ht : ∀ c ∈ l, 0 < c := fun c hc => hl c (List.mem_cons_of_mem _ hc)
    change ribbonProductSubstitution inner
      (complete a * ribbonWord (b :: l) - ribbonWord ((a + b) :: l)) =
        ribbonWord (wordNearPower inner a ++ wordCompose inner (b :: l))
    rw [map_sub, map_mul, ribbonProductSubstitution_complete, ih b hb ht,
      ih (a + b) (by omega) ht]
    have hn1 := word_ne_nil_of_sum_pos (wordNearPower inner a)
      (by rw [wordNearPower_sum]; exact Nat.mul_pos ha hi)
    have hn2 := word_ne_nil_of_sum_pos (wordCompose inner (b :: l))
      (by rw [wordCompose_sum, List.sum_cons]; exact Nat.mul_pos (by omega) hi)
    rw [ribbon_append_near _ _ hn1 hn2, wordCompose_near_head inner hi a b hb l]

/-- The complete-generator substitution is the actual literal composition of positive words. -/
theorem ribbonProductSubstitution_word (inner outer : List ℕ) (hi : 0 < inner.sum)
    (ho : ∀ a ∈ outer, 0 < a) :
    ribbonProductSubstitution inner (ribbonWord outer) = ribbonWord (wordCompose inner outer) := by
  cases outer with
  | nil => change ribbonProductSubstitution inner 1 = 1; exact map_one _
  | cons a l =>
    exact ribbonProductSubstitution_tail inner hi a (ho a List.mem_cons_self) l
      (fun b hb => ho b (List.mem_cons_of_mem _ hb))

/-- The canonical ordinary composition product obeys the actual ribbon substitution identity. -/
theorem ribbon_composition_substitution {m n : ℕ} (γ : Composition m)
    (β : Composition n) (hn : 0 < n) :
    ribbonWord (compositionProduct γ β).blocks =
      ribbonProductSubstitution β.blocks (ribbonWord γ.blocks) := by
  rw [compositionProduct_blocks γ β hn, ← wordCompose_eq_flatten]
  exact (ribbonProductSubstitution_word β.blocks γ.blocks
    (by rw [β.blocks_sum]; exact hn) (fun a ha => γ.blocks_pos ha)).symm

/-- Every actual outer ribbon equality survives ordinary composition with a fixed inner. -/
theorem compositionProduct_ribbon_eq_of_outer_eq {m n : ℕ}
    (γ δ : Composition m) (β : Composition n) (hn : 0 < n)
    (he : ribbonWord γ.blocks = ribbonWord δ.blocks) :
    ribbonWord (compositionProduct γ β).blocks = ribbonWord (compositionProduct δ β).blocks := by
  rw [ribbon_composition_substitution γ β hn, ribbon_composition_substitution δ β hn, he]

/-- Reversing an outer factor is a genuine ribbon equality of the composed row words. -/
theorem compositionProduct_outer_reverse {m n : ℕ}
    (γ : Composition m) (β : Composition n) (hm : 0 < m) (hn : 0 < n) :
    ribbonWord (compositionProduct γ.reverse β).blocks =
      ribbonWord (compositionProduct γ β).blocks :=
  compositionProduct_ribbon_eq_of_outer_eq γ.reverse γ β hn (ribbonWord_reverse γ hm)

/-- Equality of every actual ordinary near-power ribbon function. -/
def ribbonPowerEquiv (u v : List ℕ) : Prop :=
  ∀ m : ℕ, ribbonWord (wordNearPower u m) = ribbonWord (wordNearPower v m)

/-- Every word supplies its own near-power equivalence without a positivity restriction. -/
theorem ribbonPowerEquiv_refl (w : List ℕ) : ribbonPowerEquiv w w := fun _ => rfl

/-- Global reversal produces near-power equivalence, not merely equality of the first power. -/
theorem ribbonPowerEquiv_reverse (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    ribbonPowerEquiv w.reverse w := by
  intro m
  rw [← wordNearPower_reverse]
  exact ribbonWord_reverse_word _ (wordNearPower_pos w hw m)

/-- Equal actual near powers give the same complete-generator substitution homomorphism. -/
theorem ribbonProductSubstitution_eq_of_powerEquiv (u v : List ℕ)
    (he : ribbonPowerEquiv u v) :
    ribbonProductSubstitution u = ribbonProductSubstitution v := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [ribbonProductSubstitution]
  · intro j
    simp only [ribbonProductSubstitution, MvPolynomial.eval₂Hom_X']
    exact he j.val

/-- Actual near-power equivalences compose in both factors of the ordinary word product. -/
theorem ribbonPowerEquiv_compose (inner otherInner outer otherOuter : List ℕ)
    (hi : 0 < inner.sum) (hj : 0 < otherInner.sum)
    (ho : ∀ a ∈ outer, 0 < a) (hp : ∀ a ∈ otherOuter, 0 < a)
    (heInner : ribbonPowerEquiv inner otherInner)
    (heOuter : ribbonPowerEquiv outer otherOuter) :
    ribbonPowerEquiv (wordCompose inner outer) (wordCompose otherInner otherOuter) := by
  intro m
  rw [← wordCompose_nearPower inner outer hi ho,
    ← wordCompose_nearPower otherInner otherOuter hj hp]
  rw [← ribbonProductSubstitution_word inner _ hi (wordNearPower_pos outer ho m),
    ← ribbonProductSubstitution_word otherInner _ hj (wordNearPower_pos otherOuter hp m),
    ribbonProductSubstitution_eq_of_powerEquiv inner otherInner heInner, heOuter m]

end SkewClassInflation
