/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryCoreRecovery
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Proper suffix sets and composition recovery

Formalizes `eq:suffix-set` and the composition-recovery step following
`eq:suffix-support-recovery` in `shields-2026-skew-class-inflation.tex`.
Mathlib's composition-boundary equivalence records the partial sums of the
reversed block list, hence the suffix sums of the original composition.
Sorry-free.
-/

namespace SkewClassInflation

/-- Proper suffix sums are the positive nonterminal prefix boundaries of the reversed block list. -/
def suffixSet {M : ℕ} (α : Composition M) : Finset ℕ :=
  ((α.reverse.boundaries.erase 0).erase (Fin.last M)).image Fin.val

/-- Membership is literal proper-boundary membership in the reversed composition. -/
theorem suffixSet_mem_iff {M : ℕ} (α : Composition M) (i : Fin (M + 1))
    (hi0 : i ≠ 0) (hiM : i ≠ Fin.last M) :
    i.val ∈ suffixSet α ↔ i ∈ α.reverse.boundaries := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
    have hji : j = i := Fin.ext he
    subst j
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)
  · intro h
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_erase.mpr ⟨hiM, Finset.mem_erase.mpr ⟨hi0, h⟩⟩, rfl⟩

/-- Suffix sums are strictly between zero and the total size, including the singleton case. -/
theorem suffixSet_subset {M : ℕ} (α : Composition M) : suffixSet α ⊆ Finset.Ioo 0 M := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  have hiM := (Finset.mem_erase.mp hi).1
  have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
  have hM : i.val ≠ M := fun h => hiM (Fin.ext h)
  have hlt := i.isLt
  exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩

/-- Proper suffix sums recover the complete ordered composition, not merely its part multiset. -/
theorem suffixSet_injective {M : ℕ} : Function.Injective (@suffixSet M) := by
  intro α β he
  have hb : α.reverse.boundaries = β.reverse.boundaries := by
    ext i
    by_cases hi0 : i = 0
    · subst i
      exact iff_of_true α.reverse.toCompositionAsSet.zero_mem β.reverse.toCompositionAsSet.zero_mem
    · by_cases hiM : i = Fin.last M
      · subst i
        exact iff_of_true α.reverse.toCompositionAsSet.getLast_mem
          β.reverse.toCompositionAsSet.getLast_mem
      · rw [← suffixSet_mem_iff α i hi0 hiM, ← suffixSet_mem_iff β i hi0 hiM, he]
  exact Composition.reverse_injective
    ((compositionEquiv M).injective (CompositionAsSet.ext hb))

/-- A nonempty composition has exactly one fewer proper suffix sum than blocks. -/
theorem suffixSet_card {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (suffixSet α).card + 1 = α.length := by
  have hlast : (Fin.last M : Fin (M + 1)) ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at hh
    omega
  have hmem0 : (0 : Fin (M + 1)) ∈ α.reverse.boundaries := by
    exact α.reverse.toCompositionAsSet.zero_mem
  have hmemM : Fin.last M ∈ α.reverse.boundaries := by
    exact α.reverse.toCompositionAsSet.getLast_mem
  have hlen : 0 < α.length := Composition.length_pos_of_pos α hM
  rw [suffixSet, Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hlast, hmemM⟩),
    Finset.card_erase_of_mem hmem0, Composition.card_boundaries_eq_succ_length]
  have hr : α.reverse.length = α.length := by simp [Composition.length, Composition.reverse]
  omega

/-- The concrete boundary core assigned to a positive composition. -/
def compositionCore (B : BoundaryParameters) {M : ℕ} (hM : 0 < M) (α : Composition M) :
    SkewJacobiNegative.BetaDiagram (M + 1) := B.core M hM (suffixSet α)

/-- Equality of actual boundary-core Schur functions recovers the outer composition exactly. -/
theorem compositionCore_schur_injective (B : BoundaryParameters) {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun α : Composition M => (compositionCore B hM α).schur) := by
  intro α β he
  apply suffixSet_injective
  exact B.core_suffix_set_injective M hM _ _ (suffixSet_subset α) (suffixSet_subset β) he

end SkewClassInflation
