/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Kernel
import Mathlib.Data.Finset.Max

/-!
# Standard tableaux as successive largest entries

The standard-tableau count in «Recovering the factors» (`sec:extraction`,
`eq:character`, `eq:penultimate`, `eq:last`) of
`shields-2026-skew-marked-factor.tex`.
A list records the cells in decreasing label order.  The complete deletion
condition is proved equivalent to a permutation of all cells whose labels
increase in the northwest cell order.  Thus the count is an actual tableau
count, not an assumed terminal derivative coefficient.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan
open scoped BigOperators

/-- An integer row-column coordinate of a diagram cell. -/
abbrev Cell := ℤ × ℤ

/-- The cells that may receive the largest label of a standard tableau. -/
def removableCells (D : Diagram) : Finset Cell :=
  D.filter fun x => ∀ y ∈ D, x.1 ≤ y.1 → x.2 ≤ y.2 → y = x

@[simp]
theorem mem_removableCells {D : Diagram} {x : Cell} :
    x ∈ removableCells D ↔ x ∈ D ∧
      ∀ y ∈ D, x.1 ≤ y.1 → x.2 ≤ y.2 → y = x := by
  simp only [removableCells, Finset.mem_filter]

/-- A finite nonempty cell set always has a possible largest tableau entry. -/
theorem removableCells_nonempty {D : Diagram} (hD : D.Nonempty) :
    (removableCells D).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := D.exists_max_image (fun x : Cell => x.1 + x.2) hD
  refine ⟨x, mem_removableCells.mpr ⟨hx, ?_⟩⟩
  intro y hy hrow hcol
  have hs := hmax y hy
  apply Prod.ext <;> omega

/-- Complete removal in decreasing label order. -/
def IsTableauDeletion : Diagram → List Cell → Prop
  | D, [] => D = ∅
  | D, x :: xs => x ∈ removableCells D ∧ IsTableauDeletion (D.erase x) xs

/-- Decreasing labels encode exactly a standard tableau on the northwest cell poset. -/
theorem isTableauDeletion_iff (D : Diagram) (l : List Cell) :
    IsTableauDeletion D l ↔ l.Nodup ∧ l.toFinset = D ∧
      l.Pairwise (fun x y => ¬ (x.1 ≤ y.1 ∧ x.2 ≤ y.2)) := by
  classical
  induction l generalizing D with
  | nil => simp [IsTableauDeletion, eq_comm]
  | cons x xs ih =>
    rw [IsTableauDeletion, ih, mem_removableCells, List.nodup_cons, List.pairwise_cons,
      List.toFinset_cons]
    constructor
    · rintro ⟨⟨hx, hmax⟩, hnd, hset, hpair⟩
      have hnot : x ∉ xs := by
        intro hm
        have he : x ∈ D.erase x := hset ▸ List.mem_toFinset.mpr hm
        exact (Finset.mem_erase.mp he).1 rfl
      refine ⟨⟨hnot, hnd⟩, ?_, ?_, hpair⟩
      · rw [hset, Finset.insert_erase hx]
      · intro y hy hxy
        have hm : y ∈ D.erase x := hset ▸ List.mem_toFinset.mpr hy
        have he := hmax y (Finset.mem_of_mem_erase hm) hxy.1 hxy.2
        exact (Finset.mem_erase.mp hm).1 he
    · rintro ⟨⟨hnot, hnd⟩, hset, hrel, hpair⟩
      have hx : x ∈ D := by rw [← hset]; simp
      have he : xs.toFinset = D.erase x := by
        rw [← hset, Finset.erase_insert (by simpa using hnot)]
      refine ⟨⟨hx, ?_⟩, hnd, he, hpair⟩
      intro y hy hrow hcol
      rw [← hset, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rfl
      · exact False.elim (hrel y (List.mem_toFinset.mp hy) ⟨hrow, hcol⟩)

/-- A complete tableau uses every cell once. -/
theorem tableauDeletion_length {D : Diagram} {l : List Cell}
    (h : IsTableauDeletion D l) : l.length = D.card := by
  obtain ⟨hnd, hset, _⟩ := (isTableauDeletion_iff D l).mp h
  rw [← hset, List.toFinset_card_of_nodup hnd]

/-- Finite enumeration of complete tableaux of prescribed length. -/
def deletionTableaux : ℕ → Diagram → Finset (List Cell)
  | 0, D => if D = ∅ then {[]} else ∅
  | n + 1, D => (removableCells D).biUnion fun x =>
      (deletionTableaux n (D.erase x)).image (List.cons x)

/-- The finite enumeration has exactly the claimed tableau condition. -/
theorem mem_deletionTableaux (n : ℕ) (D : Diagram) (l : List Cell) :
    l ∈ deletionTableaux n D ↔ l.length = n ∧ IsTableauDeletion D l := by
  classical
  induction n generalizing D l with
  | zero =>
    cases l <;> by_cases he : D = ∅ <;> simp [deletionTableaux, IsTableauDeletion, he]
  | succ n ih =>
    cases l with
    | nil => simp [deletionTableaux, IsTableauDeletion]
    | cons x xs =>
      simp only [deletionTableaux, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨y, hy, ys, hys, he⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨hlen, hseq⟩ := (ih _ _).mp hys
        exact ⟨by simp [hlen], hy, hseq⟩
      · rintro ⟨hlen, hx, hseq⟩
        refine ⟨x, hx, xs, (ih _ _).mpr ⟨?_, hseq⟩, rfl⟩
        simpa using hlen

/-- Standard tableaux, encoded by their decreasing-label lists. -/
def standardTableaux (D : Diagram) : Finset (List Cell) := deletionTableaux D.card D

/-- The actual finite standard-tableau count. -/
def standardTableauCount (D : Diagram) : ℕ := (standardTableaux D).card

/-- No additional length condition is hidden in the finite standard-tableau object. -/
theorem mem_standardTableaux (D : Diagram) (l : List Cell) :
    l ∈ standardTableaux D ↔ IsTableauDeletion D l := by
  rw [standardTableaux, mem_deletionTableaux]
  exact ⟨And.right, fun h => ⟨tableauDeletion_length h, h⟩⟩

@[simp]
theorem standardTableaux_empty : standardTableaux ∅ = {[]} := by
  simp [standardTableaux, deletionTableaux]

@[simp]
theorem standardTableauCount_empty : standardTableauCount ∅ = 1 := by
  simp [standardTableauCount]

/-- The topological-labeling interpretation is inhabited, including the empty tableau. -/
theorem standardTableaux_nonempty (D : Diagram) : (standardTableaux D).Nonempty := by
  classical
  induction hcard : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases he : D = ∅
    · subst D; simp
    · obtain ⟨x, hx⟩ := removableCells_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
      have hxD := (mem_removableCells.mp hx).1
      have hlt : (D.erase x).card < n := by
        rw [Finset.card_erase_of_mem hxD]
        have hn : 0 < D.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega
      obtain ⟨l, hl⟩ := ih (D.erase x).card hlt (D.erase x) rfl
      refine ⟨x :: l, (mem_standardTableaux _ _).mpr ?_⟩
      exact ⟨hx, (mem_standardTableaux _ _).mp hl⟩

/-- Positivity is a proved combinatorial witness, not a character hypothesis. -/
theorem standardTableauCount_pos (D : Diagram) : 0 < standardTableauCount D :=
  Finset.card_pos.mpr (standardTableaux_nonempty D)

/-- Deleting a removable largest entry produces a skew diagram. -/
theorem isSkew_erase_removable {D : Diagram} (hD : IsSkew D) {x : Cell}
    (hx : x ∈ removableCells D) : IsSkew (D.erase x) := by
  have hu : IsUpsetIn D {x} := by
    obtain ⟨hxD, hmax⟩ := mem_removableCells.mp hx
    refine ⟨by simpa using hxD, ?_⟩
    intro y hy z hz hrow hcol
    have he : z = x := Finset.mem_singleton.mp hz
    subst z
    exact Finset.mem_singleton.mpr (hmax y hy hrow hcol)
  simpa only [Finset.sdiff_singleton_eq_erase] using
    KernelAux.isSkew_sdiff_of_isUpsetIn hD hu

/-- A one-cell southeast ribbon is precisely a removable largest tableau entry. -/
theorem singleton_mem_rightRibbons {D : Diagram} {x : Cell} :
    ({x} : Diagram) ∈ rightRibbons D 1 ↔ x ∈ removableCells D := by
  rw [mem_rightRibbons, mem_removableCells]
  have hR : IsRibbon ({x} : Diagram) :=
    ⟨isConnectedSkew_singleton x, by simp [span, contents]⟩
  simp only [Finset.card_singleton, hR, true_and, IsUpsetIn,
    Finset.singleton_subset_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, _, h⟩
    exact ⟨hx, fun y hy hrow hcol => h y hy x rfl hrow hcol⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, hx, by intro y hy z hz; subst z; exact h y hy⟩

/-- The sign of each one-cell ribbon is positive. -/
theorem ribbonSign_singleton (x : Cell) : ribbonSign ({x} : Diagram) = 1 := by
  simp [ribbonSign, ribbonHeight, numRows, rowSet]

/-- Single-cell ribbon deletion is an exact unsigned sum over removable cells. -/
theorem rightOp_one_shape (D : Diagram) :
    rightOp 1 (shape D) = ∑ x ∈ removableCells D, shape (D.erase x) := by
  rw [KernelAux.rightOp_shape]
  apply Finset.sum_bij (fun Y _ => Classical.choose (Finset.card_eq_one.mp
    (mem_rightRibbons.mp ‹Y ∈ rightRibbons D 1›).2.1))
  · intro Y hY
    have he := Classical.choose_spec (Finset.card_eq_one.mp (mem_rightRibbons.mp hY).2.1)
    exact singleton_mem_rightRibbons.mp (he ▸ hY)
  · intro Y hY Z hZ he
    have hYeq := Classical.choose_spec (Finset.card_eq_one.mp (mem_rightRibbons.mp hY).2.1)
    have hZeq := Classical.choose_spec (Finset.card_eq_one.mp (mem_rightRibbons.mp hZ).2.1)
    rw [hYeq, hZeq, he]
  · intro x hx
    refine ⟨{x}, singleton_mem_rightRibbons.mpr hx, ?_⟩
    have h := Classical.choose_spec (Finset.card_eq_one.mp
      (mem_rightRibbons.mp (singleton_mem_rightRibbons.mpr hx)).2.1)
    exact Finset.singleton_injective (h.symm)
  · intro Y hY
    have he := Classical.choose_spec (Finset.card_eq_one.mp (mem_rightRibbons.mp hY).2.1)
    have hs : ribbonSign Y = 1 := by
      exact (congrArg ribbonSign he).trans (ribbonSign_singleton _)
    have hd : D \ Y = D.erase (Classical.choose
        (Finset.card_eq_one.mp (mem_rightRibbons.mp hY).2.1)) :=
      (congrArg (fun Z : Diagram => D \ Z) he).trans
        (Finset.sdiff_singleton_eq_erase _ _)
    rw [hs, Int.cast_one, one_smul]
    exact congrArg shape hd

end SkewMarkedFactor
