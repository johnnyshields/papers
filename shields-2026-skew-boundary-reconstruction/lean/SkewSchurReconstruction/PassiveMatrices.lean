/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Passive-column capacity

Generic matrix arguments for “The passive tail” (`app:rank4`), specifically
“Starvation and both-passive vanishing” (`lem:starvation`, `cor:both-passive`)
and “Mixed factorization” (`prop:block-factorization`, `eq:block-det`).
The nonzero maximal minor is an explicit mathematical hypothesis; the
skew-Schur producer of that hypothesis is outside this module.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Hall's capacity obstruction for rows supported on a restricted column set. -/
theorem det_eq_zero_of_passive_capacity {m : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (high passive : Finset (Fin m))
    (hzero : ∀ i ∈ high, ∀ j, j ∉ passive → S i j = 0)
    (hcapacity : passive.card < high.card) : S.det = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hp : (∏ j, S (σ j) j) = 0 := by
    by_contra hprod
    have hmap : Set.MapsTo σ.symm high passive := by
      intro i hi
      by_contra hout
      have hz : S (σ (σ.symm i)) (σ.symm i) = 0 := by
        simpa using hzero i hi (σ.symm i) hout
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ (σ.symm i)) hz)
    have hc := Finset.card_le_card_of_injOn σ.symm hmap σ.symm.injective.injOn
    omega
  rw [hp]
  simp

/-- A nonzero determinant supplies the passive capacity bound. -/
theorem passive_capacity_of_det_ne_zero {m : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (high passive : Finset (Fin m))
    (hzero : ∀ i ∈ high, ∀ j, j ∉ passive → S i j = 0)
    (hdet : S.det ≠ 0) : high.card ≤ passive.card := by
  by_contra hc
  exact hdet (det_eq_zero_of_passive_capacity S high passive hzero (by omega))

/-- Capacity for an arbitrary square submatrix retaining every high row and avoiding
all removed columns.  Both selection maps are injective. -/
theorem retained_submatrix_passive_capacity {a b m : ℕ}
    (M : Matrix (Fin a) (Fin b) R) (high : Finset (Fin a))
    (passive removed : Finset (Fin b))
    (rows : Fin m → Fin a) (cols : Fin m → Fin b)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (hcover : ∀ r ∈ high, ∃ i, rows i = r)
    (havoid : ∀ j, cols j ∉ removed)
    (hzero : ∀ r ∈ high, ∀ c, c ∉ passive → M r c = 0)
    (hdet : (M.submatrix rows cols).det ≠ 0) :
    high.card ≤ (passive \ removed).card := by
  classical
  let H : Finset (Fin m) := Finset.univ.filter (fun i => rows i ∈ high)
  let P : Finset (Fin m) := Finset.univ.filter (fun j => cols j ∈ passive)
  have himage : H.image rows = high := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.mem_filter.mp hi).2
    · intro hr
      obtain ⟨i, hi⟩ := hcover r hr
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.symm ▸ hr⟩, hi⟩
  have hH : H.card = high.card := by
    rw [← himage, Finset.card_image_of_injective H hrows]
  have hP : P.card ≤ (passive \ removed).card := by
    apply Finset.card_le_card_of_injOn cols
    · intro j hj
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hj).2, havoid j⟩
    · exact hcols.injOn
  have hc : H.card ≤ P.card := by
    apply passive_capacity_of_det_ne_zero (M.submatrix rows cols) H P _ hdet
    intro i hi j hj
    have hri : rows i ∈ high := (Finset.mem_filter.mp hi).2
    have hcj : cols j ∉ passive := by
      intro hcj
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcj⟩)
    exact hzero (rows i) hri (cols j) hcj
  omega

/-- A square submatrix retaining all high rows vanishes when too few passive columns remain. -/
theorem retained_submatrix_det_eq_zero {a b m : ℕ}
    (M : Matrix (Fin a) (Fin b) R) (high : Finset (Fin a))
    (passive removed : Finset (Fin b))
    (rows : Fin m → Fin a) (cols : Fin m → Fin b)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (hcover : ∀ r ∈ high, ∃ i, rows i = r)
    (havoid : ∀ j, cols j ∉ removed)
    (hzero : ∀ r ∈ high, ∀ c, c ∉ passive → M r c = 0)
    (hcapacity : (passive \ removed).card < high.card) :
    (M.submatrix rows cols).det = 0 := by
  by_contra hdet
  have hc := retained_submatrix_passive_capacity M high passive removed rows cols
    hrows hcols hcover havoid hzero hdet
  omega

/-- The exact one-column-deletion count in `lem:starvation`, including one passive column. -/
theorem high_card_le_passive_sub_one {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) R) (high : Finset (Fin n))
    (passive : Finset (Fin (n + 1))) (j : Fin (n + 1)) (hj : j ∈ passive)
    (hzero : ∀ r ∈ high, ∀ c, c ∉ passive → M r c = 0)
    (hdet : (M.submatrix id j.succAbove).det ≠ 0) :
    high.card ≤ passive.card - 1 := by
  have hc := retained_submatrix_passive_capacity M high passive {j} id j.succAbove
    Function.injective_id Fin.succAbove_right_injective
    (fun r _ => ⟨r, rfl⟩)
    (fun i h => Fin.succAbove_ne j i (Finset.mem_singleton.mp h)) hzero hdet
  simpa only [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hj] using hc

/-- Under saturated capacity, deleting two distinct passive columns kills every square
submatrix retaining all high rows, as in `cor:both-passive`. -/
theorem both_passive_submatrix_det_eq_zero {a b m : ℕ}
    (M : Matrix (Fin a) (Fin b) R) (high : Finset (Fin a))
    (passive : Finset (Fin b)) (i j : Fin b)
    (hi : i ∈ passive) (hj : j ∈ passive) (hij : i ≠ j)
    (hsaturated : high.card = passive.card - 1)
    (rows : Fin m → Fin a) (cols : Fin m → Fin b)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (hcover : ∀ r ∈ high, ∃ k, rows k = r)
    (havoid_i : ∀ k, cols k ≠ i) (havoid_j : ∀ k, cols k ≠ j)
    (hzero : ∀ r ∈ high, ∀ c, c ∉ passive → M r c = 0) :
    (M.submatrix rows cols).det = 0 := by
  classical
  have hjerase : j ∈ passive.erase i := by simp [hj, hij.symm]
  have hc : (passive \ ({i, j} : Finset (Fin b))).card = passive.card - 2 := by
    have he : passive \ ({i, j} : Finset (Fin b)) = (passive.erase i).erase j := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
      tauto
    rw [he, Finset.card_erase_of_mem hjerase, Finset.card_erase_of_mem hi]
    omega
  have hp : 2 ≤ passive.card := by
    have hpos := Finset.card_pos.mpr ⟨j, hjerase⟩
    rw [Finset.card_erase_of_mem hi] at hpos
    omega
  apply retained_submatrix_det_eq_zero M high passive {i, j} rows cols
    hrows hcols hcover
  · intro k
    simp [havoid_i k, havoid_j k]
  · exact hzero
  · rw [hc, hsaturated]
    omega

/-- Ordered active/high and active/passive blocks factor without any permutation sign.
This is the generic sorted-index matrix identity underlying `prop:block-factorization`. -/
theorem det_sorted_passive_blocks {l h : ℕ}
    (S : Matrix (Fin (l + h)) (Fin (l + h)) R)
    (hzero : ∀ i : Fin h, ∀ j : Fin l, S (Fin.natAdd l i) (Fin.castAdd h j) = 0) :
    S.det = (S.submatrix (Fin.castAdd h) (Fin.castAdd h)).det *
      (S.submatrix (Fin.natAdd l) (Fin.natAdd l)).det := by
  classical
  let L := S.submatrix (Fin.castAdd h) (Fin.castAdd h)
  let B := S.submatrix (Fin.castAdd h) (Fin.natAdd l)
  let H := S.submatrix (Fin.natAdd l) (Fin.natAdd l)
  have he : S.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks L B 0 H := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.submatrix, Matrix.fromBlocks, finSumFinEquiv, L, B, H, hzero]
  calc
    S.det = (S.submatrix finSumFinEquiv finSumFinEquiv).det :=
      (Matrix.det_submatrix_equiv_self finSumFinEquiv S).symm
    _ = (Matrix.fromBlocks L B 0 H).det := congrArg Matrix.det he
    _ = L.det * H.det := Matrix.det_fromBlocks_zero₂₁ L B H
    _ = _ := rfl

end SkewSchurReconstruction
