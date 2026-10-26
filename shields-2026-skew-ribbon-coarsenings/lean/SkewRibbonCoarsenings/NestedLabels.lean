/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The labeled list of the nested marked identity

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector` (`eq:detector-list`,
`eq:layers`).

The labeled list `𝐚 = (a, y_{L-1}, …, y_0, r, s, z)` is the function `detList` on the `L + 4`
positions `Fin (L + 4)`: position `0` carries `a`, position `L - k` carries `y_k` for `k < L`, and
positions `L + 1, L + 2, L + 3` carry `r, s, z`.  `Jset L j` is the set of positions of the labels
`y_0, …, y_{j-1}, r, s, z` (the list `𝐌` of `thm:nested` after `j` layers have been peeled).
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

namespace Nested

/-- `eq:detector-list`: the labeled list `(a, y_{L-1}, …, y_0, r, s, z)` as a function on
`Fin (L + 4)`. -/
def detList (L a r s z : ℕ) (y : ℕ → ℕ) (i : Fin (L + 4)) : ℕ :=
  if i.val = 0 then a else if i.val ≤ L then y (L - i.val) else
    if i.val = L + 1 then r else if i.val = L + 2 then s else z

/-- The position of `a`. -/
def idxA (L : ℕ) : Fin (L + 4) := ⟨0, by omega⟩

/-- The position of `y_k`. -/
def yIdx (L k : ℕ) : Fin (L + 4) := ⟨L - k, by omega⟩

/-- The position of `r`. -/
def rIdx (L : ℕ) : Fin (L + 4) := ⟨L + 1, by omega⟩

/-- The position of `s`. -/
def sIdx (L : ℕ) : Fin (L + 4) := ⟨L + 2, by omega⟩

/-- The position of `z`. -/
def zIdx (L : ℕ) : Fin (L + 4) := ⟨L + 3, by omega⟩

/-- The positions of `y_0, …, y_{j-1}, r, s, z`. -/
def Jset (L j : ℕ) : Finset (Fin (L + 4)) :=
  Finset.univ.filter fun i => L + 1 ≤ i.val + j

variable {L : ℕ} {a r s z : ℕ} {y : ℕ → ℕ}

lemma mem_Jset {j : ℕ} {i : Fin (L + 4)} : i ∈ Jset L j ↔ L + 1 ≤ i.val + j := by
  simp [Jset]

lemma detList_idxA : detList L a r s z y (idxA L) = a := by
  simp [detList, idxA]

lemma detList_yIdx {k : ℕ} (hk : k < L) : detList L a r s z y (yIdx L k) = y k := by
  have h1 : (yIdx L k).val ≠ 0 := by simp [yIdx]; omega
  have h2 : (yIdx L k).val ≤ L := by simp [yIdx]
  simp only [detList, h1, h2, if_false, if_true]
  congr 1
  simp only [yIdx]
  omega

lemma detList_rIdx : detList L a r s z y (rIdx L) = r := by
  simp [detList, rIdx]

lemma detList_sIdx : detList L a r s z y (sIdx L) = s := by
  simp [detList, sIdx]

lemma detList_zIdx : detList L a r s z y (zIdx L) = z := by
  simp [detList, zIdx]

lemma yIdx_ne_idxA {k : ℕ} (hk : k < L) : yIdx L k ≠ idxA L := by
  simp [yIdx, idxA, Fin.ext_iff]; omega

lemma Jset_zero : Jset L 0 = {rIdx L, sIdx L, zIdx L} := by
  ext i
  simp only [mem_Jset, Finset.mem_insert, Finset.mem_singleton, rIdx, sIdx, zIdx, Fin.ext_iff]
  omega

lemma Jset_succ {j : ℕ} (hj : j ≤ L) : Jset L (j + 1) = insert (yIdx L j) (Jset L j) := by
  ext i
  simp only [mem_Jset, Finset.mem_insert, yIdx, Fin.ext_iff]
  omega

lemma yIdx_notMem_Jset {j : ℕ} (hj : j ≤ L) : yIdx L j ∉ Jset L j := by
  simp only [mem_Jset, yIdx]
  omega

lemma Jset_top : Jset L L = (Finset.univ : Finset (Fin (L + 4))).erase (idxA L) := by
  ext i
  simp only [mem_Jset, Finset.mem_erase, Finset.mem_univ, and_true, idxA, ne_eq, Fin.ext_iff]
  omega

lemma univ_eq_insert : (Finset.univ : Finset (Fin (L + 4))) = insert (idxA L) (Jset L L) := by
  rw [Jset_top, Finset.insert_erase (Finset.mem_univ _)]

lemma idxA_notMem_Jset {j : ℕ} (hj : j ≤ L) : idxA L ∉ Jset L j := by
  simp only [mem_Jset, idxA]
  omega

lemma Jset_mono {j k : ℕ} (h : j ≤ k) : Jset L j ⊆ Jset L k := by
  intro i hi
  rw [mem_Jset] at hi ⊢
  omega

/-- The layer values: `lab k = y_k` for `k < L` and `lab L = a`. -/
def lab (L a : ℕ) (y : ℕ → ℕ) (k : ℕ) : ℕ := if k < L then y k else a

lemma detList_yIdx' {k : ℕ} (hk : k ≤ L) :
    detList L a r s z y (yIdx L k) = lab L a y k := by
  rcases Nat.lt_or_ge k L with h | h
  · rw [detList_yIdx h, lab, if_pos h]
  · have hk' : k = L := le_antisymm hk h
    subst hk'
    have : yIdx k k = idxA k := by simp [yIdx, idxA]
    rw [this, detList_idxA, lab, if_neg (lt_irrefl _)]

lemma Jset_top_univ : Jset L (L + 1) = Finset.univ := by
  ext i
  simp only [mem_Jset, Finset.mem_univ, iff_true]
  omega

lemma yIdx_top : yIdx L L = idxA L := by simp [yIdx, idxA]

lemma sum_Jset_zero : ∑ i ∈ Jset L 0, detList L a r s z y i = r + s + z := by
  have h1 : rIdx L ∉ ({sIdx L, zIdx L} : Finset (Fin (L + 4))) := by
    simp [rIdx, sIdx, zIdx, Fin.ext_iff]
  have h2 : sIdx L ∉ ({zIdx L} : Finset (Fin (L + 4))) := by
    simp [sIdx, zIdx, Fin.ext_iff]
  rw [Jset_zero, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton,
    detList_rIdx, detList_sIdx, detList_zIdx]
  ring

lemma sum_Jset {j : ℕ} (hj : j ≤ L + 1) :
    ∑ i ∈ Jset L j, detList L a r s z y i = (∑ k ∈ Finset.range j, lab L a y k) + (r + s + z) := by
  induction j with
  | zero => simpa using sum_Jset_zero (L := L) (a := a) (r := r) (s := s) (z := z) (y := y)
  | succ j ih =>
    rw [Jset_succ (by omega), Finset.sum_insert (yIdx_notMem_Jset (by omega)),
      detList_yIdx' (by omega), ih (by omega), Finset.sum_range_succ]
    ring

lemma sum_univ :
    ∑ i, detList L a r s z y i = (∑ k ∈ Finset.range (L + 1), lab L a y k) + (r + s + z) := by
  rw [← Jset_top_univ, sum_Jset le_rfl]

/-- The positions of the bottom labels `r, s, z`. -/
def Bset (L : ℕ) : Finset (Fin (L + 4)) := {rIdx L, sIdx L, zIdx L}

/-- The positions of the layer labels `y_0, …, y_{j-1}`. -/
def Yset (L j : ℕ) : Finset (Fin (L + 4)) :=
  Finset.univ.filter fun i => L + 1 ≤ i.val + j ∧ i.val ≤ L

lemma mem_Bset {i : Fin (L + 4)} : i ∈ Bset L ↔ L < i.val := by
  simp only [Bset, Finset.mem_insert, Finset.mem_singleton, rIdx, sIdx, zIdx, Fin.ext_iff]
  have := i.isLt
  omega

lemma mem_Yset {j : ℕ} {i : Fin (L + 4)} : i ∈ Yset L j ↔ L + 1 ≤ i.val + j ∧ i.val ≤ L := by
  simp [Yset]

lemma Jset_eq (j : ℕ) : Jset L j = Yset L j ∪ Bset L := by
  ext i
  simp only [mem_Jset, Finset.mem_union, mem_Yset, mem_Bset]
  omega

lemma disjoint_Yset_Bset (j : ℕ) : Disjoint (Yset L j) (Bset L) := by
  rw [Finset.disjoint_left]
  intro i hi hb
  rw [mem_Yset] at hi
  rw [mem_Bset] at hb
  omega

lemma Yset_zero : Yset L 0 = ∅ := by
  ext i
  simp only [mem_Yset, Finset.notMem_empty, iff_false]
  omega

lemma Yset_succ {j : ℕ} (hj : j ≤ L) : Yset L (j + 1) = insert (yIdx L j) (Yset L j) := by
  ext i
  simp only [mem_Yset, Finset.mem_insert, yIdx, Fin.ext_iff]
  omega

lemma yIdx_notMem_Yset {j : ℕ} (hj : j ≤ L) : yIdx L j ∉ Yset L j := by
  simp only [mem_Yset, yIdx]
  omega

lemma Yset_subset_Jset (j : ℕ) : Yset L j ⊆ Jset L j := by
  rw [Jset_eq]; exact Finset.subset_union_left

lemma exists_yIdx {j : ℕ} {i : Fin (L + 4)} (hi : i ∈ Yset L j) :
    ∃ k, k < j ∧ i = yIdx L k := by
  rw [mem_Yset] at hi
  refine ⟨L - i.val, by omega, ?_⟩
  simp only [yIdx, Fin.ext_iff]
  omega

lemma yIdx_injective {k k' : ℕ} (hk : k ≤ L) (hk' : k' ≤ L) (h : yIdx L k = yIdx L k') :
    k = k' := by
  simp only [yIdx, Fin.ext_iff] at h
  omega

lemma yIdx_mem_Jset {j k : ℕ} (hk : k ≤ L) (hkj : k < j) : yIdx L k ∈ Jset L j := by
  simp only [mem_Jset, yIdx]
  omega

lemma Jset_erase {j : ℕ} (hj : j ≤ L) : (Jset L (j + 1)).erase (yIdx L j) = Jset L j := by
  rw [Jset_succ hj, Finset.erase_insert (fun h => yIdx_notMem_Jset hj h)]

lemma Jset_top_erase : (Finset.univ : Finset (Fin (L + 4))).erase (idxA L) = Jset L L := by
  rw [← Jset_top]

lemma Bset_subset_Jset (j : ℕ) : Bset L ⊆ Jset L j := by
  rw [Jset_eq]; exact Finset.subset_union_right

lemma Bset_nonempty : (Bset L).Nonempty := ⟨rIdx L, by simp [Bset]⟩

lemma rIdx_ne_sIdx : rIdx L ≠ sIdx L := by simp [rIdx, sIdx, Fin.ext_iff]
lemma rIdx_ne_zIdx : rIdx L ≠ zIdx L := by simp [rIdx, zIdx, Fin.ext_iff]
lemma sIdx_ne_zIdx : sIdx L ≠ zIdx L := by simp [sIdx, zIdx, Fin.ext_iff]

lemma yIdx_notMem_Bset {k : ℕ} (_hk : k ≤ L) : yIdx L k ∉ Bset L := by
  rw [mem_Bset]; simp [yIdx]

lemma idxA_notMem_Bset : idxA L ∉ Bset L := by
  rw [mem_Bset]; simp [idxA]

end Nested

end SkewRibbonCoarsenings
