/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Permutations that split `Fin N` into a monotone block and its complement

A `BlockMono` is a permutation of `Fin N` that is strictly monotone on the initial block
`Fin k` and strictly monotone on the complement, with the initial block landing on a
prescribed `k`-element selection.

## Main results

* `Shields.BlockMono`: the structure.
* `Shields.BlockMono.exists_blockMono`: every strictly monotone `f : Fin k → Fin N` extends to one.
* `Shields.BlockMono.sign`: its sign is `(-1) ^ (∑ i, f i + k.choose 2)`.

## Implementation notes

**`import Mathlib` is retained deliberately, and the specific list beneath it is exact.** This
file builds against those modules alone.  What the blanket import still carries is the transitive
Mathlib that *consumers* of this file rely on: dropping it here leaves the shared tree green and
breaks a paper that imports it.  Removing it therefore belongs to a pass that sweeps every
consuming tree's imports in the same change, and a Mathlib PR would carry the specific list only.

This is the index bookkeeping behind any statement that compares a minor on a selection with the
determinant of the whole matrix -- the two signs contributed by the row and the column selection
each take this form, so the binomial terms cancel and what survives is a checkerboard.

## Tags

permutation, sign, minor, block matrix
-/

open Finset

namespace Shields

variable {N : ℕ}

/-- A permutation of `Fin N` that is strictly increasing on `{0,…,k-1}` and,
separately, on `{k,…,N-1}`.  Equivalently: the assembly of a `k`-element
increasing selection with the increasing enumeration of its complement. -/
structure BlockMono (k : ℕ) {N : ℕ} (ρ : Equiv.Perm (Fin N)) : Prop where
  /-- Strictly increasing below `k`. -/
  lower : ∀ i j : Fin N, i < j → (j : ℕ) < k → ρ i < ρ j
  /-- Strictly increasing from `k` on. -/
  upper : ∀ i j : Fin N, i < j → k ≤ (i : ℕ) → ρ i < ρ j

namespace BlockMono

variable {k : ℕ} {ρ : Equiv.Perm (Fin N)}

/-- The number of positions sent strictly below `ρ i` is `ρ i`: a permutation is a
bijection, so the count is the size of `Iio (ρ i)`. -/
theorem card_filter_lt (ρ : Equiv.Perm (Fin N)) (i : Fin N) :
    (univ.filter fun j : Fin N => ρ j < ρ i).card = (ρ i : ℕ) := by
  have hmap : (univ.filter fun j : Fin N => ρ j < ρ i)
      = (Finset.Iio (ρ i)).map ρ.symm.toEmbedding := by
    ext j
    simp only [mem_filter, mem_univ, true_and, Finset.mem_map, Finset.mem_Iio,
      Equiv.coe_toEmbedding, Equiv.symm_apply_eq]
    exact ⟨fun h => ⟨ρ j, h, rfl⟩, fun ⟨v, hv, hvj⟩ => hvj ▸ hv⟩
  rw [hmap, Finset.card_map, Fin.card_Iio]

/-- Below `k`, the permutation is order-reflecting: `ρ j < ρ i` and `j < k` force
`j < i`. -/
theorem lt_of_apply_lt (h : BlockMono k ρ) {i j : Fin N} (hi : (i : ℕ) < k)
    (hj : (j : ℕ) < k) (hlt : ρ j < ρ i) : j < i := by
  rcases lt_trichotomy j i with hji | rfl | hij
  · exact hji
  · exact absurd hlt (lt_irrefl _)
  · exact absurd (h.lower i j hij hj) (not_lt.mpr hlt.le)

/-- Of the `ρ i` positions sent below `ρ i`, exactly `i` lie below `k`. -/
theorem card_filter_lower (h : BlockMono k ρ) {i : Fin N} (hi : (i : ℕ) < k) :
    (univ.filter fun j : Fin N => (j : ℕ) < k ∧ ρ j < ρ i).card = (i : ℕ) := by
  have hset : (univ.filter fun j : Fin N => (j : ℕ) < k ∧ ρ j < ρ i)
      = univ.filter fun j : Fin N => j < i := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hjk, hlt⟩
      exact h.lt_of_apply_lt hi hjk hlt
    · intro hji
      exact ⟨by omega, h.lower j i hji hi⟩
  rw [hset]
  have : (univ.filter fun j : Fin N => j < i) = Finset.Iio i := by
    ext j; simp
  rw [this, Fin.card_Iio]

/-- The remaining `ρ i - i` positions sent below `ρ i` lie at or above `k`. -/
theorem card_filter_upper (h : BlockMono k ρ) {i : Fin N} (hi : (i : ℕ) < k) :
    (univ.filter fun j : Fin N => k ≤ (j : ℕ) ∧ ρ j < ρ i).card
      = (ρ i : ℕ) - (i : ℕ) := by
  have hsplit : (univ.filter fun j : Fin N => (j : ℕ) < k ∧ ρ j < ρ i).card
      + (univ.filter fun j : Fin N => k ≤ (j : ℕ) ∧ ρ j < ρ i).card
      = (univ.filter fun j : Fin N => ρ j < ρ i).card := by
    rw [← Finset.card_union_of_disjoint, ← Finset.filter_or]
    · congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨_, h2⟩ | ⟨_, h2⟩) <;> exact h2
      · intro h2
        rcases lt_or_ge (j : ℕ) k with hjk | hjk
        · exact Or.inl ⟨hjk, h2⟩
        · exact Or.inr ⟨hjk, h2⟩
    · rw [Finset.disjoint_left]
      intro j hj1 hj2
      rw [Finset.mem_filter] at hj1 hj2
      omega
  rw [card_filter_lt ρ i, h.card_filter_lower hi] at hsplit
  omega

/-- A selected position is never moved down: `i ≤ ρ i` for `i < k`. -/
theorem le_apply (h : BlockMono k ρ) {i : Fin N} (hi : (i : ℕ) < k) :
    (i : ℕ) ≤ (ρ i : ℕ) := by
  have h1 : (univ.filter fun j : Fin N => (j : ℕ) < k ∧ ρ j < ρ i)
      ⊆ univ.filter fun j : Fin N => ρ j < ρ i := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.2⟩
  have := Finset.card_le_card h1
  rw [h.card_filter_lower hi, card_filter_lt ρ i] at this
  exact this

/-! ### The sign

`Equiv.Perm.sign_eq_prod_prod_Ioi` writes the sign as a product over ordered
pairs.  Both blocks are increasing, so a pair inside one block never contributes;
the surviving pairs are those with `i < k ≤ j`, and for fixed `i` there are
`ρ i - i` of them. -/

/-- The inner product over `j > i` for a *selected* `i`: only the unselected `j`
matter, and they contribute `(-1)^{ρ i - i}`. -/
private theorem prod_Ioi_lower (h : BlockMono k ρ) {i : Fin N} (hi : (i : ℕ) < k) :
    (∏ j ∈ Finset.Ioi i, if ρ i < ρ j then (1 : ℤˣ) else -1)
      = (-1) ^ ((ρ i : ℕ) - (i : ℕ)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ioi i) (fun j : Fin N => (j : ℕ) < k)]
  have hone : (∏ j ∈ (Finset.Ioi i).filter (fun j : Fin N => (j : ℕ) < k),
      if ρ i < ρ j then (1 : ℤˣ) else -1) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    rw [Finset.mem_filter, Finset.mem_Ioi] at hj
    rw [if_pos (h.lower i j hj.1 hj.2)]
  rw [hone, one_mul]
  have hfil : (Finset.Ioi i).filter (fun j : Fin N => ¬ (j : ℕ) < k)
      = univ.filter (fun j : Fin N => k ≤ (j : ℕ)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ioi, mem_univ, true_and, not_lt]
    exact ⟨fun hj => hj.2, fun hj => ⟨by omega, hj⟩⟩
  rw [hfil, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [← h.card_filter_upper hi]
  congr 1
  ext j
  simp only [Finset.mem_filter, mem_univ, true_and, not_lt]
  constructor
  · rintro ⟨hjk, hnot⟩
    refine ⟨hjk, lt_of_le_of_ne hnot ?_⟩
    intro hc
    exact absurd (ρ.injective hc) (by intro h'; omega)
  · rintro ⟨hjk, hlt⟩
    exact ⟨hjk, hlt.le⟩

/-- **The sign of a block-monotone permutation.**  Inversions occur only between a
selected and an unselected position, and position `i < k` accounts for `ρ i - i`
of them. -/
theorem sign (h : BlockMono k ρ) :
    Equiv.Perm.sign ρ
      = (-1) ^ (∑ i ∈ univ.filter fun i : Fin N => (i : ℕ) < k, ((ρ i : ℕ) + (i : ℕ))) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi,
    ← Finset.prod_filter_mul_prod_filter_not univ (fun i : Fin N => (i : ℕ) < k)]
  have hupper : (∏ i ∈ univ.filter (fun i : Fin N => ¬ (i : ℕ) < k),
      ∏ j ∈ Finset.Ioi i, if ρ i < ρ j then (1 : ℤˣ) else -1) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    rw [Finset.mem_filter, not_lt] at hi
    refine Finset.prod_eq_one fun j hj => ?_
    rw [Finset.mem_Ioi] at hj
    rw [if_pos (h.upper i j hj hi.2)]
  rw [hupper, mul_one, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_filter] at hi
  rw [h.prod_Ioi_lower hi.2]
  have hle := h.le_apply hi.2
  have : (ρ i : ℕ) + (i : ℕ) = ((ρ i : ℕ) - (i : ℕ)) + 2 * (i : ℕ) := by omega
  rw [this, pow_add, pow_mul]
  simp

end BlockMono

/-! ### Every increasing selection extends to a block-monotone permutation -/

/-- The permutation assembled from a `k`-element subset `s` and the increasing enumeration of its
complement: the first `k` positions are sent to `s` in order, the remaining `N - k` to `sᶜ` in
order.  This is Mathlib's `finSumEquivOfFinset` transported along `Fin N ≃ Fin k ⊕ Fin (N-k)`. -/
private def blockPerm {k : ℕ} {s : Finset (Fin N)} (hm : #s = k) (hn : #sᶜ = N - k)
    (hNk : N = k + (N - k)) : Equiv.Perm (Fin N) :=
  ((finCongr hNk).trans finSumFinEquiv.symm).trans (finSumEquivOfFinset hm hn)

/-- On the low block, `blockPerm` is the increasing enumeration of `s`. -/
private theorem blockPerm_apply_lt {k : ℕ} {s : Finset (Fin N)} (hm : #s = k) (hn : #sᶜ = N - k)
    (hNk : N = k + (N - k)) {i : Fin N} (hi : (i : ℕ) < k) :
    blockPerm hm hn hNk i = s.orderEmbOfFin hm ⟨i, hi⟩ := by
  simp only [blockPerm, Equiv.trans_apply, finCongr_apply]
  rw [show (Fin.cast hNk i) = Fin.castAdd _ ⟨i, hi⟩ from rfl,
    finSumFinEquiv_symm_apply_castAdd, finSumEquivOfFinset_inl]

/-- On the high block, `blockPerm` is the increasing enumeration of `sᶜ`. -/
private theorem blockPerm_apply_ge {k : ℕ} {s : Finset (Fin N)} (hm : #s = k) (hn : #sᶜ = N - k)
    (hNk : N = k + (N - k)) {i : Fin N} (hi : k ≤ (i : ℕ)) :
    blockPerm hm hn hNk i = sᶜ.orderEmbOfFin hn ⟨(i : ℕ) - k, by have := i.isLt; omega⟩ := by
  simp only [blockPerm, Equiv.trans_apply, finCongr_apply]
  rw [show (Fin.cast hNk i) = Fin.natAdd _ ⟨(i : ℕ) - k, by have := i.isLt; omega⟩ from
      Fin.ext (by simp; omega),
    finSumFinEquiv_symm_apply_natAdd, finSumEquivOfFinset_inr]

/-- **The complement of an increasing selection.**  For strictly monotone
`f : Fin k → Fin N` there is a permutation of `Fin N` that agrees with `f` on
`{0,…,k-1}` and enumerates the complement of the range of `f` increasingly
above.

Agreement with `f` on the low block is `orderEmbOfFin_unique` -- a strictly monotone map is the
increasing enumeration of its own image. -/
theorem exists_blockMono {k : ℕ} (hk : k ≤ N) {f : Fin k → Fin N} (hf : StrictMono f) :
    ∃ ρ : Equiv.Perm (Fin N), BlockMono k ρ ∧
      ∀ a : Fin k, ρ ⟨a, lt_of_lt_of_le a.isLt hk⟩ = f a := by
  have hm : #(univ.image f) = k := by
    rw [Finset.card_image_of_injective _ hf.injective]; simp
  have hn : #(univ.image f)ᶜ = N - k := by
    rw [Finset.card_compl, hm]; simp
  have hNk : N = k + (N - k) := by omega
  refine ⟨blockPerm hm hn hNk, ⟨fun i j hij hjk => ?_, fun i j hij hik => ?_⟩, fun a => ?_⟩
  · have hik : (i : ℕ) < k := lt_trans (by exact_mod_cast hij) hjk
    rw [blockPerm_apply_lt hm hn hNk hik, blockPerm_apply_lt hm hn hNk hjk]
    exact ((univ.image f).orderEmbOfFin hm).strictMono (by simpa using hij)
  · have hjk : k ≤ (j : ℕ) := le_trans hik (le_of_lt (by exact_mod_cast hij))
    rw [blockPerm_apply_ge hm hn hNk hik, blockPerm_apply_ge hm hn hNk hjk]
    refine ((univ.image f)ᶜ.orderEmbOfFin hn).strictMono ?_
    have : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
    simp only [Fin.mk_lt_mk]
    omega
  · rw [blockPerm_apply_lt hm hn hNk (show ((⟨a, lt_of_lt_of_le a.isLt hk⟩ : Fin N) : ℕ) < k from
      a.isLt)]
    simpa using (congrFun (Finset.orderEmbOfFin_unique hm
      (fun i => Finset.mem_image_of_mem f (mem_univ i)) hf) a).symm


/-! ### Axiom footprint -/

/-- info: 'Shields.BlockMono.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockMono.sign

/-- info: 'Shields.exists_blockMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_blockMono

end Shields
