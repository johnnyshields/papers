/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/NestedSubsets.lean
import SkewRibbonCoarsenings.NestedLabels

/-!
# Subset sums of a layered list on a divisibility grid

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:detector` (`thm:nested`): the
"lowest neutral layer" argument showing that the only proper nonempty subset sums of a layered
labeled list on a grid are those of the distinguished label and of its complement.

`bottom_subsets` treats the three bottom labels (`eq:layers`: `e` divides their total and none of
them), `layer_singleton` the layer labels, and `grid_step` the list `(y_{i-1}, …, y_0, r, s, z)`.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

section Bottom

variable {ι : Type*} [DecidableEq ι]

/-- The nonempty proper subsets of the three bottom labels have sums off the `E`-grid when `E`
divides the total but none of the three labels: for two labels the sum is the negative of the
remaining label modulo `E`. -/
theorem bottom_subsets (m : ι → ℕ) {α β γ : ι} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (E : ℕ) (hr : ¬ E ∣ m α) (hs : ¬ E ∣ m β) (hz : ¬ E ∣ m γ)
    (hR : E ∣ m α + m β + m γ) :
    ∀ X ⊆ ({α, β, γ} : Finset ι), X.Nonempty → X ≠ {α, β, γ} → ¬ E ∣ ∑ i ∈ X, m i := by
  intro X hX hne hXB hE
  have hsum : ∑ i ∈ X, m i =
      (if α ∈ X then m α else 0) + (if β ∈ X then m β else 0) + (if γ ∈ X then m γ else 0) := by
    have : ∑ i ∈ ({α, β, γ} : Finset ι), (if i ∈ X then m i else 0) = ∑ i ∈ X, m i := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hX]
    rw [← this, Finset.sum_insert (by simp [hαβ, hαγ]), Finset.sum_insert (by simp [hβγ]),
      Finset.sum_singleton]
    ring
  have hmem : ∀ i, i ∈ X → i = α ∨ i = β ∨ i = γ := by
    intro i hi
    simpa using hX hi
  by_cases ha : α ∈ X <;> by_cases hb : β ∈ X <;> by_cases hc : γ ∈ X <;>
    simp only [ha, hb, hc, if_true, if_false] at hsum <;> rw [hsum] at hE
  · exact hXB (by
      ext i; simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hi; exact hmem i hi
      · rintro (rfl | rfl | rfl) <;> assumption)
  · exact hz ((Nat.dvd_add_right (by simpa using hE)).mp hR)
  · refine hs ((Nat.dvd_add_right (a := E) (b := m α + m γ) (c := m β) (by simpa using hE)).mp ?_)
    rwa [show m α + m γ + m β = m α + m β + m γ by ring]
  · exact hr (by simpa using hE)
  · refine hr ((Nat.dvd_add_right (a := E) (b := m β + m γ) (c := m α) (by simpa using hE)).mp ?_)
    rwa [show m β + m γ + m α = m α + m β + m γ by ring]
  · exact hs (by simpa using hE)
  · exact hz (by simpa using hE)
  · exact Finset.not_nonempty_empty (by
      have : X = ∅ := by
        ext i
        simp only [Finset.notMem_empty, iff_false]
        intro hi
        rcases hmem i hi with rfl | rfl | rfl <;> contradiction
      rwa [this] at hne)

end Bottom

section Layers

open Nested

variable {L n a r s z : ℕ} {y p : ℕ → ℕ}

/-- The arithmetic hypotheses of `eq:chain`, `eq:detector-list` and `eq:layers` on the integers
`p_0 ∣ ⋯ ∣ p_L`, the layers `y_k`, the bottom labels `r, s, z`, and the weight `n`:
`p_i ∣ p_{i+1}`, `p_L ∣ n` and `p_L ∣ a`, the total is `n`, `y_k ∈ p_k ℤ ∖ p_{k+1} ℤ`, and
`p_0 ∤ r, s, z`. -/
structure LayerData (L : ℕ) (p : ℕ → ℕ) (n a r s z : ℕ) (y : ℕ → ℕ) : Prop where
  chain : ∀ i < L, p i ∣ p (i + 1)
  dvd_a : p L ∣ a
  dvd_n : p L ∣ n
  sum_eq : a + ∑ k ∈ Finset.range L, y k + (r + s + z) = n
  dvd_y : ∀ k < L, p k ∣ y k
  ndvd_y : ∀ k < L, ¬ p (k + 1) ∣ y k
  ndvd_r : ¬ p 0 ∣ r
  ndvd_s : ¬ p 0 ∣ s
  ndvd_z : ¬ p 0 ∣ z

namespace LayerData

variable (h : LayerData L p n a r s z y)
include h

lemma chain_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) : p i ∣ p j := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j hij ih => exact (ih (by omega)).trans (h.chain j (by omega))

lemma dvd_lab {k : ℕ} (hk : k ≤ L) : p k ∣ lab L a y k := by
  rcases Nat.lt_or_ge k L with hlt | hge
  · rw [lab, if_pos hlt]; exact h.dvd_y k hlt
  · have : k = L := le_antisymm hk hge
    subst this
    rw [lab, if_neg (lt_irrefl _)]; exact h.dvd_a

lemma dvd_n_of {k : ℕ} (hk : k ≤ L) : p k ∣ n := (h.chain_le hk le_rfl).trans h.dvd_n

lemma sum_lab : (∑ k ∈ Finset.range (L + 1), lab L a y k) + (r + s + z) = n := by
  rw [Finset.sum_range_succ, lab, if_neg (lt_irrefl _)]
  have : ∑ k ∈ Finset.range L, lab L a y k = ∑ k ∈ Finset.range L, y k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [lab, if_pos (Finset.mem_range.mp hk)]
  rw [this]
  have := h.sum_eq
  omega

/-- A nonempty set of layer positions `y_0, …, y_{j-1}` has sum not divisible by `p_j`: its lowest
layer `y_k` is the only summand not divisible by `p_{k+1}`, and `p_{k+1} ∣ p_j`. -/
lemma layers_ndvd : ∀ j, j ≤ L → ∀ X : Finset (Fin (L + 4)), X ⊆ Yset L j → X.Nonempty →
    ¬ p j ∣ ∑ i ∈ X, detList L a r s z y i := by
  intro j
  induction j with
  | zero =>
    intro _ X hX hne
    rw [Yset_zero] at hX
    exact absurd (Finset.subset_empty.mp hX ▸ hne) Finset.not_nonempty_empty
  | succ j ih =>
    intro hj X hX hne hd
    rw [Yset_succ (by omega)] at hX
    have hdj : p j ∣ ∑ i ∈ X, detList L a r s z y i := (h.chain j (by omega)).trans hd
    by_cases hmem : yIdx L j ∈ X
    · have hsub : X.erase (yIdx L j) ⊆ Yset L j := by
        intro i hi
        rw [Finset.mem_erase] at hi
        have := hX hi.2
        rw [Finset.mem_insert] at this
        exact this.resolve_left hi.1
      have hsum : ∑ i ∈ X, detList L a r s z y i =
          lab L a y j + ∑ i ∈ X.erase (yIdx L j), detList L a r s z y i := by
        rw [← Finset.add_sum_erase X _ hmem, detList_yIdx' (by omega)]
      rw [hsum] at hd hdj
      by_cases he : (X.erase (yIdx L j)).Nonempty
      · have h2 : p j ∣ ∑ i ∈ X.erase (yIdx L j), detList L a r s z y i :=
          (Nat.dvd_add_right (h.dvd_lab (by omega))).mp hdj
        exact ih (by omega) _ hsub he h2
      · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, add_zero] at hd
        rw [lab, if_pos (by omega)] at hd
        exact h.ndvd_y j (by omega) hd
    · have hsub : X ⊆ Yset L j := by
        intro i hi
        have := hX hi
        rw [Finset.mem_insert] at this
        exact this.resolve_left (fun h' => hmem (h' ▸ hi))
      exact ih (by omega) X hsub hne hdj

lemma dvd_T {j : ℕ} (hj : j ≤ L) :
    p j ∣ ∑ i ∈ Jset L j, detList L a r s z y i := by
  have hn : ∑ k ∈ Finset.range (L + 1), lab L a y k + (r + s + z) = n := h.sum_lab
  have hT : ∑ i ∈ Jset L j, detList L a r s z y i =
      (∑ k ∈ Finset.range j, lab L a y k) + (r + s + z) := sum_Jset (by omega)
  have hsplit : ∑ k ∈ Finset.range (L + 1), lab L a y k =
      ∑ k ∈ Finset.range j, lab L a y k + ∑ k ∈ Finset.Ico j (L + 1), lab L a y k :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  have hdvdn : p j ∣ n := h.dvd_n_of hj
  have hdvdI : p j ∣ ∑ k ∈ Finset.Ico j (L + 1), lab L a y k := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact (h.chain_le hk.1 (by omega)).trans (h.dvd_lab (by omega))
  rw [hT]
  have : p j ∣ (∑ k ∈ Finset.range j, lab L a y k + (r + s + z)) +
      ∑ k ∈ Finset.Ico j (L + 1), lab L a y k := by
    rw [← hn, hsplit] at hdvdn
    have e : ∑ k ∈ Finset.range j, lab L a y k + ∑ k ∈ Finset.Ico j (L + 1), lab L a y k +
        (r + s + z) = (∑ k ∈ Finset.range j, lab L a y k + (r + s + z)) +
        ∑ k ∈ Finset.Ico j (L + 1), lab L a y k := by ring
    rwa [e] at hdvdn
  exact (Nat.dvd_add_left hdvdI).mp this

lemma dvd_zero_lab {k : ℕ} (hk : k ≤ L) : p 0 ∣ lab L a y k :=
  (h.chain_le (Nat.zero_le k) hk).trans (h.dvd_lab hk)

lemma dvd_zero_sum_Yset {j : ℕ} (hj : j ≤ L + 1) {Z : Finset (Fin (L + 4))} (hZ : Z ⊆ Yset L j) :
    p 0 ∣ ∑ i ∈ Z, detList L a r s z y i := by
  apply Finset.dvd_sum
  intro i hi
  obtain ⟨k, hk, rfl⟩ := exists_yIdx (hZ hi)
  rw [detList_yIdx' (by omega)]
  exact h.dvd_zero_lab (by omega)

lemma dvd_zero_bottom : p 0 ∣ r + s + z := by
  have h1 : p 0 ∣ n := h.dvd_n_of (Nat.zero_le L)
  have h2 : p 0 ∣ ∑ k ∈ Finset.range (L + 1), lab L a y k := by
    apply Finset.dvd_sum
    intro k hk
    exact h.dvd_zero_lab (by have := Finset.mem_range.mp hk; omega)
  have h3 := h.sum_lab
  rw [← h3] at h1
  exact (Nat.dvd_add_right h2).mp h1

/-- `grid_jset`: a nonempty set of positions of `y_0, …, y_{j-1}, r, s, z` whose sum is divisible
by `p_j` is the whole set.  This is the lowest-layer argument of `thm:nested`, together with
`bottom_subsets` for mixed subsets of the bottom labels. -/
lemma grid_jset {j : ℕ} (hj : j ≤ L) {X : Finset (Fin (L + 4))} (hX : X ⊆ Jset L j)
    (hne : X.Nonempty) (hd : p j ∣ ∑ i ∈ X, detList L a r s z y i) : X = Jset L j := by
  have hJ : Jset L j = Yset L j ∪ Bset L := Jset_eq j
  by_cases hB1 : X ∩ Bset L = ∅
  · exfalso
    have hXY : X ⊆ Yset L j := by
      intro i hi
      have := hX hi
      rw [hJ, Finset.mem_union] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd (Finset.mem_inter.mpr ⟨hi, h'⟩) (by rw [hB1]; simp)
    exact h.layers_ndvd j hj X hXY hne hd
  by_cases hB2 : Bset L ⊆ X
  · -- the complement in `Jset L j` consists of layers
    have hC : Jset L j \ X ⊆ Yset L j := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      have := hi.1
      rw [hJ, Finset.mem_union] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd (hB2 h') hi.2
    have hsum := Finset.sum_sdiff hX (f := detList L a r s z y)
    have hdC : p j ∣ ∑ i ∈ Jset L j \ X, detList L a r s z y i := by
      have hT := h.dvd_T (a := a) (r := r) (s := s) (z := z) (y := y) hj
      rw [← hsum] at hT
      exact (Nat.dvd_add_left hd).mp hT
    by_cases hCe : (Jset L j \ X).Nonempty
    · exact absurd hdC (h.layers_ndvd j hj _ hC hCe)
    · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hCe
      exact Finset.Subset.antisymm hX hCe
  · exfalso
    have hXB : X ∩ Bset L ⊆ ({rIdx L, sIdx L, zIdx L} : Finset (Fin (L + 4))) :=
      fun i hi => (Finset.mem_inter.mp hi).2
    have hXY : X \ Bset L ⊆ Yset L j := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      have := hX hi.1
      rw [hJ, Finset.mem_union] at this
      exact this.resolve_right hi.2
    have hsplit : ∑ i ∈ X ∩ Bset L, detList L a r s z y i +
        ∑ i ∈ X \ Bset L, detList L a r s z y i = ∑ i ∈ X, detList L a r s z y i :=
      Finset.sum_inter_add_sum_sdiff _ _ _
    have hY0 : p 0 ∣ ∑ i ∈ X \ Bset L, detList L a r s z y i :=
      h.dvd_zero_sum_Yset (by omega) hXY
    have hX0 : p 0 ∣ ∑ i ∈ X, detList L a r s z y i := (h.chain_le (Nat.zero_le j) hj).trans hd
    rw [← hsplit] at hX0
    have hB0 : p 0 ∣ ∑ i ∈ X ∩ Bset L, detList L a r s z y i := (Nat.dvd_add_left hY0).mp hX0
    have hne' : (X ∩ Bset L).Nonempty := Finset.nonempty_iff_ne_empty.mpr hB1
    have hne'' : X ∩ Bset L ≠ Bset L := fun h' => hB2 (h' ▸ Finset.inter_subset_left)
    exact bottom_subsets (detList L a r s z y) (rIdx_ne_sIdx (L := L)) (rIdx_ne_zIdx (L := L))
      (sIdx_ne_zIdx (L := L)) (p 0)
      (by rw [detList_rIdx]; exact h.ndvd_r) (by rw [detList_sIdx]; exact h.ndvd_s)
      (by rw [detList_zIdx]; exact h.ndvd_z)
      (by rw [detList_rIdx, detList_sIdx, detList_zIdx]; exact h.dvd_zero_bottom)
      (X ∩ Bset L) hXB hne' hne'' hB0

/-- The whole list: a proper nonempty subset of the `L + 4` positions whose sum is divisible by
`p_L` is `{a}` or its complement.  These are the only proper subset sums on the `d`-grid, since
`p_L ∣ d`. -/
lemma grid_univ {X : Finset (Fin (L + 4))} (hne : X.Nonempty) (hX : X ≠ Finset.univ)
    (hd : p L ∣ ∑ i ∈ X, detList L a r s z y i) :
    X = {idxA L} ∨ X = (Finset.univ : Finset (Fin (L + 4))).erase (idxA L) := by
  by_cases hmem : idxA L ∈ X
  · left
    have hsub : X.erase (idxA L) ⊆ Jset L L := by
      intro i hi
      rw [Finset.mem_erase] at hi
      rw [Jset_top, Finset.mem_erase]
      exact ⟨hi.1, Finset.mem_univ _⟩
    have hsum : ∑ i ∈ X, detList L a r s z y i =
        a + ∑ i ∈ X.erase (idxA L), detList L a r s z y i := by
      rw [← Finset.add_sum_erase X _ hmem, detList_idxA]
    rw [hsum] at hd
    have hd' : p L ∣ ∑ i ∈ X.erase (idxA L), detList L a r s z y i :=
      (Nat.dvd_add_right h.dvd_a).mp hd
    by_cases he : (X.erase (idxA L)).Nonempty
    · exfalso
      have := h.grid_jset le_rfl hsub he hd'
      apply hX
      have h2 : X.erase (idxA L) = Jset L L := this
      rw [← Finset.insert_erase hmem, h2, ← univ_eq_insert]
    · have h0 := Finset.not_nonempty_iff_eq_empty.mp he
      ext i
      rw [Finset.mem_singleton]
      constructor
      · intro hi
        by_contra hne'
        have : i ∈ X.erase (idxA L) := Finset.mem_erase.mpr ⟨hne', hi⟩
        rw [h0] at this
        simp at this
      · rintro rfl; exact hmem
  · right
    have hsub : X ⊆ Jset L L := by
      intro i hi
      rw [Jset_top, Finset.mem_erase]
      exact ⟨fun h' => hmem (h' ▸ hi), Finset.mem_univ _⟩
    rw [← Jset_top]
    exact h.grid_jset le_rfl hsub hne hd

/-- One layer of the list `(y_{i-1}, …, y_0, r, s, z)`: a nonempty subset of its positions whose
sum is divisible by `p_{i-1}` is `{y_{i-1}}`, the complement of `y_{i-1}`, or everything. -/
lemma grid_step {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ L) {X : Finset (Fin (L + 4))}
    (hX : X ⊆ Jset L i) (hne : X.Nonempty)
    (hd : p (i - 1) ∣ ∑ k ∈ X, detList L a r s z y k) :
    X = {yIdx L (i - 1)} ∨ X = Jset L (i - 1) ∨ X = Jset L i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hd ⊢
  rw [Jset_succ (by omega)] at hX ⊢
  by_cases hmem : yIdx L j ∈ X
  · have hsub : X.erase (yIdx L j) ⊆ Jset L j := by
      intro i' hi'
      rw [Finset.mem_erase] at hi'
      have := hX hi'.2
      rw [Finset.mem_insert] at this
      exact this.resolve_left hi'.1
    have hsum : ∑ i' ∈ X, detList L a r s z y i' =
        lab L a y j + ∑ i' ∈ X.erase (yIdx L j), detList L a r s z y i' := by
      rw [← Finset.add_sum_erase X _ hmem, detList_yIdx' (by omega)]
    rw [hsum] at hd
    have hd' : p j ∣ ∑ i' ∈ X.erase (yIdx L j), detList L a r s z y i' :=
      (Nat.dvd_add_right (h.dvd_lab (by omega))).mp hd
    by_cases he : (X.erase (yIdx L j)).Nonempty
    · right; right
      have := h.grid_jset (by omega) hsub he hd'
      rw [← Finset.insert_erase hmem, this]
    · left
      have h0 := Finset.not_nonempty_iff_eq_empty.mp he
      ext i'
      rw [Finset.mem_singleton]
      constructor
      · intro hi'
        by_contra hne'
        have : i' ∈ X.erase (yIdx L j) := Finset.mem_erase.mpr ⟨hne', hi'⟩
        rw [h0] at this
        simp at this
      · rintro rfl; exact hmem
  · right; left
    have hsub : X ⊆ Jset L j := by
      intro i' hi'
      have := hX hi'
      rw [Finset.mem_insert] at this
      exact this.resolve_left (fun h' => hmem (h' ▸ hi'))
    exact h.grid_jset (by omega) hsub hne hd

end LayerData

end Layers


end SkewRibbonCoarsenings
