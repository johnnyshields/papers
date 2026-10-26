/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Seam.lean
import SkewRibbonCoarsenings.Defs

/-!
# The seam identity

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:algebra` (`eq:seam`).

For the concatenation `α · β` and the near-concatenation `α ⊙ β` of compositions of weights
`n, n' > 0`, `G_{α·β} = G_α G_β + G_{α⊙β}`: a coarsening of `α · β` either retains the joining
seam, in which case it is a coarsening of `α` followed by a coarsening of `β`, or erases it.
The module also proves that `G` is invariant under reversal of the composition.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

lemma sup_insert_shift (n : ℕ) (U : Finset ℕ) :
    (insert n (U.image (n + ·))).sup id = n + U.sup id := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.insert_comm, Finset.sup_insert, ih, Finset.sup_insert]
    simp only [id]
    omega

lemma sup_glue (n : ℕ) (T1 U : Finset ℕ) (h1 : ∀ x ∈ T1, x < n) :
    (insert n (T1 ∪ U.image (n + ·))).sup id = n + U.sup id := by
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
    rcases hy with rfl | h | ⟨u, hu, rfl⟩
    · simp
    · have := h1 y h
      simp only [id]; omega
    · have : u ≤ U.sup id := Finset.le_sup (f := id) hu
      simp only [id]; omega
  · rw [← sup_insert_shift]
    apply Finset.sup_mono
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_union] at hy ⊢
    tauto

lemma gaps_glue (n n' : ℕ) (T1 T2 : Finset ℕ) (h1 : ∀ x ∈ T1, x < n)
    (hn' : 0 < n') (h2 : ∀ x ∈ T2, 0 < x ∧ x < n') :
    gaps (n + n') (T1 ∪ T2.image (n + ·) ∪ {n}) = gaps n T1 + gaps n' T2 := by
  set X := T1 ∪ T2.image (n + ·) ∪ {n} with hX
  have hset : insert (n + n') X = insert n T1 ∪ (insert n' T2).image (n + ·) := by
    ext x
    simp only [hX, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
      Finset.image_insert]
    constructor
    · rintro (h | (h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inl h)
    · rintro ((h | h) | h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inr h))
  have hdisj : Disjoint (insert n T1) ((insert n' T2).image (n + ·)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_image] at hx hx'
    obtain ⟨u, hu, rfl⟩ := hx'
    have hu0 : 0 < u := by
      rcases hu with rfl | hu
      · exact hn'
      · exact (h2 u hu).1
    rcases hx with h | h
    · omega
    · have := h1 _ h; omega
  unfold gaps
  rw [hset, ← Finset.disjUnion_eq_union _ _ hdisj]
  change Multiset.map _ (_ + _) = _
  rw [Multiset.map_add]
  congr 1
  · apply Multiset.map_congr rfl
    intro x hx
    simp only [Finset.mem_val, Finset.mem_insert] at hx
    have hx' : x ≤ n := by
      rcases hx with rfl | hx
      · exact le_rfl
      · exact (h1 _ hx).le
    congr 2
    ext y
    simp only [hX, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨(h | ⟨u, hu, rfl⟩) | rfl, hy⟩
      · exact ⟨h, hy⟩
      · exfalso
        have := (h2 u hu).1
        omega
      · omega
    · rintro ⟨h, hy⟩; exact ⟨Or.inl (Or.inl h), hy⟩
  · rw [Finset.image_val_of_injOn (fun a _ b _ h => by simpa using h), Multiset.map_map]
    apply Multiset.map_congr rfl
    intro u hu
    simp only [Finset.mem_val, Finset.mem_insert] at hu
    have hu0 : 0 < u := by
      rcases hu with rfl | hu
      · exact hn'
      · exact (h2 u hu).1
    have hfil : (X.filter (· < n + u)) = insert n (T1 ∪ ((T2.filter (· < u)).image (n + ·))) := by
      ext y
      simp only [hX, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro ⟨(h | ⟨v, hv, rfl⟩) | rfl, hy⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨v, ⟨hv, by omega⟩, rfl⟩)
        · exact Or.inl rfl
      · rintro (rfl | h | ⟨v, ⟨hv, hvu⟩, rfl⟩)
        · exact ⟨Or.inr rfl, by omega⟩
        · have := h1 _ h
          exact ⟨Or.inl (Or.inl h), by omega⟩
        · exact ⟨Or.inl (Or.inr ⟨v, hv, rfl⟩), by omega⟩
    simp only [Function.comp, hfil]
    rw [sup_glue n T1 _ h1]
    omega

lemma sum_powerset_near {M : Type*} [AddCommMonoid M] (n : ℕ) (S S' : Finset ℕ)
    (hS : ∀ x ∈ S, x < n) (f : Finset ℕ → M) :
    ∑ T ∈ (S ∪ S'.image (n + ·)).powerset, f T
      = ∑ p ∈ S.powerset ×ˢ S'.powerset, f (p.1 ∪ p.2.image (n + ·)) := by
  symm
  refine Finset.sum_nbij' (fun p => p.1 ∪ p.2.image (n + ·))
    (fun T => (T.filter (· < n), (T.filter (n ≤ ·)).image (· - n))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T1, T2⟩ h
    simp only [mem_product, mem_powerset] at h
    simp only [mem_powerset]
    exact union_subset_union h.1 (image_subset_image h.2)
  · intro T hT
    simp only [mem_powerset] at hT
    simp only [mem_product, mem_powerset]
    constructor
    · exact fun x hx => by
        have := mem_filter.mp hx
        have := hT this.1
        simp only [mem_union, mem_image] at this
        rcases this with h | ⟨u, _, hu⟩
        · exact h
        · have := (mem_filter.mp hx).2; omega
    · intro y hy
      simp only [mem_image, mem_filter] at hy
      obtain ⟨x, ⟨hx, hnx⟩, rfl⟩ := hy
      have := hT hx
      simp only [mem_union, mem_image] at this
      rcases this with h | ⟨u, hu, rfl⟩
      · have := hS x h; omega
      · simpa using hu
  · rintro ⟨T1, T2⟩ h
    simp only [mem_product, mem_powerset] at h
    ext1
    · simp only
      ext x
      simp only [mem_filter, mem_union, mem_image]
      constructor
      · rintro ⟨h1 | ⟨u, hu, rfl⟩, hx⟩
        · exact h1
        · omega
      · intro hx
        exact ⟨Or.inl hx, hS x (h.1 hx)⟩
    · simp only
      ext y
      simp only [mem_image, mem_filter, mem_union]
      constructor
      · rintro ⟨x, ⟨h1 | ⟨u, hu, rfl⟩, hnx⟩, rfl⟩
        · have := hS x (h.1 h1); omega
        · simpa using hu
      · intro hy
        exact ⟨n + y, ⟨Or.inr ⟨y, hy, rfl⟩, by omega⟩, by omega⟩
  · intro T hT
    simp only [mem_powerset] at hT
    simp only
    ext x
    simp only [mem_union, mem_filter, mem_image]
    constructor
    · rintro (⟨hx, _⟩ | ⟨y, ⟨a, ⟨ha, hna⟩, rfl⟩, rfl⟩)
      · exact hx
      · rwa [Nat.add_sub_cancel' hna]
    · intro hx
      by_cases hxn : x < n
      · exact Or.inl ⟨hx, hxn⟩
      · exact Or.inr ⟨x - n, ⟨x, ⟨hx, by omega⟩, rfl⟩, by omega⟩
  · rintro ⟨T1, T2⟩ h
    rfl


/-- `eq:seam`: `G_{α·β} = G_α G_β + G_{α⊙β}` for compositions of positive weights `n, n'` with
cut sets `S, S'`. -/
theorem G_concat_cuts (n n' : ℕ) (S S' : Finset ℕ) (_hn : 0 < n) (hn' : 0 < n')
    (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    G (n + n') (concatCuts n S S') = G n S * G n' S' + G (n + n') (nearCuts n S S') := by
  have hS1 : ∀ x ∈ S, x < n := fun x hx => (Finset.mem_Ioo.mp (hS hx)).2
  have hS2 : ∀ x ∈ S', 0 < x ∧ x < n' := fun x hx => Finset.mem_Ioo.mp (hS' hx)
  have hnot : n ∉ nearCuts n S S' := by
    simp only [nearCuts, Finset.mem_union, Finset.mem_image, not_or]
    refine ⟨fun h => lt_irrefl _ (hS1 n h), ?_⟩
    rintro ⟨x, hx, h⟩
    have := (hS2 x hx).1
    omega
  have hcc : concatCuts n S S' = insert n (nearCuts n S S') := by
    simp only [concatCuts, nearCuts]
    rw [Finset.union_right_comm, Finset.union_comm _ {n}]
    rfl
  unfold G
  rw [hcc, Finset.sum_powerset_insert hnot, add_comm]
  congr 1
  · rw [Finset.sum_mul_sum, ← Finset.sum_product']
    rw [nearCuts, sum_powerset_near n S S' hS1]
    refine Finset.sum_congr rfl ?_
    rintro ⟨T1, T2⟩ h
    simp only [mem_product, mem_powerset] at h
    have h1 : ∀ x ∈ T1, x < n := fun x hx => hS1 x (h.1 hx)
    have h2 : ∀ x ∈ T2, 0 < x ∧ x < n' := fun x hx => hS2 x (h.2 hx)
    rw [show insert n (T1 ∪ T2.image (n + ·)) = T1 ∪ T2.image (n + ·) ∪ {n} from by
      rw [Finset.union_comm _ {n}]; rfl, gaps_glue n n' T1 T2 h1 hn' h2, Multiset.map_add,
      Multiset.prod_add]

lemma gaps_empty (n : ℕ) : gaps n ∅ = {n} := by simp [gaps]

lemma revCuts_mem {n : ℕ} {S : Finset ℕ} {x : ℕ} :
    x ∈ revCuts n S ↔ ∃ y ∈ S, n - y = x := by
  simp [revCuts]

lemma revCuts_isCutSet {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) : IsCutSet n (revCuts n S) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := revCuts_mem.mp hx
  have := Finset.mem_Ioo.mp (hS hy)
  exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩

lemma revCuts_revCuts {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) : revCuts n (revCuts n S) = S := by
  ext x
  rw [revCuts_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := revCuts_mem.mp hy
    have := Finset.mem_Ioo.mp (hS hz)
    rwa [show n - (n - z) = z by omega]
  · intro hx
    have := Finset.mem_Ioo.mp (hS hx)
    exact ⟨n - x, revCuts_mem.mpr ⟨x, hx, rfl⟩, by omega⟩

/-- Reversal preserves the block lengths of a coarsening. -/
lemma gaps_revCuts (n : ℕ) (T : Finset ℕ) (hT : IsCutSet n T) :
    gaps n (revCuts n T) = gaps n T := by
  obtain ⟨c, hc⟩ : ∃ c, T.card = c := ⟨_, rfl⟩
  induction c generalizing n T with
  | zero =>
    rw [Finset.card_eq_zero] at hc
    subst hc
    simp [revCuts]
  | succ c ih =>
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    set m := T.max' hne with hm
    have hmT : m ∈ T := Finset.max'_mem T hne
    have hm0 := Finset.mem_Ioo.mp (hT hmT)
    set T1 := T.erase m with hT1
    have hT1m : ∀ x ∈ T1, 0 < x ∧ x < m := by
      intro x hx
      have hxT := Finset.mem_of_mem_erase hx
      have hxm : x ≠ m := Finset.ne_of_mem_erase hx
      have := Finset.le_max' T x hxT
      have := (Finset.mem_Ioo.mp (hT hxT)).1
      exact ⟨by omega, lt_of_le_of_ne ‹x ≤ m› hxm⟩
    have hT1c : IsCutSet m T1 := fun x hx => Finset.mem_Ioo.mpr (hT1m x hx)
    have hTeq : T = T1 ∪ {m} := by
      rw [hT1]; ext x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro hx; by_cases h : x = m <;> simp [h, hx]
      · rintro (⟨_, hx⟩ | rfl) <;> assumption
    have hcard : T1.card = c := by rw [hT1, Finset.card_erase_of_mem hmT]; omega
    -- gaps of T
    have hg1 : gaps n T = gaps m T1 + {n - m} := by
      have := gaps_glue m (n - m) T1 ∅ (fun x hx => (hT1m x hx).2) (by omega) (by simp)
      rw [show m + (n - m) = n by omega, gaps_empty] at this
      rw [hTeq]; simpa using this
    -- reversal of T
    have hrev : revCuts n T = (revCuts m T1).image ((n - m) + ·) ∪ {n - m} := by
      ext x
      simp only [revCuts, Finset.mem_image, Finset.mem_union, Finset.mem_singleton, hTeq]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with hy | rfl
        · exact Or.inl ⟨m - y, ⟨y, hy, rfl⟩, by have := hT1m y hy; omega⟩
        · exact Or.inr rfl
      · rintro (⟨z, ⟨y, hy, rfl⟩, rfl⟩ | rfl)
        · exact ⟨y, Or.inl hy, by have := hT1m y hy; omega⟩
        · exact ⟨m, Or.inr rfl, rfl⟩
    have hrc : ∀ x ∈ revCuts m T1, 0 < x ∧ x < m := fun x hx => Finset.mem_Ioo.mp
      (revCuts_isCutSet hT1c hx)
    have hg2 : gaps n (revCuts n T) = gaps m (revCuts m T1) + {n - m} := by
      have := gaps_glue (n - m) m ∅ (revCuts m T1) (by simp) (by omega) hrc
      rw [show n - m + m = n by omega, gaps_empty] at this
      rw [hrev, show (revCuts m T1).image ((n - m) + ·) ∪ {n - m} =
        ∅ ∪ (revCuts m T1).image ((n - m) + ·) ∪ {n - m} by simp, this, add_comm]
    rw [hg2, hg1, ih m T1 hT1c hcard]

/-- Reversal invariance of the coarsening polynomial: `G_{β*} = G_β`. -/
theorem G_revCuts (n : ℕ) (S : Finset ℕ) (hS : IsCutSet n S) : G n (revCuts n S) = G n S := by
  have hmono : ∀ T U : Finset ℕ, T ⊆ U → revCuts n T ⊆ revCuts n U :=
    fun T U h => Finset.image_subset_image h
  unfold G
  refine Finset.sum_nbij' (revCuts n) (revCuts n) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    simpa [revCuts_revCuts hS] using hmono _ _ hT
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    exact hmono _ _ hT
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact revCuts_revCuts (fun z hz => by
      have := hT hz
      exact revCuts_isCutSet hS this)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact revCuts_revCuts (fun z hz => hS (hT hz))
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [gaps_revCuts n T (fun z hz => revCuts_isCutSet hS (hT hz))]

end SkewRibbonCoarsenings
