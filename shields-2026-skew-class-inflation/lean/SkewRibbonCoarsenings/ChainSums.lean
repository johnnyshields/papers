/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/ChainSums.lean
import SkewRibbonCoarsenings.Antichain
import SkewRibbonCoarsenings.Defs

/-!
# Chain sums are sums over orderings; the labeled count `K` as a chain sum

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:detector` (the sentence after
`lem:antichain`: "for a labeled coarsening take `F(I) = b(∑_{i ∈ I} a_i)`; the chain sum is
`eq:K`").

`chainSum_eq_sum_ord` identifies the chain sum with the sum, over the orderings of `J \ I`, of
the product of the weights of the proper prefixes; `chainSum_cutWeight` identifies the chain sum
of the cut indicator with `K S a`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

section Ord

variable {ι : Type*} [DecidableEq ι]

/-- The orderings of a finite set `T`: the duplicate-free lists whose underlying set is `T`. -/
noncomputable def ord (T : Finset ι) : Finset (List ι) := T.toList.permutations.toFinset

lemma mem_ord {T : Finset ι} {l : List ι} : l ∈ ord T ↔ l.Nodup ∧ l.toFinset = T := by
  unfold ord
  rw [List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    refine ⟨h.nodup_iff.mpr T.nodup_toList, ?_⟩
    rw [List.toFinset_eq_of_perm _ _ h, Finset.toList_toFinset]
  · rintro ⟨h1, h2⟩
    apply List.perm_of_nodup_nodup_toFinset_eq h1 T.nodup_toList
    rw [h2, Finset.toList_toFinset]

lemma ord_empty : ord (∅ : Finset ι) = {[]} := by
  ext l
  simp only [mem_ord, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro rfl; simp

lemma ord_singleton (x : ι) : ord ({x} : Finset ι) = {[x]} := by
  ext l
  simp only [mem_ord, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rcases l with _ | ⟨y, _ | ⟨z, l⟩⟩
    · simp at h2
    · simpa using h2
    · have : ({y, z} : Finset ι) ⊆ {x} := by
        rw [← h2]; intro w hw; simp at hw ⊢; tauto
      have hyx : y = x := by simpa using this (by simp)
      have hzx : z = x := by simpa using this (by simp)
      exact absurd (by simp [hyx, hzx]) (List.nodup_cons.mp h1).1
  · rintro rfl; simp

lemma sum_ord {M : Type*} [AddCommMonoid M] {T : Finset ι} (hT : T.Nonempty) (f : List ι → M) :
    ∑ l ∈ ord T, f l = ∑ x ∈ T, ∑ l ∈ ord (T.erase x), f (x :: l) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun p _ => p.1 :: p.2) ?_ ?_ ?_ ?_
  · rintro ⟨x, l⟩ hp
    simp only [Finset.mem_sigma, mem_ord] at hp
    obtain ⟨hx, hl1, hl2⟩ := hp
    rw [mem_ord]
    have hxl : x ∉ l := by
      intro h
      have : x ∈ l.toFinset := List.mem_toFinset.mpr h
      rw [hl2] at this
      simp at this
    refine ⟨List.nodup_cons.mpr ⟨hxl, hl1⟩, ?_⟩
    rw [List.toFinset_cons, hl2]
    exact Finset.insert_erase hx
  · rintro ⟨x, l⟩ _ ⟨y, l'⟩ _ h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro l hl
    rw [mem_ord] at hl
    cases l with
    | nil =>
      exfalso
      obtain ⟨x, hx⟩ := hT
      rw [← hl.2] at hx
      simp at hx
    | cons x l =>
      refine ⟨⟨x, l⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, mem_ord]
      have hn := List.nodup_cons.mp hl.1
      refine ⟨?_, hn.2, ?_⟩
      · rw [← hl.2]; simp
      · rw [← hl.2, List.toFinset_cons, Finset.erase_insert]
        simpa using hn.1
  · intro p _; rfl

/-- The weight of an ordering `l` started from `I`: the product of `F` over the proper nonempty
prefixes, each added to `I`.  Orderings of length `≤ 1` have weight one. -/
def listWeight {R : Type*} [CommRing R] (F : Finset ι → R) : Finset ι → List ι → R
  | _, [] => 1
  | _, [_] => 1
  | I, x :: y :: l => F (insert x I) * listWeight F (insert x I) (y :: l)

variable {R : Type*} [CommRing R]

lemma listWeight_cons_of_ne_nil (F : Finset ι → R) (I : Finset ι) (x : ι) {l : List ι}
    (hl : l ≠ []) : listWeight F I (x :: l) = F (insert x I) * listWeight F (insert x I) l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons y l => rfl

/-- `eq:K` as a sum over orderings: the chain sum from `I` to `J` is the sum, over the orderings
of `J \ I`, of the weight of the ordering. -/
theorem chainSum_eq_sum_ord (F : Finset ι → R) (I J : Finset ι) :
    chainSum F I J = ∑ l ∈ ord (J \ I), listWeight F I l := by
  induction hc : (J \ I).card using Nat.strong_induction_on generalizing I with
  | _ c ih =>
  by_cases h1 : (J \ I).card ≤ 1
  · rw [chainSum_of_card_le h1]
    have : (J \ I).card = 0 ∨ (J \ I).card = 1 := by omega
    rcases this with h0 | h0
    · rw [Finset.card_eq_zero.mp h0, ord_empty, Finset.sum_singleton]; rfl
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h0
      rw [hx, ord_singleton, Finset.sum_singleton]; rfl
  · have h2 : 2 ≤ (J \ I).card := by omega
    have hne : (J \ I).Nonempty := Finset.card_pos.mp (by omega)
    rw [chainSum_of_two_le h2, sum_ord hne]
    apply Finset.sum_congr rfl
    intro x hx
    have hset : (J \ I).erase x = J \ insert x I := (Finset.sdiff_insert J I x).symm
    rw [hset, ih _ (hc ▸ card_sdiff_insert_lt hx) _ rfl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [mem_ord] at hl
    have hl0 : l ≠ [] := by
      rintro rfl
      have : (J \ insert x I).Nonempty := by
        rw [← hset]
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hx]; omega
      obtain ⟨y, hy⟩ := this
      rw [← hl.2] at hy
      simp at hy
    rw [listWeight_cons_of_ne_nil F I x hl0]

end Ord

section Perm

variable {R : Type*} [CommRing R]

/-- `listWeight` as a product over the proper nonempty prefixes. -/
lemma listWeight_eq_prod {ι : Type*} [DecidableEq ι] (F : Finset ι → R) :
    ∀ (l : List ι) (I : Finset ι),
      listWeight F I l = ∏ j ∈ Finset.Ico 1 l.length, F (I ∪ (l.take j).toFinset)
  | [], I => by simp [listWeight]
  | [x], I => by simp [listWeight]
  | x :: y :: l, I => by
    rw [listWeight, listWeight_eq_prod F (y :: l) (insert x I)]
    have h1 : Finset.Ico 1 (x :: y :: l).length = insert 1 (Finset.Ico 2 (x :: y :: l).length) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert, List.length_cons]; omega
    rw [h1, Finset.prod_insert (by simp)]
    congr 1
    · simp
    · have : Finset.Ico 2 (x :: y :: l).length = (Finset.Ico 1 (y :: l).length).map
          (addRightEmbedding 1) := by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_map, addRightEmbedding_apply, List.length_cons]
        constructor
        · intro h; exact ⟨j - 1, by omega, by omega⟩
        · rintro ⟨k, hk, rfl⟩; omega
      rw [this, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro j _
      simp [Finset.insert_union]

lemma take_ofFn_toFinset {r : ℕ} (π : Equiv.Perm (Fin r)) (j : ℕ) :
    (List.take j (List.ofFn (fun i => π i))).toFinset =
      (Finset.univ.filter fun i : Fin r => i.val < j).image π := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp at hk
    refine ⟨⟨k, by omega⟩, by simp; omega, ?_⟩
    simp
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.val, by simp; omega, ?_⟩
    simp

/-- The number of orderings in `ord univ` is the number of permutations. -/
lemma card_ord_univ (r : ℕ) : (ord (Finset.univ : Finset (Fin r))).card = r.factorial := by
  unfold ord
  rw [List.toFinset_card_of_nodup, List.length_permutations, Finset.length_toList,
    Finset.card_univ, Fintype.card_fin]
  exact List.nodup_permutations _ (Finset.nodup_toList _)

/-- Chain sums over the full label set `Fin r` are sums over permutations: for `g : ℕ → R` and the
labels `a`, the chain sum of the weights `F(I) = g(∑_{i ∈ I} a_i)` is the sum over orderings `π`
of the product of `g` over the proper partial sums.  Maximal chains of the Boolean lattice are
the orderings of the labels. -/
theorem chainSum_eq_sum_perm (g : ℕ → R) {r : ℕ} (a : Fin r → ℕ) :
    chainSum (fun X : Finset (Fin r) => g (∑ i ∈ X, a i)) ∅ Finset.univ =
      ∑ π : Equiv.Perm (Fin r), ∏ j ∈ Finset.Ico 1 r, g (partialSum a π j) := by
  rw [chainSum_eq_sum_ord, Finset.sdiff_empty]
  let e : Equiv.Perm (Fin r) → List (Fin r) := fun π => List.ofFn (fun i => π i)
  have hinj : Function.Injective e := by
    intro π σ h
    refine Equiv.ext fun i => ?_
    have := congrArg (fun l => l[i.val]?) h
    simpa [e] using this
  have hmem : ∀ π : Equiv.Perm (Fin r), e π ∈ ord (Finset.univ : Finset (Fin r)) := by
    intro π
    rw [mem_ord]
    refine ⟨List.nodup_ofFn.mpr π.injective, ?_⟩
    ext x
    simp only [e, List.mem_toFinset, Finset.mem_univ, iff_true]
    rw [List.mem_ofFn]
    exact ⟨π.symm x, by simp⟩
  have himg : (Finset.univ : Finset (Equiv.Perm (Fin r))).image e = ord Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      obtain ⟨π, _, rfl⟩ := Finset.mem_image.mp hl
      exact hmem π
    · rw [card_ord_univ, Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
  rw [← himg, Finset.sum_image (fun π _ σ _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro π _
  rw [listWeight_eq_prod]
  simp only [Finset.empty_union]
  have hlen : (e π).length = r := by simp [e]
  rw [hlen]
  have hps : ∀ j, ∑ i ∈ (List.take j (e π)).toFinset, a i = partialSum a π j := by
    intro j
    rw [take_ofFn_toFinset, Finset.sum_image (fun x _ y _ h => π.injective h)]
    rfl
  simp only [hps]

/-- The cut weights of the labeled count: `1` if the total is a retained cut, else `0`. -/
def cutWeight (S : Finset ℕ) (t : ℕ) : ℤ := if t ∈ S then 1 else 0

/-- `eq:K`: the labeled count `K_b(a)` is the chain sum from `∅` to the full label set of the
weights `F(I) = b(∑_{i ∈ I} a_i)`, where `b` is the indicator of the retained cuts `S`.  Maximal
chains correspond to orderings of the labels, that is, to permutations. -/
theorem K_eq_chainSum (S : Finset ℕ) {r : ℕ} (a : Fin r → ℕ) :
    (K S a : ℤ) =
      chainSum (fun X : Finset (Fin r) => cutWeight S (∑ i ∈ X, a i)) ∅ Finset.univ := by
  rw [chainSum_eq_sum_perm, K, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro π _
  simp only [cutWeight]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_Ico]
  congr 1
  apply propext
  constructor
  · intro h j hj
    rw [Finset.mem_Ico] at hj
    exact h j hj.2 hj.1
  · intro h j hj hj0
    exact h j (Finset.mem_Ico.mpr ⟨hj0, hj⟩)

end Perm

end SkewRibbonCoarsenings
