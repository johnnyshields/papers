/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Chain sums on the Boolean lattice and the antichain cancellation

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector` (`lem:antichain`).

For a finite label set `ι` and weights `F : Finset ι → R` in a commutative ring, `chainSum F I J`
is the sum, over maximal chains `I = I₀ ⊂ I₁ ⊂ ⋯ ⊂ I_m = J` of the Boolean lattice, of the product
of the weights at the intermediate vertices `I₁, …, I_{m-1}`.  It is defined by first-step
recursion; the identification with sums over orderings is in `SkewRibbonCoarsenings.ChainSums`.
`chainSum_antichain` is `lem:antichain` on an arbitrary interval `[I, J]`, and
`antichain_cancellation` is the statement of the paper (`I = ∅`, `J = M`).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

section ChainSum

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]

/-- The chain sum `Z_F(I, J)` of `sec:detector`: the sum over maximal chains from `I` to `J` of
the product of the weights at the intermediate vertices, endpoints omitted.  A chain without an
intermediate vertex (`|J \ I| ≤ 1`) contributes `1`.  Only the values of `F` at vertices
strictly between `I` and `J` matter (`chainSum_congr`). -/
def chainSum (F : Finset ι → R) (I J : Finset ι) : R :=
  if (J \ I).card ≤ 1 then 1 else
    ∑ x ∈ (J \ I).attach, F (insert x.1 I) * chainSum F (insert x.1 I) J
termination_by (J \ I).card
decreasing_by
  apply Finset.card_lt_card
  have hx := x.2
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x.1, hx, by simp⟩
  · intro y hy; simp at hy ⊢; tauto

lemma chainSum_of_card_le {F : Finset ι → R} {I J : Finset ι} (h : (J \ I).card ≤ 1) :
    chainSum F I J = 1 := by
  rw [chainSum, ite_eq_left_iff]
  intro h'; exact absurd h h'

lemma chainSum_of_two_le {F : Finset ι → R} {I J : Finset ι} (h : 2 ≤ (J \ I).card) :
    chainSum F I J = ∑ x ∈ J \ I, F (insert x I) * chainSum F (insert x I) J := by
  rw [chainSum, ite_eq_right_iff.mpr (fun h' => by omega)]
  exact Finset.sum_attach (J \ I) (fun x => F (insert x I) * chainSum F (insert x I) J)

lemma card_sdiff_insert_lt {I J : Finset ι} {x : ι} (hx : x ∈ J \ I) :
    (J \ insert x I).card < (J \ I).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert _ _))]
  exact ⟨x, hx, by simp⟩

lemma insert_ssubset_of_two_le {I J : Finset ι} {x : ι} (hIJ : I ⊆ J) (hx : x ∈ J \ I)
    (h : 2 ≤ (J \ I).card) : insert x I ⊂ J := by
  rw [Finset.mem_sdiff] at hx
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < (J \ I).card) x
  rw [Finset.mem_sdiff] at hy
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset hx.1 hIJ, ?_⟩
  intro heq
  have : y ∈ insert x I := heq ▸ hy.1
  rw [Finset.mem_insert] at this
  rcases this with h1 | h1
  · exact hyx h1
  · exact hy.2 h1

lemma two_le_card_of_ssubset {I J X : Finset ι} (hI : I ⊂ X) (hX : X ⊂ J) :
    2 ≤ (J \ I).card := by
  obtain ⟨u, huX, huI⟩ := Finset.exists_of_ssubset hI
  obtain ⟨v, hvJ, hvX⟩ := Finset.exists_of_ssubset hX
  have hu : u ∈ J \ I := Finset.mem_sdiff.mpr ⟨hX.subset huX, huI⟩
  have hv : v ∈ J \ I := Finset.mem_sdiff.mpr ⟨hvJ, fun h => hvX (hI.subset h)⟩
  have : u ≠ v := fun h => hvX (h ▸ huX)
  exact Finset.one_lt_card.mpr ⟨u, hu, v, hv, this⟩

/-- The chain sum depends only on the weights strictly between the endpoints. -/
lemma chainSum_congr {F F' : Finset ι → R} {I J : Finset ι} (hIJ : I ⊆ J)
    (h : ∀ X, I ⊂ X → X ⊂ J → F X = F' X) : chainSum F I J = chainSum F' I J := by
  induction hc : (J \ I).card using Nat.strong_induction_on generalizing I J with
  | _ c ih =>
  by_cases h1 : (J \ I).card ≤ 1
  · rw [chainSum_of_card_le h1, chainSum_of_card_le h1]
  · have h2 : 2 ≤ (J \ I).card := by omega
    rw [chainSum_of_two_le h2, chainSum_of_two_le h2]
    apply Finset.sum_congr rfl
    intro x hx
    have hxs := hx
    have hxJ : insert x I ⊂ J := insert_ssubset_of_two_le hIJ hx h2
    rw [Finset.mem_sdiff] at hx
    have hIx : I ⊂ insert x I := Finset.ssubset_insert hx.2
    congr 1
    · exact h _ hIx hxJ
    · exact ih _ (hc ▸ card_sdiff_insert_lt hxs) hxJ.subset
        (fun X h1 h2 => h X (hIx.trans h1) h2) rfl

/-- Chain sums over `I ∪ K ⊆ I ∪ J'` with `I` disjoint from `J'` are chain sums for the shifted
weights `X ↦ F (I ∪ X)` over `K ⊆ J'`. -/
lemma chainSum_union_left {F : Finset ι → R} {I J' : Finset ι} (hd : Disjoint I J')
    (K : Finset ι) : chainSum F (I ∪ K) (I ∪ J') = chainSum (fun X => F (I ∪ X)) K J' := by
  have hcard : ∀ K : Finset ι, ((I ∪ J') \ (I ∪ K)) = J' \ K := by
    intro K; ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_⟩
      rintro (h | h)
      · exact Finset.disjoint_left.mp hd h h1
      · exact h2 h
  induction hc : (J' \ K).card using Nat.strong_induction_on generalizing K with
  | _ c ih =>
  by_cases h1 : (J' \ K).card ≤ 1
  · rw [chainSum_of_card_le (by rw [hcard K]; exact h1), chainSum_of_card_le h1]
  · have h2 : 2 ≤ (J' \ K).card := by omega
    rw [chainSum_of_two_le (by rw [hcard K]; exact h2), chainSum_of_two_le h2, hcard K]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.union_insert]
    congr 1
    exact ih _ (hc ▸ card_sdiff_insert_lt hx) _ rfl

/-- The weight of a chain continuing from the vertex `K` to the endpoint `X`, with the weight at
`K` included and the endpoint `X` excluded: `1` if `K = X`, else `F K * Z_F(K, X)`. -/
def yTerm (F : Finset ι → R) (K X : Finset ι) : R :=
  if K = X then 1 else F K * chainSum F K X

lemma chainSum_eq_sum_yTerm {F : Finset ι → R} {I X : Finset ι} (h : I ⊂ X) :
    chainSum F I X = ∑ x ∈ X \ I, yTerm F (insert x I) X := by
  by_cases h1 : (X \ I).card ≤ 1
  · have hc : (X \ I).card = 1 := by
      have : 0 < (X \ I).card := Finset.card_pos.mpr (by
        obtain ⟨y, hy, hyI⟩ := Finset.exists_of_ssubset h
        exact ⟨y, by simp [hy, hyI]⟩)
      omega
    obtain ⟨x0, hx0⟩ := Finset.card_eq_one.mp hc
    rw [chainSum_of_card_le h1, hx0, Finset.sum_singleton, yTerm]
    have hx0m : x0 ∈ X \ I := by rw [hx0]; simp
    rw [Finset.mem_sdiff] at hx0m
    rw [if_pos]
    apply Finset.Subset.antisymm
    · exact Finset.insert_subset hx0m.1 h.subset
    · intro y hy
      by_cases hyI : y ∈ I
      · exact Finset.mem_insert_of_mem hyI
      · have : y ∈ X \ I := by simp [hy, hyI]
        rw [hx0] at this
        simp at this
        simp [this]
  · have h2 : 2 ≤ (X \ I).card := by omega
    rw [chainSum_of_two_le h2]
    apply Finset.sum_congr rfl
    intro x hx
    have := insert_ssubset_of_two_le h.subset hx h2
    rw [yTerm, if_neg this.ne]

/-- `lem:antichain` on an arbitrary interval `[I, J]`: if `F'` agrees with `F` off an antichain
`A` of vertices, then the difference of the chain sums from `I` to `J` is the sum, over the
vertices of `A` strictly between `I` and `J`, of the increment times the chain sums below and
above.  The statement of the paper is `antichain_cancellation`. -/
theorem chainSum_antichain {A : Finset (Finset ι)} (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι)))
    {F F' : Finset ι → R} {I J : Finset ι} (hIJ : I ⊆ J)
    (hdiff : ∀ X, I ⊂ X → X ⊂ J → X ∉ A → F' X = F X) :
    chainSum F' I J - chainSum F I J =
      ∑ X ∈ A, if I ⊂ X ∧ X ⊂ J then
        (F' X - F X) * (chainSum F I X * chainSum F X J) else 0 := by
  induction hc : (J \ I).card using Nat.strong_induction_on generalizing I J with
  | _ c ih =>
  by_cases hEq : I = J
  · subst hEq
    rw [chainSum_of_card_le (by simp), chainSum_of_card_le (by simp), sub_self]
    symm
    apply Finset.sum_eq_zero
    intro X _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact absurd (h1.trans h2) (lt_irrefl _)
  have hIJs : I ⊂ J := Finset.ssubset_iff_subset_ne.mpr ⟨hIJ, hEq⟩
  -- the difference of the continuation terms at `K ⊆ J`
  have hD : ∀ K, I ⊂ K → K ⊆ J → (J \ K).card < (J \ I).card →
      yTerm F' K J - yTerm F K J =
        ∑ X ∈ A, if K ⊆ X ∧ X ⊂ J then (F' X - F X) * (yTerm F K X * chainSum F X J) else 0 := by
    intro K hIK hKJ hlt
    by_cases hKJ' : K = J
    · subst hKJ'
      simp only [yTerm, if_true, sub_self]
      symm
      apply Finset.sum_eq_zero
      intro X _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact absurd (h1.trans_lt h2) (lt_irrefl _)
    have hKs : K ⊂ J := Finset.ssubset_iff_subset_ne.mpr ⟨hKJ, hKJ'⟩
    have hIH := ih _ (hc ▸ hlt) hKJ (fun X h1 h2 h3 => hdiff X (hIK.trans h1) h2 h3) rfl
    by_cases hKA : K ∈ A
    · have hnone : ∀ X ∈ A, K ⊂ X → False := fun X hX hKX =>
        hA hKA hX (ne_of_lt hKX) hKX.subset
      have hz : chainSum F' K J = chainSum F K J := by
        apply chainSum_congr hKJ
        intro X h1 h2
        by_cases hXA : X ∈ A
        · exact (hnone X hXA h1).elim
        · exact hdiff X (hIK.trans h1) h2 hXA
      rw [Finset.sum_eq_single K]
      · simp only [yTerm, hKJ', if_true, if_false, hz]
        rw [if_pos ⟨subset_rfl, hKs⟩]
        ring
      · intro X hX hXK
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hnone X hX (Finset.ssubset_iff_subset_ne.mpr ⟨h1, fun h => hXK h.symm⟩)
      · intro h; exact absurd hKA h
    · have hFK : F' K = F K := hdiff K hIK hKs hKA
      have hrw : yTerm F' K J - yTerm F K J = F K * (chainSum F' K J - chainSum F K J) := by
        simp only [yTerm, if_neg hKJ', hFK]; ring
      rw [hrw, hIH, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X hX
      have hXK : K ≠ X := fun h => hKA (h ▸ hX)
      by_cases hc1 : K ⊂ X ∧ X ⊂ J
      · rw [if_pos hc1, if_pos ⟨hc1.1.subset, hc1.2⟩, yTerm, if_neg hc1.1.ne]
        ring
      · rw [if_neg hc1, if_neg, mul_zero]
        rintro ⟨h1, h2⟩
        exact hc1 ⟨Finset.ssubset_iff_subset_ne.mpr ⟨h1, hXK⟩, h2⟩
  -- assemble over the first label
  have hsub : ∀ x ∈ J \ I, insert x I ⊆ J := fun x hx =>
    Finset.insert_subset (Finset.mem_sdiff.mp hx).1 hIJ
  rw [chainSum_eq_sum_yTerm hIJs, chainSum_eq_sum_yTerm hIJs, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun x hx => hD (insert x I)
      (Finset.ssubset_insert (Finset.mem_sdiff.mp hx).2) (hsub x hx)
      (hc ▸ card_sdiff_insert_lt hx)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X hX
  by_cases hc1 : I ⊂ X ∧ X ⊂ J
  · rw [if_pos hc1, chainSum_eq_sum_yTerm hc1.1, Finset.sum_mul, Finset.mul_sum]
    have hfil : (J \ I).filter (fun x => insert x I ⊆ X) = X \ I := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.insert_subset_iff]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨hc1.2.subset h3, h2⟩, h3, hc1.1.subset⟩
    rw [← Finset.sum_filter_add_sum_filter_not (J \ I) (fun x => insert x I ⊆ X), hfil]
    rw [Finset.sum_eq_zero (s := (J \ I).filter (fun x => ¬ insert x I ⊆ X)), add_zero]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos ⟨Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp hx).1, hc1.1.subset⟩, hc1.2⟩]
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hx.2 h1
  · rw [if_neg hc1]
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hc1
    refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.subset_insert _ _).trans h1, ?_⟩, h2⟩
    rintro rfl
    exact (Finset.mem_sdiff.mp hx).2 (h1 (Finset.mem_insert_self _ _))

/-- Transport of chain sums along an injective relabeling of the vertices. -/
lemma chainSum_map {κ : Type*} [DecidableEq κ] (f : ι ↪ κ) (F : Finset κ → R) (I J : Finset ι) :
    chainSum F (I.map f) (J.map f) = chainSum (fun X => F (X.map f)) I J := by
  induction hc : (J \ I).card using Nat.strong_induction_on generalizing I with
  | _ c ih =>
  have hsd : (J.map f) \ (I.map f) = (J \ I).map f := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_map]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h2⟩
      exact ⟨x, ⟨hx, fun h => h2 ⟨x, h, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxI⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, fun ⟨x', h', hx'⟩ => hxI (f.injective hx' ▸ h')⟩
  have hcard : ((J.map f) \ (I.map f)).card = (J \ I).card := by
    rw [hsd, Finset.card_map]
  by_cases h1 : (J \ I).card ≤ 1
  · rw [chainSum_of_card_le (by rw [hcard]; exact h1), chainSum_of_card_le h1]
  · have h2 : 2 ≤ (J \ I).card := by omega
    rw [chainSum_of_two_le (by rw [hcard]; exact h2), chainSum_of_two_le h2, hsd,
      Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x hx
    have himg : insert (f x) (I.map f) = (insert x I).map f := by
      rw [Finset.map_insert]
    rw [himg, ih _ (hc ▸ card_sdiff_insert_lt hx) _ rfl]

/-- `lem:antichain`: if `F'` differs from `F` only at the vertices of an antichain `𝒜` of proper
nonempty subsets of the label set, with increments `δ_I = F'(I) - F(I)`, then
`Z_{F'}(∅, M) - Z_F(∅, M) = ∑_{I ∈ 𝒜} δ_I Z_F(∅, I) Z_F(I, M)`. -/
theorem antichain_cancellation [Fintype ι] {A : Finset (Finset ι)}
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι)))
    (hprop : ∀ X ∈ A, X.Nonempty ∧ X ≠ Finset.univ)
    {F F' : Finset ι → R} (hdiff : ∀ X, X.Nonempty → X ≠ Finset.univ → X ∉ A → F' X = F X) :
    chainSum F' ∅ Finset.univ - chainSum F ∅ Finset.univ =
      ∑ X ∈ A, (F' X - F X) * (chainSum F ∅ X * chainSum F X Finset.univ) := by
  rw [chainSum_antichain hA (Finset.empty_subset _) fun X h1 h2 h3 =>
    hdiff X (Finset.nonempty_iff_ne_empty.mpr (Finset.ssubset_iff_subset_ne.mp h1).2.symm)
      (Finset.ssubset_iff_subset_ne.mp h2).2 h3]
  apply Finset.sum_congr rfl
  intro X hX
  obtain ⟨h1, h2⟩ := hprop X hX
  rw [if_pos]
  exact ⟨Finset.nonempty_iff_ne_empty.mp h1 |> fun h => Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.empty_subset _, fun h' => h h'.symm⟩,
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, h2⟩⟩

/-- `lem:antichain` applied to the antichain `{{x}, T \ {x}}` of complementary vertices: if `F'`
and `F` agree strictly between `∅` and `T` except at `{x}` and `T \ {x}`, with increments `θ` and
`-θ`, then the chain sums differ by `θ` times the difference of the two chain sums over
`T \ {x}` (the first with every weight shifted by `x`).  Both chains through `{x}` and `T \ {x}`
split uniquely, and the two remaining factors are `1`. -/
theorem chainSum_contraction {T : Finset ι} {x : ι} (hx : x ∈ T) (hne : (T.erase x).Nonempty)
    {F F' : Finset ι → R} (θ : R)
    (hdiff : ∀ X, ∅ ⊂ X → X ⊂ T → X ≠ {x} → X ≠ T.erase x → F' X = F X)
    (h1 : F' {x} - F {x} = θ) (h2 : F' (T.erase x) - F (T.erase x) = -θ) :
    chainSum F' ∅ T - chainSum F ∅ T =
      θ * (chainSum (fun X => F (insert x X)) ∅ (T.erase x) - chainSum F ∅ (T.erase x)) := by
  have hxR : x ∉ T.erase x := Finset.notMem_erase x T
  have hne1 : ({x} : Finset ι) ≠ T.erase x := by
    intro h; apply hxR; rw [← h]; exact Finset.mem_singleton_self x
  have hanti : IsAntichain (· ⊆ ·) (({{x}, T.erase x} : Finset (Finset ι)) : Set (Finset ι)) := by
    intro u hu v hv huv hsub
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact huv rfl
    · exact hxR (hsub (Finset.mem_singleton_self x))
    · obtain ⟨y, hy⟩ := hne
      have := hsub hy
      rw [Finset.mem_singleton] at this
      exact hxR (this ▸ hy)
    · exact huv rfl
  have hsingle : ∅ ⊂ ({x} : Finset ι) := Finset.empty_ssubset.mpr (Finset.singleton_nonempty x)
  have hsT : ({x} : Finset ι) ⊂ T := by
    obtain ⟨y, hy⟩ := hne
    rw [Finset.ssubset_iff_of_subset (Finset.singleton_subset_iff.mpr hx)]
    exact ⟨y, Finset.mem_of_mem_erase hy, by
      rw [Finset.mem_singleton]; exact (Finset.ne_of_mem_erase hy)⟩
  have hRne : ∅ ⊂ T.erase x := Finset.empty_ssubset.mpr hne
  have hRT : T.erase x ⊂ T := Finset.erase_ssubset hx
  rw [chainSum_antichain hanti (Finset.empty_subset _) (fun X h1' h2' h3 => by
    by_cases hc1 : X = {x}
    · exact absurd (by simp [hc1]) h3
    · by_cases hc2 : X = T.erase x
      · exact absurd (by simp [hc2]) h3
      · exact hdiff X h1' h2' hc1 hc2), Finset.sum_pair hne1, if_pos ⟨hsingle, hsT⟩,
    if_pos ⟨hRne, hRT⟩]
  have hZ1 : chainSum F ∅ {x} = 1 := chainSum_of_card_le (by simp)
  have hZ2 : chainSum F (T.erase x) T = 1 := chainSum_of_card_le (by
    have : T \ T.erase x = {x} := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro ⟨h, h'⟩; by_contra hne'; exact h' ⟨hne', h⟩
      · rintro rfl; exact ⟨hx, fun h => h.1 rfl⟩
    rw [this]; simp)
  have hZ3 : chainSum F {x} T = chainSum (fun X => F (insert x X)) ∅ (T.erase x) := by
    have := chainSum_union_left (F := F) (I := {x}) (J' := T.erase x)
      (Finset.disjoint_singleton_left.mpr hxR) ∅
    rw [Finset.union_empty, Finset.singleton_union, Finset.insert_erase hx] at this
    rw [this]
    simp [Finset.singleton_union]
  rw [hZ1, hZ2, hZ3, h1, h2]
  ring

end ChainSum

end SkewRibbonCoarsenings
