/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Defs

/-!
# Labeled counts and the label factor

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:algebra`
(`eq:K`, `lem:labels`, `eq:label-factor`, `rem:modular-order`).

For a labeled positive list `a` of total `n` and a cut set `S`, the labeled count `K S a` equals
`κ(λ) · m_β(λ)` where `λ = sort a` and `m_β(λ) = mult n S λ`.  The proof matches orderings of the
labels with retained-cut subsets: an ordering is sent to the cut set of its partial sums, a
retained-cut subset with block lengths `λ` has exactly one numerical ordering of `λ`, and the
orderings of the labels realizing it form one coset of the stabilizer of `a`, of order `κ(λ)`.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-- The multiplicity factor `κ(λ) = ∏_j ν_j(λ)!` of `sec:algebra`, `ν_j` the multiplicity of the
part `j` in the multiset `λ`. -/
def kappa (lam : Multiset ℕ) : ℕ := ∏ j ∈ lam.toFinset, (lam.count j).factorial

/-- `λ = sort a`: the multiset of values of the labeled list `a`. -/
def sortParts {r : ℕ} (a : Fin r → ℕ) : Multiset ℕ := Multiset.map a Finset.univ.val

/-- Sum of the first `j` entries of the list `ℓ` in its given order. -/
def prefixSum {r : ℕ} (ℓ : Fin r → ℕ) (j : ℕ) : ℕ := ∑ i : Fin r with i.val < j, ℓ i

/-- The cut set of the list `ℓ`: its proper prefix sums. -/
def cutsOf {r : ℕ} (ℓ : Fin r → ℕ) : Finset ℕ := (Finset.Ioo 0 r).image (prefixSum ℓ)

/-- The boundary set `{0, n} ∪ T`. -/
def bdry (n : ℕ) (T : Finset ℕ) : Finset ℕ := insert 0 (insert n T)

section Prefix

variable {r : ℕ} (ℓ : Fin r → ℕ)

theorem prefixSum_zero : prefixSum ℓ 0 = 0 := by simp [prefixSum]

theorem prefixSum_of_le {j : ℕ} (hj : r ≤ j) : prefixSum ℓ j = ∑ i, ℓ i := by
  unfold prefixSum
  rw [Finset.filter_true_of_mem]
  intro i _; exact lt_of_lt_of_le i.2 hj

theorem prefixSum_mono {j k : ℕ} (h : j ≤ k) : prefixSum ℓ j ≤ prefixSum ℓ k := by
  unfold prefixSum
  apply Finset.sum_le_sum_of_subset
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem prefixSum_succ {j : ℕ} (hj : j < r) :
    prefixSum ℓ (j + 1) = prefixSum ℓ j + ℓ ⟨j, hj⟩ := by
  unfold prefixSum
  have : (Finset.univ.filter fun i : Fin r => i.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter fun i : Fin r => i.val < j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem prefixSum_lt {j k : ℕ} (hpos : ∀ i, 0 < ℓ i) (hjk : j < k) (hk : k ≤ r) :
    prefixSum ℓ j < prefixSum ℓ k := by
  have := prefixSum_succ ℓ (j := j) (by omega)
  have h2 := hpos ⟨j, by omega⟩
  have := prefixSum_mono ℓ (show j + 1 ≤ k by omega)
  omega

theorem prefixSum_strictMono (hpos : ∀ i, 0 < ℓ i) :
    StrictMono (fun i : Fin (r + 1) => prefixSum ℓ i) :=
  fun i k h => prefixSum_lt ℓ hpos (Fin.lt_def.mp h) (by omega)

theorem prefixSum_injOn (hpos : ∀ i, 0 < ℓ i) :
    Set.InjOn (prefixSum ℓ) (Finset.Iic r : Finset ℕ) := by
  intro j hj k hk h
  simp only [Finset.coe_Iic, Set.mem_Iic] at hj hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact absurd h (prefixSum_lt ℓ hpos h1 hk).ne
  · exact absurd h (prefixSum_lt ℓ hpos h1 hj).ne'

theorem card_cutsOf (hpos : ∀ i, 0 < ℓ i) : (cutsOf ℓ).card = r - 1 := by
  unfold cutsOf
  rw [Finset.card_image_of_injOn, Nat.card_Ioo]
  · omega
  · intro j hj k hk h
    simp only [Finset.coe_Ioo, Set.mem_Ioo] at hj hk
    exact prefixSum_injOn ℓ hpos (by simp; omega) (by simp; omega) h

theorem cutsOf_subset (hpos : ∀ i, 0 < ℓ i) :
    cutsOf ℓ ⊆ Finset.Ioo 0 (∑ i, ℓ i) := by
  intro x hx
  unfold cutsOf at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  simp only [Finset.mem_Ioo] at hj ⊢
  rw [← prefixSum_of_le ℓ (le_refl r)]
  exact ⟨by simpa [prefixSum_zero] using prefixSum_lt ℓ hpos hj.1 (by omega),
    prefixSum_lt ℓ hpos hj.2 le_rfl⟩

/-- Filtering the cut set below the prefix sum at `j` gives the earlier prefix sums. -/
theorem filter_cutsOf_lt (hpos : ∀ i, 0 < ℓ i) {j : ℕ} (hj : j ≤ r) :
    (cutsOf ℓ).filter (· < prefixSum ℓ j) = (Finset.Ioo 0 j).image (prefixSum ℓ) := by
  ext x
  simp only [cutsOf, Finset.mem_filter, Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hlt⟩
    refine ⟨i, ⟨hi.1, ?_⟩, rfl⟩
    by_contra hij
    exact absurd (prefixSum_mono ℓ (not_lt.mp hij)) (not_le.mpr hlt)
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, ⟨hi.1, by omega⟩, rfl⟩, prefixSum_lt ℓ hpos hi.2 hj⟩

theorem sup_filter_cutsOf (hpos : ∀ i, 0 < ℓ i) {j : ℕ} (hj : j ≤ r) (hj0 : 0 < j) :
    ((cutsOf ℓ).filter (· < prefixSum ℓ j)).sup id = prefixSum ℓ (j - 1) := by
  rw [filter_cutsOf_lt ℓ hpos hj]
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_Ioo] at hi
    exact prefixSum_mono ℓ (by omega)
  · by_cases h1 : j = 1
    · subst h1; simp [prefixSum_zero]
    · exact Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨j - 1, by simp; omega, rfl⟩)

/-- The block lengths of the coarsening retaining the cuts of `ℓ` are the entries of `ℓ`. -/
theorem gaps_cutsOf (hpos : ∀ i, 0 < ℓ i) (hr : 0 < r) :
    gaps (∑ i, ℓ i) (cutsOf ℓ) = sortParts ℓ := by
  set n := ∑ i, ℓ i with hn
  have hnP : prefixSum ℓ r = n := prefixSum_of_le ℓ le_rfl
  have hins : insert n (cutsOf ℓ) = (Finset.Ioc 0 r).image (prefixSum ℓ) := by
    have : Finset.Ioc 0 r = insert r (Finset.Ioo 0 r) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ioo]; omega
    rw [this, Finset.image_insert, hnP]; rfl
  have hinj : Set.InjOn (prefixSum ℓ) (Finset.Ioc 0 r : Finset ℕ) := by
    intro j hj k hk h
    simp only [Finset.coe_Ioc, Set.mem_Ioc] at hj hk
    exact prefixSum_injOn ℓ hpos (by simp; omega) (by simp; omega) h
  unfold gaps
  rw [hins, Finset.image_val_of_injOn hinj, Multiset.map_map]
  have h1 : ∀ j ∈ (Finset.Ioc 0 r).val,
      ((fun x => x - ((cutsOf ℓ).filter (· < x)).sup id) ∘ prefixSum ℓ) j =
        (fun j => if h : j < r then ℓ ⟨j, h⟩ else 0) (j - 1) := by
    intro j hj
    have hj' : j ∈ Finset.Ioc 0 r := hj
    rw [Finset.mem_Ioc] at hj'
    simp only [Function.comp]
    rw [sup_filter_cutsOf ℓ hpos hj'.2 hj'.1]
    have hlt : j - 1 < r := by omega
    simp only [hlt, ↓reduceDIte]
    have := prefixSum_succ ℓ hlt
    rw [show j - 1 + 1 = j by omega] at this
    omega
  rw [Multiset.map_congr rfl h1]
  set f : ℕ → ℕ := fun j => if h : j < r then ℓ ⟨j, h⟩ else 0 with hf
  have h2 : (Finset.Ioc 0 r).val.map (· - 1) = (Finset.range r).val := by
    have : (Finset.range r) = (Finset.Ioc 0 r).image (· - 1) := by
      ext x; simp only [Finset.mem_range, Finset.mem_image, Finset.mem_Ioc]
      constructor
      · intro h; exact ⟨x + 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨y, hy, rfl⟩; omega
    rw [this, Finset.image_val_of_injOn]
    intro x hx y hy hxy
    simp only [Finset.coe_Ioc, Set.mem_Ioc] at hx hy
    simp only at hxy
    omega
  have h3 : (Finset.univ : Finset (Fin r)).val.map Fin.val = (Finset.range r).val := by
    have : (Finset.univ : Finset (Fin r)).map Fin.valEmbedding = Finset.range r := by
      ext x; simp
    rw [← this]; rfl
  have h4 : Multiset.map (fun x => f (x - 1)) (Finset.Ioc 0 r).val =
      Multiset.map f (Multiset.map (· - 1) (Finset.Ioc 0 r).val) := by
    rw [Multiset.map_map]; rfl
  rw [h4, h2, ← h3, Multiset.map_map]
  unfold sortParts
  apply Multiset.map_congr rfl
  intro i _
  simp [hf, i.2]

/-- The prefix-sum function of a positive list is determined by its cut set and total. -/
theorem range_prefixSum (hpos : ∀ i, 0 < ℓ i) (hr : 0 < r) :
    Set.range (fun i : Fin (r + 1) => prefixSum ℓ i) = ↑(bdry (∑ i, ℓ i) (cutsOf ℓ)) := by
  ext x
  simp only [Set.mem_range, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, bdry]
  constructor
  · rintro ⟨j, rfl⟩
    have hj : (j : ℕ) ≤ r := by omega
    rcases Nat.lt_or_ge (j : ℕ) r with h | h
    · rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · left; rw [h0, prefixSum_zero]
      · right; right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Ioo.mpr ⟨h0, h⟩, rfl⟩
    · right; left
      rw [prefixSum_of_le ℓ h]
  · rintro (rfl | h | h)
    · exact ⟨0, by simp [prefixSum_zero]⟩
    · exact ⟨Fin.last r, by simp [prefixSum_of_le ℓ (le_refl r), h]⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      rw [Finset.mem_Ioo] at hj
      exact ⟨⟨j, by omega⟩, rfl⟩

theorem list_eq_of_cutsOf_eq {ℓ ℓ' : Fin r → ℕ} (hpos : ∀ i, 0 < ℓ i) (hpos' : ∀ i, 0 < ℓ' i)
    (hr : 0 < r) (hsum : ∑ i, ℓ i = ∑ i, ℓ' i) (hc : cutsOf ℓ = cutsOf ℓ') : ℓ = ℓ' := by
  have hP : (fun i : Fin (r + 1) => prefixSum ℓ i) = fun i : Fin (r + 1) => prefixSum ℓ' i := by
    rw [← StrictMono.range_inj_of_wellFoundedLT (prefixSum_strictMono ℓ hpos)
      (prefixSum_strictMono ℓ' hpos'), range_prefixSum ℓ hpos hr, range_prefixSum ℓ' hpos' hr,
      hsum, hc]
  funext i
  have h1 := prefixSum_succ ℓ i.2
  have h2 := prefixSum_succ ℓ' i.2
  have h3 := congrFun hP i.castSucc
  have h4 := congrFun hP i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h3 h4
  simp only [Fin.eta] at h1 h2
  omega

end Prefix

section Construction

variable {n : ℕ}

theorem bdry_card (hn : 0 < n) {T : Finset ℕ} (hT : T ⊆ Finset.Ioo 0 n) :
    (bdry n T).card = T.card + 2 := by
  have hnT : n ∉ T := fun h => by have := Finset.mem_Ioo.mp (hT h); omega
  have h0 : (0 : ℕ) ∉ insert n T := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by omega, fun h => by have := Finset.mem_Ioo.mp (hT h); omega⟩
  unfold bdry
  rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem hnT]

theorem mem_bdry_le (hn : 0 < n) {T : Finset ℕ} (hT : T ⊆ Finset.Ioo 0 n) {x : ℕ}
    (hx : x ∈ bdry n T) : x ≤ n := by
  simp only [bdry, Finset.mem_insert] at hx
  rcases hx with rfl | rfl | h
  · omega
  · exact le_rfl
  · exact (Finset.mem_Ioo.mp (hT h)).2.le

/-- Every cut set `T ⊆ {1, …, n-1}` is the cut set of a positive list of total `n`, namely the
list of its successive block lengths. -/
theorem exists_list_of_cuts (hn : 0 < n) {T : Finset ℕ} (hT : T ⊆ Finset.Ioo 0 n) :
    ∃ ℓ : Fin (T.card + 1) → ℕ, (∀ i, 0 < ℓ i) ∧ ∑ i, ℓ i = n ∧ cutsOf ℓ = T := by
  have hcard : (bdry n T).card = T.card + 1 + 1 := bdry_card hn hT
  set p := (bdry n T).orderEmbOfFin hcard with hp
  have hmem : ∀ i, p i ∈ bdry n T := fun i => Finset.orderEmbOfFin_mem _ _ i
  have hrange : Set.range p = ↑(bdry n T) := Finset.range_orderEmbOfFin _ _
  have hp0 : p 0 = 0 := by
    have h0 : (0 : ℕ) ∈ Set.range p := by rw [hrange]; simp [bdry]
    obtain ⟨k, hk⟩ := h0
    have : p 0 ≤ p k := p.monotone (Fin.zero_le k)
    have h2 : p 0 ∈ bdry n T := hmem 0
    omega
  have hpl : p (Fin.last _) = n := by
    have h0 : n ∈ Set.range p := by rw [hrange]; simp [bdry]
    obtain ⟨k, hk⟩ := h0
    have : p k ≤ p (Fin.last _) := p.monotone (Fin.le_last k)
    have := mem_bdry_le hn hT (hmem (Fin.last _))
    omega
  set ℓ : Fin (T.card + 1) → ℕ := fun i => p i.succ - p i.castSucc with hℓ
  have hpos : ∀ i, 0 < ℓ i := by
    intro i
    have : p i.castSucc < p i.succ := p.strictMono (Fin.castSucc_lt_succ)
    show 0 < p i.succ - p i.castSucc
    omega
  have hpre : ∀ (j : ℕ) (hj : j < T.card + 2), prefixSum ℓ j = p ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; rw [prefixSum_zero]; exact hp0.symm
    | succ j ih =>
      intro hj
      rw [prefixSum_succ ℓ (by omega), ih (by omega)]
      have : p ⟨j, by omega⟩ < p ⟨j + 1, hj⟩ := p.strictMono (Fin.mk_lt_mk.mpr (by omega))
      simp only [hℓ]
      have e1 : (⟨j, by omega⟩ : Fin (T.card + 1)).succ = ⟨j + 1, hj⟩ := rfl
      have e2 : (⟨j, by omega⟩ : Fin (T.card + 1)).castSucc = ⟨j, by omega⟩ := rfl
      rw [e1, e2]; omega
  have htot : ∑ i, ℓ i = n := by
    rw [← prefixSum_of_le ℓ (le_refl _), hpre _ (by omega)]
    exact hpl
  refine ⟨ℓ, hpos, htot, ?_⟩
  ext x
  unfold cutsOf
  simp only [Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [hpre j (by omega)]
    have hm := hmem ⟨j, by omega⟩
    have h1 : p 0 < p ⟨j, by omega⟩ := p.strictMono (Fin.mk_lt_mk.mpr hj.1)
    have h2 : p ⟨j, by omega⟩ < p (Fin.last _) :=
      p.strictMono (Fin.mk_lt_mk.mpr (by simp; omega))
    simp only [bdry, Finset.mem_insert] at hm
    rcases hm with h | h | h
    · omega
    · omega
    · exact h
  · intro hx
    have hx' : x ∈ bdry n T := by simp [bdry, hx]
    have : x ∈ Set.range p := by rw [hrange]; exact hx'
    obtain ⟨k, hk⟩ := this
    have hxT := Finset.mem_Ioo.mp (hT hx)
    have hk0 : 0 < (k : ℕ) := by
      by_contra h
      have hk0' : k = 0 := by
        apply Fin.ext
        rw [Fin.val_zero]
        omega
      subst hk0'
      rw [hp0] at hk; omega
    have hkl : (k : ℕ) < T.card + 1 := by
      by_contra h
      have hkl' : k = Fin.last _ := by ext; simp; omega
      subst hkl'
      rw [hpl] at hk; omega
    refine ⟨k, ⟨hk0, hkl⟩, ?_⟩
    rw [hpre k k.2]; exact hk

end Construction

section Counting

variable {r : ℕ}

theorem sortParts_comp_perm (a : Fin r → ℕ) (π : Equiv.Perm (Fin r)) :
    sortParts (fun i => a (π i)) = sortParts a := by
  unfold sortParts
  have := Multiset.map_univ_val_equiv π
  conv_rhs => rw [← this]
  rw [Multiset.map_map]; rfl

theorem sum_comp_perm (a : Fin r → ℕ) (π : Equiv.Perm (Fin r)) :
    ∑ i, a (π i) = ∑ i, a i := Equiv.sum_comp π a

theorem count_sortParts (a : Fin r → ℕ) (v : ℕ) :
    (sortParts a).count v = Fintype.card {x // a x = v} := by
  unfold sortParts
  rw [Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val, eq_comm]

theorem exists_perm_of_sortParts_eq {b c : Fin r → ℕ} (h : sortParts b = sortParts c) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, c (σ i) = b i := by
  have hc : ∀ v, Fintype.card {x // b x = v} = Fintype.card {x // c x = v} := by
    intro v; rw [← count_sortParts, ← count_sortParts, h]
  exact ⟨Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq (hc v)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem kappa_sortParts (a : Fin r → ℕ) :
    kappa (sortParts a) = Fintype.card {g : Equiv.Perm (Fin r) // a ∘ g = a} := by
  rw [DomMulAct.stabilizer_card']
  unfold kappa
  have : (sortParts a).toFinset = Finset.univ.image a := by
    ext x; simp [sortParts]
  rw [this]
  exact Finset.prod_congr rfl fun v _ => by rw [count_sortParts]

/-- The orderings of the labels realizing a given cut set. -/
noncomputable def fiber (a : Fin r → ℕ) (T : Finset ℕ) : Finset (Equiv.Perm (Fin r)) :=
  Finset.univ.filter fun π => cutsOf (fun i => a (π i)) = T

theorem card_fiber_pos (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) {n : ℕ} (hn : 0 < n)
    (hsum : ∑ i, a i = n) {T : Finset ℕ} (hT : T ⊆ Finset.Ioo 0 n)
    (hg : gaps n T = sortParts a) : (fiber a T).card = kappa (sortParts a) := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hsum; omega
    · exact h
  have hTcard : T.card + 1 = r := by
    have h1 : (gaps n T).card = T.card + 1 := by
      unfold gaps
      rw [Multiset.card_map]
      show (insert n T).card = _
      rw [Finset.card_insert_of_notMem]
      intro h; have := Finset.mem_Ioo.mp (hT h); omega
    have h2 : (sortParts a).card = r := by simp [sortParts]
    rw [← h2, ← hg, h1]
  subst hTcard
  obtain ⟨ℓ, hℓpos, hℓsum, hℓc⟩ := exists_list_of_cuts hn hT
  have hℓg : sortParts ℓ = sortParts a := by
    have h := gaps_cutsOf ℓ hℓpos (Nat.succ_pos _)
    rw [hℓsum, hℓc] at h
    rw [← h, hg]
  obtain ⟨σ, hσ⟩ := exists_perm_of_sortParts_eq hℓg
  rw [kappa_sortParts]
  -- fiber = {π | a ∘ π = ℓ} = {g ∘ σ'}
  have hfib : ∀ π : Equiv.Perm (Fin (T.card + 1)),
      π ∈ fiber a T ↔ (fun i => a (π i)) = ℓ := by
    intro π
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact list_eq_of_cutsOf_eq (fun i => ha _) hℓpos (Nat.succ_pos _)
        (by rw [sum_comp_perm, hsum, hℓsum]) (h.trans hℓc.symm)
    · intro h; rw [h, hℓc]
  rw [Fintype.card_subtype]
  apply Finset.card_nbij' (fun π => π * σ⁻¹) (fun g => g * σ)
  · intro π hπ
    have h := (hfib π).mp (Finset.mem_coe.mp hπ)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    funext j
    have h1 := congrFun h (σ⁻¹ j)
    have h2 := hσ (σ⁻¹ j)
    simp only [Function.comp, Equiv.Perm.coe_mul, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h1 h2 ⊢
    rw [h1, ← h2]
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg
    refine Finset.mem_coe.mpr ((hfib _).mpr ?_)
    funext j
    have h1 := congrFun hg (σ j)
    have h2 := hσ j
    simp only [Function.comp, Equiv.Perm.coe_mul] at h1 h2 ⊢
    rw [h1, h2]
  · intro π _; simp
  · intro g _; simp

end Counting

section Main

variable {n r : ℕ}

theorem cutsOf_subset_iff {a : Fin r → ℕ} {S : Finset ℕ} (π : Equiv.Perm (Fin r)) :
    (∀ j < r, 0 < j → partialSum a π j ∈ S) ↔ cutsOf (fun i => a (π i)) ⊆ S := by
  unfold cutsOf
  rw [Finset.image_subset_iff]
  constructor
  · intro h j hj
    rw [Finset.mem_Ioo] at hj
    exact h j hj.2 hj.1
  · intro h j hj hj0
    exact h j (Finset.mem_Ioo.mpr ⟨hj0, hj⟩)

/-- `lem:labels`, `eq:label-factor` (first identity).  For a positive labeled list `a` of total
`n > 0` and a composition of weight `n` with cut set `S`, the labeled count of `eq:K` is
`K_b(a) = κ(λ) m_β(λ)` with `λ = sort a`.  (`n > 0` excludes the empty list, whose labeled count
is `1` while the weight-zero composition is not a composition of a positive weight.) -/
theorem labeled_count_eq (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) (a : Fin r → ℕ)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) :
    K S a = kappa (sortParts a) * mult n S (sortParts a) := by
  classical
  have hS' : S ⊆ Finset.Ioo 0 n := hS
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hsum; omega
    · exact h
  unfold K
  have hmaps : Set.MapsTo (fun π : Equiv.Perm (Fin r) => cutsOf (fun i => a (π i)))
      ↑(Finset.univ.filter fun π : Equiv.Perm (Fin r) =>
        ∀ j < r, 0 < j → partialSum a π j ∈ S) ↑S.powerset := by
    intro π hπ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    exact (cutsOf_subset_iff π).mp hπ
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  unfold mult
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hfib : (Finset.univ.filter fun π : Equiv.Perm (Fin r) =>
        ∀ j < r, 0 < j → partialSum a π j ∈ S).filter
        (fun π => cutsOf (fun i => a (π i)) = T) = fiber a T := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fiber]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(cutsOf_subset_iff π).mpr (h ▸ hT), h⟩
  rw [hfib]
  by_cases hg : gaps n T = sortParts a
  · rw [if_pos hg]
    have := card_fiber_pos a ha hn hsum (hT.trans hS') hg
    rw [this, mul_one]
  · rw [if_neg hg, mul_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro π hπ
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    apply hg
    have hpos : ∀ i, 0 < a (π i) := fun i => ha _
    have h := gaps_cutsOf (fun i => a (π i)) hpos hr
    rw [Equiv.sum_comp π a, hsum, hπ] at h
    rw [h, sortParts_comp_perm]

theorem kappa_pos (lam : Multiset ℕ) : 0 < kappa lam :=
  Finset.prod_pos fun j _ => Nat.factorial_pos _

/-- `lem:labels`, `eq:label-factor` (second identity): two compositions of weight `n` with cut
sets `S, S'`.  `ΔK = κ(λ) Δm` in `ℤ`. -/
theorem labeled_diff_eq (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) :
    (K S a : ℤ) - K S' a =
      (kappa (sortParts a) : ℤ) * ((mult n S (sortParts a) : ℤ) - mult n S' (sortParts a)) := by
  rw [labeled_count_eq hn hS a ha hsum, labeled_count_eq hn hS' a ha hsum]
  push_cast; ring

/-- A multiset `λ` has distinct parts except possibly one repeated pair: every part occurs at
most twice, and at most one part occurs twice. -/
def DistinctExceptPair (lam : Multiset ℕ) : Prop :=
  (∀ j, lam.count j ≤ 2) ∧ (lam.toFinset.filter fun j => lam.count j = 2).card ≤ 1

theorem distinctExceptPair_of_kappa_le_two {lam : Multiset ℕ} (h : kappa lam ≤ 2) :
    DistinctExceptPair lam := by
  have hfac : ∀ j ∈ lam.toFinset, 1 ≤ (lam.count j).factorial := fun j _ => Nat.factorial_pos _
  have hle : ∀ j, lam.count j ≤ 2 := by
    intro j
    by_cases hj : j ∈ lam.toFinset
    · by_contra hc
      push_neg at hc
      have h3 : 3 ≤ (lam.count j).factorial :=
        le_trans (by decide : 3 ≤ (3 : ℕ).factorial) (Nat.factorial_le hc)
      have : (lam.count j).factorial ≤ kappa lam := by
        unfold kappa
        exact Finset.single_le_prod' hfac hj
      omega
    · simp [Multiset.count_eq_zero_of_notMem (by simpa using hj)]
  refine ⟨hle, ?_⟩
  by_contra hc
  push_neg at hc
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_filter] at hx hy
  have hsub : ({x, y} : Finset ℕ) ⊆ lam.toFinset := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx.1
    · exact hy.1
  have : ∏ j ∈ ({x, y} : Finset ℕ), (lam.count j).factorial ≤ kappa lam :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i _ _ => Nat.factorial_pos _)
  rw [Finset.prod_pair hxy, hx.2, hy.2] at this
  simp [Nat.factorial] at this
  omega

/-- `lem:labels` (final assertion).  If `0 < |ΔK| ≤ 2`, then `Δm ∈ {-2, -1, 1, 2}` and `λ` has
distinct parts except possibly one repeated pair. -/
theorem labeled_diff_small (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (h0 : (K S a : ℤ) - K S' a ≠ 0) (h2 : |(K S a : ℤ) - K S' a| ≤ 2) :
    ((mult n S (sortParts a) : ℤ) - mult n S' (sortParts a) ∈ ({-2, -1, 1, 2} : Set ℤ)) ∧
      DistinctExceptPair (sortParts a) := by
  rw [labeled_diff_eq hn hS hS' a ha hsum] at h0 h2
  set m : ℤ := (mult n S (sortParts a) : ℤ) - mult n S' (sortParts a) with hm
  set k : ℤ := (kappa (sortParts a) : ℤ) with hk
  have hkpos : 1 ≤ k := by have := kappa_pos (sortParts a); omega
  have hm0 : m ≠ 0 := fun h => h0 (by rw [h]; ring)
  have habs : |k * m| = k * |m| := by rw [abs_mul, abs_of_pos (by omega)]
  have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
  have hk2 : k ≤ 2 := by nlinarith
  have hm2 : |m| ≤ 2 := by nlinarith
  refine ⟨?_, distinctExceptPair_of_kappa_le_two (by omega)⟩
  rcases abs_cases m with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> omega

/-- `rem:modular-order`: a nonzero integer of magnitude at most two is nonzero modulo every
`q ≥ 3`.  Applied to `ΔK` it is converted first by `eq:label-factor`; see
`labeled_diff_small_not_dvd`. -/
theorem not_dvd_of_abs_le_two {D : ℤ} (hD0 : D ≠ 0) (hD : |D| ≤ 2) {q : ℕ} (hq : 3 ≤ q) :
    ¬ (q : ℤ) ∣ D := by
  intro h
  have := Int.le_of_dvd (abs_pos.mpr hD0) ((dvd_abs _ _).mpr h)
  omega

/-- `rem:modular-order`: under `0 < |ΔK| ≤ 2`, the ordinary discrepancy `Δm` is nonzero modulo
every `q ≥ 3`; no division by `κ(λ)` in a finite field is involved, since `Δm ∈ {±1, ±2}` is
read off over `ℤ` by `labeled_diff_small`. -/
theorem labeled_diff_small_not_dvd (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (h0 : (K S a : ℤ) - K S' a ≠ 0) (h2 : |(K S a : ℤ) - K S' a| ≤ 2) {q : ℕ} (hq : 3 ≤ q) :
    ¬ (q : ℤ) ∣ (mult n S (sortParts a) : ℤ) - mult n S' (sortParts a) := by
  obtain ⟨hm, _⟩ := labeled_diff_small hn hS hS' a ha hsum h0 h2
  have hm0 : (mult n S (sortParts a) : ℤ) - mult n S' (sortParts a) ≠ 0 := by
    intro h; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm; omega
  refine not_dvd_of_abs_le_two hm0 ?_ hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h | h | h | h <;> rw [h] <;> norm_num

/-- `rem:modular-order`, the worked example: `K_b(1,1,1) = 6` for `β = (1,1,1)`, while the
ordinary coefficient `m_β(1,1,1)` is one. -/
theorem labeled_example_ones : K {1, 2} (fun _ : Fin 3 => 1) = 6 ∧ mult 3 {1, 2} {1, 1, 1} = 1 := by
  decide

end Main

end SkewRibbonCoarsenings
