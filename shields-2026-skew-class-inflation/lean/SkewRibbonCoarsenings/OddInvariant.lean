/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/OddInvariant.lean
import SkewRibbonCoarsenings.AlternatingNear

/-!
# The all-odd invariant lifts

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:depth`
(`thm:lift`, `eq:OA-lift`).

A word of `N` alternating cells `R, S, R, …` together with a set `A` of available cell boundaries
is the cut set `wordBd`.  Its coarsening polynomial decomposes over the retained subsets `B ⊆ A`
as a product of segment inventories (`G_wordBd`), each segment being a pure alternating
near-concatenation (`segG`), with start parity tracked by decorating every block of a coarsening
with the parity of its left endpoint (`gapsD`).  Reflection (`G_revCuts`'s block-level form,
`gapsD_revCuts`) exchanges the two orientations of each odd-cell segment and fixes each even-cell
segment (`segProd_refl_eq`, `segProd_refl_sub`).  `lift_diff_ordGe` combines this with the
telescoping product of `ordGE_multiset_prod_sub`, and `OA_lift` is `eq:OA-lift`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial Finset

/-- The predecessor of `x` among the retained cuts `T` (zero if there is none). -/
def predOf (T : Finset ℕ) (x : ℕ) : ℕ := (T.filter (· < x)).sup id

/-- Block lengths of the coarsening retaining `T`, each decorated with the parity of its left
endpoint shifted by the phase `p`. -/
def gapsD (n p : ℕ) (T : Finset ℕ) : Multiset (ℕ × ℕ) :=
  (insert n T).val.map fun x => (x - predOf T x, (p + predOf T x) % 2)

lemma map_fst_gapsD (n p : ℕ) (T : Finset ℕ) : (gapsD n p T).map Prod.fst = gaps n T := by
  simp [gapsD, gaps, predOf, Multiset.map_map]

lemma gapsD_empty (n p : ℕ) : gapsD n p ∅ = {(n, p % 2)} := by
  simp [gapsD, predOf]

lemma gapsD_glue (n n' p : ℕ) (T1 T2 : Finset ℕ) (h1 : ∀ x ∈ T1, x < n)
    (hn' : 0 < n') (h2 : ∀ x ∈ T2, 0 < x ∧ x < n') :
    gapsD (n + n') p (T1 ∪ T2.image (n + ·) ∪ {n}) = gapsD n p T1 + gapsD n' (p + n) T2 := by
  set X := T1 ∪ T2.image (n + ·) ∪ {n} with hX
  have hset : insert (n + n') X = insert n T1 ∪ (insert n' T2).image (n + ·) := by
    ext x
    simp only [hX, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
      Finset.image_insert]
    grind
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
  unfold gapsD
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
    have : predOf X x = predOf T1 x := by
      unfold predOf
      congr 1
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
    rw [this]
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
    simp only [Function.comp, predOf, hfil]
    rw [sup_glue n T1 _ h1]
    refine Prod.ext ?_ ?_ <;> simp only <;> omega

lemma gapsD_shift (n p c : ℕ) (T : Finset ℕ) :
    gapsD n (p + c) T = (gapsD n p T).map fun x => (x.1, (x.2 + c) % 2) := by
  unfold gapsD
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp]
  refine Prod.ext rfl ?_
  simp only
  omega

/-- Reflection of a decorated block: same length, start parity of the reflected block. -/
def flipD (n : ℕ) (x : ℕ × ℕ) : ℕ × ℕ := (x.1, (x.2 + x.1 + n) % 2)

lemma gapsD_revCuts (n : ℕ) (p : ℕ) (T : Finset ℕ) (hT : IsCutSet n T) :
    gapsD n p (revCuts n T) = (gapsD n p T).map (flipD n) := by
  obtain ⟨c, hc⟩ : ∃ c, T.card = c := ⟨_, rfl⟩
  induction c generalizing n p T with
  | zero =>
    rw [Finset.card_eq_zero] at hc
    subst hc
    simp [revCuts, gapsD_empty, flipD]
    omega
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
    have hg1 : gapsD n p T = gapsD m p T1 + {(n - m, (p + m) % 2)} := by
      have := gapsD_glue m (n - m) p T1 ∅ (fun x hx => (hT1m x hx).2) (by omega) (by simp)
      rw [show m + (n - m) = n by omega, gapsD_empty] at this
      rw [hTeq]; simpa using this
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
    have hg2 : gapsD n p (revCuts n T) =
        {(n - m, p % 2)} + gapsD m (p + (n - m)) (revCuts m T1) := by
      have := gapsD_glue (n - m) m p ∅ (revCuts m T1) (by simp) (by omega) hrc
      rw [show n - m + m = n by omega, gapsD_empty] at this
      rw [hrev, show (revCuts m T1).image ((n - m) + ·) ∪ {n - m} =
        ∅ ∪ (revCuts m T1).image ((n - m) + ·) ∪ {n - m} by simp, this]
    rw [hg2, hg1, ih m (p + (n - m)) T1 hT1c hcard, gapsD_shift, Multiset.map_map,
      Multiset.map_add, Multiset.map_singleton, add_comm]
    congr 1
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp, flipD]
      refine Prod.ext rfl ?_
      simp only
      omega
    · simp only [flipD]
      congr 1
      refine Prod.ext rfl ?_
      simp only
      omega

/-! ### Decomposition of a word with available boundaries into segments -/

section Decomp

variable {w : ℕ} {R S : Finset ℕ}

/-- The inventory of a pure alternating word of `L` cells, started at phase `q`; a block of length
`L` with start parity `q` is decorated as `(L, q)`. -/
noncomputable def segG (w : ℕ) (R S : Finset ℕ) (x : ℕ × ℕ) : Lam :=
  G (x.1 * w) (wordCuts w R S x.2 x.1)

lemma segG_congr {p q : ℕ} (h : p % 2 = q % 2) (L : ℕ) :
    segG w R S (L, p) = segG w R S (L, q) := by
  unfold segG
  rw [wordCuts_congr h]

/-- The product of the segment inventories of the coarsening retaining the boundaries `B`. -/
noncomputable def segProd (w : ℕ) (R S : Finset ℕ) (N p : ℕ) (B : Finset ℕ) : Lam :=
  ((gapsD N p B).map (segG w R S)).prod

lemma segProd_insert_min {N p a : ℕ} {B : Finset ℕ} (hN : a < N) (hB : ∀ x ∈ B, a < x ∧ x < N) :
    segProd w R S N p (insert a B) =
      segG w R S (a, p % 2) * segProd w R S (N - a) (p + a) (B.image (· - a)) := by
  have h := gapsD_glue a (N - a) p ∅ (B.image (· - a)) (by simp) (by omega) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have := hB y hy
    omega)
  rw [show a + (N - a) = N by omega] at h
  have hset : (∅ : Finset ℕ) ∪ (B.image (· - a)).image (a + ·) ∪ {a} = insert a B := by
    ext x
    simp only [Finset.empty_union, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
      Finset.mem_insert]
    constructor
    · rintro (⟨z, ⟨y, hy, rfl⟩, rfl⟩ | rfl)
      · right; have := hB y hy; rwa [show a + (y - a) = y by omega]
      · left; rfl
    · rintro (rfl | hx)
      · right; rfl
      · left; refine ⟨x - a, ⟨x, hx, rfl⟩, ?_⟩
        have := hB x hx; omega
  rw [hset] at h
  unfold segProd
  rw [h, gapsD_empty, Multiset.map_add, Multiset.prod_add]
  simp

lemma segProd_empty (p N : ℕ) : segProd w R S N p ∅ = segG w R S (N, p % 2) := by
  simp [segProd, gapsD_empty]

lemma image_sub_add {a : ℕ} {A : Finset ℕ} (h : ∀ x ∈ A, a < x) :
    (A.image (· - a)).image (a + ·) = A := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have := h z hz
    rwa [show a + (z - a) = z by omega]
  · intro hx
    exact ⟨x - a, ⟨x, hx, rfl⟩, by have := h x hx; omega⟩

lemma image_add_sub (a : ℕ) (A : Finset ℕ) : (A.image (a + ·)).image (· - a) = A := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨a + x, ⟨x, hx, rfl⟩, by simp⟩

/-- `eq:OA-lift`, grouping by retained cell boundaries: the coarsening polynomial of a word with
available cell boundaries `A` is the sum, over the retained subsets `B ⊆ A`, of the products of
the segment inventories.

**Differs from the paper's route.**  The paper states the grouping in words; here it is the
proved decomposition lemma `G_wordBd`, by induction on `A` through `eq:seam` at the first retained
boundary. -/
theorem G_wordBd (hw : 0 < w) (hR : IsCutSet w R) (hS : IsCutSet w S) :
    ∀ (c p N : ℕ) (A : Finset ℕ), A.card = c → (∀ x ∈ A, 0 < x ∧ x < N) →
      G (N * w) (wordBd w R S p N A) = ∑ B ∈ A.powerset, segProd w R S N p B := by
  intro c
  induction c with
  | zero =>
    intro p N A hc _
    rw [Finset.card_eq_zero] at hc
    subst hc
    rw [wordBd_empty]
    simp only [Finset.powerset_empty, Finset.sum_singleton, segProd_empty, segG]
    rw [wordCuts_congr (p' := p % 2) (by omega)]
  | succ c ih =>
    intro p N A hc hA
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    set a := A.min' hne with ha
    have haA : a ∈ A := Finset.min'_mem A hne
    set A' := A.erase a with hA'
    have hA'gt : ∀ x ∈ A', a < x ∧ x < N := by
      intro x hx
      have hxA := Finset.mem_of_mem_erase hx
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      exact ⟨lt_of_le_of_ne (Finset.min'_le A x hxA) (Ne.symm hxa), (hA x hxA).2⟩
    have hAeq : A = insert a A' := (Finset.insert_erase haA).symm
    have hcard : A'.card = c := by rw [hA', Finset.card_erase_of_mem haA]; omega
    obtain ⟨ha0, haN⟩ := hA a haA
    have haA' : a ∉ A' := Finset.notMem_erase a A
    set Br := A'.image (· - a) with hBrdef
    have hBr : ∀ x ∈ Br, 0 < x ∧ x < N - a := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have := hA'gt y hy
      omega
    have hBrcard : Br.card = c := by
      rw [hBrdef, Finset.card_image_of_injOn, hcard]
      intro x hx y hy hxy
      have := hA'gt x hx
      have := hA'gt y hy
      simp only at hxy
      omega
    have hsum : a * w + (N - a) * w = N * w := by rw [← add_mul]; congr 1; omega
    have hseam := G_concat_cuts (a * w) ((N - a) * w) (wordCuts w R S p a)
      (wordBd w R S (p + a) (N - a) Br) (Nat.mul_pos ha0 hw) (Nat.mul_pos (by omega) hw)
      (isCutSet_wordCuts hR hS p a) (isCutSet_wordBd hw hR hS (p + a) (N - a) hBr)
    have hnear : nearCuts (a * w) (wordCuts w R S p a) (wordBd w R S (p + a) (N - a) Br) =
        wordBd w R S p N A' := by
      have := wordBd_near w R S p a (N - a) ∅ Br
      rw [wordBd_empty, show a + (N - a) = N by omega, Finset.empty_union,
        hBrdef, image_sub_add (fun x hx => (hA'gt x hx).1)] at this
      exact this
    rw [hsum, concatCuts_eq_insert_near, hnear] at hseam
    have hLHS : wordBd w R S p N A = insert (a * w) (wordBd w R S p N A') := by
      rw [hAeq]; exact wordBd_insert w R S p N a A'
    rw [hLHS, hseam, ih p N A' hcard (fun x hx => ⟨by have := hA'gt x hx; omega, (hA'gt x hx).2⟩),
      ih (p + a) (N - a) Br hBrcard hBr]
    rw [hAeq, Finset.sum_powerset_insert haA']
    rw [add_comm]
    congr 1
    -- the terms retaining the cut `a`
    have h1 : ∀ B ∈ A'.powerset, segProd w R S N p (insert a B) =
        segG w R S (a, p % 2) * segProd w R S (N - a) (p + a) (B.image (· - a)) := by
      intro B hB
      exact segProd_insert_min haN (fun x hx => hA'gt x (Finset.mem_powerset.mp hB hx))
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : ∑ B ∈ A'.powerset, segProd w R S (N - a) (p + a) (B.image (· - a)) =
        ∑ B ∈ Br.powerset, segProd w R S (N - a) (p + a) B := by
      refine Finset.sum_nbij' (fun B => B.image (· - a)) (fun B => B.image (a + ·)) ?_ ?_ ?_ ?_
        (fun _ _ => rfl)
      · intro B hB
        rw [Finset.mem_powerset] at hB ⊢
        exact Finset.image_subset_image hB
      · intro B hB
        rw [Finset.mem_powerset] at hB ⊢
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hB hy)
        have := hA'gt z hz
        rwa [show a + (z - a) = z by omega]
      · intro B hB
        rw [Finset.mem_powerset] at hB
        exact image_sub_add (fun x hx => (hA'gt x (hB hx)).1)
      · intro B hB
        exact image_add_sub a B
    rw [h2]
    unfold segG
    rw [wordCuts_congr (p' := p % 2) (by omega)]

end Decomp

section Reflect

variable {w : ℕ} {R S : Finset ℕ}

lemma predOf_mem {T : Finset ℕ} (x : ℕ) : predOf T x = 0 ∨ predOf T x ∈ T := by
  unfold predOf
  by_cases h : (T.filter (· < x)).Nonempty
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup _ h id
    right
    rw [hsup]
    exact (Finset.mem_filter.mp ha).1
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h]; rfl

lemma card_gapsD (n p : ℕ) (T : Finset ℕ) : Multiset.card (gapsD n p T) = (insert n T).card := by
  unfold gapsD
  rw [Multiset.card_map]
  rfl

lemma gapsD_fst_pos {n p : ℕ} {T : Finset ℕ} (hn : 0 < n) (hT : IsCutSet n T) :
    ∀ x ∈ gapsD n p T, 0 < x.1 := by
  intro x hx
  have : x.1 ∈ (gapsD n p T).map Prod.fst := Multiset.mem_map_of_mem _ hx
  rw [map_fst_gapsD] at this
  exact gaps_pos hn hT _ this

lemma gapsD_fst_even {n p : ℕ} {T : Finset ℕ} (hn : n % 2 = 0) (hT : ∀ x ∈ T, x % 2 = 0) :
    ∀ x ∈ gapsD n p T, x.1 % 2 = 0 := by
  intro x hx
  unfold gapsD at hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  have hy' : y % 2 = 0 := by
    rcases Finset.mem_insert.mp hy with rfl | h
    · exact hn
    · exact hT y h
  have hp : predOf T y % 2 = 0 := by
    rcases predOf_mem (T := T) y with h | h
    · rw [h]
    · exact hT _ h
  have : predOf T y ≤ y := by
    unfold predOf
    exact Finset.sup_le fun b hb => (Finset.mem_filter.mp hb).2.le
  simp only
  omega

lemma segG_ordGe_one (hw : 0 < w) (hR : IsCutSet w R) (hS : IsCutSet w S) {L : ℕ} (hL : 0 < L)
    (q : ℕ) : ordGE 1 (segG w R S (L, q)) :=
  ordGE_G_one (Nat.mul_pos hL hw) (isCutSet_wordCuts hR hS q L)

lemma segG_flip_even {N L q : ℕ} (hN : N % 2 = 0) (hL : L % 2 = 0) :
    segG w R S (flipD N (L, q)) = segG w R S (L, q) := by
  unfold flipD
  exact segG_congr (by simp only; omega) L

lemma ordGE_multiset_prod_sub {ι : Type*} {s0 : ℕ} (M : Multiset ι) (f g : ι → Lam)
    (hf : ∀ x ∈ M, ordGE 1 (f x)) (hg : ∀ x ∈ M, ordGE 1 (g x))
    (hfg : ∀ x ∈ M, ordGE (s0 + 1) (f x - g x)) :
    ordGE (s0 + Multiset.card M) ((M.map f).prod - (M.map g).prod) := by
  induction M using Multiset.induction with
  | empty => simpa using ordGE_zero (R := ℤ) s0
  | cons a M ih =>
    have hf' : ∀ x ∈ M, ordGE 1 (f x) := fun x hx => hf x (Multiset.mem_cons_of_mem hx)
    have hg' : ∀ x ∈ M, ordGE 1 (g x) := fun x hx => hg x (Multiset.mem_cons_of_mem hx)
    have hfg' : ∀ x ∈ M, ordGE (s0 + 1) (f x - g x) :=
      fun x hx => hfg x (Multiset.mem_cons_of_mem hx)
    have ih' := ih hf' hg' hfg'
    have e : ((a ::ₘ M).map f).prod - ((a ::ₘ M).map g).prod =
        f a * ((M.map f).prod - (M.map g).prod) + (f a - g a) * (M.map g).prod := by
      simp only [Multiset.map_cons, Multiset.prod_cons]; ring
    rw [e]
    have h1 := ordGE_mul (hf a (Multiset.mem_cons_self _ _)) ih'
    have hgp : ordGE (Multiset.card M) (M.map g).prod := by
      have := ordGE_multiset_prod (M.map g) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        exact hg' y hy)
      simpa using this
    have h2 := ordGE_mul (hfg a (Multiset.mem_cons_self _ _)) hgp
    rw [Multiset.card_cons]
    exact ordGE_add (ordGE_mono (by omega) h1) (ordGE_mono (by omega) h2)

/-- `eq:OA-lift`, even-segment case: the inventory of the coarsening retaining the boundary set `B`, against that of the reflected
boundary set: equal when all segments have even length. -/
lemma segProd_refl_eq {N : ℕ} (hN : N % 2 = 0) {B : Finset ℕ} (hB : IsCutSet N B)
    (hev : ∀ x ∈ B, x % 2 = 0) :
    segProd w R S N 0 (revCuts N B) = segProd w R S N 0 B := by
  unfold segProd
  rw [gapsD_revCuts N 0 B hB, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_)
  have hx' := gapsD_fst_even hN hev x hx
  obtain ⟨L, q⟩ := x
  exact segG_flip_even hN hx'

/-- `eq:OA-lift`, telescoping step: reflection changes the segment inventory only at order `s0 + |B| + 1`, given the all-odd
invariant, once some retained boundary exists in each parity class: here `|B| ≥ 2`. -/
lemma segProd_refl_sub (hw : 0 < w) (hR : IsCutSet w R) (hS : IsCutSet w S) {s0 N : ℕ}
    (hN : N % 2 = 0) (hOA : ∀ j : ℕ, ordGE (s0 + 1)
      (segG w R S (2 * j + 1, 0) - segG w R S (2 * j + 1, 1)))
    {B : Finset ℕ} (hB : IsCutSet N B) (hN0 : 0 < N) :
    ordGE (s0 + (B.card + 1)) (segProd w R S N 0 B - segProd w R S N 0 (revCuts N B)) := by
  unfold segProd
  rw [gapsD_revCuts N 0 B hB, Multiset.map_map]
  have hcard : Multiset.card (gapsD N 0 B) = B.card + 1 := by
    rw [card_gapsD, Finset.card_insert_of_notMem]
    intro h
    exact lt_irrefl _ (Finset.mem_Ioo.mp (hB h)).2
  have hpos := gapsD_fst_pos (p := 0) hN0 hB
  have := ordGE_multiset_prod_sub (s0 := s0) (gapsD N 0 B) (segG w R S)
    (segG w R S ∘ flipD N)
    (fun x hx => by
      obtain ⟨L, q⟩ := x
      exact segG_ordGe_one hw hR hS (hpos _ hx) q)
    (fun x hx => by
      obtain ⟨L, q⟩ := x
      exact segG_ordGe_one hw hR hS (hpos _ hx) _)
    (fun x hx => by
      obtain ⟨L, q⟩ := x
      by_cases hL : L % 2 = 0
      · simp only [Function.comp]
        rw [segG_flip_even hN hL, sub_self]
        exact ordGE_zero _
      · have hL' : L = 2 * (L / 2) + 1 := by omega
        simp only [Function.comp, flipD]
        rw [hL']
        have hoa := hOA (L / 2)
        rcases Nat.mod_two_eq_zero_or_one q with hq | hq
        · rw [segG_congr (p := q) (q := 0) (by omega),
            segG_congr (p := (q + (2 * (L / 2) + 1) + N) % 2) (q := 1) (by omega)]
          exact hoa
        · rw [segG_congr (p := q) (q := 1) (by omega),
            segG_congr (p := (q + (2 * (L / 2) + 1) + N) % 2) (q := 0) (by omega)]
          have := ordGE_sub (ordGE_zero (R := ℤ) (s0 + 1)) hoa
          simpa using this)
  rw [hcard] at this
  exact this

end Reflect

/-- The available cell boundaries (in cell units) of `m` lifted factors alternating between the
local boundary patterns `X` (even index) and `Y` (odd index); each lifted factor has six cells. -/
def liftBd (X Y : Finset ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun i => (if i % 2 = 0 then X else Y).image (6 * i + ·)

lemma mem_liftBd {X Y : Finset ℕ} {m x : ℕ} :
    x ∈ liftBd X Y m ↔ ∃ i < m, ∃ y ∈ (if i % 2 = 0 then X else Y), 6 * i + y = x := by
  simp [liftBd]

lemma liftBd_odd_step (X Y : Finset ℕ) (j : ℕ) :
    liftBd X Y (2 * j + 3) =
      liftBd X Y (2 * j + 1) ∪ (Y ∪ X.image (6 + ·)).image (6 * (2 * j + 1) + ·) := by
  ext x
  simp only [mem_liftBd, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    by_cases h1 : i < 2 * j + 1
    · exact Or.inl ⟨i, h1, y, hy, rfl⟩
    · right
      by_cases h2 : i = 2 * j + 1
      · subst h2
        have : ((2 * j + 1) % 2 = 0) = False := by simp [Nat.add_mod]
        rw [if_neg (by omega)] at hy
        exact ⟨y, Or.inl hy, rfl⟩
      · have h3 : i = 2 * j + 2 := by omega
        subst h3
        rw [if_pos (by omega)] at hy
        exact ⟨6 + y, Or.inr ⟨y, hy, rfl⟩, by ring⟩
  · rintro (⟨i, hi, y, hy, rfl⟩ | ⟨z, (hz | ⟨y, hy, rfl⟩), rfl⟩)
    · exact ⟨i, by omega, y, hy, rfl⟩
    · refine ⟨2 * j + 1, by omega, z, ?_, rfl⟩
      rw [if_neg (by omega)]; exact hz
    · refine ⟨2 * j + 2, by omega, y, ?_, by ring⟩
      rw [if_pos (by omega)]; exact hy

lemma altCuts_lift (w : ℕ) (R S X Y : Finset ℕ) (j : ℕ) :
    altCuts (6 * w) (wordBd w R S 0 6 X) (wordBd w R S 0 6 Y) j =
      wordBd w R S 0 (6 * (2 * j + 1)) (liftBd X Y (2 * j + 1)) := by
  induction j with
  | zero =>
    simp only [altCuts, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    unfold wordBd liftBd
    simp
  | succ j ih =>
    rw [altCuts, ih]
    have h1 : nearCuts (6 * w) (wordBd w R S 0 6 Y) (wordBd w R S 0 6 X) =
        wordBd w R S 0 12 (Y ∪ X.image (6 + ·)) := by
      rw [wordBd_near' w R S 6 6 (by omega)]
    have e1 : (2 * j + 1) * (6 * w) = (6 * (2 * j + 1)) * w := by ring
    rw [h1, e1, wordBd_near' w R S (6 * (2 * j + 1)) 12 (by omega),
      show 6 * (2 * j + 1) + 12 = 6 * (2 * (j + 1) + 1) by ring,
      show 2 * (j + 1) + 1 = 2 * j + 3 by ring, liftBd_odd_step]


lemma liftBd_bounds (X Y : Finset ℕ) (hX : ∀ x ∈ X, 0 < x ∧ x < 6) (hY : ∀ x ∈ Y, 0 < x ∧ x < 6)
    (m : ℕ) : ∀ x ∈ liftBd X Y m, 0 < x ∧ x < 6 * m := by
  intro x hx
  obtain ⟨i, hi, y, hy, rfl⟩ := mem_liftBd.mp hx
  have : 0 < y ∧ y < 6 := by
    split_ifs at hy
    · exact hX y hy
    · exact hY y hy
  omega

lemma revCuts_liftBd (m : ℕ) (hm : m % 2 = 1) :
    revCuts (6 * m) (liftBd {2, 3} {3, 4} m) = liftBd {3, 4} {2, 3} m := by
  ext x
  rw [revCuts_mem, mem_liftBd]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, z, hz, rfl⟩ := mem_liftBd.mp hy
    refine ⟨m - 1 - i, by omega, 6 - z, ?_, ?_⟩
    · by_cases hi2 : i % 2 = 0
      · have h2 : (m - 1 - i) % 2 = 0 := by omega
        rw [if_pos hi2] at hz
        rw [if_pos h2]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        omega
      · have h2 : ¬ (m - 1 - i) % 2 = 0 := by omega
        rw [if_neg hi2] at hz
        rw [if_neg h2]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        omega
    · by_cases hi2 : i % 2 = 0
      · rw [if_pos hi2] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        omega
      · rw [if_neg hi2] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        omega
  · rintro ⟨i, hi, z, hz, rfl⟩
    refine ⟨6 * (m - 1 - i) + (6 - z), mem_liftBd.mpr ⟨m - 1 - i, by omega, 6 - z, ?_, rfl⟩, ?_⟩
    · by_cases hi2 : i % 2 = 0
      · have h2 : (m - 1 - i) % 2 = 0 := by omega
        rw [if_pos hi2] at hz
        rw [if_pos h2]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        omega
      · have h2 : ¬ (m - 1 - i) % 2 = 0 := by omega
        rw [if_neg hi2] at hz
        rw [if_neg h2]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        omega
    · by_cases hi2 : i % 2 = 0
      · rw [if_pos hi2] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        omega
      · rw [if_neg hi2] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        omega

lemma liftBd_odd (m x : ℕ) (hx : x % 2 = 1) :
    x ∈ liftBd {2, 3} {3, 4} m ↔ x ∈ liftBd {3, 4} {2, 3} m := by
  simp only [mem_liftBd]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    refine ⟨i, hi, y, ?_, rfl⟩
    split_ifs at hy ⊢ <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢ <;> omega
  · rintro ⟨i, hi, y, hy, rfl⟩
    refine ⟨i, hi, y, ?_, rfl⟩
    split_ifs at hy ⊢ <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢ <;> omega

/-- Reflect a retained boundary set unless all its elements are odd. -/
def reflUnlessOdd (N : ℕ) (B : Finset ℕ) : Finset ℕ :=
  open Classical in if ∀ x ∈ B, x % 2 = 1 then B else revCuts N B

lemma reflUnlessOdd_mem {N : ℕ} {P Q : Finset ℕ} (hPQ : revCuts N P = Q)
    (hodd : ∀ x, x % 2 = 1 → (x ∈ P ↔ x ∈ Q)) {B : Finset ℕ} (hB : B ∈ P.powerset) :
    reflUnlessOdd N B ∈ Q.powerset := by
  rw [Finset.mem_powerset] at hB ⊢
  unfold reflUnlessOdd
  split_ifs with h
  · intro x hx; exact (hodd x (h x hx)).mp (hB hx)
  · rw [← hPQ]; exact Finset.image_subset_image hB

lemma reflUnlessOdd_invol {N : ℕ} (hN : N % 2 = 0) {B : Finset ℕ} (hB : IsCutSet N B) :
    reflUnlessOdd N (reflUnlessOdd N B) = B := by
  unfold reflUnlessOdd
  by_cases h : ∀ x ∈ B, x % 2 = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]
    have h' : ¬ ∀ x ∈ revCuts N B, x % 2 = 1 := by
      intro hall
      apply h
      intro x hx
      have := hall (N - x) (revCuts_mem.mpr ⟨x, hx, rfl⟩)
      have hxN := (Finset.mem_Ioo.mp (hB hx)).2
      omega
    rw [if_neg h']
    exact revCuts_revCuts hB

/-- `eq:OA-lift`, one odd length (the core of the argument by telescoping): the lifted pair, for
`m` lifted factors with `m` odd, differs only at ordinary degree `s + 2` or higher.  The case
"both parities occur" needs at least two retained boundaries, so at least three segments, which is
the `B.card + 1 ≥ 3` in `segProd_refl_sub`.  The core of `eq:OA-lift` at one odd length: the lifted pair differs only at ordinary degree
`s + 2` or higher, given the all-odd invariant for the old cells. -/
theorem lift_diff_ordGe {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) {s : ℕ} (hs : 1 ≤ s)
    (hOA : ∀ j : ℕ, ordGE s (segG w R S (2 * j + 1, 0) - segG w R S (2 * j + 1, 1)))
    (m : ℕ) (hm : m % 2 = 1) :
    ordGE (s + 2) (G (6 * m * w) (wordBd w R S 0 (6 * m) (liftBd {2, 3} {3, 4} m)) -
      G (6 * m * w) (wordBd w R S 0 (6 * m) (liftBd {3, 4} {2, 3} m))) := by
  obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
  have hN : (6 * m) % 2 = 0 := by omega
  have hN0 : 0 < 6 * m := by omega
  have h23 : ∀ x ∈ ({2, 3} : Finset ℕ), 0 < x ∧ x < 6 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega
  have h34 : ∀ x ∈ ({3, 4} : Finset ℕ), 0 < x ∧ x < 6 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega
  have hA1c := liftBd_bounds {2, 3} {3, 4} h23 h34 m
  have hA2c := liftBd_bounds {3, 4} {2, 3} h34 h23 m
  have hc1 : IsCutSet (6 * m) (liftBd {2, 3} {3, 4} m) :=
    fun x hx => Finset.mem_Ioo.mpr (hA1c x hx)
  have hr1 := revCuts_liftBd m hm
  have hr2 : revCuts (6 * m) (liftBd {3, 4} {2, 3} m) = liftBd {2, 3} {3, 4} m := by
    rw [← hr1]; exact revCuts_revCuts hc1
  rw [G_wordBd hw hR hS _ 0 (6 * m) _ rfl hA1c, G_wordBd hw hR hS _ 0 (6 * m) _ rfl hA2c]
  have hsum : ∑ B ∈ (liftBd {3, 4} {2, 3} m).powerset, segProd w R S (6 * m) 0 B =
      ∑ B ∈ (liftBd {2, 3} {3, 4} m).powerset,
        segProd w R S (6 * m) 0 (reflUnlessOdd (6 * m) B) := by
    symm
    refine Finset.sum_nbij' (reflUnlessOdd (6 * m)) (reflUnlessOdd (6 * m)) ?_ ?_ ?_ ?_
      (fun _ _ => rfl)
    · intro B hB
      exact reflUnlessOdd_mem hr1 (liftBd_odd m) hB
    · intro B hB
      exact reflUnlessOdd_mem hr2 (fun x hx => (liftBd_odd m x hx).symm) hB
    · intro B hB
      exact reflUnlessOdd_invol hN (fun x hx => hc1 ((Finset.mem_powerset.mp hB) hx))
    · intro B hB
      exact reflUnlessOdd_invol hN (fun x hx => Finset.mem_Ioo.mpr (hA2c x ((Finset.mem_powerset.mp hB) hx)))
  rw [hsum, ← Finset.sum_sub_distrib]
  refine ordGE_sum _ _ fun B hB => ?_
  have hBc : IsCutSet (6 * m) B := fun x hx => Finset.mem_Ioo.mpr (hA1c x ((Finset.mem_powerset.mp hB) hx))
  have hOA' : ∀ j : ℕ, ordGE (s0 + 1)
      (segG w R S (2 * j + 1, 0) - segG w R S (2 * j + 1, 1)) := hOA
  unfold reflUnlessOdd
  by_cases hodd : ∀ x ∈ B, x % 2 = 1
  · rw [if_pos hodd, sub_self]; exact ordGE_zero _
  · rw [if_neg hodd]
    by_cases hev : ∀ x ∈ B, x % 2 = 0
    · rw [segProd_refl_eq hN hBc hev, sub_self]; exact ordGE_zero _
    · push_neg at hodd hev
      obtain ⟨a, haB, ha⟩ := hodd
      obtain ⟨b, hbB, hb⟩ := hev
      have hcard : 2 ≤ B.card := by
        rw [Nat.succ_le_iff, Finset.one_lt_card]
        exact ⟨a, haB, b, hbB, by rintro rfl; omega⟩
      have := segProd_refl_sub hw hR hS hN hOA' hBc hN0
      exact ordGE_mono (by omega) this

lemma segG_zero_eq (w : ℕ) (R S : Finset ℕ) (j : ℕ) :
    segG w R S (2 * j + 1, 0) = G ((2 * j + 1) * w) (altCuts w R S j) := by
  unfold segG; rw [altCuts_eq_wordCuts]

lemma segG_one_eq (w : ℕ) (R S : Finset ℕ) (j : ℕ) :
    segG w R S (2 * j + 1, 1) = G ((2 * j + 1) * w) (altCuts w S R j) := by
  unfold segG
  rw [altCuts_eq_wordCuts]
  show G _ (wordCuts w R S (0 + 1) _) = _
  rw [wordCuts_swap]

/-- `eq:OA-lift`: for `s ≥ 2`, the all-odd invariant `OA_s(R,S)` implies `OA_{s+2}(R',S')` for the
lifted roots `R' = E · (F ⊙ E)`, `S' = (E ⊙ F) · E` of `eq:sharpness-lift`.

**Differs from the paper's route.**  The paper splits the retained boundary sets `B` into
"only odd", "only even" and "both parities" and reflects in each case; here a single involution
`B ↦ B` (all boundaries odd) / `B ↦ revCuts B` (otherwise) matches the terms of the two sides, and
the three cases are separated inside `lift_diff_ordGe`. -/
theorem OA_lift {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R) (hS : IsCutSet w S)
    {s : ℕ} (hs : 2 ≤ s) (h : OA w R S s) : OA (6 * w) (liftR w R S) (liftS w R S) (s + 2) := by
  rw [OA_iff] at h ⊢
  have hOA : ∀ j : ℕ, ordGE s (segG w R S (2 * j + 1, 0) - segG w R S (2 * j + 1, 1)) := by
    intro j
    rw [segG_zero_eq, segG_one_eq]
    exact h j
  intro j
  rw [liftR_eq, liftS_eq, altCuts_lift, altCuts_lift]
  have e : (2 * j + 1) * (6 * w) = 6 * (2 * j + 1) * w := by ring
  rw [e]
  exact lift_diff_ordGe hw hR hS (by omega) hOA (2 * j + 1) (by omega)

end SkewRibbonCoarsenings
