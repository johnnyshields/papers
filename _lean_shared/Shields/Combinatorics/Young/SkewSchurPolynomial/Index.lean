/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Shields.Combinatorics.Young.SkewSchurPolynomial.Super

/-!
# The index dictionary: the hook criterion as a packing rule on a row set

The hook criterion of `Shields.Combinatorics.Young.SkewSchurPolynomial.Super` is a statement
about the parts of `λ` and `μ`.  A packing argument wants a statement about a row set alone,
and `betaDiagram` is what connects them.  Everything here is a self-contained claim about
`Finset ℕ` and `YoungDiagram`; no tableau appears.

## Main definitions

* `Shields.betaDiagram`, `Shields.belowCount`, `Shields.tailSet`, `Shields.BlockCondition`:
  the dictionary.  Sorted enumerations are avoided throughout -- `i_v ≥ x` says exactly that at
  most `v` elements of `I` lie below `x`, so the whole dictionary is expressible in
  `belowCount`.

## Main statements

* `Shields.indexHook_iff_blockCondition`, `Shields.superSkewSchur_betaDiagram_pos_iff`: the
  dictionary and its composite with the criterion -- every window of `a - b` consecutive sites
  in `{b, …, n-1}` holds at least `k - b` points of the index set.
* `Shields.adm_iff_rowLen_of_superSkewSchur_pos` and
  `Shields.adm_iff_blockCondition_of_superSkewSchur`:
  the criterion applied to an abstract admissibility predicate.  Skew Jacobi--Trudi -- what
  identifies a Toeplitz minor with `superSkewSchur` -- is **not** proved here and is not
  asserted anywhere; both take it as an explicit hypothesis `hJT` in their own types, so nothing
  downstream can consume it by accident.
* `Shields.not_blockCondition_example` and its neighbors: non-vacuity witnesses, the dictionary
  evaluated at one concrete index set.

## Tags

Young diagram, hook, packing, index set
-/

namespace Shields

open Finset

variable {R : Type*} [CommSemiring R]

/-! ## Discharging an admissibility predicate

The route from a Toeplitz minor to a combinatorial description of the admissible
index sets passes through two steps: skew Jacobi--Trudi, and the hook criterion.
The lemmas below discharge the second and leave the first visible in the
type. -/

/-- The hook criterion as a rewriting step on an admissibility predicate.  Given
the skew Jacobi--Trudi identification `hJT` — admissibility of `I` is positivity
of the two-alphabet function of the shape `lamOf I / muOf I`, which is *not*
proved here — admissibility is equivalent to the part inequalities
`λ_{u+b} ≤ μ_u + a` of the hook criterion. -/
theorem adm_iff_rowLen_of_superSkewSchur_pos {Adm : Finset ℕ → Prop} {a b : ℕ}
    {β α : ℕ → ℝ} (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i)
    (lamOf muOf : Finset ℕ → YoungDiagram) (hcont : ∀ I, muOf I ≤ lamOf I)
    (hJT : ∀ I, Adm I ↔ 0 < superSkewSchur (lamOf I) (muOf I) b a β α)
    (I : Finset ℕ) :
    Adm I ↔ ∀ u : ℕ, (lamOf I).rowLen (u + b) ≤ (muOf I).rowLen u + a := by
  rw [hJT I, superSkewSchur_pos_iff_rowLen (hcont I) hβ hα]

/-! ## The index dictionary and the packing rule

The hook criterion is a statement about the parts of `λ` and `μ`; a packing
argument wants a statement about a row set alone.  The shape construction
`betaDiagram` connects them, and under it the criterion `λ_{u+b} - μ_u ≤ a` reads
`j_u + k + b ≤ i_{u+b} + a` — carried here over `ℕ` with `a` and `k` on opposite
sides, because the shift `k + b - a` is genuinely negative on part of the range.

Sorted enumerations are avoided throughout.  `i_v ≥ x` says exactly that at most
`v` elements of `I` lie below `x`, so the whole dictionary is expressible in
`belowCount`, and the row-to-column relation becomes the *definition* of the
column set rather than a hypothesis about it — `tailSet_compl` proves it agrees
with the complement description.

Nothing in this paper consumes this section. -/

/-- The number of elements of `I` strictly below `y`. -/
def belowCount (I : Finset ℕ) (y : ℕ) : ℕ := (I.filter (· < y)).card

theorem belowCount_zero (I : Finset ℕ) : belowCount I 0 = 0 := by
  simp [belowCount]

theorem belowCount_mono (I : Finset ℕ) {y₁ y₂ : ℕ} (h : y₁ ≤ y₂) :
    belowCount I y₁ ≤ belowCount I y₂ :=
  Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

theorem belowCount_le_card (I : Finset ℕ) (y : ℕ) : belowCount I y ≤ I.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- A window of `r` sites is the difference of two below-counts. -/
theorem belowCount_window (I : Finset ℕ) (t r : ℕ) :
    (I ∩ Finset.Ico t (t + r)).card + belowCount I t = belowCount I (t + r) := by
  have hsub : I.filter (· < t) ⊆ I.filter (· < t + r) := fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩
  have heq : I ∩ Finset.Ico t (t + r) = I.filter (· < t + r) \ I.filter (· < t) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_filter, Finset.mem_sdiff,
      not_and, not_lt]
    constructor
    · rintro ⟨hx, ht, hlt⟩
      exact ⟨⟨hx, hlt⟩, fun _ => ht⟩
    · rintro ⟨⟨hx, hlt⟩, h2⟩
      exact ⟨hx, h2 hx, hlt⟩
  rw [belowCount, belowCount, heq]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- An initial block of `I` makes the below-count exact. -/
theorem belowCount_eq_self {I : Finset ℕ} {k : ℕ} (hkI : ∀ x, x < k → x ∈ I) {y : ℕ}
    (hy : y ≤ k) : belowCount I y = y := by
  have : I.filter (· < y) = Finset.range y := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hkI x (lt_of_lt_of_le h hy), h⟩⟩
  rw [belowCount, this, Finset.card_range]

theorem belowCount_eq_card {I : Finset ℕ} {n y : ℕ} (hIn : I ⊆ Finset.range n) (hy : n ≤ y) :
    belowCount I y = I.card := by
  have : I.filter (· < y) = I := by
    apply Finset.filter_true_of_mem
    intro x hx
    exact lt_of_lt_of_le (Finset.mem_range.mp (hIn hx)) hy
  rw [belowCount, this]

/-- The column set built from the row set, rather than assumed to satisfy the
relation between them. -/
def tailSet (n k : ℕ) (I : Finset ℕ) : Finset ℕ :=
  (I.filter (k ≤ ·)).image (· - k) ∪ Finset.Ico (n - k) n

@[simp]
theorem mem_tailSet {n k x : ℕ} {I : Finset ℕ} :
    x ∈ tailSet n k I ↔ x + k ∈ I ∨ (n - k ≤ x ∧ x < n) := by
  simp only [tailSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro (⟨y, ⟨hy, hky⟩, rfl⟩ | h)
    · exact Or.inl (by rwa [Nat.sub_add_cancel hky])
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨x + k, ⟨h, Nat.le_add_left _ _⟩, by omega⟩
    · exact Or.inr h

/-- On complement sets, `tailSet` returns `[n] \ C`. -/
theorem tailSet_compl {n k : ℕ} (C : Finset ℕ) (hC : C ⊆ Finset.range (n - k)) :
    tailSet n k (Finset.range n \ C.image (· + k)) = Finset.range n \ C := by
  ext x
  simp only [mem_tailSet, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image, not_exists,
    not_and]
  constructor
  · rintro (⟨hlt, hne⟩ | ⟨h1, h2⟩)
    · exact ⟨by omega, fun hx => hne x hx rfl⟩
    · refine ⟨h2, fun hx => ?_⟩
      have := Finset.mem_range.mp (hC hx)
      omega
  · rintro ⟨hlt, hx⟩
    rcases lt_or_ge x (n - k) with h | h
    · refine Or.inl ⟨by omega, fun c hc hck => hx ?_⟩
      have hcx : c = x := by omega
      exact hcx ▸ hc
    · exact Or.inr ⟨h, hlt⟩

/-- The below-counts of the row set and the column set, related.  For
`y ≤ n - k` the correction vanishes and this is `belowCount J y + k =
belowCount I (y + k)`; past that point the trailing block `{n-k, …, n-1}` of
the trailing block contributes. -/
theorem belowCount_tailSet {n k : ℕ} (I : Finset ℕ) (hIn : I ⊆ Finset.range n)
    (hkI : ∀ x, x < k → x ∈ I) (y : ℕ) :
    belowCount (tailSet n k I) y + k = belowCount I (y + k) + (min y n - (n - k)) := by
  set A : Finset ℕ := (Finset.range y).filter (fun x => x + k ∈ I) with hAdef
  set B : Finset ℕ := Finset.Ico (n - k) (min y n) with hBdef
  have hsplit : (tailSet n k I).filter (· < y) = A ∪ B := by
    ext x
    simp only [hAdef, hBdef, Finset.mem_filter, mem_tailSet, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h | ⟨h1, h2⟩, hxy⟩
      · exact Or.inl ⟨hxy, h⟩
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (⟨hxy, hxI⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl hxI, hxy⟩
      · exact ⟨Or.inr ⟨h1, by omega⟩, by omega⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [hAdef, Finset.mem_filter, Finset.mem_range] at hxA
    simp only [hBdef, Finset.mem_Ico] at hxB
    have := Finset.mem_range.mp (hIn hxA.2)
    omega
  have hAcard : A.card = (I ∩ Finset.Ico k (k + y)).card := by
    have himg : A.image (· + k) = I ∩ Finset.Ico k (k + y) := by
      ext w
      simp only [hAdef, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
        Finset.mem_inter, Finset.mem_Ico]
      constructor
      · rintro ⟨x, ⟨hx, hxI⟩, rfl⟩
        exact ⟨hxI, by omega, by omega⟩
      · rintro ⟨hwI, hkw, hwy⟩
        exact ⟨w - k, ⟨by omega, by rwa [Nat.sub_add_cancel hkw]⟩, by omega⟩
    rw [← himg, Finset.card_image_of_injective _ (add_left_injective k)]
  have hwin := belowCount_window I k y
  have hbk : belowCount I k = k := belowCount_eq_self hkI le_rfl
  have hy : belowCount I (y + k) = belowCount I (k + y) := by rw [Nat.add_comm]
  rw [belowCount, hsplit, Finset.card_union_of_disjoint hdisj, hAcard, hBdef, Nat.card_Ico, hy]
  omega

/-- The index form of the hook condition, in below-count form.  Comparing
`i_{u+b}` with a threshold is comparing a below-count with `u + b`, so the
quantifier over `u` becomes one over the pair of thresholds `y` and `z`, tied by
`y + k + b = z + a` — the shift `k + b - a` written without subtraction. -/
def IndexHook (n k a b : ℕ) (I : Finset ℕ) : Prop :=
  ∀ y z : ℕ, y + k + b = z + a → belowCount I z ≤ belowCount (tailSet n k I) y + b

/-- Every window of `a - b` consecutive sites inside `range n` holds at least
`k - b` points of `I`.  This is the packing rule with its restriction `b ≤ t`
dropped; `allWindows_iff_blockCondition` puts it back. -/
def AllWindows (n k a b : ℕ) (I : Finset ℕ) : Prop :=
  ∀ t : ℕ, t + (a - b) ≤ n → k - b ≤ (I ∩ Finset.Ico t (t + (a - b))).card

/-- The packing rule, in the shape an admissibility hypothesis states it. -/
def BlockCondition (n k a b : ℕ) (I : Finset ℕ) : Prop :=
  ∀ t : ℕ, b ≤ t → t + (a - b) ≤ n → k - b ≤ (I ∩ Finset.Ico t (t + (a - b))).card

/-- The windows below `t = b` carry no information: the initial block of `I`
forces them, using `k ≤ a` to compare `k - b` with the window width `a - b`. -/
theorem allWindows_iff_blockCondition {n k a b : ℕ} (hka : k ≤ a) {I : Finset ℕ}
    (hkI : ∀ x, x < k → x ∈ I) :
    AllWindows n k a b I ↔ BlockCondition n k a b I := by
  constructor
  · intro h t _ ht
    exact h t ht
  · intro h t ht
    rcases le_or_gt b t with hbt | hbt
    · exact h t hbt ht
    · have hsub : Finset.Ico t (min (t + (a - b)) k) ⊆ I ∩ Finset.Ico t (t + (a - b)) := by
        intro x hx
        simp only [Finset.mem_Ico, Finset.mem_inter] at hx ⊢
        exact ⟨hkI x (by omega), hx.1, by omega⟩
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega

/-- The below-count form of the index hook condition is a single window
inequality carrying a correction term, uniform in the threshold. -/
theorem indexHook_iff_window_tail {n k a b : ℕ} (hba : b < a) {I : Finset ℕ}
    (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    IndexHook n k a b I ↔
      ∀ z : ℕ, k ≤ z + (a - b) →
        k - b ≤ (I ∩ Finset.Ico z (z + (a - b))).card
          + (min (z + (a - b) - k) n - (n - k)) := by
  constructor
  · intro h z hz
    have hyk : (z + (a - b) - k) + k = z + (a - b) := by omega
    have hid := belowCount_tailSet I hIn hkI (z + (a - b) - k)
    rw [hyk] at hid
    have hw := belowCount_window I z (a - b)
    have := h (z + (a - b) - k) z (by omega)
    omega
  · intro h y z hyz
    have hyk : y + k = z + (a - b) := by omega
    have hid := belowCount_tailSet I hIn hkI y
    rw [hyk] at hid
    have hw := belowCount_window I z (a - b)
    have hz := h z (by omega)
    have hmin : min (z + (a - b) - k) n = min y n := by omega
    rw [hmin] at hz
    omega

/-- Under the shape construction, the hook criterion is exactly the packing rule:
every window of `a - b` consecutive sites in the tail `{b, …, n-1}` holds at least
`k - b` points of the row set.

`b < k ≤ a` is not needed here; `b < a` is, since with `a ≤ b` the windows are
empty and carry nothing. -/
theorem indexHook_iff_blockCondition {n k a b : ℕ} (hba : b < a) (hka : k ≤ a) (hkn : k ≤ n)
    {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    IndexHook n k a b I ↔ BlockCondition n k a b I := by
  rw [indexHook_iff_window_tail hba hIn hkI, ← allWindows_iff_blockCondition hka hkI]
  constructor
  · -- from the corrected form to every window inside `range n`
    intro h t ht
    rcases le_or_gt k (t + (a - b)) with hk | hk
    · have := h t hk
      have hmin : min (t + (a - b) - k) n - (n - k) = 0 := by omega
      omega
    · -- the window sits inside the initial block `{0, …, k-1}`
      have hsub : Finset.Ico t (t + (a - b)) ⊆ I ∩ Finset.Ico t (t + (a - b)) := by
        intro x hx
        simp only [Finset.mem_Ico] at hx
        exact Finset.mem_inter.mpr ⟨hkI x (by omega), Finset.mem_Ico.mpr hx⟩
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega
  · -- from every window inside `range n` to the corrected form
    intro h z hz
    rcases le_or_gt (z + (a - b)) n with hzn | hzn
    · have := h z hzn
      have hmin : min (z + (a - b) - k) n - (n - k) = 0 := by omega
      omega
    rcases le_or_gt n (z + (a - b) - k) with hbig | hbig
    · -- the correction is already `k`
      have hmin : min (z + (a - b) - k) n - (n - k) = k := by omega
      omega
    -- the correction is `z + (a - b) - n`; compare with the last full window
    have hmin : min (z + (a - b) - k) n - (n - k) = z + (a - b) - n := by omega
    rw [hmin]
    rcases le_or_gt (a - b) n with hrn | hrn
    · have hlast := h (n - (a - b)) (by omega)
      have hsub : I ∩ Finset.Ico (n - (a - b)) (n - (a - b) + (a - b))
          ⊆ Finset.Ico (n - (a - b)) z ∪ I ∩ Finset.Ico z (z + (a - b)) := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_Ico] at hx
        rcases lt_or_ge x z with hxz | hxz
        · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨hx.2.1, hxz⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hx.1, Finset.mem_Ico.mpr ⟨hxz, by omega⟩⟩)
      have hcard := Finset.card_le_card hsub
      have hun := Finset.card_union_le (Finset.Ico (n - (a - b)) z)
        (I ∩ Finset.Ico z (z + (a - b)))
      rw [Nat.card_Ico] at hun
      omega
    · -- a window wider than `n`: the initial block alone already fills it
      have hzk : z < k := by omega
      have hsub : Finset.Ico z k ⊆ I ∩ Finset.Ico z (z + (a - b)) := by
        intro x hx
        simp only [Finset.mem_Ico] at hx
        exact Finset.mem_inter.mpr ⟨hkI x hx.2, Finset.mem_Ico.mpr ⟨hx.1, by omega⟩⟩
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega

/-! ## The shape of an index set

The shapes are built from an index set directly, without sorting it:
`λ_u = L - i_u + u` says that row `u` of the diagram reaches column `j` exactly
when fewer than `u` elements of `I` lie at or above `L + u - j`, and that is a
`belowCount` statement.  `betaDiagram I L` is the resulting diagram,
`mem_betaDiagram` its cells, and `noBigRect_betaDiagram` the dictionary itself:
the block condition on the pair of shapes is the index inequality on the pair of
index sets. -/

theorem belowCount_add_le (I : Finset ℕ) (t r : ℕ) :
    belowCount I (t + r) ≤ belowCount I t + r := by
  have hw := belowCount_window I t r
  have hle : (I ∩ Finset.Ico t (t + r)).card ≤ r := by
    have h := Finset.card_le_card
      (Finset.inter_subset_right (s₁ := I) (s₂ := Finset.Ico t (t + r)))
    rwa [Nat.card_Ico, Nat.add_sub_cancel_left] at h
  omega

/-- Moving up and to the left in the array keeps a cell. -/
theorem betaMem_lower {I : Finset ℕ} {L v j v' j' : ℕ} (hv : v' ≤ v) (hj : j' ≤ j)
    (h : v < belowCount I (L + v + 1 - j)) : v' < belowCount I (L + v' + 1 - j') := by
  have hmono : belowCount I (L + v + 1 - j) ≤ belowCount I (L + v + 1 - j') :=
    belowCount_mono I (by omega)
  have hstep : belowCount I (L + v + 1 - j')
      ≤ belowCount I (L + v' + 1 - j') + (v - v') :=
    le_trans (belowCount_mono I (show L + v + 1 - j' ≤ (L + v' + 1 - j') + (v - v') by omega))
      (belowCount_add_le I _ _)
  omega

/-- The Young diagram of an index set: row `u` has length `L - i_u + u`, where
`i_1 < ⋯ < i_m` enumerates `I`. -/
def betaDiagram (I : Finset ℕ) (L : ℕ) : YoungDiagram where
  cells := (Finset.range I.card ×ˢ Finset.range (L + I.card + 1)).filter
    fun p => p.1 < belowCount I (L + p.1 + 1 - p.2)
  isLowerSet := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ hle hmem
    obtain ⟨hv, hj⟩ := Prod.mk_le_mk.mp hle
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem ⊢
    obtain ⟨⟨_, h2⟩, h3⟩ := hmem
    have hcore := betaMem_lower hv hj h3
    exact ⟨⟨lt_of_lt_of_le hcore (belowCount_le_card _ _), by omega⟩, hcore⟩

theorem mem_betaDiagram {I : Finset ℕ} {L v j : ℕ} :
    (v, j) ∈ betaDiagram I L ↔ v < belowCount I (L + v + 1 - j) := by
  rw [← YoungDiagram.mem_cells]
  simp only [betaDiagram, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨lt_of_lt_of_le h (belowCount_le_card _ _), ?_⟩, h⟩⟩
  have hvc : v < I.card := lt_of_lt_of_le h (belowCount_le_card _ _)
  by_contra hj
  rw [show L + v + 1 - j = 0 by omega, belowCount_zero] at h
  omega

theorem tailSet_subset_range {n k : ℕ} {I : Finset ℕ} (hIn : I ⊆ Finset.range n) :
    tailSet n k I ⊆ Finset.range n := by
  intro x hx
  rw [mem_tailSet] at hx
  rw [Finset.mem_range]
  rcases hx with h | h
  · have := Finset.mem_range.mp (hIn h)
    omega
  · exact h.2

/-- The two index sets have the same size. -/
theorem card_tailSet {n k : ℕ} {I : Finset ℕ} (hIn : I ⊆ Finset.range n)
    (hkI : ∀ x, x < k → x ∈ I) (hkn : k ≤ n) :
    (tailSet n k I).card = I.card := by
  have h1 : belowCount (tailSet n k I) n = (tailSet n k I).card :=
    belowCount_eq_card (tailSet_subset_range hIn) le_rfl
  have h2 := belowCount_tailSet I hIn hkI n
  rw [belowCount_eq_card hIn (Nat.le_add_right n k)] at h2
  omega

/-- `μ ⊆ λ`, the containment the construction produces: the offset drops by `k`
and each `j_u` is at most the corresponding `i_u`. -/
theorem betaDiagram_tailSet_le {n k L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    betaDiagram (tailSet n k I) Lk ≤ betaDiagram I L := by
  intro c hc
  obtain ⟨v, j⟩ := c
  rw [mem_betaDiagram] at hc ⊢
  rcases le_or_gt j (Lk + v + 1) with hj | hj
  · have hid := belowCount_tailSet I hIn hkI (Lk + v + 1 - j)
    rw [show Lk + v + 1 - j + k = L + v + 1 - j by omega] at hid
    omega
  · rw [show Lk + v + 1 - j = 0 by omega, belowCount_zero] at hc
    omega

/-- **The index dictionary.**  Under the shape construction, the block condition
of the hook criterion on the pair of shapes is the index hook condition on the
pair of index sets.  `L` has to be large, which is `n ≤ Lk` here. -/
theorem noBigRect_betaDiagram {n k a b L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n)
    (hnL : n ≤ Lk) {I : Finset ℕ} (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    NoBigRect (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b a ↔ IndexHook n k a b I := by
  constructor
  · intro h y z hyz
    by_contra hcon
    set v := belowCount (tailSet n k I) y with hv
    rcases le_or_gt y n with hyn | hyn
    · have hnot : (v, Lk + v + 1 - y) ∉ betaDiagram (tailSet n k I) Lk := by
        rw [mem_betaDiagram, show Lk + v + 1 - (Lk + v + 1 - y) = y by omega]
        omega
      refine hnot (h v (Lk + v + 1 - y) ?_)
      rw [mem_betaDiagram, show L + (v + b) + 1 - (Lk + v + 1 - y + a) = z by omega]
      omega
    · have hsat : v = I.card := by
        rw [hv, belowCount_eq_card (tailSet_subset_range hIn) (le_of_lt hyn)]
        exact card_tailSet hIn hkI hkn
      have := belowCount_le_card I z
      omega
  · intro h v j hmem
    rw [mem_betaDiagram] at hmem ⊢
    have hZle : L + (v + b) + 1 - (j + a) ≤ (Lk + v + 1 - j) + k + b - a := by omega
    rcases le_or_gt a ((Lk + v + 1 - j) + k + b) with hge | hlt
    · have hidx := h (Lk + v + 1 - j) ((Lk + v + 1 - j) + k + b - a) (by omega)
      have hmono := belowCount_mono I hZle
      omega
    · rw [show L + (v + b) + 1 - (j + a) = 0 by omega, belowCount_zero] at hmem
      omega

/-- **The dictionary end to end on the index sets.**  For a row set `I` with an
initial block, `J = tailSet n k I` its column set and the shapes above, the
branching sum is positive exactly when `I` satisfies the packing rule.

What this does not contain is skew Jacobi--Trudi: nothing here says the branching
sum is a Toeplitz minor.  That step enters
`adm_iff_blockCondition_of_superSkewSchur` as an explicit hypothesis. -/
theorem superSkewSchur_betaDiagram_pos_iff {n k a b L Lk : ℕ} (hL : Lk + k = L)
    (hkn : k ≤ n) (hnL : n ≤ Lk) (hba : b < a) (hka : k ≤ a) {I : Finset ℕ}
    (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) {β α : ℕ → ℝ}
    (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i) :
    0 < superSkewSchur (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b a β α
      ↔ BlockCondition n k a b I := by
  rw [superSkewSchur_pos_iff (betaDiagram_tailSet_le hL hkn hIn hkI) hβ hα,
    noBigRect_betaDiagram hL hkn hnL hIn hkI, indexHook_iff_blockCondition hba hka hkn hIn hkI]

/-- An admissibility predicate, discharged down to skew Jacobi--Trudi.  The one
remaining hypothesis, `hJT`, is the identification of the Toeplitz minor with the
branching sum on the shapes above; everything after it — the hook criterion and
the packing rule — is proved here. -/
theorem adm_iff_blockCondition_of_superSkewSchur {Adm : Finset ℕ → Prop}
    {n k a b L Lk : ℕ} (hL : Lk + k = L) (hkn : k ≤ n) (hnL : n ≤ Lk) (hba : b < a)
    (hka : k ≤ a) {β α : ℕ → ℝ} (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i)
    (hJT : ∀ I, I ⊆ Finset.range n → (∀ x, x < k → x ∈ I) →
      (Adm I ↔ 0 < superSkewSchur (betaDiagram I L) (betaDiagram (tailSet n k I) Lk) b a β α))
    (I : Finset ℕ) (hIn : I ⊆ Finset.range n) (hkI : ∀ x, x < k → x ∈ I) :
    Adm I ↔ BlockCondition n k a b I := by
  rw [hJT I hIn hkI, superSkewSchur_betaDiagram_pos_iff hL hkn hnL hba hka hIn hkI hβ hα]

/-! ## Non-vacuity

Both verdicts of `superSkewSchur_pos_iff` occur, on the smallest shapes that
exhibit them at `b = a = 1`.  The `2 × 2` square holds a block of `b+1 = 2` rows
by `a+1 = 2` columns and its two-alphabet function vanishes; the single row of
length two holds no such block and its two-alphabet function is positive. -/

theorem not_noBigRect_rect_two : ¬ NoBigRect (rect 2 2) ⊥ 1 1 := fun h =>
  YoungDiagram.notMem_bot (0, 0) (h 0 0 (mem_rect.mpr ⟨one_lt_two, one_lt_two⟩))

theorem superSkewSchur_rect_two_eq_zero (β α : ℕ → R) :
    superSkewSchur (rect 2 2) ⊥ 1 1 β α = 0 :=
  superSkewSchur_eq_zero_of_block (i := 0) (j := 0) β α bot_le
    (mem_rect.mpr ⟨one_lt_two, one_lt_two⟩) (YoungDiagram.notMem_bot _)

theorem superSkewSchur_rect_one_two_pos {β α : ℕ → ℝ}
    (hβ : ∀ i, i < 1 → 0 < β i) (hα : ∀ i, i < 1 → 0 < α i) :
    0 < superSkewSchur (rect 1 2) ⊥ 1 1 β α := by
  rw [superSkewSchur_bot_pos_iff hβ hα]
  have h : (rect 1 2).rowLen 1 = 0 := by
    by_contra hne
    exact absurd
      (mem_rect.mp (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne))).1 (by omega)
  omega

/-! The dictionary at one concrete index set.  For `I = {0, 1, 3}` and `L = 3`,
the construction gives `λ = (4, 4, 3)`, so row `0` stops at column `4` and row `2`
at column `3`. -/

theorem mem_betaDiagram_example : (0, 3) ∈ betaDiagram {0, 1, 3} 3 :=
  mem_betaDiagram.mpr (by decide)

theorem notMem_betaDiagram_example : (0, 4) ∉ betaDiagram {0, 1, 3} 3 := fun h =>
  absurd (mem_betaDiagram.mp h) (by decide)

theorem mem_betaDiagram_example_row_two : (2, 2) ∈ betaDiagram {0, 1, 3} 3 :=
  mem_betaDiagram.mpr (by decide)

theorem notMem_betaDiagram_example_row_two : (2, 3) ∉ betaDiagram {0, 1, 3} 3 := fun h =>
  absurd (mem_betaDiagram.mp h) (by decide)

/-- `tailSet` is not the identity: at `n = 4`, `k = 1` the row set `{0, 1, 3}`
has column set `{0, 2, 3}`. -/
theorem tailSet_example : tailSet 4 1 {0, 1, 3} = {0, 2, 3} := by decide

/-- Both verdicts of `indexHook_iff_blockCondition` occur.  At `n = 4`, `k = 1`,
`a = 2`, `b = 0` the row set `{0, 1, 3}` meets every window of two consecutive
sites, and `{0, 1}` misses the window `{2, 3}` at `t = 2`. -/
theorem blockCondition_example : BlockCondition 4 1 2 0 {0, 1, 3} := by
  intro t _ ht
  have htle : t ≤ 2 := by omega
  interval_cases t <;> decide

theorem not_blockCondition_example : ¬ BlockCondition 4 1 2 0 {0, 1} := fun h =>
  absurd (h 2 (Nat.zero_le _) (by norm_num)) (by decide)

end Shields
