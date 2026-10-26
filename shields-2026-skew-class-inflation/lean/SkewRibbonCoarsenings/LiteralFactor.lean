/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/LiteralFactor.lean
import SkewRibbonCoarsenings.CompositionProduct

/-!
# Literal inner factors

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:algebra` (`lem:literal-factor`).

A composition of weight `n` with cut set `S` has a literal inner factor of weight `p ∣ n` when
`S = compCuts (n / p) A p E` for cut sets `A` of weight `n / p` and `E` of weight `p`
(`eq:composition-cuts`).  `literal_factor` proves that this holds exactly when the cuts off the
`p`-grid repeat with period `p` (`OffGridPeriodic`), that the factors are then unique (inner cuts
`S ∩ {1, …, p-1}`, outer cuts `{j : j p ∈ S}`), and that two compositions have the same inner
factor exactly when their off-grid cuts agree and repeat with that period.  The list form is
`literal_factor_parts`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-- The cuts of `S` off the `p`-grid repeat with period `p`. -/
def OffGridPeriodic (n : ℕ) (S : Finset ℕ) (p : ℕ) : Prop :=
  ∀ x, x + p < n → ¬ p ∣ x → (x ∈ S ↔ x + p ∈ S)

/-- Membership in `compCuts` at a point off the `p`-grid. -/
lemma mem_compCuts_of_not_dvd {m : ℕ} {A : Finset ℕ} {p : ℕ} {E : Finset ℕ} (hp : 0 < p)
    (hE : IsCutSet p E) {x : ℕ} (hx : ¬ p ∣ x) (hxm : x < m * p) :
    x ∈ compCuts m A p E ↔ x % p ∈ E := by
  rw [mem_compCuts]
  constructor
  · rintro (⟨y, _, rfl⟩ | ⟨j, hj, e, he, rfl⟩)
    · exact absurd (dvd_mul_right _ _) hx
    · have := Finset.mem_Ioo.mp (hE he)
      have : (j * p + e) % p = e := by
        rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt this.2
      rwa [this]
  · intro h
    refine Or.inr ⟨x / p, ?_, x % p, h, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using hxm)
    · exact Nat.div_add_mod' x p

/-- Membership in `compCuts` at a point on the `p`-grid. -/
lemma mem_compCuts_of_dvd {m : ℕ} {A : Finset ℕ} {p : ℕ} {E : Finset ℕ} (hp : 0 < p)
    (hE : IsCutSet p E) (y : ℕ) : p * y ∈ compCuts m A p E ↔ y ∈ A := by
  rw [mem_compCuts]
  constructor
  · rintro (⟨z, hz, h⟩ | ⟨j, hj, e, he, h⟩)
    · rwa [Nat.eq_of_mul_eq_mul_left hp h] at hz
    · have := Finset.mem_Ioo.mp (hE he)
      exfalso
      have h1 : p ∣ e := by
        have : p ∣ j * p + e := h ▸ dvd_mul_right p y
        exact (Nat.dvd_add_right (dvd_mul_left p j)).mp this
      exact absurd (Nat.le_of_dvd this.1 h1) (by omega)
  · intro h; exact Or.inl ⟨y, h, rfl⟩

/-- Off the `p`-grid, a periodic cut set is determined by residues. -/
lemma mem_iff_mod_of_periodic {n : ℕ} {S : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (hper : OffGridPeriodic n S p) :
    ∀ x, x < n → ¬ p ∣ x → (x ∈ S ↔ x % p ∈ S) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx hxd
    by_cases hlt : x < p
    · rw [Nat.mod_eq_of_lt hlt]
    · have hxp : x = (x - p) + p := by omega
      have hnd : ¬ p ∣ (x - p) := fun h => hxd (by
        have := Nat.dvd_add_right h |>.mpr (dvd_refl p)
        rwa [← hxp] at this)
      have h1 := hper (x - p) (by omega) hnd
      have h2 := ih (x - p) (by omega) (by omega) hnd
      have h3 : x % p = (x - p) % p := by
        conv_lhs => rw [hxp]
        exact Nat.add_mod_right _ _
      rw [h3, ← h2, h1, ← hxp]

/-- The inner cuts `S ∩ {1, …, p-1}` of `lem:literal-factor`. -/
def innerCuts (p : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter (· < p)

/-- The outer cuts `{j : j p ∈ S}` of `lem:literal-factor`, for a composition of weight `n`. -/
def outerCuts (n p : ℕ) (S : Finset ℕ) : Finset ℕ := (Finset.range (n / p)).filter (p * · ∈ S)

/-- `lem:literal-factor`, cut-set form.  For a composition of weight `n` with cut set `S` and
`p ∣ n`, `0 < p`: it has a literal inner factor of weight `p` (`S = compCuts (n / p) A p E`,
`eq:composition-cuts`) precisely when its cuts off the `p`-grid repeat with period `p`. -/
theorem literal_factor_iff {n p : ℕ} {S : Finset ℕ} (hp : 0 < p) (hpn : p ∣ n)
    (hS : IsCutSet n S) :
    (∃ A E, IsCutSet (n / p) A ∧ IsCutSet p E ∧ S = compCuts (n / p) A p E) ↔
      OffGridPeriodic n S p := by
  obtain ⟨m, rfl⟩ := hpn
  have hm : p * m / p = m := Nat.mul_div_cancel_left m hp
  rw [hm]
  constructor
  · rintro ⟨A, E, hA, hE, rfl⟩ x hx hnd
    have hx1 : x < m * p := by rw [mul_comm]; omega
    have hx2 : x + p < m * p := by rw [mul_comm]; omega
    have hnd2 : ¬ p ∣ (x + p) := fun h => hnd ((Nat.dvd_add_left (dvd_refl p)).mp h)
    rw [mem_compCuts_of_not_dvd hp hE hnd hx1, mem_compCuts_of_not_dvd hp hE hnd2 hx2,
      Nat.add_mod_right]
  · intro hper
    refine ⟨outerCuts (p * m) p S, innerCuts p S, ?_, ?_, ?_⟩
    · intro j hj
      simp only [outerCuts, hm, Finset.mem_filter, Finset.mem_range] at hj
      have := Finset.mem_Ioo.mp (hS hj.2)
      have h0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · simp at this
        · exact h
      exact Finset.mem_Ioo.mpr ⟨h0, hj.1⟩
    · intro x hx
      simp only [innerCuts, Finset.mem_filter] at hx
      exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp (hS hx.1)).1, hx.2⟩
    · have hE : IsCutSet p (innerCuts p S) := by
        intro x hx
        simp only [innerCuts, Finset.mem_filter] at hx
        exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp (hS hx.1)).1, hx.2⟩
      ext x
      have hxS : x ∈ S → x < m * p := fun h => by
        have := (Finset.mem_Ioo.mp (hS h)).2; rwa [mul_comm] at this
      by_cases hd : p ∣ x
      · obtain ⟨y, rfl⟩ := hd
        rw [mem_compCuts_of_dvd hp hE]
        simp only [outerCuts, hm, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro h
          refine ⟨?_, h⟩
          have := (Finset.mem_Ioo.mp (hS h)).2
          by_contra hc
          have : p * m ≤ p * y := Nat.mul_le_mul_left _ (by omega)
          omega
        · exact fun h => h.2
      · by_cases hxn : x < m * p
        · rw [mem_compCuts_of_not_dvd hp hE hd hxn]
          simp only [innerCuts, Finset.mem_filter]
          rw [mul_comm] at hxn
          rw [mem_iff_mod_of_periodic hp hper x hxn hd]
          constructor
          · intro h; exact ⟨h, Nat.mod_lt _ hp⟩
          · intro h; exact h.1
        · constructor
          · intro h; exact absurd (hxS h) hxn
          · intro h
            exfalso
            rw [mem_compCuts] at h
            rcases h with ⟨y, _, rfl⟩ | ⟨j, hj, e, he, rfl⟩
            · exact hd (dvd_mul_right _ _)
            · have := (Finset.mem_Ioo.mp (hE he)).2
              apply hxn
              calc j * p + e < j * p + p := by omega
                _ = (j + 1) * p := by ring
                _ ≤ m * p := Nat.mul_le_mul_right _ hj

/-- Uniqueness in `lem:literal-factor`: if `S = compCuts m A p E` with `A`, `E` admissible, the
inner cuts are `S ∩ {1, …, p-1}` and the outer cuts are `{j : j p ∈ S}`.  (The composition is
nonempty: `0 < m`.) -/
theorem literal_factor_unique {m p : ℕ} {S A E : Finset ℕ} (hp : 0 < p) (hm : 0 < m)
    (hA : IsCutSet m A) (hE : IsCutSet p E) (hS : S = compCuts m A p E) :
    E = innerCuts p S ∧ A = outerCuts (m * p) p S := by
  subst hS
  constructor
  · ext x
    simp only [innerCuts, Finset.mem_filter, mem_compCuts]
    constructor
    · intro hx
      have hxp := (Finset.mem_Ioo.mp (hE hx)).2
      have hxp0 := (Finset.mem_Ioo.mp (hE hx)).1
      exact ⟨Or.inr ⟨0, hm, x, hx, by simp⟩, hxp⟩
    · rintro ⟨(⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩), hxp⟩
      · have := (Finset.mem_Ioo.mp (hA hy)).1
        have : p ≤ p * y := Nat.le_mul_of_pos_right _ this
        omega
      · have : j = 0 := by
          by_contra hj0
          have : p ≤ j * p := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj0)
          omega
        subst this
        simpa using he
  · ext y
    have hm' : m * p / p = m := Nat.mul_div_cancel _ hp
    simp only [outerCuts, hm', Finset.mem_filter, Finset.mem_range]
    rw [mem_compCuts_of_dvd hp hE]
    constructor
    · intro h; exact ⟨(Finset.mem_Ioo.mp (hA h)).2, h⟩
    · exact fun h => h.2

/-- Same inner factor in `lem:literal-factor`: for two cut sets of weight `n` whose cuts off the
`p`-grid repeat with period `p`, the inner factors agree exactly when the off-grid cuts agree. -/
theorem literal_factor_same_inner {n p : ℕ} {S S' : Finset ℕ} (hp : 0 < p)
    (hS : IsCutSet n S) (hS' : IsCutSet n S') (hper : OffGridPeriodic n S p)
    (hper' : OffGridPeriodic n S' p) :
    innerCuts p S = innerCuts p S' ↔ ∀ x, ¬ p ∣ x → (x ∈ S ↔ x ∈ S') := by
  constructor
  · intro h x hx
    by_cases hxn : x < n
    · rw [mem_iff_mod_of_periodic hp hper x hxn hx, mem_iff_mod_of_periodic hp hper' x hxn hx]
      have hlt := Nat.mod_lt x hp
      have := Finset.ext_iff.mp h (x % p)
      simpa [innerCuts, hlt] using this
    · have h1 : x ∉ S := fun hh => hxn (Finset.mem_Ioo.mp (hS hh)).2
      have h2 : x ∉ S' := fun hh => hxn (Finset.mem_Ioo.mp (hS' hh)).2
      simp [h1, h2]
  · intro h
    ext x
    simp only [innerCuts, Finset.mem_filter]
    by_cases hx0 : x = 0
    · subst hx0
      have h1 : 0 ∉ S := fun hh => by simpa using (Finset.mem_Ioo.mp (hS hh)).1
      have h2 : 0 ∉ S' := fun hh => by simpa using (Finset.mem_Ioo.mp (hS' hh)).1
      simp [h1, h2]
    · constructor
      · rintro ⟨hx, hxp⟩
        exact ⟨(h x (fun hd => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hd; omega)).mp hx,
          hxp⟩
      · rintro ⟨hx, hxp⟩
        exact ⟨(h x (fun hd => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hd; omega)).mpr hx,
          hxp⟩

/-! ### The list form -/

/-- `lem:literal-factor`, existence: a composition `β` (list of parts) of weight `n`, with
`0 < p ∣ n`, has a literal inner factor of weight `p` (`β = α ∘ ε`, `|ε| = p`) precisely when its
cuts off the `p`-grid repeat with period `p`. -/
theorem literal_factor_parts_iff {β : List ℕ} {p : ℕ} (hβ : IsParts β) (hp : 0 < p)
    (hpn : p ∣ β.sum) :
    (∃ α ε : List ℕ, IsParts α ∧ IsParts ε ∧ ε.sum = p ∧ β = compose α ε) ↔
      OffGridPeriodic β.sum (partsCuts β) p := by
  rw [← literal_factor_iff hp hpn (partsCuts_isCutSet hβ)]
  constructor
  · rintro ⟨α, ε, hα, hε, hεp, rfl⟩
    have hε0 : ε ≠ [] := by
      rintro rfl; simp at hεp; omega
    refine ⟨partsCuts α, partsCuts ε, ?_, ?_, ?_⟩
    · rw [sum_compose, hεp, Nat.mul_div_cancel _ hp]; exact partsCuts_isCutSet hα
    · rw [← hεp]; exact partsCuts_isCutSet hε
    · rw [partsCuts_compose hα hε0, sum_compose, hεp, Nat.mul_div_cancel _ hp]
  · rintro ⟨A, E, hA, hE, hS⟩
    obtain ⟨α, hα, hαs, hαc⟩ := exists_parts_of_isCutSet _ _ hA
    obtain ⟨ε, hε, hεs, hεc⟩ := exists_parts_of_isCutSet _ _ hE
    have hε0 : ε ≠ [] := by rintro rfl; simp at hεs; omega
    refine ⟨α, ε, hα, hε, hεs, ?_⟩
    apply partsCuts_injective hβ (isParts_compose hε)
    · rw [sum_compose, hαs, hεs, Nat.div_mul_cancel hpn]
    · rw [partsCuts_compose hα hε0, hαs, hεs, hαc, hεc]; exact hS

/-- `lem:literal-factor`, uniqueness: at a fixed weight `p` the factors of a composition are
unique. -/
theorem literal_factor_parts_unique {α ε α' ε' : List ℕ} (hα : IsParts α) (hε : IsParts ε)
    (hα' : IsParts α') (hε' : IsParts ε') (hαne : α ≠ []) (hεne : ε ≠ [])
    (hp : ε.sum = ε'.sum) (h : compose α ε = compose α' ε') : α = α' ∧ ε = ε' := by
  have hε'ne : ε' ≠ [] := by
    rintro rfl
    simp only [List.sum_nil] at hp
    exact hεne (eq_nil_of_sum_eq_zero hε hp)
  have hpos : 0 < ε.sum := sum_pos_of_ne_nil hε hεne
  have hm : 0 < α.sum := sum_pos_of_ne_nil hα hαne
  have hsum : α.sum = α'.sum := by
    have := congrArg List.sum h
    rw [sum_compose, sum_compose, ← hp] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hc := congrArg partsCuts h
  rw [partsCuts_compose hα hεne, partsCuts_compose hα' hε'ne, ← hsum, ← hp] at hc
  have hA' : IsCutSet α.sum (partsCuts α') := by rw [hsum]; exact partsCuts_isCutSet hα'
  have hE' : IsCutSet ε.sum (partsCuts ε') := by rw [hp]; exact partsCuts_isCutSet hε'
  obtain ⟨hE, hA⟩ := literal_factor_unique hpos hm (partsCuts_isCutSet hα)
    (partsCuts_isCutSet hε) rfl
  obtain ⟨hE2, hA2⟩ := literal_factor_unique hpos hm hA' hE' hc
  constructor
  · exact partsCuts_injective hα hα' hsum (hA.trans hA2.symm)
  · exact partsCuts_injective hε hε' hp (hE.trans hE2.symm)

end SkewRibbonCoarsenings
