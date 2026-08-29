/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Shields.Combinatorics.Young.SkewSchurPolynomial.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Super skew Schur functions and the supersymmetric hook criterion

Mathlib has no supersymmetric (two-alphabet) Schur function, so there is no object for a hook
criterion to be stated about.  This file supplies it over the skew theory of
`Shields.Combinatorics.Young.SkewSchurPolynomial.Basic`, proves the Berele--Regev branching
rule for it, and reads the criterion off that rule.

## Main definitions

* `Shields.SuperSkewSSYT`: a **super semistandard tableau** of shape `lam / mu` over `b` even
  and `a` odd letters, in the sense of Berele--Regev: weakly increasing in both directions, with
  an even letter allowed to repeat along a row but not down a column and an odd letter down a
  column but not along a row.  Letters are naturals, the even alphabet `< b` first.
* `Shields.superSkewSchur`: the supersymmetric skew Schur function, defined as the generating
  function of those tableaux.
* `Shields.NoBigRect`: the skew shape `lam / mu` contains no block of `b+1` rows by `a+1`
  columns.

## Main statements

* `Shields.superSkewSchur_eq_branching`: **the Berele--Regev branching rule.**  A super tableau
  splits at the boundary between the two alphabets; the cells carrying an even letter form a
  skew shape `nu / mu`, which is the intermediate diagram of the sum.  The even half is an
  ordinary tableau of `nu / mu` and the odd half is one of the *conjugate* shape
  `lam' / nu'`, which is where the transpose in the second factor comes from.  It is a theorem
  rather than a definition, and it needs `mu ≤ lam` -- without containment the branching sum is
  empty while tableaux still exist.
* `Shields.superSkewSchur_pos_iff`: **the supersymmetric hook criterion.**  With `mu ≤ lam` and
  all variables positive, it is positive exactly when `NoBigRect`, equivalently
  `lam.rowLen (i + b) ≤ mu.rowLen i + a` for every `i`.  The vanishing half splits each `nu` by
  whether the lower-left corner of the block lies in it; the positive half evaluates at
  `ν_u = max(μ_u, λ_u - a)`, realized as `mu ⊔ dropCols lam a`.
* `Shields.superSkewSchur_bot_pos_iff`: the straight-shape form, `λ_{b+1} ≤ a`, i.e. `(b, a)`
  hook containment.

## Tags

Schur polynomial, supersymmetric, Berele--Regev, branching rule, hook
-/

namespace Shields

open Finset

variable {R : Type*} [CommSemiring R]

/-! ## The two-alphabet function

The branching formula needs the shape `lam` with its first `a` columns removed,
which is `λ_u - a`.
-/

/-- `lam` with its first `a` columns deleted: `(i, j) ∈ dropCols lam a` exactly
when `(i, j + a) ∈ lam`, so its row lengths are `lam.rowLen i - a`. -/
def dropCols (lam : YoungDiagram) (a : ℕ) : YoungDiagram where
  cells := lam.cells.filter fun c => (c.1, c.2 + a) ∈ lam
  isLowerSet := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ ⟨hi, hj⟩ hd
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hd ⊢
    exact ⟨lam.up_left_mem hi hj hd.1,
      lam.up_left_mem hi (Nat.add_le_add_right hj a) hd.2⟩

@[simp]
theorem mem_dropCols {lam : YoungDiagram} {a i j : ℕ} :
    (i, j) ∈ dropCols lam a ↔ (i, j + a) ∈ lam := by
  constructor
  · intro h
    have := (YoungDiagram.mem_cells (μ := dropCols lam a) (i, j)).mpr h
    simp only [dropCols, Finset.mem_filter, YoungDiagram.mem_cells] at this
    exact this.2
  · intro h
    have : (i, j) ∈ (dropCols lam a).cells := by
      simp only [dropCols, Finset.mem_filter, YoungDiagram.mem_cells]
      exact ⟨lam.up_left_mem le_rfl (Nat.le_add_right j a) h, h⟩
    exact (YoungDiagram.mem_cells _).mp this

theorem dropCols_le (lam : YoungDiagram) (a : ℕ) : dropCols lam a ≤ lam := by
  intro c hc
  obtain ⟨i, j⟩ := c
  exact lam.up_left_mem le_rfl (Nat.le_add_right j a) (mem_dropCols.mp hc)

/-! ## Super tableaux

The two-alphabet analogue of `SkewSSYT`, in the sense of Berele--Regev.  Letters are naturals:
`k < b` is the even letter `k`, and `b ≤ k < b + a` is the odd letter `k - b`, so the even
alphabet precedes the odd one.  A filling is weakly increasing in both directions; an even letter
may repeat along a row but not down a column, and an odd letter may repeat down a column but not
along a row.
-/

/-- A **super semistandard tableau** of skew shape `lam / mu` over `b` even and `a` odd letters. -/
structure SuperSkewSSYT (lam mu : YoungDiagram) (b a : ℕ) where
  /-- The entry at `(i, j)`. -/
  entry : ℕ → ℕ → ℕ
  /-- Entries on the skew shape are letters of the alphabet. -/
  lt' : ∀ {i j : ℕ}, (i, j) ∈ skewCells lam mu → entry i j < b + a
  /-- Entries weakly increase along a row. -/
  row_weak' : ∀ {i j₁ j₂ : ℕ}, j₁ < j₂ → (i, j₂) ∈ lam → (i, j₁) ∉ mu → entry i j₁ ≤ entry i j₂
  /-- Entries weakly increase down a column. -/
  col_weak' : ∀ {i₁ i₂ j : ℕ}, i₁ < i₂ → (i₂, j) ∈ lam → (i₁, j) ∉ mu → entry i₁ j ≤ entry i₂ j
  /-- An even letter does not repeat down a column. -/
  col_strict_even' : ∀ {i₁ i₂ j : ℕ}, i₁ < i₂ → (i₂, j) ∈ lam → (i₁, j) ∉ mu →
    entry i₁ j < b → entry i₁ j < entry i₂ j
  /-- An odd letter does not repeat along a row. -/
  row_strict_odd' : ∀ {i j₁ j₂ : ℕ}, j₁ < j₂ → (i, j₂) ∈ lam → (i, j₁) ∉ mu →
    b ≤ entry i j₁ → entry i j₁ < entry i j₂
  /-- The filling vanishes off the skew shape. -/
  zeros' : ∀ {i j : ℕ}, (i, j) ∉ skewCells lam mu → entry i j = 0

namespace SuperSkewSSYT

variable {lam mu : YoungDiagram} {b a : ℕ}

instance instFunLike : FunLike (SuperSkewSSYT lam mu b a) ℕ (ℕ → ℕ) where
  coe := SuperSkewSSYT.entry
  coe_injective T T' h := by cases T; cases T'; congr

theorem lt_add (T : SuperSkewSSYT lam mu b a) {i j : ℕ} (h : (i, j) ∈ skewCells lam mu) :
    T i j < b + a := T.lt' h

theorem row_weak (T : SuperSkewSSYT lam mu b a) {i j₁ j₂ : ℕ} (hj : j₁ < j₂)
    (hlam : (i, j₂) ∈ lam) (hmu : (i, j₁) ∉ mu) : T i j₁ ≤ T i j₂ := T.row_weak' hj hlam hmu

theorem col_weak (T : SuperSkewSSYT lam mu b a) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hlam : (i₂, j) ∈ lam) (hmu : (i₁, j) ∉ mu) : T i₁ j ≤ T i₂ j := T.col_weak' hi hlam hmu

theorem col_strict_even (T : SuperSkewSSYT lam mu b a) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hlam : (i₂, j) ∈ lam) (hmu : (i₁, j) ∉ mu) (hb : T i₁ j < b) : T i₁ j < T i₂ j :=
  T.col_strict_even' hi hlam hmu hb

theorem row_strict_odd (T : SuperSkewSSYT lam mu b a) {i j₁ j₂ : ℕ} (hj : j₁ < j₂)
    (hlam : (i, j₂) ∈ lam) (hmu : (i, j₁) ∉ mu) (hb : b ≤ T i j₁) : T i j₁ < T i j₂ :=
  T.row_strict_odd' hj hlam hmu hb

theorem zeros (T : SuperSkewSSYT lam mu b a) {i j : ℕ} (h : (i, j) ∉ skewCells lam mu) :
    T i j = 0 := T.zeros' h

@[ext] theorem ext {T T' : SuperSkewSSYT lam mu b a} (h : ∀ i j, T i j = T' i j) : T = T' :=
  DFunLike.coe_injective (funext fun i => funext fun j => h i j)

/-- **Monotone in both coordinates at once.**  The route from `(i₁, j₁)` to `(i₂, j₂)` goes
through `(i₁, j₂)`, which is a skew cell because `lam` and `mu` are lower sets. -/
theorem mono (T : SuperSkewSSYT lam mu b a) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂)
    (h₂ : (i₂, j₂) ∈ lam) (h₁ : (i₁, j₁) ∉ mu) : T i₁ j₁ ≤ T i₂ j₂ := by
  have hmid_lam : (i₁, j₂) ∈ lam := lam.up_left_mem hi le_rfl h₂
  have hmid_mu : (i₁, j₂) ∉ mu := fun hc => h₁ (mu.up_left_mem le_rfl hj hc)
  have step₁ : T i₁ j₁ ≤ T i₁ j₂ := by
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact le_rfl
    · exact T.row_weak hlt hmid_lam h₁
  have step₂ : T i₁ j₂ ≤ T i₂ j₂ := by
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact le_rfl
    · exact T.col_weak hlt h₂ hmid_mu
  exact step₁.trans step₂

/-- A super tableau is determined by its restriction to the skew cells. -/
theorem restrict_injective (lam mu : YoungDiagram) (b a : ℕ) :
    Function.Injective fun (T : SuperSkewSSYT lam mu b a) (c : skewCells lam mu) =>
      (⟨T c.1.1 c.1.2, T.lt_add c.2⟩ : Fin (b + a)) := by
  intro T T' h
  refine SuperSkewSSYT.ext fun i j => ?_
  by_cases hc : (i, j) ∈ skewCells lam mu
  · exact congrArg Fin.val (congrFun h ⟨(i, j), hc⟩)
  · rw [T.zeros hc, T'.zeros hc]

noncomputable instance instFintype (lam mu : YoungDiagram) (b a : ℕ) :
    Fintype (SuperSkewSSYT lam mu b a) :=
  Fintype.ofInjective _ (restrict_injective lam mu b a)

end SuperSkewSSYT

/-- The weight of a super letter: `β k` for the even letter `k < b`, `α (k - b)` for the odd
letter `b ≤ k`. -/
def superWeight (b : ℕ) (β α : ℕ → R) (k : ℕ) : R := if k < b then β k else α (k - b)

omit [CommSemiring R] in
@[simp] theorem superWeight_of_lt {b k : ℕ} (β α : ℕ → R) (h : k < b) :
    superWeight b β α k = β k := if_pos h

omit [CommSemiring R] in
@[simp] theorem superWeight_of_le {b k : ℕ} (β α : ℕ → R) (h : b ≤ k) :
    superWeight b β α k = α (k - b) := if_neg (Nat.not_lt.mpr h)

/-- **The supersymmetric skew Schur function**, defined as Berele--Regev define it: the
generating function of the super tableaux of shape `lam / mu`, each weighted by the product of
its letters' variables,

`s_{lam/mu}(β | α) = ∑_T ∏_{(i,j) ∈ lam/mu} x_{T i j}`,

where `x_k` is `β k` for an even letter and `α (k - b)` for an odd one.  The branching formula
`s_{lam/mu}(β | α) = ∑_{mu ⊆ nu ⊆ lam} s_{nu/mu}(β) · s_{lam'/nu'}(α)` is
`superSkewSchur_eq_branching`. -/
noncomputable def superSkewSchur (lam mu : YoungDiagram) (b a : ℕ) (β α : ℕ → R) : R :=
  ∑ T : SuperSkewSSYT lam mu b a, ∏ c ∈ skewCells lam mu, superWeight b β α (T c.1 c.2)

/-! ### The even/odd split

A super tableau splits at the boundary between the two alphabets.  The cells carrying an even
letter form a skew shape `nu / mu` with `mu ⊆ nu ⊆ lam`, because the filling is weakly increasing
in both directions and the even letters precede the odd ones; what is left, `lam / nu`, carries
the odd letters, and its *transpose* is an ordinary tableau.
-/

namespace SuperSkewSSYT

variable {lam mu : YoungDiagram} {b a : ℕ}

/-- The shape cut out by the even letters: `mu` together with the cells of `lam / mu` whose entry
is an even letter.  It is a Young diagram because `T` is monotone in both coordinates. -/
def evenPart (T : SuperSkewSSYT lam mu b a) : YoungDiagram where
  cells := mu.cells ∪ (skewCells lam mu).filter fun c => T c.1 c.2 < b
  isLowerSet := by
    rintro ⟨i₂, j₂⟩ ⟨i₁, j₁⟩ ⟨hi, hj⟩ hmem
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_filter, YoungDiagram.mem_cells,
      mem_skewCells] at hmem ⊢
    by_cases h₁ : (i₁, j₁) ∈ mu
    · exact Or.inl h₁
    refine Or.inr ⟨⟨?_, h₁⟩, ?_⟩
    · rcases hmem with h | ⟨⟨h, -⟩, -⟩
      · exact absurd (mu.up_left_mem hi hj h) h₁
      · exact lam.up_left_mem hi hj h
    · rcases hmem with h | ⟨⟨h, -⟩, hlt⟩
      · exact absurd (mu.up_left_mem hi hj h) h₁
      · exact lt_of_le_of_lt (T.mono hi hj h h₁) hlt

theorem mem_evenPart {T : SuperSkewSSYT lam mu b a} {i j : ℕ} :
    (i, j) ∈ T.evenPart ↔ (i, j) ∈ mu ∨ ((i, j) ∈ skewCells lam mu ∧ T i j < b) := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h)
  · rintro (h | ⟨h₁, h₂⟩)
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h₁, h₂⟩)

theorem mu_le_evenPart (T : SuperSkewSSYT lam mu b a) : mu ≤ T.evenPart := by
  intro c hc
  exact mem_evenPart.mpr (Or.inl hc)

theorem evenPart_le (T : SuperSkewSSYT lam mu b a) (hmu : mu ≤ lam) : T.evenPart ≤ lam := by
  rintro ⟨i, j⟩ hc
  rcases mem_evenPart.mp hc with h | ⟨h, -⟩
  · exact hmu h
  · exact (mem_skewCells.mp h).1

theorem evenPart_mem_youngIcc (T : SuperSkewSSYT lam mu b a) (hmu : mu ≤ lam) :
    T.evenPart ∈ youngIcc mu lam :=
  mem_youngIcc.mpr ⟨T.mu_le_evenPart, T.evenPart_le hmu⟩

/-- A skew cell of `evenPart T / mu` is a cell of `lam`. -/
theorem mem_lam_of_mem_even {T : SuperSkewSSYT lam mu b a} {i j : ℕ}
    (h : (i, j) ∈ skewCells T.evenPart mu) : (i, j) ∈ lam := by
  obtain ⟨h₁, h₂⟩ := mem_skewCells.mp h
  rcases mem_evenPart.mp h₁ with hc | ⟨hc, -⟩
  · exact absurd hc h₂
  · exact (mem_skewCells.mp hc).1

/-- On the even part the entry is an even letter. -/
theorem lt_of_mem_evenPart {T : SuperSkewSSYT lam mu b a} {i j : ℕ}
    (h : (i, j) ∈ skewCells T.evenPart mu) : T i j < b := by
  obtain ⟨h₁, h₂⟩ := mem_skewCells.mp h
  rcases mem_evenPart.mp h₁ with h | ⟨-, hlt⟩
  · exact absurd h h₂
  · exact hlt

/-- Off the even part the entry is an odd letter. -/
theorem le_of_mem_odd {T : SuperSkewSSYT lam mu b a} {i j : ℕ}
    (h : (i, j) ∈ skewCells lam T.evenPart) : b ≤ T i j := by
  obtain ⟨h₁, h₂⟩ := mem_skewCells.mp h
  by_contra hlt
  exact h₂ (mem_evenPart.mpr (Or.inr ⟨mem_skewCells.mpr ⟨h₁, fun hc =>
    h₂ (mem_evenPart.mpr (Or.inl hc))⟩, Nat.not_le.mp hlt⟩))

end SuperSkewSSYT

/-! ### Restricting a super tableau to its two halves -/

namespace SuperSkewSSYT

variable {lam mu : YoungDiagram} {b a : ℕ}

/-- The even half: the entries on `evenPart T / mu`, an ordinary tableau with letters `< b`. -/
def evenTab (T : SuperSkewSSYT lam mu b a) : BoundedSkewSSYT T.evenPart mu b :=
  ⟨{ entry := fun i j => if (i, j) ∈ skewCells T.evenPart mu then T i j else 0
     row_weak' := by
       intro i j₁ j₂ hj hnu hmu
       obtain ⟨h₁, h₂⟩ := mem_skewCells_of_row hj hnu hmu
       rw [if_pos h₁, if_pos h₂]
       exact T.row_weak hj (mem_lam_of_mem_even h₂) hmu
     col_strict' := by
       intro i₁ i₂ j hi hnu hmu
       obtain ⟨h₁, h₂⟩ := mem_skewCells_of_col hi hnu hmu
       rw [if_pos h₁, if_pos h₂]
       exact T.col_strict_even hi (mem_lam_of_mem_even h₂) hmu (lt_of_mem_evenPart h₁)
     zeros' := by intro i j h; rw [if_neg h] }, by
    intro i j h
    change (if (i, j) ∈ skewCells T.evenPart mu then T i j else 0) < b
    rw [if_pos h]
    exact lt_of_mem_evenPart h⟩

/-- The odd half, transposed: the entries on `lam / evenPart T`, shifted down by `b` and read
with the indices swapped, an ordinary tableau of `lam' / (evenPart T)'` with letters `< a`. -/
def oddTab (T : SuperSkewSSYT lam mu b a) :
    BoundedSkewSSYT lam.transpose T.evenPart.transpose a :=
  ⟨{ entry := fun c r => T r c - b
     row_weak' := by
       intro c r₁ r₂ hr hlam hnu
       rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk] at hlam
       rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk] at hnu
       exact Nat.sub_le_sub_right
         (T.col_weak hr hlam fun hc => hnu (T.mu_le_evenPart hc)) b
     col_strict' := by
       intro c₁ c₂ r hc hlam hnu
       rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk] at hlam
       rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk] at hnu
       have hmu : (r, c₁) ∉ mu := fun h => hnu (T.mu_le_evenPart h)
       have hcell : (r, c₁) ∈ skewCells lam T.evenPart :=
         mem_skewCells.mpr ⟨lam.up_left_mem le_rfl hc.le hlam, hnu⟩
       have hb : b ≤ T r c₁ := le_of_mem_odd hcell
       have hlt := T.row_strict_odd hc hlam hmu hb
       omega
     zeros' := by
       intro c r h
       rw [mem_skewCells] at h
       push Not at h
       rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk] at h
       by_cases hlam : (r, c) ∈ lam
       · have hnu : (r, c) ∈ T.evenPart := by
           have := h hlam
           rwa [YoungDiagram.mem_transpose, Prod.swap_prod_mk] at this
         by_cases hmu : (r, c) ∈ mu
         · have : T r c = 0 := T.zeros fun hcc => (mem_skewCells.mp hcc).2 hmu
           omega
         · have : T r c < b := lt_of_mem_evenPart (mem_skewCells.mpr ⟨hnu, hmu⟩)
           omega
       · have : T r c = 0 := T.zeros (notMem_skewCells_of_notMem hlam)
         omega }, by
    intro c r hcell
    change T r c - b < a
    rw [mem_skewCells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
      YoungDiagram.mem_transpose, Prod.swap_prod_mk] at hcell
    have hodd : (r, c) ∈ skewCells lam T.evenPart := mem_skewCells.mpr hcell
    have h1 : b ≤ T r c := le_of_mem_odd hodd
    have h2 : T r c < b + a :=
      T.lt_add (mem_skewCells.mpr ⟨hcell.1, fun h => hcell.2 (T.mu_le_evenPart h)⟩)
    omega⟩

end SuperSkewSSYT

/-! ### Reassembling a super tableau from its two halves -/

/-- For `mu ⊆ nu ⊆ lam` the skew cells of `lam / mu` split into those of `nu / mu` and those of
`lam / nu`. -/
theorem mem_skewCells_split {lam mu nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam)
    {c : ℕ × ℕ} :
    c ∈ skewCells lam mu ↔ c ∈ skewCells nu mu ∨ c ∈ skewCells lam nu := by
  simp only [mem_skewCells]
  constructor
  · rintro ⟨hl, hm⟩
    by_cases hn : c ∈ nu
    · exact Or.inl ⟨hn, hm⟩
    · exact Or.inr ⟨hl, hn⟩
  · rintro (⟨hn, hm⟩ | ⟨hl, hn⟩)
    · exact ⟨hnl hn, hm⟩
    · exact ⟨hl, fun hc => hn (hmn hc)⟩

theorem skewCells_disjoint {lam mu nu : YoungDiagram} :
    Disjoint (skewCells nu mu) (skewCells lam nu) := by
  rw [Finset.disjoint_left]
  intro c h₁ h₂
  exact (mem_skewCells.mp h₂).2 (mem_skewCells.mp h₁).1

namespace SuperSkewSSYT

variable {lam mu : YoungDiagram} {b a : ℕ}

/-- The super tableau assembled from an even tableau on `nu / mu` and a transposed odd tableau
on `lam' / nu'`. -/
def ofParts {nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam)
    (E : BoundedSkewSSYT nu mu b) (O : BoundedSkewSSYT lam.transpose nu.transpose a) :
    SuperSkewSSYT lam mu b a where
  entry i j :=
    if (i, j) ∈ skewCells nu mu then E i j
    else if (i, j) ∈ skewCells lam nu then O j i + b else 0
  lt' := by
    intro i j h
    rcases (mem_skewCells_split hmn hnl).mp h with he | ho
    · rw [if_pos he]
      exact lt_of_lt_of_le (E.lt_of_mem_cells he) (Nat.le_add_right _ _)
    · rw [if_neg (Finset.disjoint_left.mp skewCells_disjoint · ho |> fun f => f), if_pos ho]
      have : O j i < a := O.lt_of_mem_cells (by
        rw [mem_skewCells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
          YoungDiagram.mem_transpose, Prod.swap_prod_mk]
        exact mem_skewCells.mp ho)
      omega
  row_weak' := by
    intro i j₁ j₂ hj hlam hmu
    have h₁lam : (i, j₁) ∈ lam := lam.up_left_mem le_rfl hj.le hlam
    by_cases hn₁ : (i, j₁) ∈ nu
    · have he₁ : (i, j₁) ∈ skewCells nu mu := mem_skewCells.mpr ⟨hn₁, hmu⟩
      rw [if_pos he₁]
      by_cases hn₂ : (i, j₂) ∈ nu
      · have he₂ : (i, j₂) ∈ skewCells nu mu :=
          mem_skewCells.mpr ⟨hn₂, fun hc => hmu (mu.up_left_mem le_rfl hj.le hc)⟩
        rw [if_pos he₂]
        exact E.1.row_weak hj hn₂ hmu
      · have ho₂ : (i, j₂) ∈ skewCells lam nu := mem_skewCells.mpr ⟨hlam, hn₂⟩
        rw [if_neg (notMem_skewCells_of_notMem hn₂), if_pos ho₂]
        exact le_trans (E.lt_of_mem_cells he₁).le (Nat.le_add_left _ _)
    · have hn₂ : (i, j₂) ∉ nu := fun hc => hn₁ (nu.up_left_mem le_rfl hj.le hc)
      have ho₁ : (i, j₁) ∈ skewCells lam nu := mem_skewCells.mpr ⟨h₁lam, hn₁⟩
      have ho₂ : (i, j₂) ∈ skewCells lam nu := mem_skewCells.mpr ⟨hlam, hn₂⟩
      rw [if_neg (notMem_skewCells_of_notMem hn₁), if_pos ho₁,
        if_neg (notMem_skewCells_of_notMem hn₂), if_pos ho₂]
      have := O.1.col_strict hj (by
        rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]; exact hlam) (by
        rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]; exact hn₁)
      omega
  col_weak' := by
    intro i₁ i₂ j hi hlam hmu
    have h₁lam : (i₁, j) ∈ lam := lam.up_left_mem hi.le le_rfl hlam
    by_cases hn₁ : (i₁, j) ∈ nu
    · have he₁ : (i₁, j) ∈ skewCells nu mu := mem_skewCells.mpr ⟨hn₁, hmu⟩
      rw [if_pos he₁]
      by_cases hn₂ : (i₂, j) ∈ nu
      · have he₂ : (i₂, j) ∈ skewCells nu mu :=
          mem_skewCells.mpr ⟨hn₂, fun hc => hmu (mu.up_left_mem hi.le le_rfl hc)⟩
        rw [if_pos he₂]
        exact (E.1.col_strict hi hn₂ hmu).le
      · have ho₂ : (i₂, j) ∈ skewCells lam nu := mem_skewCells.mpr ⟨hlam, hn₂⟩
        rw [if_neg (notMem_skewCells_of_notMem hn₂), if_pos ho₂]
        exact le_trans (E.lt_of_mem_cells he₁).le (Nat.le_add_left _ _)
    · have hn₂ : (i₂, j) ∉ nu := fun hc => hn₁ (nu.up_left_mem hi.le le_rfl hc)
      have ho₁ : (i₁, j) ∈ skewCells lam nu := mem_skewCells.mpr ⟨h₁lam, hn₁⟩
      have ho₂ : (i₂, j) ∈ skewCells lam nu := mem_skewCells.mpr ⟨hlam, hn₂⟩
      rw [if_neg (notMem_skewCells_of_notMem hn₁), if_pos ho₁,
        if_neg (notMem_skewCells_of_notMem hn₂), if_pos ho₂]
      have := O.1.row_weak hi (by
        rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]; exact hlam) (by
        rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]; exact hn₁)
      omega
  col_strict_even' := by
    intro i₁ i₂ j hi hlam hmu hb
    have h₁lam : (i₁, j) ∈ lam := lam.up_left_mem hi.le le_rfl hlam
    have hn₁ : (i₁, j) ∈ nu := by
      by_contra hn
      have ho₁ : (i₁, j) ∈ skewCells lam nu := mem_skewCells.mpr ⟨h₁lam, hn⟩
      rw [if_neg (notMem_skewCells_of_notMem hn), if_pos ho₁] at hb
      omega
    have he₁ : (i₁, j) ∈ skewCells nu mu := mem_skewCells.mpr ⟨hn₁, hmu⟩
    rw [if_pos he₁]
    by_cases hn₂ : (i₂, j) ∈ nu
    · rw [if_pos (mem_skewCells.mpr
        ⟨hn₂, fun hc => hmu (mu.up_left_mem hi.le le_rfl hc)⟩)]
      exact E.1.col_strict hi hn₂ hmu
    · have ho₂ : (i₂, j) ∈ skewCells lam nu := mem_skewCells.mpr ⟨hlam, hn₂⟩
      rw [if_neg (notMem_skewCells_of_notMem hn₂), if_pos ho₂]
      have hE : E i₁ j < b := E.lt_of_mem_cells he₁
      omega
  row_strict_odd' := by
    intro i j₁ j₂ hj hlam hmu hb
    have h₁lam : (i, j₁) ∈ lam := lam.up_left_mem le_rfl hj.le hlam
    have hn₁ : (i, j₁) ∉ nu := by
      intro hn
      rw [if_pos (mem_skewCells.mpr ⟨hn, hmu⟩)] at hb
      have hE : E i j₁ < b := E.lt_of_mem_cells (mem_skewCells.mpr ⟨hn, hmu⟩)
      omega
    have hn₂ : (i, j₂) ∉ nu := fun hc => hn₁ (nu.up_left_mem le_rfl hj.le hc)
    have ho₁ : (i, j₁) ∈ skewCells lam nu := mem_skewCells.mpr ⟨h₁lam, hn₁⟩
    have ho₂ : (i, j₂) ∈ skewCells lam nu := mem_skewCells.mpr ⟨hlam, hn₂⟩
    rw [if_neg (notMem_skewCells_of_notMem hn₁), if_pos ho₁,
      if_neg (notMem_skewCells_of_notMem hn₂), if_pos ho₂]
    have hO : O j₁ i < O j₂ i := O.1.col_strict hj (by
      rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]; exact hlam) (by
      rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]; exact hn₁)
    omega
  zeros' := by
    intro i j h
    rw [mem_skewCells_split hmn hnl] at h
    push Not at h
    rw [if_neg h.1, if_neg h.2]

end SuperSkewSSYT

/-! ### The two halves determine the tableau -/

namespace SuperSkewSSYT

variable {lam mu : YoungDiagram} {b a : ℕ}

@[simp] theorem ofParts_apply {nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam)
    (E : BoundedSkewSSYT nu mu b) (O : BoundedSkewSSYT lam.transpose nu.transpose a) (i j : ℕ) :
    ofParts hmn hnl E O i j =
      if (i, j) ∈ skewCells nu mu then E i j
      else if (i, j) ∈ skewCells lam nu then O j i + b else 0 := rfl

/-- The even part of an assembled tableau is the shape it was assembled along. -/
theorem evenPart_ofParts {nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam)
    (E : BoundedSkewSSYT nu mu b) (O : BoundedSkewSSYT lam.transpose nu.transpose a) :
    (ofParts hmn hnl E O).evenPart = nu := by
  ext ⟨i, j⟩
  rw [show ((i, j) ∈ (ofParts hmn hnl E O).evenPart.cells) =
      ((i, j) ∈ (ofParts hmn hnl E O).evenPart) from rfl, mem_evenPart]
  constructor
  · rintro (h | ⟨hc, hlt⟩)
    · exact hmn h
    · by_cases hn : (i, j) ∈ nu
      · exact hn
      · exfalso
        have ho : (i, j) ∈ skewCells lam nu := mem_skewCells.mpr ⟨(mem_skewCells.mp hc).1, hn⟩
        rw [ofParts_apply, if_neg (notMem_skewCells_of_notMem hn), if_pos ho] at hlt
        omega
  · intro hn
    by_cases hm : (i, j) ∈ mu
    · exact Or.inl hm
    · have he : (i, j) ∈ skewCells nu mu := mem_skewCells.mpr ⟨hn, hm⟩
      refine Or.inr ⟨mem_skewCells.mpr ⟨hnl hn, hm⟩, ?_⟩
      rw [ofParts_apply, if_pos he]
      exact E.lt_of_mem_cells he

/-- Reassembling a tableau from its own two halves returns it. -/
theorem ofParts_evenTab_oddTab (T : SuperSkewSSYT lam mu b a) (hmu : mu ≤ lam) :
    ofParts T.mu_le_evenPart (T.evenPart_le hmu) T.evenTab T.oddTab = T := by
  ext i j
  rw [ofParts_apply]
  by_cases he : (i, j) ∈ skewCells T.evenPart mu
  · rw [if_pos he]
    change (if (i, j) ∈ skewCells T.evenPart mu then T i j else 0) = T i j
    rw [if_pos he]
  · rw [if_neg he]
    by_cases ho : (i, j) ∈ skewCells lam T.evenPart
    · rw [if_pos ho]
      change T i j - b + b = T i j
      have := le_of_mem_odd ho
      omega
    · rw [if_neg ho]
      exact (T.zeros fun hc => by
        rcases (mem_skewCells_split T.mu_le_evenPart (T.evenPart_le hmu)).mp hc with h | h
        · exact he h
        · exact ho h).symm

/-- The even half of an assembled tableau agrees with the half it was assembled from.  Stated on
entries, since the two live in types indexed by shapes that are equal but not syntactically so. -/
theorem evenTab_ofParts_apply {nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam)
    (E : BoundedSkewSSYT nu mu b) (O : BoundedSkewSSYT lam.transpose nu.transpose a) (i j : ℕ) :
    (ofParts hmn hnl E O).evenTab i j = E i j := by
  change (if (i, j) ∈ skewCells (ofParts hmn hnl E O).evenPart mu
    then (ofParts hmn hnl E O) i j else 0) = E i j
  rw [evenPart_ofParts]
  by_cases he : (i, j) ∈ skewCells nu mu
  · rw [if_pos he, ofParts_apply, if_pos he]
  · rw [if_neg he, E.1.zeros he]

/-- The odd half of an assembled tableau agrees with the half it was assembled from. -/
theorem oddTab_ofParts_apply {nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam)
    (E : BoundedSkewSSYT nu mu b) (O : BoundedSkewSSYT lam.transpose nu.transpose a) (c r : ℕ) :
    (ofParts hmn hnl E O).oddTab c r = O c r := by
  change (ofParts hmn hnl E O) r c - b = O c r
  by_cases ho : (r, c) ∈ skewCells lam nu
  · rw [ofParts_apply, if_neg (notMem_skewCells_of_notMem (mem_skewCells.mp ho).2),
      if_pos ho]
    omega
  · have hz : O c r = 0 := O.1.zeros (by
      rw [mem_skewCells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
        YoungDiagram.mem_transpose, Prod.swap_prod_mk]
      rw [mem_skewCells] at ho
      push Not at ho
      exact fun hcon => hcon.2 (ho hcon.1))
    rw [hz, ofParts_apply]
    by_cases he : (r, c) ∈ skewCells nu mu
    · rw [if_pos he]
      have hE : E r c < b := E.lt_of_mem_cells he
      omega
    · rw [if_neg he, if_neg ho]
      omega

@[simp] theorem evenTab_apply (T : SuperSkewSSYT lam mu b a) (i j : ℕ) :
    T.evenTab i j = if (i, j) ∈ skewCells T.evenPart mu then T i j else 0 := rfl

@[simp] theorem oddTab_apply (T : SuperSkewSSYT lam mu b a) (c r : ℕ) :
    T.oddTab c r = T r c - b := rfl

/-- The even half at a shape known to be the even part. -/
def evenTabAt (T : SuperSkewSSYT lam mu b a) {nu : YoungDiagram} (h : T.evenPart = nu) :
    BoundedSkewSSYT nu mu b := by subst h; exact T.evenTab

/-- The odd half at a shape known to be the even part. -/
def oddTabAt (T : SuperSkewSSYT lam mu b a) {nu : YoungDiagram} (h : T.evenPart = nu) :
    BoundedSkewSSYT lam.transpose nu.transpose a := by subst h; exact T.oddTab

@[simp] theorem evenTabAt_apply (T : SuperSkewSSYT lam mu b a) {nu : YoungDiagram}
    (h : T.evenPart = nu) (i j : ℕ) : T.evenTabAt h i j = T.evenTab i j := by subst h; rfl

@[simp] theorem oddTabAt_apply (T : SuperSkewSSYT lam mu b a) {nu : YoungDiagram}
    (h : T.evenPart = nu) (c r : ℕ) : T.oddTabAt h c r = T.oddTab c r := by subst h; rfl

end SuperSkewSSYT

/-! ### The Berele--Regev branching rule -/

theorem skewCells_eq_union {lam mu nu : YoungDiagram} (hmn : mu ≤ nu) (hnl : nu ≤ lam) :
    skewCells lam mu = skewCells nu mu ∪ skewCells lam nu := by
  ext c
  rw [Finset.mem_union]
  exact mem_skewCells_split hmn hnl

/-- Transposing a skew shape swaps the coordinates of its cells. -/
theorem prod_skewCells_transpose {M : Type*} [CommMonoid M] (lam mu : YoungDiagram)
    (f : ℕ → ℕ → M) :
    ∏ c ∈ skewCells lam.transpose mu.transpose, f c.1 c.2
      = ∏ c ∈ skewCells lam mu, f c.2 c.1 := by
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ (fun a _ => Prod.swap_swap a)
    (fun a _ => Prod.swap_swap a) (fun a _ => rfl)
  · intro c hc
    rw [mem_skewCells, YoungDiagram.mem_transpose, YoungDiagram.mem_transpose] at hc
    exact mem_skewCells.mpr hc
  · intro c hc
    rw [mem_skewCells] at hc
    rw [mem_skewCells, YoungDiagram.mem_transpose, YoungDiagram.mem_transpose]
    exact hc

/-- **The Berele--Regev branching rule.**  A super tableau splits at the boundary between the two
alphabets, and the shape cut out by the even letters is the intermediate diagram:

`s_{lam/mu}(β | α) = ∑_{mu ⊆ nu ⊆ lam} s_{nu/mu}(β) · s_{lam'/nu'}(α)`. -/
theorem superSkewSchur_eq_branching (lam mu : YoungDiagram) (b a : ℕ) (β α : ℕ → R)
    (hmu : mu ≤ lam) :
    superSkewSchur lam mu b a β α =
      ∑ nu ∈ youngIcc mu lam, skewSchur nu mu b β * skewSchur lam.transpose nu.transpose a α := by
  classical
  rw [superSkewSchur, ← Finset.sum_fiberwise_of_maps_to
    (fun (T : SuperSkewSSYT lam mu b a) (_ : T ∈ Finset.univ) => T.evenPart_mem_youngIcc hmu)]
  refine Finset.sum_congr rfl fun nu hnu => ?_
  obtain ⟨hmn, hnl⟩ := mem_youngIcc.mp hnu
  rw [skewSchur, skewSchur, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_bij'
    (fun T hT => (T.evenTabAt (Finset.mem_filter.mp hT).2,
      T.oddTabAt (Finset.mem_filter.mp hT).2))
    (fun p _ => SuperSkewSSYT.ofParts hmn hnl p.1 p.2)
    (fun _ _ => Finset.mem_univ _) (fun p _ => ?_) (fun T hT => ?_) (fun p _ => ?_)
    (fun T hT => ?_)
  · -- the assembled tableau lies in the fiber over `nu`
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      SuperSkewSSYT.evenPart_ofParts hmn hnl p.1 p.2⟩
  · -- assembling the two halves of `T` returns `T`
    have hT' := (Finset.mem_filter.mp hT).2
    subst hT'
    exact SuperSkewSSYT.ofParts_evenTab_oddTab T hmu
  · -- taking the two halves of an assembled tableau returns them
    refine Prod.ext (BoundedSkewSSYT.ext fun i j => ?_) (BoundedSkewSSYT.ext fun c r => ?_)
    · rw [SuperSkewSSYT.evenTabAt_apply, SuperSkewSSYT.evenTab_ofParts_apply]
    · rw [SuperSkewSSYT.oddTabAt_apply, SuperSkewSSYT.oddTab_ofParts_apply]
  · -- the weight splits as the product of the two halves' weights
    have hT' := (Finset.mem_filter.mp hT).2
    have h1 : ∏ c ∈ skewCells nu mu, superWeight b β α (T c.1 c.2)
        = ∏ c ∈ skewCells nu mu, β (T.evenTabAt hT' c.1 c.2) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      have hlt : T c.1 c.2 < b := by subst hT'; exact SuperSkewSSYT.lt_of_mem_evenPart hc
      rw [superWeight_of_lt _ _ hlt, SuperSkewSSYT.evenTabAt_apply,
        SuperSkewSSYT.evenTab_apply, if_pos (by subst hT'; exact hc)]
    have h2 : ∏ c ∈ skewCells lam nu, superWeight b β α (T c.1 c.2)
        = ∏ c ∈ skewCells lam.transpose nu.transpose, α (T.oddTabAt hT' c.1 c.2) := by
      rw [prod_skewCells_transpose lam nu fun i j => α (T.oddTabAt hT' i j)]
      refine Finset.prod_congr rfl fun c hc => ?_
      have hle : b ≤ T c.1 c.2 := by subst hT'; exact SuperSkewSSYT.le_of_mem_odd hc
      rw [superWeight_of_le _ _ hle, SuperSkewSSYT.oddTabAt_apply, SuperSkewSSYT.oddTab_apply]
    rw [skewCells_eq_union hmn hnl, Finset.prod_union skewCells_disjoint, h1, h2]

/-- At `a = 0` only `nu = lam` survives, and the branching sum is the one-alphabet
skew Schur function in the even variables. -/
theorem superSkewSchur_zero_odd {lam mu : YoungDiagram} {b : ℕ} (β α : ℕ → R)
    (hmu : mu ≤ lam) : superSkewSchur lam mu b 0 β α = skewSchur lam mu b β := by
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ hmu]
  rw [Finset.sum_eq_single_of_mem lam (mem_youngIcc.mpr ⟨hmu, le_rfl⟩)]
  · rw [skewSchur_of_le 0 α le_rfl, mul_one]
  · intro nu hnu hne
    have hle : nu ≤ lam := (mem_youngIcc.mp hnu).2
    have hne' : skewCells lam.transpose nu.transpose ≠ ∅ := fun hcon =>
      hne (le_antisymm hle
        (YoungDiagram.transpose_le_iff.mp (skewCells_eq_empty_iff.mp hcon)))
    obtain ⟨j, hj⟩ := exists_skewColLen_pos hne'
    rw [skewSchur_eq_zero_of_lt_skewColLen α hj, mul_zero]

/-- At `b = 0` only `nu = mu` survives, and the branching sum is the one-alphabet
skew Schur function of the conjugate shape in the odd variables. -/
theorem superSkewSchur_zero_even {lam mu : YoungDiagram} {a : ℕ} (β α : ℕ → R)
    (hmu : mu ≤ lam) :
    superSkewSchur lam mu 0 a β α = skewSchur lam.transpose mu.transpose a α := by
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ hmu]
  rw [Finset.sum_eq_single_of_mem mu (mem_youngIcc.mpr ⟨le_rfl, hmu⟩)]
  · rw [skewSchur_of_le 0 β le_rfl, one_mul]
  · intro nu hnu hne
    have hle : mu ≤ nu := (mem_youngIcc.mp hnu).1
    have hne' : skewCells nu mu ≠ ∅ := fun hcon =>
      hne (le_antisymm (skewCells_eq_empty_iff.mp hcon) hle)
    obtain ⟨j, hj⟩ := exists_skewColLen_pos hne'
    rw [skewSchur_eq_zero_of_lt_skewColLen β hj, zero_mul]

/-- Compatibility with `Shields.Combinatorics.Young.SchurPolynomial`: at `mu = ⊥` and `a = 0` the
branching sum is the one-alphabet Schur polynomial of that module, so the theory here extends it
rather than running beside it. -/
theorem superSkewSchur_bot_zero_odd (lam : YoungDiagram) (b : ℕ) (β α : ℕ → R) :
    superSkewSchur lam ⊥ b 0 β α = schur lam b β := by
  rw [superSkewSchur_zero_odd β α bot_le, skewSchur_bot]

/-! ## The skew-hook criterion -/

/-- The skew diagram `lam / mu` carries no block of `b+1` rows by `a+1` columns.
A block with upper-left corner `(i, j)` is present exactly when its lower-right
corner lies in `lam` and its upper-left corner lies outside `mu`, so its absence
is the implication below.

This is the right-hand side of the hook criterion; the equivalent form `λ_{u+b} - μ_u ≤ a` is
`noBigRect_iff_rowLen`.  The block has `b+1` rows and
`a+1` columns: `λ_{u+b} - μ_u > a` puts `a+1` common columns into the `b+1` rows
`u, …, u+b`. -/
def NoBigRect (lam mu : YoungDiagram) (b a : ℕ) : Prop :=
  ∀ i j : ℕ, (i + b, j + a) ∈ lam → (i, j) ∈ mu

/-- **The hook criterion, right-hand side, in part form.**  The block condition
on `lam / mu` is `λ_{u+b} ≤ μ_u + a` for every `u`; the conditions with `u + b`
past the last row hold automatically, because `rowLen` vanishes there. -/
theorem noBigRect_iff_rowLen {lam mu : YoungDiagram} {a b : ℕ} :
    NoBigRect lam mu b a ↔ ∀ i : ℕ, lam.rowLen (i + b) ≤ mu.rowLen i + a := by
  constructor
  · intro h i
    by_contra hlt
    have hc : (i + b, mu.rowLen i + a) ∈ lam :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact YoungDiagram.notMem_iff_le_rowLen.mpr le_rfl (h i (mu.rowLen i) hc)
  · intro h i j hc
    have h1 : j + a < lam.rowLen (i + b) := YoungDiagram.mem_iff_lt_rowLen.mp hc
    have h2 := h i
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)

/-- **The vanishing half of the hook criterion.**  A block of `b+1` rows by
`a+1` columns inside `lam / mu` kills every summand of the branching formula.
Split on the lower-left corner `(i+b, j)` of the
block: inside `nu` it makes column `j` of `nu / mu` at least `b+1` tall, outside
`nu` it makes row `i+b` of `lam / nu` at least `a+1` long. -/
theorem superSkewSchur_eq_zero_of_block {lam mu : YoungDiagram} {a b i j : ℕ}
    (β α : ℕ → R) (hml : mu ≤ lam) (hlam : (i + b, j + a) ∈ lam) (hmu : (i, j) ∉ mu) :
    superSkewSchur lam mu b a β α = 0 := by
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ hml]
  refine Finset.sum_eq_zero fun nu _ => ?_
  by_cases hnu : (i + b, j) ∈ nu
  · -- column `j` of `nu / mu` is at least `b+1` tall
    have h1 : i + b < nu.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hnu
    have h2 : mu.colLen j ≤ i := YoungDiagram.notMem_iff_le_colLen.mp hmu
    have : b < skewColLen nu mu j := by simp only [skewColLen]; omega
    rw [skewSchur_eq_zero_of_lt_skewColLen β this, zero_mul]
  · -- row `i + b` of `lam / nu` is at least `a+1` long
    have h1 : j + a < lam.rowLen (i + b) := YoungDiagram.mem_iff_lt_rowLen.mp hlam
    have h2 : nu.rowLen (i + b) ≤ j := YoungDiagram.notMem_iff_le_rowLen.mp hnu
    have : a < skewColLen lam.transpose nu.transpose (i + b) := by
      rw [skewColLen_transpose]
      simp only [skewRowLen]
      omega
    rw [skewSchur_eq_zero_of_lt_skewColLen α this, mul_zero]

/-- The intermediate shape the positivity half of the criterion evaluates at,
`μ ⊔ dropCols lam a`, lies between `μ` and `λ`, so it is a term of the branching
sum. -/
theorem le_sup_dropCols {lam mu : YoungDiagram} {a : ℕ} (hmu : mu ≤ lam) :
    mu ≤ mu ⊔ dropCols lam a ∧ mu ⊔ dropCols lam a ≤ lam :=
  ⟨le_sup_left, sup_le hmu (dropCols_le lam a)⟩

/-- Every column of `ν / μ` has height at most `b`, for `ν = μ ⊔ dropCols lam a`.
A taller column would put the corner `(mu.colLen j, j)` outside `mu` with
`(mu.colLen j + b, j + a)` inside `lam`, which is the forbidden block. -/
theorem skewColLen_sup_dropCols_le {lam mu : YoungDiagram} {a b : ℕ}
    (h : NoBigRect lam mu b a) (j : ℕ) :
    skewColLen (mu ⊔ dropCols lam a) mu j ≤ b := by
  by_contra hcon
  simp only [skewColLen] at hcon
  set c := mu.colLen j with hc
  have hmem : (c + b, j) ∈ mu ⊔ dropCols lam a :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hcnot : (c, j) ∉ mu := YoungDiagram.notMem_iff_le_colLen.mpr le_rfl
  rcases YoungDiagram.mem_sup.mp hmem with hin | hin
  · exact hcnot (mu.up_left_mem (Nat.le_add_right c b) le_rfl hin)
  · exact hcnot (h c j (mem_dropCols.mp hin))

/-- Every row of `lam / ν` has length at most `a`, for `ν = μ ⊔ dropCols lam a`.
A longer row would put a cell of `dropCols lam a` past the end of row `i` of
`ν`. -/
theorem skewRowLen_sup_dropCols_le (lam mu : YoungDiagram) (a i : ℕ) :
    skewRowLen lam (mu ⊔ dropCols lam a) i ≤ a := by
  by_contra hcon
  simp only [skewRowLen] at hcon
  set w := (mu ⊔ dropCols lam a).rowLen i with hw
  have hlam : (i, w + a) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hin : (i, w) ∈ mu ⊔ dropCols lam a :=
    YoungDiagram.mem_sup.mpr (Or.inr (mem_dropCols.mpr hlam))
  exact YoungDiagram.notMem_iff_le_rowLen.mpr le_rfl hin

/-- **The positivity half of the hook criterion.** -/
theorem superSkewSchur_pos {lam mu : YoungDiagram} {a b : ℕ} {β α : ℕ → ℝ}
    (hmu : mu ≤ lam) (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i)
    (h : NoBigRect lam mu b a) : 0 < superSkewSchur lam mu b a β α := by
  rw [superSkewSchur_eq_branching _ _ _ _ _ _ hmu]
  refine Finset.sum_pos' (fun nu _ => ?_) ⟨mu ⊔ dropCols lam a, ?_, ?_⟩
  · exact mul_nonneg (skewSchur_nonneg fun i hi => (hβ i hi).le)
      (skewSchur_nonneg fun i hi => (hα i hi).le)
  · exact mem_youngIcc.mpr (le_sup_dropCols hmu)
  · refine mul_pos (skewSchur_pos hβ (skewColLen_sup_dropCols_le h))
      (skewSchur_pos hα fun i => ?_)
    rw [skewColLen_transpose]
    exact skewRowLen_sup_dropCols_le lam mu a i

/-- **The supersymmetric hook criterion.**  With `mu ⊆ lam`, `b`
positive even variables and `a` positive odd variables, the supersymmetric skew
Schur function of `lam / mu` is positive exactly when `lam / mu` contains no
block of `b+1` rows by `a+1` columns. -/
theorem superSkewSchur_pos_iff {lam mu : YoungDiagram} {a b : ℕ} {β α : ℕ → ℝ}
    (hmu : mu ≤ lam) (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i) :
    0 < superSkewSchur lam mu b a β α ↔ NoBigRect lam mu b a := by
  refine ⟨fun hpos i j hcell => ?_, superSkewSchur_pos hmu hβ hα⟩
  by_contra hij
  exact absurd (superSkewSchur_eq_zero_of_block β α hmu hcell hij) (ne_of_gt hpos)

/-- The hook criterion in part form. -/
theorem superSkewSchur_pos_iff_rowLen {lam mu : YoungDiagram} {a b : ℕ} {β α : ℕ → ℝ}
    (hmu : mu ≤ lam) (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i) :
    0 < superSkewSchur lam mu b a β α ↔
      ∀ i : ℕ, lam.rowLen (i + b) ≤ mu.rowLen i + a := by
  rw [superSkewSchur_pos_iff hmu hβ hα, noBigRect_iff_rowLen]

/-- **The straight-shape case.**  At `mu = ⊥` the criterion is `λ_{b+1} ≤ a`: the
shape fits inside the hook with `b` rows of unbounded length and `a` unbounded
columns.  `lam.rowLen b` is `λ_{b+1}`, since `rowLen` counts rows from zero. -/
theorem superSkewSchur_bot_pos_iff {lam : YoungDiagram} {a b : ℕ} {β α : ℕ → ℝ}
    (hβ : ∀ i, i < b → 0 < β i) (hα : ∀ i, i < a → 0 < α i) :
    0 < superSkewSchur lam ⊥ b a β α ↔ lam.rowLen b ≤ a := by
  rw [superSkewSchur_pos_iff_rowLen bot_le hβ hα]
  refine ⟨fun h => by simpa [rowLen_bot] using h 0, fun h i => ?_⟩
  rw [rowLen_bot]
  exact le_trans (lam.rowLen_anti b (i + b) (Nat.le_add_left b i)) (by omega)

end Shields
