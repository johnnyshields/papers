/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.TwoRowFormulas
import SkewMarkedFactor.MixedCovariance
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase

/-!
# Unions of separated rows

Complete homogeneous monomials as skew diagrams.  For a list `l = [j₀, j₁, …]` the diagram
`rowUnion l i e` consists of the rows of `j₀, j₁, …` cells, placed from the top row `i`
downward, each row ending one column before the previous one begins.  Consecutive rows are
at content distance two and edge-nonadjacent, so the diagram is skew, its Schur function is
`h_{j₀} h_{j₁} ⋯`, and every modified composition is the product of the values on the rows.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- Rows of `l`, from row `i` downward, the first ending at column `e` (exclusive), each next
row ending one column before the previous one starts. -/
def rowUnion : List ℕ → ℤ → ℤ → Diagram
  | [], _, _ => ∅
  | j :: l, i, e => translate (i, e - j) (rowCells 0 (j : ℤ)) ∪ rowUnion l (i + 1) (e - j - 1)

theorem rowUnion_cons (j : ℕ) (l : List ℕ) (i e : ℤ) :
    rowUnion (j :: l) i e =
      translate (i, e - j) (rowCells 0 (j : ℤ)) ∪ rowUnion l (i + 1) (e - j - 1) := rfl

theorem mem_rowUnion_cons {j : ℕ} {l : List ℕ} {i e a b : ℤ} :
    (a, b) ∈ rowUnion (j :: l) i e ↔
      (a = i ∧ e - j ≤ b ∧ b < e) ∨ (a, b) ∈ rowUnion l (i + 1) (e - j - 1) := by
  rw [rowUnion_cons, Finset.mem_union, mem_translate, Prod.mk_sub_mk, mem_rowCells]
  constructor
  · rintro (⟨h1, h2, h3⟩ | h)
    · exact Or.inl ⟨by omega, by omega, by omega⟩
    · exact Or.inr h
  · rintro (⟨h1, h2, h3⟩ | h)
    · exact Or.inl ⟨by omega, by omega, by omega⟩
    · exact Or.inr h

theorem rowUnion_bound (l : List ℕ) : ∀ (i e : ℤ) (x : ℤ × ℤ), x ∈ rowUnion l i e →
    i ≤ x.1 ∧ x.2 < e := by
  induction l with
  | nil => intro i e x hx; simp [rowUnion] at hx
  | cons j l ih =>
    rintro i e ⟨a, b⟩ hx
    rcases mem_rowUnion_cons.mp hx with ⟨h1, h2, h3⟩ | h
    · exact ⟨by simp only; omega, by simp only; omega⟩
    · have := ih _ _ _ h
      simp only at this ⊢
      have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
      exact ⟨by omega, by omega⟩

theorem isSkew_rowUnion (l : List ℕ) : ∀ i e : ℤ, IsSkew (rowUnion l i e) := by
  induction l with
  | nil => intro i e; intro x hx; simp [rowUnion] at hx
  | cons j l ih =>
    intro i e
    rintro ⟨a, b⟩ hx ⟨c, d⟩ hy h1 h2 i' hi j' hj
    simp only [Finset.mem_Icc] at hi hj
    simp only at h1 h2 hi hj
    have hjn : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    rcases mem_rowUnion_cons.mp hx with ⟨ha, hb1, hb2⟩ | hx'
    · rcases mem_rowUnion_cons.mp hy with ⟨hc, hd1, hd2⟩ | hy'
      · exact mem_rowUnion_cons.mpr (Or.inl ⟨by omega, by omega, by omega⟩)
      · have := rowUnion_bound l _ _ _ hy'
        simp only at this
        omega
    · rcases mem_rowUnion_cons.mp hy with ⟨hc, hd1, hd2⟩ | hy'
      · have := rowUnion_bound l _ _ _ hx'
        simp only at this
        omega
      · exact mem_rowUnion_cons.mpr (Or.inr (ih _ _ _ hx' _ hy' h1 h2 i' (Finset.mem_Icc.mpr hi)
          j' (Finset.mem_Icc.mpr hj)))

theorem rowUnion_sep {j : ℕ} {l : List ℕ} {i e : ℤ} :
    Disjoint (translate (i, e - j) (rowCells 0 (j : ℤ))) (rowUnion l (i + 1) (e - j - 1)) ∧
      ∀ a ∈ translate (i, e - j) (rowCells 0 (j : ℤ)), ∀ b ∈ rowUnion l (i + 1) (e - j - 1),
        ¬ CellAdj a b := by
  have key : ∀ a ∈ translate (i, e - j) (rowCells 0 (j : ℤ)),
      ∀ b ∈ rowUnion l (i + 1) (e - j - 1), b.2 + 2 ≤ a.2 := by
    intro a ha b hb
    obtain ⟨a1, a2⟩ := a
    rw [mem_translate, Prod.mk_sub_mk, mem_rowCells] at ha
    have := rowUnion_bound l _ _ _ hb
    simp only at this ha ⊢
    have hjn : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    omega
  refine ⟨Finset.disjoint_left.mpr fun a ha hb => ?_, fun a ha b hb hadj => ?_⟩
  · have := key a ha a hb
    omega
  · have := key a ha b hb
    unfold CellAdj at hadj
    have h1 : 0 ≤ |a.1 - b.1| := abs_nonneg _
    have h2 : a.2 - b.2 ≤ |a.2 - b.2| := le_abs_self _
    omega

theorem cellSchur_rowUnion (l : List ℕ) : ∀ i e : ℤ,
    cellSchur (rowUnion l i e) = (l.map hPos).prod := by
  induction l with
  | nil => intro i e; simp [rowUnion, cellSchur_empty]
  | cons j l ih =>
    intro i e
    obtain ⟨hd, hn⟩ := rowUnion_sep (j := j) (l := l) (i := i) (e := e)
    rw [rowUnion_cons, Gluing.cellSchur_union hd hn, cellSchur_translate, cellSchur_rowCells, hh_natCast, ih]
    simp

/-- A modified composition that is multiplicative over separated unions and translation
invariant is the product over the rows of a row union. -/
theorem rowUnion_mul (F : Diagram → Lambda)
    (hU : ∀ A B : Diagram, Disjoint A B → (∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) →
      F (A ∪ B) = F A * F B)
    (hT : ∀ (t : ℤ × ℤ) (X : Diagram), F (translate t X) = F X) (hE : F ∅ = 1)
    (l : List ℕ) : ∀ i e : ℤ,
    F (rowUnion l i e) = (l.map fun j : ℕ => F (rowCells 0 (j : ℤ))).prod := by
  induction l with
  | nil => intro i e; simpa [rowUnion] using hE
  | cons j l ih =>
    intro i e
    obtain ⟨hd, hn⟩ := rowUnion_sep (j := j) (l := l) (i := i) (e := e)
    rw [rowUnion_cons, hU _ _ hd hn, hT, ih]
    simp

end SkewMarkedFactor
