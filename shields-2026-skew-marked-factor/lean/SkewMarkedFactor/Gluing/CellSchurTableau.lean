/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/CellSchurTableau.lean
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Common
import SkewMarkedFactor.Gluing.CellSchur

/-!
# The tableau skew Schur function of a disconnected skew shape

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the paragraph on profiles: the function of a skew diagram is the product of the functions of its
connected components.

`aeval_cellSchur_skewDiagram` (in `SkewMarkedFactor.Gluing.CellSchur`) identifies `s_D`
    with the tableau skew
Schur polynomial for a connected skew diagram.  Here the identification is extended to every skew
shape `λ / μ`, connected or not:

* `skewSchur_mul_of_split`: the tableau sum of a skew shape that splits into two pieces sharing no
  row and no column is the product of the tableau sums of the pieces;
* `exists_young_pair_of_isSkew`: a skew diagram in the quadrant is the shape `λ / μ` of a pair of
  Young diagrams;
* `cellSchur_union`: `s` is multiplicative over a disjoint union with no adjacent cells;
* `aeval_cellSchur_skewDiagram_all`: for every `μ ≤ λ`, the specialization of `s_D`,
  `D = λ / μ`, is the tableau skew Schur polynomial of `λ / μ`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

open Shields

/-! ### The tableau sum over a split shape -/

section Split

variable {lam mu lam₁ mu₁ lam₂ mu₂ : YoungDiagram} {b : ℕ}

/-- The skew shape `λ / μ` is the disjoint union of `λ₁ / μ₁` and `λ₂ / μ₂`, and no cell of the
first shares a row or a column with a cell of the second. -/
structure SkewSplit (lam mu lam₁ mu₁ lam₂ mu₂ : YoungDiagram) : Prop where
  /-- The cells of `λ / μ` are those of the two pieces. -/
  union : skewCells lam mu = skewCells lam₁ mu₁ ∪ skewCells lam₂ mu₂
  /-- The two pieces have no common cell. -/
  disjoint : Disjoint (skewCells lam₁ mu₁) (skewCells lam₂ mu₂)
  /-- No row meets both pieces. -/
  row : ∀ i j₁ j₂ : ℕ, (i, j₁) ∈ skewCells lam₁ mu₁ → (i, j₂) ∈ skewCells lam₂ mu₂ → False
  /-- No column meets both pieces. -/
  col : ∀ i₁ i₂ j : ℕ, (i₁, j) ∈ skewCells lam₁ mu₁ → (i₂, j) ∈ skewCells lam₂ mu₂ → False

namespace SkewSplit

variable (S : SkewSplit lam mu lam₁ mu₁ lam₂ mu₂)
include S

theorem notMem₂ {c : ℕ × ℕ} (h : c ∈ skewCells lam₁ mu₁) : c ∉ skewCells lam₂ mu₂ :=
  Finset.disjoint_left.mp S.disjoint h

theorem notMem₁ {c : ℕ × ℕ} (h : c ∈ skewCells lam₂ mu₂) : c ∉ skewCells lam₁ mu₁ :=
  fun h' => Finset.disjoint_left.mp S.disjoint h' h

/-- The pointwise sum of a tableau of each piece is a tableau of the whole shape. -/
def sumTableau (T₁ : BoundedSkewSSYT lam₁ mu₁ b) (T₂ : BoundedSkewSSYT lam₂ mu₂ b) :
    BoundedSkewSSYT lam mu b := by
  have h1 : ∀ i j, (i, j) ∈ skewCells lam₁ mu₁ → T₂ i j = 0 :=
    fun i j h => T₂.zeros (S.notMem₂ h)
  have h2 : ∀ i j, (i, j) ∈ skewCells lam₂ mu₂ → T₁ i j = 0 :=
    fun i j h => T₁.zeros (S.notMem₁ h)
  refine ⟨{ entry := fun i j => T₁ i j + T₂ i j, row_weak' := ?_, col_strict' := ?_,
            zeros' := ?_ }, ?_⟩
  · intro i j₁ j₂ hj hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_row hj hlam hmu
    rw [S.union, Finset.mem_union] at hc₁ hc₂
    rcases hc₁ with hc₁ | hc₁ <;> rcases hc₂ with hc₂ | hc₂
    · have := T₁.1.row_weak hj (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i j₁ + T₂ i j₁ ≤ T₁ i j₂ + T₂ i j₂
      rw [h1 _ _ hc₁, h1 _ _ hc₂]; omega
    · exact (S.row i j₁ j₂ hc₁ hc₂).elim
    · exact (S.row i j₂ j₁ hc₂ hc₁).elim
    · have := T₂.1.row_weak hj (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i j₁ + T₂ i j₁ ≤ T₁ i j₂ + T₂ i j₂
      rw [h2 _ _ hc₁, h2 _ _ hc₂]; omega
  · intro i₁ i₂ j hi hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_col hi hlam hmu
    rw [S.union, Finset.mem_union] at hc₁ hc₂
    rcases hc₁ with hc₁ | hc₁ <;> rcases hc₂ with hc₂ | hc₂
    · have := T₁.1.col_strict hi (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i₁ j + T₂ i₁ j < T₁ i₂ j + T₂ i₂ j
      rw [h1 _ _ hc₁, h1 _ _ hc₂]; omega
    · exact (S.col i₁ i₂ j hc₁ hc₂).elim
    · exact (S.col i₂ i₁ j hc₂ hc₁).elim
    · have := T₂.1.col_strict hi (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i₁ j + T₂ i₁ j < T₁ i₂ j + T₂ i₂ j
      rw [h2 _ _ hc₁, h2 _ _ hc₂]; omega
  · intro i j hc
    have h₁ : (i, j) ∉ skewCells lam₁ mu₁ := fun h =>
      hc (by rw [S.union]; exact Finset.mem_union_left _ h)
    have h₂ : (i, j) ∉ skewCells lam₂ mu₂ := fun h =>
      hc (by rw [S.union]; exact Finset.mem_union_right _ h)
    change T₁ i j + T₂ i j = 0
    rw [T₁.zeros h₁, T₂.zeros h₂]
  · intro i j hc
    rw [S.union, Finset.mem_union] at hc
    change T₁ i j + T₂ i j < b
    rcases hc with hc | hc
    · rw [h1 _ _ hc]; exact T₁.lt_of_mem_cells hc
    · rw [h2 _ _ hc, zero_add]; exact T₂.lt_of_mem_cells hc

end SkewSplit

/-- The restriction of a tableau to a sub-shape: keep the entries on the cells of `λ' / μ'` and
set the others to zero. -/
def restrictTableau {lam' mu' : YoungDiagram} (T : BoundedSkewSSYT lam mu b)
    (hsub : skewCells lam' mu' ⊆ skewCells lam mu) : BoundedSkewSSYT lam' mu' b := by
  refine ⟨{ entry := fun i j => if (i, j) ∈ skewCells lam' mu' then T i j else 0,
            row_weak' := ?_, col_strict' := ?_, zeros' := ?_ }, ?_⟩
  · intro i j₁ j₂ hj hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_row hj hlam hmu
    rw [ite_eq_left hc₁, ite_eq_left hc₂]
    exact T.1.row_weak hj (mem_skewCells.mp (hsub hc₂)).1 (mem_skewCells.mp (hsub hc₁)).2
  · intro i₁ i₂ j hi hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_col hi hlam hmu
    rw [ite_eq_left hc₁, ite_eq_left hc₂]
    exact T.1.col_strict hi (mem_skewCells.mp (hsub hc₂)).1 (mem_skewCells.mp (hsub hc₁)).2
  · intro i j hc
    exact ite_eq_right hc
  · intro i j hc
    change (if (i, j) ∈ skewCells lam' mu' then T i j else 0) < b
    rw [ite_eq_left hc]
    exact T.lt_of_mem_cells (hsub hc)

theorem restrictTableau_apply {lam' mu' : YoungDiagram} (T : BoundedSkewSSYT lam mu b)
    (hsub : skewCells lam' mu' ⊆ skewCells lam mu) (i j : ℕ) :
    restrictTableau T hsub i j = if (i, j) ∈ skewCells lam' mu' then T i j else 0 := rfl

namespace SkewSplit

variable (S : SkewSplit lam mu lam₁ mu₁ lam₂ mu₂)
include S

theorem sub₁ : skewCells lam₁ mu₁ ⊆ skewCells lam mu := by
  rw [S.union]; exact Finset.subset_union_left

theorem sub₂ : skewCells lam₂ mu₂ ⊆ skewCells lam mu := by
  rw [S.union]; exact Finset.subset_union_right

/-- A tableau of a split shape is a pair of tableaux of the pieces. -/
def tableauEquiv :
    BoundedSkewSSYT lam₁ mu₁ b × BoundedSkewSSYT lam₂ mu₂ b ≃ BoundedSkewSSYT lam mu b where
  toFun p := S.sumTableau p.1 p.2
  invFun T := (restrictTableau T S.sub₁, restrictTableau T S.sub₂)
  left_inv p := by
    obtain ⟨T₁, T₂⟩ := p
    refine Prod.ext ?_ ?_
    · apply BoundedSkewSSYT.ext
      intro i j
      rw [restrictTableau_apply]
      change (if (i, j) ∈ skewCells lam₁ mu₁ then T₁ i j + T₂ i j else 0) = T₁ i j
      by_cases h : (i, j) ∈ skewCells lam₁ mu₁
      · rw [ite_eq_left h, T₂.zeros (S.notMem₂ h)]; rfl
      · rw [ite_eq_right h, T₁.zeros h]
    · apply BoundedSkewSSYT.ext
      intro i j
      rw [restrictTableau_apply]
      change (if (i, j) ∈ skewCells lam₂ mu₂ then T₁ i j + T₂ i j else 0) = T₂ i j
      by_cases h : (i, j) ∈ skewCells lam₂ mu₂
      · rw [ite_eq_left h, T₁.zeros (S.notMem₁ h)]; simp
      · rw [ite_eq_right h, T₂.zeros h]
  right_inv T := by
    apply BoundedSkewSSYT.ext
    intro i j
    change (restrictTableau T S.sub₁ i j) + (restrictTableau T S.sub₂ i j) = T i j
    rw [restrictTableau_apply, restrictTableau_apply]
    by_cases h₁ : (i, j) ∈ skewCells lam₁ mu₁
    · rw [ite_eq_left h₁, ite_eq_right (S.notMem₂ h₁)]; rfl
    · by_cases h₂ : (i, j) ∈ skewCells lam₂ mu₂
      · rw [ite_eq_right h₁, ite_eq_left h₂]; simp
      · have : (i, j) ∉ skewCells lam mu := by
          rw [S.union]
          simp only [Finset.mem_union, not_or]
          exact ⟨h₁, h₂⟩
        rw [ite_eq_right h₁, ite_eq_right h₂, T.zeros this]

variable {R : Type*} [CommSemiring R]

/-- **The tableau sum of a split shape is the product of the tableau sums of its pieces.** -/
theorem skewSchur_mul (x : ℕ → R) :
    skewSchur lam mu b x = skewSchur lam₁ mu₁ b x * skewSchur lam₂ mu₂ b x := by
  unfold skewSchur
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type' (f := fun
    (T₁ : BoundedSkewSSYT lam₁ mu₁ b) (T₂ : BoundedSkewSSYT lam₂ mu₂ b) =>
    (∏ c ∈ skewCells lam₁ mu₁, x (T₁.1 c.1 c.2)) * ∏ c ∈ skewCells lam₂ mu₂, x (T₂.1 c.1 c.2))]
  refine (Fintype.sum_equiv S.tableauEquiv _ _ fun p => ?_).symm
  change _ = ∏ c ∈ skewCells lam mu, x ((S.sumTableau p.1 p.2) c.1 c.2)
  have h := Finset.prod_union
    (f := fun c : ℕ × ℕ => x ((S.sumTableau p.1 p.2).1 c.1 c.2)) S.disjoint
  rw [← S.union] at h
  refine Eq.trans ?_ h.symm
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    change x (p.1 c.1 c.2) = x (p.1 c.1 c.2 + p.2 c.1 c.2)
    rw [p.2.zeros (S.notMem₂ hc), add_zero]
  · refine Finset.prod_congr rfl fun c hc => ?_
    change x (p.2 c.1 c.2) = x (p.1 c.1 c.2 + p.2 c.1 c.2)
    rw [p.1.zeros (S.notMem₁ hc), zero_add]

end SkewSplit

end Split

/-! ### Skew diagrams in the quadrant are shapes `λ / μ` -/

section Pair

/-- The cell diagram of `λ / μ` is a skew diagram. -/
theorem isSkew_skewDiagram (lam mu : YoungDiagram) : IsSkew (skewDiagram lam mu) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨a, b, rfl⟩ := nat_cell_of_mem_skewDiagram hx
  obtain ⟨c, d, rfl⟩ := nat_cell_of_mem_skewDiagram hy
  simp only [Finset.mem_Icc] at hi hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = (i' : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = (j' : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hac : a ≤ c := by simpa using h1
  have hbd : b ≤ d := by simpa using h2
  have hai : a ≤ i' := by exact_mod_cast hi.1
  have hic : i' ≤ c := by exact_mod_cast hi.2
  have hbj : b ≤ j' := by exact_mod_cast hj.1
  have hjd : j' ≤ d := by exact_mod_cast hj.2
  rw [mem_skewDiagram_nat, mem_skewCells] at hx hy ⊢
  exact ⟨lam.up_left_mem hic hjd hy.1, fun h => hx.2 (mu.up_left_mem hai hbj h)⟩

/-- A skew diagram in the quadrant is the cell diagram of a skew shape `λ / μ` of Young
diagrams: `λ` is the set of cells weakly northwest of a cell of the diagram, and `μ` is `λ`
without the diagram. -/
theorem exists_young_pair_of_isSkew {D : Diagram} (hD : IsSkew D)
    (hnn : ∀ x ∈ D, 0 ≤ x.1 ∧ 0 ≤ x.2) :
    ∃ lam mu : YoungDiagram, mu ≤ lam ∧ skewDiagram lam mu = D := by
  classical
  set N : Finset (ℕ × ℕ) := D.image (fun x => (x.1.toNat, x.2.toNat)) with hNdef
  have hN : ∀ a b : ℕ, (a, b) ∈ N ↔ ((a : ℤ), (b : ℤ)) ∈ D := by
    intro a b
    constructor
    · intro h
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
      have h1 := hnn x hx
      have ha : x.1.toNat = a := congrArg Prod.fst hxe
      have hb : x.2.toNat = b := congrArg Prod.snd hxe
      have : x = ((a : ℤ), (b : ℤ)) := by ext <;> simp <;> omega
      rwa [← this]
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, by simp⟩
  have hconv : ∀ p q r : ℕ × ℕ, p ∈ N → q ∈ N → p ≤ r → r ≤ q → r ∈ N := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨i, j⟩ hp hq hpr hrq
    obtain ⟨hai, hbj⟩ := Prod.mk_le_mk.mp hpr
    obtain ⟨hic, hjd⟩ := Prod.mk_le_mk.mp hrq
    rw [hN] at hp hq ⊢
    exact hD.mem hp hq (by exact_mod_cast hai.trans hic) (by exact_mod_cast hbj.trans hjd)
      (by exact_mod_cast hai) (by exact_mod_cast hic) (by exact_mod_cast hbj)
      (by exact_mod_cast hjd)
  set L : Finset (ℕ × ℕ) := N.biUnion (fun p => Finset.Iic p) with hLdef
  have hL : ∀ r, r ∈ L ↔ ∃ p ∈ N, r ≤ p := by
    intro r
    simp only [hLdef, Finset.mem_biUnion, Finset.mem_Iic]
  have hNL : N ⊆ L := fun p hp => (hL p).mpr ⟨p, hp, le_rfl⟩
  let lam : YoungDiagram := ⟨L, fun a b hba ha => by
    rw [Finset.mem_coe, hL] at ha ⊢
    obtain ⟨p, hp, hap⟩ := ha
    exact ⟨p, hp, hba.trans hap⟩⟩
  let mu : YoungDiagram := ⟨L \ N, fun a b hba ha => by
    rw [Finset.mem_coe, Finset.mem_sdiff] at ha ⊢
    obtain ⟨haL, haN⟩ := ha
    obtain ⟨p, hp, hap⟩ := (hL a).mp haL
    refine ⟨(hL b).mpr ⟨p, hp, hba.trans hap⟩, fun hb => haN ?_⟩
    exact hconv b p a hb hp hba hap⟩
  refine ⟨lam, mu, fun x hx => (Finset.mem_sdiff.mp hx).1, ?_⟩
  have hcells : skewCells lam mu = N := by
    ext c
    rw [mem_skewCells]
    change c ∈ L ∧ c ∉ L \ N ↔ c ∈ N
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hc, hc'⟩
      by_contra hcN
      exact hc' ⟨hc, hcN⟩
    · intro hc
      exact ⟨hNL hc, fun h => h.2 hc⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hx
    rw [mem_skewDiagram_nat, hcells, hN] at hx
    exact hx
  · intro hx
    obtain ⟨a, b⟩ := x
    obtain ⟨hx1, hx2⟩ := hnn _ hx
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = (i : ℤ) := ⟨a.toNat, (Int.toNat_of_nonneg hx1).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, b = (j : ℤ) := ⟨b.toNat, (Int.toNat_of_nonneg hx2).symm⟩
    rw [mem_skewDiagram_nat, hcells, hN]
    exact hx

end Pair

/-! ### `s` over a union without adjacent cells -/

section Union

attribute [local instance 10] Classical.propDecidable

theorem DiagReach.mem_of_mem {D : Diagram} {x y : ℤ × ℤ} (hx : x ∈ D) (h : DiagReach D x y) :
    y ∈ D := by
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact hab.2.1

variable {A B : Diagram}

theorem diagReach_union_left (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) {x y : ℤ × ℤ}
    (hx : x ∈ A) (h : DiagReach (A ∪ B) x y) : DiagReach A x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hbc ih =>
    have hbA : b ∈ A := DiagReach.mem_of_mem hx ih
    have hcA : c ∈ A := by
      rcases Finset.mem_union.mp hbc.2.1 with h | h
      · exact h
      · exact absurd hbc.2.2 (hadj b hbA c h)
    exact Relation.ReflTransGen.tail ih ⟨hbA, hcA, hbc.2.2⟩

theorem filter_union_left (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) {x : ℤ × ℤ} (hx : x ∈ A) :
    (A ∪ B).filter (DiagReach (A ∪ B) x) = A.filter (DiagReach A x) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨-, hr⟩
    have := diagReach_union_left hadj hx hr
    exact ⟨DiagReach.mem_of_mem hx this, this⟩
  · rintro ⟨hy, hr⟩
    exact ⟨Or.inl hy, hr.mono Finset.subset_union_left⟩

/-- The components of a union of two diagrams with no adjacent cells are the components of the
two diagrams. -/
theorem edgeComponents_union (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) :
    edgeComponents (A ∪ B) = edgeComponents A ∪ edgeComponents B := by
  have hadj' : ∀ b ∈ B, ∀ a ∈ A, ¬ CellAdj b a := fun b hb a ha h => hadj a ha b hb h.symm'
  ext C
  simp only [Finset.mem_union, mem_edgeComponents]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hxA | hxB
    · exact Or.inl ⟨x, hxA, filter_union_left hadj hxA⟩
    · refine Or.inr ⟨x, hxB, ?_⟩
      rw [Finset.union_comm]
      exact filter_union_left hadj' hxB
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, (filter_union_left hadj hx).symm⟩
    · refine ⟨x, Or.inr hx, ?_⟩
      rw [Finset.union_comm]
      exact (filter_union_left hadj' hx).symm

/-- **`s` is multiplicative over a disjoint union with no adjacent cells**: the function of a
diagram is the product of the functions of unions of its components. -/
theorem cellSchur_union (hdisj : Disjoint A B) (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) :
    cellSchur (A ∪ B) = cellSchur A * cellSchur B := by
  unfold cellSchur
  rw [edgeComponents_union hadj, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro C hCA hCB
  obtain ⟨z, hz⟩ := component_nonempty hCA
  exact Finset.disjoint_left.mp hdisj (component_subset hCA hz) (component_subset hCB hz)

theorem mem_component_of_reach {D C : Diagram} (hC : C ∈ edgeComponents D) {x y : ℤ × ℤ}
    (hx : x ∈ C) (h : DiagReach D x y) : y ∈ C := by
  rw [component_eq_of_mem hC hx]
  exact Finset.mem_filter.mpr ⟨DiagReach.mem_of_mem (component_subset hC hx) h, h⟩

/-- The cells of a skew diagram outside one component form a skew diagram. -/
theorem isSkew_sdiff_component {D C : Diagram} (hs : IsSkew D) (hC : C ∈ edgeComponents D) :
    IsSkew (D \ C) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxD, hxC⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyD, -⟩ := Finset.mem_sdiff.mp hy
  simp only [Finset.mem_Icc] at hi hj
  have hz : (i, j) ∈ D := hs.mem (a := x.1) (b := x.2) (c := y.1) (d := y.2) hxD hyD h1 h2 hi.1
    hi.2 hj.1 hj.2
  refine Finset.mem_sdiff.mpr ⟨hz, fun hzC => hxC ?_⟩
  exact mem_component_of_reach hC hzC (hs.reach_rect hxD hyD h1 h2 hi.1 hi.2 hj.1 hj.2).symm

/-- **Agreement with the tableau skew Schur function for every skew shape.**  For Young diagrams
`μ ≤ λ`, connected or not, the specialization `h_k ↦ completeHom b k β` sends `s_D`,
`D = λ / μ`, to the tableau skew Schur polynomial `skewSchur λ μ b β`.  The tableau sum factors
over the edge-connected components because no row and no column of a skew shape meets two of
them; each component is a skew shape of Young diagrams (`exists_young_pair_of_isSkew`) and is
handled by `aeval_cellSchur_skewDiagram`.  The paper cites the product formula; here it is
proved, by induction on the number of cells, splitting off one component at a time. -/
theorem aeval_cellSchur_skewDiagram_all {R : Type*} [CommRing R] [Algebra ℚ R]
    {lam mu : YoungDiagram} (hmu : mu ≤ lam) (b : ℕ) (β : ℕ → R) :
    MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom b k β)
      (cellSchur (skewDiagram lam mu)) = Shields.skewSchur lam mu b β := by
  suffices h : ∀ n : ℕ, ∀ lam mu : YoungDiagram, mu ≤ lam → (skewDiagram lam mu).card = n →
      MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom b k β)
        (cellSchur (skewDiagram lam mu)) = Shields.skewSchur lam mu b β from
    h _ lam mu hmu rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lam mu hmu hn
  set D := skewDiagram lam mu with hDdef
  have hs : IsSkew D := isSkew_skewDiagram lam mu
  have hnn : ∀ y ∈ D, 0 ≤ y.1 ∧ 0 ≤ y.2 := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hy
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  by_cases hemp : D = ∅
  · -- the empty shape: both sides are `1`
    have hcells : skewCells lam mu = ∅ := by
      have : D.card = 0 := by rw [hemp]; rfl
      simpa [hDdef, skewDiagram] using this
    have : Unique (BoundedSkewSSYT lam mu b) :=
      ⟨⟨BoundedSkewSSYT.ofEmpty lam mu b hcells⟩,
        fun T => BoundedSkewSSYT.eq_of_skewCells_eq_empty hcells _ _⟩
    rw [hemp, cellSchur_empty, map_one, skewSchur, Fintype.sum_unique]
    exact (Finset.prod_eq_one fun c hc => by
      rw [hcells] at hc; exact absurd hc (Finset.notMem_empty _)).symm
  by_cases hconn : IsEdgeConnected D
  · exact aeval_cellSchur_skewDiagram hmu ⟨hs, hconn⟩ b β
  -- a component `C` and the rest `D' = D \ C`
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
  set C : Diagram := D.filter (DiagReach D x) with hCdef
  have hC : C ∈ edgeComponents D := mem_edgeComponents.mpr ⟨x, hx, rfl⟩
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
  have hCsub : C ⊆ D := component_subset hC
  have hCne : C ≠ D := fun h => hconn (h ▸ isEdgeConnected_component hC)
  set D' : Diagram := D \ C with hD'def
  have hcardC : C.card < n := hn ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hCsub, hCne⟩)
  have hcardD' : D'.card < n := hn ▸ Finset.card_lt_card (by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => ?_⟩
    have : x ∈ D' := h ▸ hx
    exact (Finset.mem_sdiff.mp this).2 hxC)
  obtain ⟨lam₁, mu₁, hmu₁, hC₁⟩ := exists_young_pair_of_isSkew (isSkew_component hs hC)
    (fun y hy => hnn y (hCsub hy))
  obtain ⟨lam₂, mu₂, hmu₂, hD₂⟩ := exists_young_pair_of_isSkew (isSkew_sdiff_component hs hC)
    (fun y hy => hnn y (Finset.sdiff_subset hy))
  -- the split of the tableau shape
  have key : ∀ (l m : YoungDiagram) (i j : ℕ),
      (i, j) ∈ skewCells l m ↔ ((i : ℤ), (j : ℤ)) ∈ skewDiagram l m :=
    fun l m i j => (mem_skewDiagram_nat i j).symm
  have hcellD : ∀ i j : ℕ, (i, j) ∈ skewCells lam mu ↔ ((i : ℤ), (j : ℤ)) ∈ D :=
    fun i j => key lam mu i j
  have hcell₁ : ∀ i j : ℕ, (i, j) ∈ skewCells lam₁ mu₁ ↔ ((i : ℤ), (j : ℤ)) ∈ C := by
    intro i j; rw [key, hC₁]
  have hcell₂ : ∀ i j : ℕ, (i, j) ∈ skewCells lam₂ mu₂ ↔ ((i : ℤ), (j : ℤ)) ∈ D' := by
    intro i j; rw [key, hD₂]
  have hrowcol : ∀ y ∈ C, ∀ z ∈ D', ¬ DiagReach D y z := fun y hy z hz hr =>
    (Finset.mem_sdiff.mp hz).2 (mem_component_of_reach hC hy hr)
  have S : SkewSplit lam mu lam₁ mu₁ lam₂ mu₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext ⟨i, j⟩
      rw [Finset.mem_union, hcellD, hcell₁, hcell₂, hD'def, Finset.mem_sdiff]
      constructor
      · intro h
        by_cases hc : ((i : ℤ), (j : ℤ)) ∈ C
        · exact Or.inl hc
        · exact Or.inr ⟨h, hc⟩
      · rintro (h | h)
        · exact hCsub h
        · exact h.1
    · rw [Finset.disjoint_left]
      rintro ⟨i, j⟩ h1 h2
      rw [hcell₁] at h1
      rw [hcell₂, hD'def, Finset.mem_sdiff] at h2
      exact h2.2 h1
    · intro i j₁ j₂ h1 h2
      rw [hcell₁] at h1
      rw [hcell₂] at h2
      exact hrowcol _ h1 _ h2 (hs.reach_row (hCsub h1) (Finset.sdiff_subset h2))
    · intro i₁ i₂ j h1 h2
      rw [hcell₁] at h1
      rw [hcell₂] at h2
      exact hrowcol _ h1 _ h2 (hs.reach_col (hCsub h1) (Finset.sdiff_subset h2))
  -- the functions multiply
  have hcs : cellSchur D = cellSchur C * cellSchur D' := by
    rw [← cellSchur_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hCsub]
    intro a ha b hb hadj
    exact hrowcol a ha b hb (Relation.ReflTransGen.single ⟨hCsub ha, Finset.sdiff_subset hb, hadj⟩)
  have ih₁ := ih _ (by rw [hC₁]; exact hcardC) lam₁ mu₁ hmu₁ rfl
  have ih₂ := ih _ (by rw [hD₂]; exact hcardD') lam₂ mu₂ hmu₂ rfl
  rw [hC₁] at ih₁
  rw [hD₂] at ih₂
  rw [hcs, map_mul, ih₁, ih₂, S.skewSchur_mul]

end Union

/-! ### Checked examples -/

section Examples

/-- The function of two non-adjacent cells is `h₁²`. -/
example : cellSchur (({(0, 0)} ∪ {(2, 2)} : Diagram)) = MvPolynomial.X 1 * MvPolynomial.X 1 := by
  rw [cellSchur_union (by decide) (by decide), cellSchur_singleton, cellSchur_singleton]

/-- The Young diagrams of the skew shape `(3, 1) / (1)`: two components, a row of two cells and
a single cell. -/
example : IsSkew (skewOf [3, 1] [1]) ∧ ¬ IsConnectedSkew (skewOf [3, 1] [1]) := by decide

end Examples

end SkewMarkedFactor.Gluing
