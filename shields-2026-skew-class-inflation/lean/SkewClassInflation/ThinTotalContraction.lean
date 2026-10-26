/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroContractionSets
import SkewClassInflation.ThinBetaSets
import SkewClassInflation.BoundaryIdentification

/-!
# The total zero contraction is the actual full thin power

Formalizes the total-contraction producer used in
`thm:two-row-thin-class` of `shields-2026-skew-class-inflation.tex`.
Distinct grid residues identify the common full betas exactly.  Every
zero seam is contracted geometrically, and the uncanceled row and column
sets then give the literal power of the total copy multiplicity.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Every point in a finite grid has its origin's residue. -/
theorem arithmeticGrid_residue (z : ℤ) (q : ℕ) (m : ℕ) (x : ℤ)
    (hx : x ∈ arithmeticGrid z q m) : (x : ZMod q) = (z : ZMod q) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  simp

/-- Distinct residue classes separate entire finite arithmetic grids. -/
theorem arithmeticGrid_disjoint (z w : ℤ) (q : ℕ) (m n : ℕ)
    (hne : (z : ZMod q) ≠ (w : ZMod q)) :
    Disjoint (arithmeticGrid z q m) (arithmeticGrid w q n) := by
  apply Finset.disjoint_left.mpr
  intro x hx hw
  exact hne ((arithmeticGrid_residue z q m x hx).symm.trans
    (arithmeticGrid_residue w q n x hw))

/-- A nonzero residue grid is disjoint from every finite set of modulus multiples. -/
theorem arithmeticGrid_multiple_disjoint (z : ℤ) (q : ℕ) (m : ℕ) (T : Finset ℕ)
    (hz : (z : ZMod q) ≠ 0) :
    Disjoint (arithmeticGrid z q m) (T.image (fun k : ℕ => (k : ℤ) * q)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hT
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hT
  have h := arithmeticGrid_residue z q m ((k : ℤ) * q) hx
  apply hz
  simpa using h.symm

/-- Separating the three residue interactions leaves only the difference of the common grids. -/
theorem separated_union_sdiff (A B C D : Finset ℤ)
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C) :
    (A ∪ B) \ (C ∪ D) = A ∪ (B \ D) := by
  classical
  ext x
  have hcA := Finset.disjoint_left.mp hAC
  have hdA := Finset.disjoint_left.mp hAD
  have hcB := Finset.disjoint_left.mp hBC
  by_cases hA : x ∈ A
  · simp [Finset.mem_sdiff, hA, hcA hA, hdA hA]
  · by_cases hB : x ∈ B
    · simp [Finset.mem_sdiff, hA, hB, hcB hB]
    · simp [Finset.mem_sdiff, hA, hB]

/-- Exchanging the one exterior grid point leaves exactly the original exterior point. -/
theorem inserted_sdiff_inserted (T : Finset ℕ) (a b : ℕ) (hab : a ≠ b) (ha : a ∉ T) :
    (insert a T) \ (insert b T) = {a} := by
  classical
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  aesop

namespace ThinParameters

variable (B : ThinParameters)

/-- The original endpoint and gap-shift residues are distinct and both nonzero. -/
theorem original_residues :
    ((B.b : ℤ) : ZMod B.boundary.q) ≠
      (((B.b : ℤ) - (B.c : ℤ) : ℤ) : ZMod B.boundary.q) ∧
    ((B.b : ℤ) : ZMod B.boundary.q) ≠ 0 ∧
    (((B.b : ℤ) - (B.c : ℤ) : ℤ) : ZMod B.boundary.q) ≠ 0 := by
  have hc := B.c_pos
  have hca := B.c_lt_a
  have hab := B.a_lt_b
  have hq := B.boundary_q_eq
  have hbc : ((B.b - B.c : ℕ) : ℤ) = (B.b : ℤ) - B.c := by omega
  have hbq : B.b < B.boundary.q := by omega
  have hbcq : B.b - B.c < B.boundary.q := by omega
  have h0q := B.boundary.q_pos
  constructor
  · have h := B.boundary.residue_ne (x := B.b) (y := B.b - B.c) hbq hbcq (by omega)
    rw [← hbc]
    simpa only [Int.cast_natCast] using h
  · constructor
    · simpa only [Int.cast_natCast, Nat.cast_zero] using
        B.boundary.residue_ne (x := B.b) (y := 0) hbq h0q (by omega)
    · have h := B.boundary.residue_ne (x := B.b - B.c) (y := 0) hbcq h0q (by omega)
      rw [← hbc]
      simpa only [Int.cast_natCast, Nat.cast_zero] using h

/-- The uncanceled original beta supports are those of the full total-multiplicity power. -/
theorem diagram_residual_sets {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.rowSet \ (B.diagram α hM).2.toBetaDiagram.colSet =
      (B.innerPower M hM).toBetaDiagram.rowSet ∧
    (B.diagram α hM).2.toBetaDiagram.colSet \ (B.diagram α hM).2.toBetaDiagram.rowSet =
      (B.innerPower M hM).toBetaDiagram.colSet := by
  classical
  let T := suffixSet α
  let f : ℕ → ℤ := fun k => (k : ℤ) * B.boundary.q
  have hf : Function.Injective f := by
    intro k l h
    have hq : (B.boundary.q : ℤ) ≠ 0 := by have := B.boundary.q_pos; omega
    exact_mod_cast mul_right_cancel₀ hq h
  have h0T : 0 ∉ T := by
    intro h
    have hh := Finset.mem_Ioo.mp (suffixSet_subset α h)
    omega
  have hMT : M ∉ T := by
    intro h
    have hh := Finset.mem_Ioo.mp (suffixSet_subset α h)
    omega
  obtain ⟨hres, hb0, hc0⟩ := B.original_residues
  have hgrid := arithmeticGrid_disjoint B.b ((B.b : ℤ) - B.c) B.boundary.q M M hres
  have hRX := arithmeticGrid_multiple_disjoint B.b B.boundary.q M (insert M T) hb0
  have hRY := arithmeticGrid_multiple_disjoint B.b B.boundary.q M (insert 0 T) hb0
  have hCX := arithmeticGrid_multiple_disjoint ((B.b : ℤ) - B.c)
    B.boundary.q M (insert M T) hc0
  have hCY := arithmeticGrid_multiple_disjoint ((B.b : ℤ) - B.c)
    B.boundary.q M (insert 0 T) hc0
  rw [B.diagram_rowSet, B.diagram_colSet]
  constructor
  · rw [separated_union_sdiff _ _ _ _ hgrid hRY hCX.symm, ← Finset.image_sdiff _ _ hf,
      inserted_sdiff_inserted T M 0 (Nat.ne_of_gt hM) hMT, Finset.image_singleton,
      B.innerPower_rowSet]
    exact Finset.union_comm _ _
  · rw [separated_union_sdiff _ _ _ _ hgrid.symm hCX hRY.symm, ← Finset.image_sdiff _ _ hf,
      inserted_sdiff_inserted T 0 M (Ne.symm (Nat.ne_of_gt hM)) h0T, Finset.image_singleton,
      B.innerPower_colSet]
    simp only [f, Nat.cast_zero, zero_mul, arithmeticGrid]
    exact Finset.union_comm _ _

/-- The genuine total zero contraction has exactly the source full-power polynomial. -/
theorem diagram_total_contraction {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (contractAllZeros (B.diagram α hM).2).2.toBetaDiagram.schur =
      (B.innerPower M hM).toBetaDiagram.schur := by
  let P := (B.diagram α hM).2
  let C := (contractAllZeros P).2.toBetaDiagram
  have hrows := B.diagram_row_count α hM
  have hzeros := B.diagram_zeroSeamCount α hM
  have hsize := contractAllZeros_size P
  have hn : M + 1 = (contractAllZeros P).1 + 1 := by
    change (B.diagram α hM).1 + 1 = M + α.length at hrows
    change zeroSeamCount P + 1 = α.length at hzeros
    omega
  have hc := contractAllZeros_sets P (B.diagram_thick α hM)
  have he := B.diagram_residual_sets α hM
  have hr : (C.reindexOrder hn).rowSet = (B.innerPower M hM).toBetaDiagram.rowSet := by
    rw [reindexOrder_rowSet]
    exact hc.1.trans he.1
  have hl : (C.reindexOrder hn).colSet = (B.innerPower M hM).toBetaDiagram.colSet := by
    rw [reindexOrder_colSet]
    exact hc.2.trans he.2
  have hs := congrArg BetaDiagram.schur (BetaDiagram.ext_sets _ _ hr hl)
  simpa only [BetaDiagram.reindexOrder_schur] using hs

end ThinParameters
end SkewClassInflation
