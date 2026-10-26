/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewJacobiNegative.TenNegativeFamilies
import SkewJacobiNegative.PositiveBorders
import SkewJacobiNegative.GammaEncoding
import SkewJacobiNegative.EndpointLeaders

/-!
# Borders of the exceptional seven-row families

The actual matrices and exact coefficients in `eq:ten-negative-border-matrices`
and `eq:ten-negative-border-separators`.  Gamma transport includes the
common-beta boundary.  The endpoint geometry and opposite-endpoint inequalities
give the exceptional-member inputs to `lem:ten-negative-endpoints`.
-/

namespace SkewJacobiNegative
namespace TenParameters

/-- Row types in the literal eight-row tied-border matrices. -/
def borderRow : TenKind → Fin 8 → Bool × ℤ
  | .fa => ![(true,8),(true,7),(false,7),(true,6),(false,6),(false,5),(true,4),(false,4)]
  | .ha => ![(true,8),(true,7),(false,7),(true,6),(false,6),(true,5),(false,5),(false,3)]
  | .fb => ![(true,8),(true,7),(false,7),(true,6),(false,6),(true,5),(true,4),(false,4)]
  | .hb => ![(true,8),(true,7),(false,7),(true,6),(false,6),(true,5),(false,5),(true,3)]

/-- The matrix entries are the actual complete generators, including all unit entries. -/
noncomputable def tiedBorderMatrix (P : TenParameters) (k : TenKind) :
    Matrix (Fin 8) (Fin 8) CompleteRing := fun i j =>
  complete ((if (borderRow k i).1 then P.a else 0) +
    ((borderRow k i).2 - (7 - (j.val : ℤ))) * P.b + P.d)

theorem b_pos (P : TenParameters) : 0 < P.b := by
  have := P.a_pos
  have := P.d_nonneg
  have := P.separated
  omega

private theorem tiedBorder_row (P : TenParameters) (k : TenKind) (i : Fin 8) :
    ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).row i =
      (if (borderRow k i).1 then P.a else 0) +
        ((borderRow k i).2-1)*P.b+P.d := by
  cases i using Fin.cases with
  | zero =>
    rw [BetaDiagram.positiveBorder_row_zero]
    cases k <;> norm_num [diagram, rowBase, borderRow] <;> ring
  | succ i =>
    rw [BetaDiagram.positiveBorder_row_succ]
    cases k <;> fin_cases i <;>
      norm_num [diagram, rowBase, borderRow] <;> ring

private theorem tiedBorder_col (P : TenParameters) (j : Fin 8) :
    ((P.diagram .fa).positiveBorder P.b P.b P.b_pos P.b_pos).col j =
      (6-(j.val : ℤ))*P.b := by
  fin_cases j <;>
    norm_num [BetaDiagram.positiveBorder, diagram, column, Fin.snoc] <;> ring

private theorem tiedBorder_col_kind (P : TenParameters) (k : TenKind) (j : Fin 8) :
    ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).col j =
      (6-(j.val : ℤ))*P.b := by
  change ((P.diagram .fa).positiveBorder P.b P.b P.b_pos P.b_pos).col j = _
  exact tiedBorder_col P j

set_option maxHeartbeats 2000000 in
/-- A beta-polynomial bridge for each of the four actual eight-row borders. -/
theorem tiedBorder_matrix (P : TenParameters) (k : TenKind) :
    ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).matrix =
      tiedBorderMatrix P k := by
  apply Matrix.ext
  intro i j
  change complete (((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).row i -
      ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).col j) = _
  rw [tiedBorder_row, tiedBorder_col_kind]
  unfold tiedBorderMatrix
  congr 1
  ring

/-- The displayed bordered determinant is not a free-standing Toeplitz surrogate. -/
theorem tiedBorder_schur (P : TenParameters) (k : TenKind) :
    ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).schur =
      (tiedBorderMatrix P k).det := by
  unfold BetaDiagram.schur
  rw [P.tiedBorder_matrix]

/-- The two-entry row-multiset equality in family A forces the common margin. -/
theorem familyA_tie (b d t : ℤ) (hb : 0 < b)
    (h : ({3*b+d, 3*b+d+t} : Multiset ℤ) = {4*b+d, 2*b+d+t}) : t = b := by
  have hm : 3*b+d ∈ ({4*b+d, 2*b+d+t} : Multiset ℤ) := by
    rw [← h]
    simp
  have hm' : 3*b+d=4*b+d ∨ 3*b+d=2*b+d+t := by simpa using hm
  rcases hm' with hm' | hm' <;> omega

/-- The same necessary margin in family B, without assuming distinct multiset entries. -/
theorem familyB_tie (a b d t : ℤ) (ha : 0 < a) (hab : a < b)
    (h : ({a+3*b+d, 3*b+d+t} : Multiset ℤ) =
      {4*b+d, a+2*b+d+t}) : t = b := by
  have hm : a+3*b+d ∈ ({4*b+d, a+2*b+d+t} : Multiset ℤ) := by
    rw [← h]
    simp
  have hm' : a+3*b+d=4*b+d ∨ a+3*b+d=a+2*b+d+t := by simpa using hm
  rcases hm' with hm' | hm' <;> omega

/-- A finite free alphabet for the literal matrices; its actual specialization is proved below. -/
noncomputable def borderSymbol (v : Bool) (r : ℤ) : MvPolynomial (Fin 18) ℚ :=
  if h : 0 ≤ r ∧ r < 9 then
    MvPolynomial.X ⟨r.toNat + (if v then 9 else 0), by
      have := h.1
      have := h.2
      cases v <;> simp <;> omega⟩
  else 0

noncomputable def universalBorderMatrix (k : TenKind) :
    Matrix (Fin 8) (Fin 8) (MvPolynomial (Fin 18) ℚ) :=
  fun i j => borderSymbol (borderRow k i).1
    ((borderRow k i).2 - (7-(j.val : ℤ)))

noncomputable def separatorExponent (second : Bool) : Fin 18 →₀ ℕ :=
  if second then
    Finsupp.single 1 3 + Finsupp.single 9 1 + Finsupp.single 10 1 +
      Finsupp.single 12 1 + Finsupp.single 14 1 + Finsupp.single 16 1
  else
    Finsupp.single 1 4 + Finsupp.single 9 1 +
      Finsupp.single 12 1 + Finsupp.single 14 1 + Finsupp.single 16 1

/-- Only variables occurring in a separator can contribute to its coefficient. -/
def separatorEmbedding : Fin 6 → Fin 18 := ![1,9,10,12,14,16]

private theorem separatorEmbedding_injective : Function.Injective separatorEmbedding := by
  decide

private noncomputable def sparseProjection :
    MvPolynomial (Fin 18) ℚ →ₐ[ℚ] MvPolynomial (Fin 6) ℚ :=
  MvPolynomial.killCompl separatorEmbedding_injective

private theorem sparseProjection_X (j : Fin 18) :
    sparseProjection (MvPolynomial.X j) =
      if j=1 then MvPolynomial.X 0 else if j=9 then MvPolynomial.X 1 else
      if j=10 then MvPolynomial.X 2 else if j=12 then MvPolynomial.X 3 else
      if j=14 then MvPolynomial.X 4 else if j=16 then MvPolynomial.X 5 else 0 := by
  classical
  by_cases h : j ∈ Set.range separatorEmbedding
  · obtain ⟨i,rfl⟩ := h
    change MvPolynomial.killCompl separatorEmbedding_injective
      (MvPolynomial.X (separatorEmbedding i)) = _
    rw [← MvPolynomial.rename_X separatorEmbedding i, MvPolynomial.killCompl_rename_app]
    fin_cases i <;> norm_num [separatorEmbedding]
  · have hz : sparseProjection (MvPolynomial.X j) = 0 := by
      unfold sparseProjection MvPolynomial.killCompl
      rw [MvPolynomial.aeval_X,dif_neg h]
    have hn (i : Fin 6) : j ≠ separatorEmbedding i := by
      intro he
      exact h ⟨i,he.symm⟩
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    have h3 := hn 3
    have h4 := hn 4
    have h5 := hn 5
    norm_num [separatorEmbedding] at h0 h1 h2 h3 h4 h5
    simp [hz,h0,h1,h2,h3,h4,h5]

private noncomputable def sparseSeparatorExponent (second : Bool) : Fin 6 →₀ ℕ :=
  if second then
    Finsupp.single 0 3 + Finsupp.single 1 1 + Finsupp.single 2 1 +
      Finsupp.single 3 1 + Finsupp.single 4 1 + Finsupp.single 5 1
  else
    Finsupp.single 0 4 + Finsupp.single 1 1 +
      Finsupp.single 3 1 + Finsupp.single 4 1 + Finsupp.single 5 1

private theorem sparseSeparatorExponent_map (second : Bool) :
    (sparseSeparatorExponent second).mapDomain separatorEmbedding = separatorExponent second := by
  cases second <;>
    simp only [sparseSeparatorExponent,separatorExponent,Bool.false_eq_true,↓reduceIte]
  all_goals
    repeat' rw [Finsupp.mapDomain_add]
    simp only [Finsupp.mapDomain_single]
    norm_num [separatorEmbedding]

private noncomputable def sparseVRow : ℤ → Fin 8 → MvPolynomial (Fin 6) ℚ
  | 8 => ![MvPolynomial.X 2,0,MvPolynomial.X 3,0,MvPolynomial.X 4,0,MvPolynomial.X 5,0]
  | 7 => ![MvPolynomial.X 1,MvPolynomial.X 2,0,MvPolynomial.X 3,0,MvPolynomial.X 4,0,MvPolynomial.X 5]
  | 6 => ![0,MvPolynomial.X 1,MvPolynomial.X 2,0,MvPolynomial.X 3,0,MvPolynomial.X 4,0]
  | 5 => ![0,0,MvPolynomial.X 1,MvPolynomial.X 2,0,MvPolynomial.X 3,0,MvPolynomial.X 4]
  | 4 => ![0,0,0,MvPolynomial.X 1,MvPolynomial.X 2,0,MvPolynomial.X 3,0]
  | 3 => ![0,0,0,0,MvPolynomial.X 1,MvPolynomial.X 2,0,MvPolynomial.X 3]
  | _ => 0

private noncomputable def sparseURow (r : ℤ) : Fin 8 → MvPolynomial (Fin 6) ℚ :=
  fun j => if (j.val : ℤ)=8-r then MvPolynomial.X 0 else 0

private noncomputable def sparseBorderMatrix : TenKind → Matrix (Fin 8) (Fin 8)
    (MvPolynomial (Fin 6) ℚ)
  | .fa => ![sparseVRow 8,sparseVRow 7,sparseURow 7,sparseVRow 6,sparseURow 6,
      sparseURow 5,sparseVRow 4,sparseURow 4]
  | .ha => ![sparseVRow 8,sparseVRow 7,sparseURow 7,sparseVRow 6,sparseURow 6,
      sparseVRow 5,sparseURow 5,sparseURow 3]
  | .fb => ![sparseVRow 8,sparseVRow 7,sparseURow 7,sparseVRow 6,sparseURow 6,
      sparseVRow 5,sparseVRow 4,sparseURow 4]
  | .hb => ![sparseVRow 8,sparseVRow 7,sparseURow 7,sparseVRow 6,sparseURow 6,
      sparseVRow 5,sparseURow 5,sparseVRow 3]

private theorem sparseBorderMatrix_eq (k : TenKind) :
    sparseBorderMatrix k = sparseProjection.mapMatrix (universalBorderMatrix k) := by
  apply Matrix.ext
  intro i j
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [sparseBorderMatrix,sparseVRow,sparseURow,AlgHom.mapMatrix_apply,
      universalBorderMatrix,borderRow,borderSymbol,sparseProjection_X]

open MvPolynomial (X)
private noncomputable def borderSeven : TenKind → Matrix (Fin 7) (Fin 7) (MvPolynomial (Fin 6) ℚ)
  | .fa => ![![X 2,X 3,0,X 4,0,X 5,0],![X 1,0,X 3,0,X 4,0,X 5],
      ![0,X 2,0,X 3,0,X 4,0],![0,X 0,0,0,0,0,0],
      ![0,0,X 0,0,0,0,0],![0,0,X 1,X 2,0,X 3,0],![0,0,0,X 0,0,0,0]]
  | .ha => ![![X 2,X 3,0,X 4,0,X 5,0],![X 1,0,X 3,0,X 4,0,X 5],
      ![0,X 2,0,X 3,0,X 4,0],![0,X 0,0,0,0,0,0],
      ![0,X 1,X 2,0,X 3,0,X 4],![0,0,X 0,0,0,0,0],![0,0,0,0,X 0,0,0]]
  | .fb => ![![X 2,X 3,0,X 4,0,X 5,0],![X 1,0,X 3,0,X 4,0,X 5],
      ![0,X 2,0,X 3,0,X 4,0],![0,X 0,0,0,0,0,0],
      ![0,X 1,X 2,0,X 3,0,X 4],![0,0,X 1,X 2,0,X 3,0],![0,0,0,X 0,0,0,0]]
  | .hb => ![![X 2,X 3,0,X 4,0,X 5,0],![X 1,0,X 3,0,X 4,0,X 5],
      ![0,X 2,0,X 3,0,X 4,0],![0,X 0,0,0,0,0,0],
      ![0,X 1,X 2,0,X 3,0,X 4],![0,0,X 0,0,0,0,0],![0,0,0,X 1,X 2,0,X 3]]

private noncomputable def borderSix : TenKind → Matrix (Fin 6) (Fin 6) (MvPolynomial (Fin 6) ℚ)
  | .fa => ![![X 2,0,X 4,0,X 5,0],![X 1,X 3,0,X 4,0,X 5],![0,0,X 3,0,X 4,0],
      ![0,X 0,0,0,0,0],![0,X 1,X 2,0,X 3,0],![0,0,X 0,0,0,0]]
  | .ha => ![![X 2,0,X 4,0,X 5,0],![X 1,X 3,0,X 4,0,X 5],![0,0,X 3,0,X 4,0],
      ![0,X 2,0,X 3,0,X 4],![0,X 0,0,0,0,0],![0,0,0,X 0,0,0]]
  | .fb => ![![X 2,0,X 4,0,X 5,0],![X 1,X 3,0,X 4,0,X 5],![0,0,X 3,0,X 4,0],
      ![0,X 2,0,X 3,0,X 4],![0,X 1,X 2,0,X 3,0],![0,0,X 0,0,0,0]]
  | .hb => ![![X 2,0,X 4,0,X 5,0],![X 1,X 3,0,X 4,0,X 5],![0,0,X 3,0,X 4,0],
      ![0,X 2,0,X 3,0,X 4],![0,X 0,0,0,0,0],![0,0,X 1,X 2,0,X 3]]

private noncomputable def borderFive : TenKind → Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 6) ℚ)
  | .fa => ![![X 2,X 4,0,X 5,0],![X 1,0,X 4,0,X 5],![0,X 3,0,X 4,0],
      ![0,X 2,0,X 3,0],![0,X 0,0,0,0]]
  | .ha => ![![X 2,X 4,0,X 5,0],![X 1,0,X 4,0,X 5],![0,X 3,0,X 4,0],
      ![0,0,X 3,0,X 4],![0,0,X 0,0,0]]
  | .fb => ![![X 2,0,0,X 5,0],![X 1,X 3,X 4,0,X 5],![0,0,0,X 4,0],
      ![0,X 2,X 3,0,X 4],![0,X 1,0,X 3,0]]
  | .hb => ![![X 2,X 4,0,X 5,0],![X 1,0,X 4,0,X 5],![0,X 3,0,X 4,0],
      ![0,0,X 3,0,X 4],![0,X 1,X 2,0,X 3]]

private def sixRow : TenKind → Fin 6
  | .fa => 3 | .ha => 4 | .fb => 5 | .hb => 4
private def sixCol : TenKind → Fin 6
  | .fa => 1 | .ha => 1 | .fb => 2 | .hb => 1

private theorem border_minor_seven (k : TenKind) :
    (sparseBorderMatrix k).submatrix (2 : Fin 8).succAbove (1 : Fin 8).succAbove =
      borderSeven k := by
  apply Matrix.ext
  intro i j
  change sparseBorderMatrix k ((2 : Fin 8).succAbove i) ((1 : Fin 8).succAbove j) =
    borderSeven k i j
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [sparseBorderMatrix,sparseVRow,sparseURow,borderSeven,
      Matrix.submatrix_apply,Fin.succAbove]

private theorem border_minor_six (k : TenKind) :
    (borderSeven k).submatrix (3 : Fin 7).succAbove (1 : Fin 7).succAbove =
      borderSix k := by
  apply Matrix.ext
  intro i j
  change borderSeven k ((3 : Fin 7).succAbove i) ((1 : Fin 7).succAbove j) =
    borderSix k i j
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [borderSeven,borderSix,Matrix.submatrix_apply,Fin.succAbove]

private theorem border_minor_five (k : TenKind) :
    (borderSix k).submatrix (sixRow k).succAbove (sixCol k).succAbove = borderFive k := by
  apply Matrix.ext
  intro i j
  change borderSix k ((sixRow k).succAbove i) ((sixCol k).succAbove j) = borderFive k i j
  cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [borderSix,borderFive,sixRow,sixCol,Matrix.submatrix_apply,Fin.succAbove]

private theorem det_single_row {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (r j : Fin (n+1))
    (hz : ∀ c, c≠j → M r c=0) :
    M.det = (-1)^(r.val+j.val)*M r j*(M.submatrix r.succAbove j.succAbove).det := by
  classical
  rw [Matrix.det_succ_row M r]
  apply Finset.sum_eq_single j
  · intro c hc hcj
    rw [hz c hcj]
    ring
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

private theorem border_det_seven (k : TenKind) :
    (sparseBorderMatrix k).det = -MvPolynomial.X 0*(borderSeven k).det := by
  have hz : ∀ c : Fin 8, c≠1 → sparseBorderMatrix k 2 c=0 := by
    intro c hc
    cases k <;> fin_cases c <;>
      first | exact False.elim (hc rfl) | norm_num [sparseBorderMatrix,sparseVRow,sparseURow]
  have hv : sparseBorderMatrix k 2 1=MvPolynomial.X 0 := by
    cases k <;> norm_num [sparseBorderMatrix,sparseURow]
  rw [det_single_row _ 2 1 hz,hv,border_minor_seven]
  norm_num

private theorem border_det_six (k : TenKind) :
    (borderSeven k).det = MvPolynomial.X 0*(borderSix k).det := by
  have hz : ∀ c : Fin 7, c≠1 → borderSeven k 3 c=0 := by
    intro c hc
    cases k <;> fin_cases c <;>
      first | exact False.elim (hc rfl) | norm_num [borderSeven]
  have hv : borderSeven k 3 1=MvPolynomial.X 0 := by
    cases k <;> norm_num [borderSeven]
  rw [det_single_row _ 3 1 hz,hv,border_minor_six]
  norm_num

private theorem border_det_five (k : TenKind) :
    (borderSix k).det =
      (-1)^((sixRow k).val+(sixCol k).val)*MvPolynomial.X 0*(borderFive k).det := by
  have hz : ∀ c : Fin 6, c≠sixCol k → borderSix k (sixRow k) c=0 := by
    intro c hc
    cases k <;> fin_cases c <;>
      first | exact False.elim (hc rfl) | norm_num [borderSix,sixRow,sixCol]
  have hv : borderSix k (sixRow k) (sixCol k)=MvPolynomial.X 0 := by
    cases k <;> norm_num [borderSix,sixRow,sixCol]
  rw [det_single_row _ (sixRow k) (sixCol k) hz,hv,border_minor_five]

private theorem border_det_reduced (k : TenKind) :
    (sparseBorderMatrix k).det =
      (if k=.fa then -(MvPolynomial.X 0)^3 else (MvPolynomial.X 0)^3)*(borderFive k).det := by
  rw [border_det_seven,border_det_six,border_det_five]
  cases k <;> norm_num [sixRow,sixCol] <;> ring

private noncomputable def borderFourFa : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 6) ℚ) :=
  ![![X 2,0,X 5,0],![X 1,X 4,0,X 5],![0,0,X 4,0],![0,0,X 3,0]]
private noncomputable def borderFourHa : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 6) ℚ) :=
  ![![X 2,X 4,X 5,0],![X 1,0,0,X 5],![0,X 3,X 4,0],![0,0,0,X 4]]
private noncomputable def borderFourFb : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 6) ℚ) :=
  ![![X 2,0,0,0],![X 1,X 3,X 4,X 5],![0,X 2,X 3,X 4],![0,X 1,0,0]]
private noncomputable def borderFourHb0 : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 6) ℚ) :=
  ![![0,X 4,0,X 5],![X 3,0,X 4,0],![0,X 3,0,X 4],![X 1,X 2,0,X 3]]
private noncomputable def borderFourHb1 : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 6) ℚ) :=
  ![![X 4,0,X 5,0],![X 3,0,X 4,0],![0,X 3,0,X 4],![X 1,X 2,0,X 3]]

private theorem border_minor_four_fa :
    (borderFive .fa).submatrix (4 : Fin 5).succAbove (1 : Fin 5).succAbove=borderFourFa := by
  apply Matrix.ext
  intro i j
  change borderFive .fa ((4 : Fin 5).succAbove i) ((1 : Fin 5).succAbove j) = borderFourFa i j
  fin_cases i <;> fin_cases j <;>
    norm_num [borderFive,borderFourFa,Matrix.submatrix_apply,Fin.succAbove]
private theorem border_minor_four_ha :
    (borderFive .ha).submatrix (4 : Fin 5).succAbove (2 : Fin 5).succAbove=borderFourHa := by
  apply Matrix.ext
  intro i j
  change borderFive .ha ((4 : Fin 5).succAbove i) ((2 : Fin 5).succAbove j) = borderFourHa i j
  fin_cases i <;> fin_cases j <;>
    norm_num [borderFive,borderFourHa,Matrix.submatrix_apply,Fin.succAbove]
private theorem border_minor_four_fb :
    (borderFive .fb).submatrix (2 : Fin 5).succAbove (3 : Fin 5).succAbove=borderFourFb := by
  apply Matrix.ext
  intro i j
  change borderFive .fb ((2 : Fin 5).succAbove i) ((3 : Fin 5).succAbove j) = borderFourFb i j
  fin_cases i <;> fin_cases j <;>
    norm_num [borderFive,borderFourFb,Matrix.submatrix_apply,Fin.succAbove]
private theorem border_minor_four_hb0 :
    (borderFive .hb).submatrix (0 : Fin 5).succAbove (0 : Fin 5).succAbove=borderFourHb0 := by
  apply Matrix.ext
  intro i j
  change borderFive .hb ((0 : Fin 5).succAbove i) ((0 : Fin 5).succAbove j) = borderFourHb0 i j
  fin_cases i <;> fin_cases j <;>
    norm_num [borderFive,borderFourHb0,Matrix.submatrix_apply,Fin.succAbove]
private theorem border_minor_four_hb1 :
    (borderFive .hb).submatrix (1 : Fin 5).succAbove (0 : Fin 5).succAbove=borderFourHb1 := by
  apply Matrix.ext
  intro i j
  change borderFive .hb ((1 : Fin 5).succAbove i) ((0 : Fin 5).succAbove j) = borderFourHb1 i j
  fin_cases i <;> fin_cases j <;>
    norm_num [borderFive,borderFourHb1,Matrix.submatrix_apply,Fin.succAbove]

private theorem border_five_fa_det :
    (borderFive .fa).det = -MvPolynomial.X 0*borderFourFa.det := by
  have hz : ∀ c : Fin 5, c≠1 → borderFive .fa 4 c=0 := by
    intro c hc
    fin_cases c <;> first | exact False.elim (hc rfl) | norm_num [borderFive]
  rw [det_single_row _ 4 1 hz,border_minor_four_fa]
  norm_num [borderFive]
private theorem border_five_ha_det :
    (borderFive .ha).det = MvPolynomial.X 0*borderFourHa.det := by
  have hz : ∀ c : Fin 5, c≠2 → borderFive .ha 4 c=0 := by
    intro c hc
    fin_cases c <;> first | exact False.elim (hc rfl) | norm_num [borderFive]
  rw [det_single_row _ 4 2 hz,border_minor_four_ha]
  norm_num [borderFive]
private theorem border_five_fb_det :
    (borderFive .fb).det = -MvPolynomial.X 4*borderFourFb.det := by
  have hz : ∀ c : Fin 5, c≠3 → borderFive .fb 2 c=0 := by
    intro c hc
    fin_cases c <;> first | exact False.elim (hc rfl) | norm_num [borderFive]
  rw [det_single_row _ 2 3 hz,border_minor_four_fb]
  norm_num [borderFive]
private theorem det_column_two {R : Type*} [CommRing R]
    (M : Matrix (Fin 5) (Fin 5) R)
    (hz : ∀ i, i≠0 → i≠1 → M i 0=0) :
    M.det = M 0 0*(M.submatrix (0 : Fin 5).succAbove (0 : Fin 5).succAbove).det -
      M 1 0*(M.submatrix (1 : Fin 5).succAbove (0 : Fin 5).succAbove).det := by
  have h2 := hz 2 (by decide) (by decide)
  have h3 := hz 3 (by decide) (by decide)
  have h4 := hz 4 (by decide) (by decide)
  rw [Matrix.det_succ_column M (0 : Fin 5)]
  norm_num [Fin.sum_univ_succ,h2,h3,h4] <;> ring

private theorem border_five_hb_det :
    (borderFive .hb).det =
      MvPolynomial.X 2*borderFourHb0.det-MvPolynomial.X 1*borderFourHb1.det := by
  have hz : ∀ i : Fin 5, i≠0 → i≠1 → borderFive .hb i 0=0 := by
    intro i hi0 hi1
    fin_cases i <;> first
      | exact False.elim (hi0 rfl)
      | exact False.elim (hi1 rfl)
      | norm_num [borderFive]
  rw [det_column_two _ hz,border_minor_four_hb0,border_minor_four_hb1]
  norm_num [borderFive]

private def tripleDet {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*e*i-a*f*h-b*d*i+b*f*g+c*d*h-c*e*g

private theorem det_four_expansion {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0*tripleDet (M 1 1) (M 1 2) (M 1 3) (M 2 1) (M 2 2) (M 2 3) (M 3 1) (M 3 2) (M 3 3) -
      M 0 1*tripleDet (M 1 0) (M 1 2) (M 1 3) (M 2 0) (M 2 2) (M 2 3) (M 3 0) (M 3 2) (M 3 3) +
      M 0 2*tripleDet (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) (M 3 0) (M 3 1) (M 3 3) -
      M 0 3*tripleDet (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) (M 3 0) (M 3 1) (M 3 2) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,tripleDet] <;> ring

private theorem coeff_mul_two (p : MvPolynomial (Fin 6) ℚ) (d : Fin 6 →₀ ℕ) :
    (p*2).coeff d = 2*p.coeff d := by
  have htwo : (2 : MvPolynomial (Fin 6) ℚ)=MvPolynomial.C (2 : ℚ) :=
    (MvPolynomial.C_eq_coe_nat (σ := Fin 6) (R := ℚ) 2).symm
  rw [htwo,mul_comm p,MvPolynomial.coeff_C_mul]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem sparseBorder_separator (second : Bool) :
    ((sparseBorderMatrix (if second then .fb else .fa)).det -
      (sparseBorderMatrix (if second then .hb else .ha)).det).coeff
        (sparseSeparatorExponent second) = -1 := by
  classical
  rw [border_det_reduced,border_det_reduced]
  cases second
  · norm_num only [Bool.false_eq_true,reduceCtorEq,↓reduceIte]
    rw [border_five_fa_det,border_five_ha_det]
    rw [det_four_expansion borderFourFa,det_four_expansion borderFourHa]
    norm_num [borderFourFa,borderFourHa,tripleDet]
    ring_nf
    norm_num [MvPolynomial.X,MvPolynomial.monomial_pow,
      MvPolynomial.monomial_mul_monomial,MvPolynomial.coeff_add,MvPolynomial.coeff_sub,
      MvPolynomial.coeff_neg,MvPolynomial.coeff_monomial,sparseSeparatorExponent,
      coeff_mul_two,Finsupp.ext_iff,Fin.forall_fin_succ,Finsupp.add_apply,Finsupp.single_apply]
  · norm_num only [reduceCtorEq,↓reduceIte]
    rw [border_five_fb_det,border_five_hb_det]
    rw [det_four_expansion borderFourFb,det_four_expansion borderFourHb0,
      det_four_expansion borderFourHb1]
    norm_num [borderFourFb,borderFourHb0,borderFourHb1,tripleDet]
    ring_nf
    norm_num [MvPolynomial.X,MvPolynomial.monomial_pow,
      MvPolynomial.monomial_mul_monomial,MvPolynomial.coeff_add,MvPolynomial.coeff_sub,
      MvPolynomial.coeff_neg,MvPolynomial.coeff_monomial,sparseSeparatorExponent,
      coeff_mul_two,Finsupp.ext_iff,Fin.forall_fin_succ,Finsupp.add_apply,Finsupp.single_apply]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact eight-row coefficient extraction in the free interlaced alphabet. -/
theorem universalBorder_separator (second : Bool) :
    ((universalBorderMatrix (if second then .fb else .fa)).det -
      (universalBorderMatrix (if second then .hb else .ha)).det).coeff
        (separatorExponent second) = -1 := by
  classical
  rw [← sparseSeparatorExponent_map]
  rw [← MvPolynomial.coeff_killCompl separatorEmbedding_injective]
  change (sparseProjection
    ((universalBorderMatrix (if second then .fb else .fa)).det -
      (universalBorderMatrix (if second then .hb else .ha)).det)).coeff
        (sparseSeparatorExponent second) = -1
  rw [map_sub,sparseProjection.map_det,sparseProjection.map_det,
    ← sparseBorderMatrix_eq,← sparseBorderMatrix_eq]
  exact sparseBorder_separator second

/-- Signed actual labels before the positive-index coercion. -/
def borderAlphabetLabel (P : TenParameters) (j : Fin 18) : ℤ :=
  (j.val % 9 : ℕ)*P.b+P.d+(if j.val<9 then 0 else P.a)

private theorem borderAlphabetLabel_pos (P : TenParameters) (hd : 0 < P.d)
    (j : Fin 18) : 0 < borderAlphabetLabel P j := by
  have ha := P.a_pos
  have hb := P.b_pos
  have hmul : 0 ≤ ((j.val % 9 : ℕ) : ℤ)*P.b := mul_nonneg (by omega) hb.le
  unfold borderAlphabetLabel
  split_ifs <;> omega

/-- The positive actual label assigned to each of the eighteen free generators. -/
def borderAlphabet (P : TenParameters) (hd : 0 < P.d) (j : Fin 18) : ℕ+ :=
  ⟨(borderAlphabetLabel P j).toNat, by
    have h := borderAlphabetLabel_pos P hd j
    omega⟩

private theorem borderAlphabet_val (P : TenParameters) (hd : 0 < P.d) (j : Fin 18) :
    ((borderAlphabet P hd j).val : ℤ) = borderAlphabetLabel P j :=
  Int.toNat_of_nonneg (borderAlphabetLabel_pos P hd j).le

theorem borderAlphabet_injective (P : TenParameters) (hd : 0 < P.d) :
    Function.Injective (borderAlphabet P hd) := by
  intro i j he
  have ha := P.a_pos
  have hab : P.a<P.b := by have := P.separated; have := P.d_nonneg; omega
  have hb := P.b_pos
  have hi := i.isLt
  have hj := j.isLt
  have he' := congrArg (fun v : ℕ+ => (v.val : ℤ)) he
  rw [borderAlphabet_val, borderAlphabet_val] at he'
  unfold borderAlphabetLabel at he'
  by_cases hi9 : i.val<9 <;> by_cases hj9 : j.val<9
  all_goals
    simp only [hi9, hj9, ↓reduceIte] at he'
    by_cases hle : i.val%9 ≤ j.val%9
    · by_cases heq : i.val%9=j.val%9
      · rw [heq] at he'
        apply Fin.ext
        omega
      · have hstep : ((i.val%9 : ℕ) : ℤ)+1 ≤ ((j.val%9 : ℕ) : ℤ) := by omega
        have hmul := mul_le_mul_of_nonneg_right hstep hb.le
        nlinarith
    · have hstep : ((j.val%9 : ℕ) : ℤ)+1 ≤ ((i.val%9 : ℕ) : ℤ) := by omega
      have hmul := mul_le_mul_of_nonneg_right hstep hb.le
      nlinarith

private theorem borderSymbol_rename (P : TenParameters) (hd : 0 < P.d)
    (v : Bool) (r : ℤ) (hr : r<9) :
    MvPolynomial.rename (borderAlphabet P hd) (borderSymbol v r) =
      complete ((if v then P.a else 0)+r*P.b+P.d) := by
  have ha := P.a_pos
  have hb := P.b_pos
  have hsep := P.separated
  by_cases hr0 : 0 ≤ r
  · let j : Fin 18 := ⟨r.toNat+(if v then 9 else 0), by cases v <;> simp <;> omega⟩
    have hrNat : r.toNat<9 := by omega
    have hlabel : borderAlphabetLabel P j = (if v then P.a else 0)+r*P.b+P.d := by
      cases v <;>
        simp [borderAlphabetLabel,j,Nat.add_mod,Nat.mod_eq_of_lt hrNat,
          Int.toNat_of_nonneg hr0,hr] <;> ring
    have hk : 0 < (if v then P.a else 0)+r*P.b+P.d := by
      rw [← hlabel]
      exact borderAlphabetLabel_pos P hd j
    have he : borderAlphabet P hd j =
        (⟨((if v then P.a else 0)+r*P.b+P.d).toNat, by omega⟩ : ℕ+) := by
      apply Subtype.ext
      change (borderAlphabet P hd j).val =
        ((if v then P.a else 0)+r*P.b+P.d).toNat
      have hval := borderAlphabet_val P hd j
      rw [hlabel] at hval
      have htarget := Int.toNat_of_nonneg hk.le
      exact_mod_cast hval.trans htarget.symm
    rw [borderSymbol, dif_pos ⟨hr0,hr⟩, MvPolynomial.rename_X, complete_of_pos hk]
    exact congrArg MvPolynomial.X he
  · have hmul := mul_le_mul_of_nonneg_right (show r ≤ -1 by omega) hb.le
    have hk : (if v then P.a else 0)+r*P.b+P.d<0 := by
      cases v <;> simp <;> nlinarith
    rw [borderSymbol, dif_neg (by omega), map_zero, complete_of_neg hk]

set_option maxHeartbeats 0 in
/-- Faithful alphabet renaming identifies the free matrix with the actual beta matrix. -/
theorem tiedBorderMatrix_rename (P : TenParameters) (hd : 0 < P.d) (k : TenKind) :
    tiedBorderMatrix P k =
      (universalBorderMatrix k).map (MvPolynomial.rename (borderAlphabet P hd)) := by
  apply Matrix.ext
  intro i j
  have hr : (borderRow k i).2 ≤ 8 := by
    cases k <;> fin_cases i <;> norm_num [borderRow]
  have hj := j.isLt
  change complete ((if (borderRow k i).1 then P.a else 0) +
      ((borderRow k i).2-(7-(j.val : ℤ)))*P.b+P.d) =
    MvPolynomial.rename (borderAlphabet P hd)
      (borderSymbol (borderRow k i).1 ((borderRow k i).2-(7-(j.val : ℤ))))
  rw [borderSymbol_rename P hd _ _ (by omega)]

private theorem matrix_map_det {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map f).det = f M.det := by
  have hm : M.map f=f.mapMatrix M := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hm,← RingHom.map_det]

private theorem tiedBorder_schur_rename (P : TenParameters) (hd : 0 < P.d) (k : TenKind) :
    ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).schur =
      MvPolynomial.rename (borderAlphabet P hd) (universalBorderMatrix k).det := by
  rw [P.tiedBorder_schur,P.tiedBorderMatrix_rename hd]
  exact matrix_map_det (R := MvPolynomial (Fin 18) ℚ) (S := CompleteRing)
    (MvPolynomial.rename (R := ℚ) (borderAlphabet P hd)).toRingHom (universalBorderMatrix k)

/-- The actual coefficient is minus one for every zero-free parameter choice in both families. -/
theorem tiedBorder_separator (P : TenParameters) (hd : 0 < P.d) (second : Bool) :
    (((P.diagram (if second then .fb else .fa)).positiveBorder
        P.b P.b P.b_pos P.b_pos).schur -
      ((P.diagram (if second then .hb else .ha)).positiveBorder
        P.b P.b P.b_pos P.b_pos).schur).coeff
      ((separatorExponent second).mapDomain (borderAlphabet P hd)) = -1 := by
  rw [P.tiedBorder_schur_rename hd,P.tiedBorder_schur_rename hd,←map_sub]
  rw [MvPolynomial.coeff_rename_mapDomain _ (P.borderAlphabet_injective hd)]
  exact universalBorder_separator second

theorem tiedBorder_schur_ne (P : TenParameters) (hd : 0 < P.d) (second : Bool) :
    ((P.diagram (if second then .fb else .fa)).positiveBorder
      P.b P.b P.b_pos P.b_pos).schur ≠
    ((P.diagram (if second then .hb else .ha)).positiveBorder
      P.b P.b P.b_pos P.b_pos).schur := by
  intro he
  have hc := P.tiedBorder_separator hd second
  rw [he, sub_self, MvPolynomial.coeff_zero] at hc
  norm_num at hc

/-- Affine homogenization of the actual family parameters. -/
def gammaParameters (P : TenParameters) : TenParameters where
  a := 2*P.a
  b := 2*P.b
  d := 2*P.d+1
  a_pos := by have := P.a_pos; omega
  d_nonneg := by have := P.d_nonneg; omega
  separated := by have := P.separated; omega

theorem gammaParameters_d_pos (P : TenParameters) : 0 < P.gammaParameters.d := by
  have := P.d_nonneg
  simp [gammaParameters]
  omega

set_option maxHeartbeats 0 in
/-- Gamma acts on the genuine bordered matrices, including every common-beta unit. -/
theorem gamma_tiedBorder_schur (P : TenParameters) (k : TenKind) :
    ((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).gamma.schur =
      ((P.gammaParameters.diagram k).positiveBorder
        P.gammaParameters.b P.gammaParameters.b
        P.gammaParameters.b_pos P.gammaParameters.b_pos).schur := by
  unfold BetaDiagram.schur
  congr 1
  apply Matrix.ext
  intro i j
  change complete (2*((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).row i+1 -
      2*((P.diagram k).positiveBorder P.b P.b P.b_pos P.b_pos).col j) =
    complete (((P.gammaParameters.diagram k).positiveBorder P.gammaParameters.b
      P.gammaParameters.b P.gammaParameters.b_pos P.gammaParameters.b_pos).row i -
      ((P.gammaParameters.diagram k).positiveBorder P.gammaParameters.b
        P.gammaParameters.b P.gammaParameters.b_pos P.gammaParameters.b_pos).col j)
  rw [tiedBorder_row, tiedBorder_col_kind, tiedBorder_row, tiedBorder_col_kind]
  simp only [gammaParameters]
  congr 1
  split_ifs <;> ring

/-- The tied border cannot merge the exceptional orbits, even on the common-beta boundary. -/
theorem tiedBorder_schur_ne_including_units (P : TenParameters) (second : Bool) :
    ((P.diagram (if second then .fb else .fa)).positiveBorder
      P.b P.b P.b_pos P.b_pos).schur ≠
    ((P.diagram (if second then .hb else .ha)).positiveBorder
      P.b P.b P.b_pos P.b_pos).schur := by
  intro he
  have hg := congrArg (gammaEncoding 8) he
  rw [← BetaDiagram.gamma_schur_encoding, ← BetaDiagram.gamma_schur_encoding,
    P.gamma_tiedBorder_schur, P.gamma_tiedBorder_schur] at hg
  exact P.gammaParameters.tiedBorder_schur_ne P.gammaParameters_d_pos second hg

/-- Either genuine positive endpoint extension of a displayed seven-row member. -/
def endpoint (P : TenParameters) (k : TenKind) (top : Bool)
    (t : ℤ) (ht : 0 < t) : BetaDiagram 7 :=
  if top then (P.diagram k).extendTop t ht else (P.diagram k).extendBottom t ht

/-- A positive endpoint never becomes a displayed exceptional representative,
even with different family parameters. -/
theorem endpoint_not_translation_exceptional (P Q : TenParameters) (k l : TenKind)
    (top : Bool) (t : ℤ) (ht : 0 < t) :
    ¬ (P.endpoint k top t ht).TranslationEquivalent (Q.diagram l) := by
  rintro ⟨c,hr,hc⟩
  have hc0 := hc 0
  have hc1 := hc 1
  have hc6 := hc 6
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  cases top <;> cases k <;> cases l <;>
    norm_num [endpoint, BetaDiagram.extendTop, BetaDiagram.extendBottom,
      diagram, rowBase, column] at hc0 hc1 hc6 hr0 hr1 hr2 <;> omega

/-- The unchanged interior row gaps cannot be an arithmetic progression.
Every reflected exceptional column list would impose exactly that progression. -/
theorem endpoint_not_rotation_exceptional (P Q : TenParameters) (k l : TenKind)
    (top : Bool) (t : ℤ) (ht : 0 < t) :
    ¬ (P.endpoint k top t ht).RotationEquivalent (Q.diagram l) := by
  rintro ⟨c,hr,hc⟩
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  have h5 := hr 5
  have h6 := hr 6
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases top <;> cases k <;>
    norm_num [endpoint, BetaDiagram.extendTop, BetaDiagram.extendBottom,
      diagram, rowBase, column, Fin.rev] at h1 h2 h3 h4 h5 h6 <;> omega

/-- Reflected positive endpoints have the same arithmetic-column obstruction. -/
theorem endpoints_not_rotation (P Q : TenParameters) (k l : TenKind)
    (top bottom : Bool) (t z : ℤ) (ht : 0 < t) (hz : 0 < z) :
    ¬ (P.endpoint k top t ht).RotationEquivalent (Q.endpoint l bottom z hz) := by
  rintro ⟨c,hr,hc⟩
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  have h5 := hr 5
  have h6 := hr 6
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases top <;> cases bottom <;> cases k <;>
    norm_num [endpoint, BetaDiagram.extendTop, BetaDiagram.extendBottom,
      diagram, rowBase, column, Fin.rev] at h1 h2 h3 h4 h5 h6 <;> omega

/-- Distinct actual core representatives remain distinct up to translation after endpoint extension. -/
theorem endpoints_not_translation_of_distinct (P : TenParameters) (k l : TenKind)
    (hkl : k ≠ l) (top bottom : Bool)
    (t z : ℤ) (ht : 0 < t) (hz : 0 < z) :
    ¬ (P.endpoint k top t ht).TranslationEquivalent (P.endpoint l bottom z hz) := by
  rintro ⟨c,hr,hc⟩
  have hc0 := hc 0
  have hc6 := hc 6
  have h4 := hr 4
  have h5 := hr 5
  have h6 := hr 6
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  cases top <;> cases bottom <;> cases k <;> cases l <;>
    norm_num [endpoint, BetaDiagram.extendTop, BetaDiagram.extendBottom,
      diagram, rowBase, column] at hc0 hc6 h4 h5 h6 <;>
    first | exact False.elim (hkl rfl) | omega

/-- The actual exceptional seven-row members have unequal geometric endpoint margins. -/
theorem exceptional_endpointLeader (P : TenParameters) (hd : 0 < P.d) (k : TenKind) :
    (P.diagram k).EndpointLeader := by
  apply (P.diagram k).endpointLeader_of_endpointCoefficient_ne_zero
  apply (P.diagram k).endpointCoefficient_ne_zero_untied
    ((P.diagram k).positiveCorner_of_connected_zeroFree (P.connected k)
      ((P.zeroFree_iff k).mpr hd))
  have ha := P.a_pos
  have hdn := P.d_nonneg
  have hb := P.separated
  have ht : (P.diagram k).topMargin=P.a := by
    cases k <;> norm_num [BetaDiagram.topMargin,diagram,rowBase] <;> ring
  have hb' : (P.diagram k).bottomMargin=P.b := by
    change (P.diagram k).col (Fin.last 5).castSucc -
      (P.diagram k).col (Fin.last 6) = P.b
    rw [show (Fin.last 5).castSucc = (5 : Fin 7) by decide,
      show Fin.last 6 = (6 : Fin 7) by decide]
    norm_num [diagram,column]
  rw [ht,hb']
  omega

theorem exceptional_endpoint_ne (P : TenParameters) (hd : 0 < P.d)
    (k : TenKind) (t : ℤ) (ht : 0 < t) :
    ((P.diagram k).extendTop t ht).schur ≠ ((P.diagram k).extendBottom t ht).schur :=
  sub_ne_zero.mp (BetaDiagram.EndpointLeader.difference_ne_zero _
    (P.exceptional_endpointLeader hd k) t ht)

private theorem gamma_family_row (P : TenParameters) (k : TenKind) (i : Fin 7) :
    (P.gammaParameters.diagram k).row i = 2*(P.diagram k).row i+1 := by
  cases k <;> fin_cases i <;> norm_num [diagram,rowBase,gammaParameters] <;> ring

private theorem gamma_family_col (P : TenParameters) (k : TenKind) (i : Fin 7) :
    (P.gammaParameters.diagram k).col i = 2*(P.diagram k).col i := by
  fin_cases i <;> norm_num [diagram,column,gammaParameters] <;> ring

set_option maxHeartbeats 0 in
/-- Gamma doubles the endpoint size on the actual family matrices. -/
theorem gamma_endpoint_schur (P : TenParameters) (k : TenKind) (top : Bool)
    (t : ℤ) (ht : 0 < t) :
    (P.endpoint k top t ht).gamma.schur =
      (P.gammaParameters.endpoint k top (2*t) (by omega)).schur := by
  unfold BetaDiagram.schur
  congr 1
  apply Matrix.ext
  intro i j
  cases top with
  | false =>
    change complete (2*(P.diagram k).row i+1 -
      2*(if j=Fin.last 6 then (P.diagram k).col j-t else (P.diagram k).col j)) =
      complete ((P.gammaParameters.diagram k).row i -
        (if j=Fin.last 6 then (P.gammaParameters.diagram k).col j-2*t
          else (P.gammaParameters.diagram k).col j))
    simp_rw [gamma_family_row,gamma_family_col]
    split_ifs <;> congr 1 <;> ring
  | true =>
    change complete (2*(if i=0 then (P.diagram k).row i+t else (P.diagram k).row i)+1 -
      2*(P.diagram k).col j) =
      complete ((if i=0 then (P.gammaParameters.diagram k).row i+2*t
        else (P.gammaParameters.diagram k).row i) - (P.gammaParameters.diagram k).col j)
    simp_rw [gamma_family_row,gamma_family_col]
    split_ifs <;> congr 1 <;> ring

/-- Positive opposite endpoints are isolated for each exceptional member, including units.
This is endpoint inequality, not an assumed rigidity theorem for the extensions. -/
theorem exceptional_endpoint_ne_including_units (P : TenParameters)
    (k : TenKind) (t : ℤ) (ht : 0 < t) :
    ((P.diagram k).extendTop t ht).schur ≠ ((P.diagram k).extendBottom t ht).schur := by
  intro he
  have hg := congrArg (gammaEncoding 7) he
  rw [← BetaDiagram.gamma_schur_encoding, ← BetaDiagram.gamma_schur_encoding] at hg
  have hg' :
      (P.gammaParameters.endpoint k true (2*t) (by omega)).schur =
        (P.gammaParameters.endpoint k false (2*t) (by omega)).schur := by
    change (P.endpoint k true t ht).gamma.schur = (P.endpoint k false t ht).gamma.schur at hg
    rw [P.gamma_endpoint_schur, P.gamma_endpoint_schur] at hg
    exact hg
  exact P.gammaParameters.exceptional_endpoint_ne P.gammaParameters_d_pos k
    (2*t) (by omega) hg'

theorem exceptional_rotated_endpoint_ne_including_units (P : TenParameters)
    (k : TenKind) (t : ℤ) (ht : 0 < t) :
    ((P.diagram k).rotate.extendTop t ht).schur ≠
      ((P.diagram k).rotate.extendBottom t ht).schur := by
  rw [BetaDiagram.rotate_extendTop_schur, BetaDiagram.rotate_extendBottom_schur]
  exact Ne.symm (P.exceptional_endpoint_ne_including_units k t ht)

end TenParameters
end SkewJacobiNegative
