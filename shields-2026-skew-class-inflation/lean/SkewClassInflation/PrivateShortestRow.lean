/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.HessenbergMembership
import SkewClassInflation.BoundaryInverse

/-!
# A private irreducible row coefficient forces an endpoint

The shortest-row argument in `lem:two-row-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  An internal private diagonal
variable leaves two actual nonempty factors, contradicting
irreducibility of its observed coefficient.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The actual consecutive row restriction, allowing an empty interval. -/
def rowInterval {n : ℕ} (D : BetaDiagram n) (a k : ℕ) (h : a + k ≤ n) : BetaDiagram k where
  row i := D.row ⟨a + i.val, by have := i.isLt; omega⟩
  col i := D.col ⟨a + i.val, by have := i.isLt; omega⟩
  row_strictAnti := by
    intro i j hij
    apply D.row_strictAnti
    change a + i.val < a + j.val
    exact Nat.add_lt_add_left hij a
  col_strictAnti := by
    intro i j hij
    apply D.col_strictAnti
    change a + i.val < a + j.val
    exact Nat.add_lt_add_left hij a
  row_nonempty i := D.row_nonempty _

/-- A nonempty consecutive restriction of a connected profile remains connected. -/
theorem rowInterval_connected {n : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (a k : ℕ) (h : a + k ≤ n) (hk : 0 < k) : (rowInterval D a k h).Connected := by
  refine ⟨hk, ?_⟩
  intro i hi
  have hd := hD.2 (⟨a + i.val, by have := i.isLt; omega⟩ : Fin n)
    (by change a + i.val + 1 < n; omega)
  exact hd

/-- Removing a nonterminal diagonal site splits its genuine complementary determinant. -/
theorem diagonal_cofactor_split {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsHessenberg D)
    (r : Fin (n + 1)) (hrn : r.val < n) :
    (D.matrix.submatrix r.succAbove r.succAbove).det =
      (rowInterval D 0 r.val (by omega)).schur *
      (rowInterval D (r.val + 1) (n - r.val) (by omega)).schur := by
  classical
  let a := r.val
  let b := n - r.val
  have hab : a + b = n := by dsimp [a, b]; omega
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr hab)
  let left : Fin a → Fin (n + 1) := fun i => ⟨i.val, by have := i.isLt; dsimp [a] at *; omega⟩
  let right : Fin b → Fin (n + 1) :=
    fun i => ⟨r.val + 1 + i.val, by have := i.isLt; dsimp [b] at *; omega⟩
  have hl (i : Fin a) : r.succAbove (e (Sum.inl i)) = left i := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change i.val < r.val
      exact i.isLt)]
    apply Fin.ext
    rfl
  have hr (i : Fin b) : r.succAbove (e (Sum.inr i)) = right i := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      change r.val ≤ a + i.val
      dsimp [a]
      omega)]
    apply Fin.ext
    change a + i.val + 1 = r.val + 1 + i.val
    dsimp [a]
    omega
  let A := (rowInterval D 0 r.val (by omega)).matrix
  let C := (rowInterval D (r.val + 1) (n - r.val) (by omega)).matrix
  let B := D.matrix.submatrix left right
  have hm : (D.matrix.submatrix r.succAbove r.succAbove).submatrix e e =
      Matrix.fromBlocks A B 0 C := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, hl]
      change complete (D.row ⟨i.val, _⟩ - D.col ⟨j.val, _⟩) =
        complete (D.row ⟨0 + i.val, _⟩ - D.col ⟨0 + j.val, _⟩)
      simp only [Nat.zero_add]
    · simp only [Matrix.submatrix_apply, hl, hr]
      rfl
    · simp only [Matrix.submatrix_apply, hr, hl]
      change complete (D.row (right i) - D.col (left j)) = 0
      apply complete_of_neg
      apply hD
      dsimp [left, right, a] at *
      have := j.isLt
      omega
    · simp only [Matrix.submatrix_apply, hr]
      rfl
  have hd := Matrix.det_submatrix_equiv_self e
    (D.matrix.submatrix r.succAbove r.succAbove)
  rw [hm, Matrix.det_fromBlocks_zero₂₁] at hd
  exact hd.symm

/-- A private diagonal variable whose coefficient is irreducible must be in an endpoint row. -/
theorem private_irreducible_row_boundary {n : ℕ} (D : BetaDiagram (n + 1))
    (hh : IsHessenberg D) (v : ℕ+) (r : Fin (n + 1))
    (he : D.matrix r r = MvPolynomial.X v)
    (hp : ∀ i j, i ≠ r ∨ j ≠ r → v ∉ (D.matrix i j).vars)
    (hi : Irreducible (MvPolynomial.pderiv v D.schur)) :
    r = 0 ∨ r = Fin.last n := by
  by_contra hb
  have hr0 : 0 < r.val := by
    have hne : r ≠ 0 := fun h => hb (Or.inl h)
    exact Fin.pos_iff_ne_zero.mpr hne
  have hrn : r.val < n := by
    have hne : r ≠ Fin.last n := fun h => hb (Or.inr h)
    have hrl := r.isLt
    have hval : r.val ≠ n := fun h => hne (Fin.ext h)
    omega
  have hd := pderiv_det_private D.matrix v r r he hp
  have hs : (-1 : CompleteRing) ^ (r.val + r.val) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  change MvPolynomial.pderiv v D.schur = _ at hd
  rw [hs, one_mul, diagonal_cofactor_split D hh r hrn] at hd
  have hprod := hi.isUnit_or_isUnit hd
  rcases hprod with hu | hu
  · exact (rowInterval D 0 r.val (by omega)).schur_not_isUnit hr0 hu
  · exact (rowInterval D (r.val + 1) (n - r.val) (by omega)).schur_not_isUnit
      (by omega) hu

/-- A unique shortest row, distinct from all gaps, produces a genuinely private diagonal entry. -/
theorem shortest_row_private {n : ℕ} (P : Profile n) (hP : SkewJacobiNegative.Staircase.Thick P)
    (a : ℕ+) (r : Fin (n + 1)) (hr : P.r r = a.val)
    (hmin : ∀ i, a.val ≤ P.r i) (hunique : ∀ i, P.r i = a.val → i = r)
    (hg : ∀ j, P.g j ≠ a.val) :
    P.toBetaDiagram.matrix r r = MvPolynomial.X a ∧
      ∀ i j, i ≠ r ∨ j ≠ r → a ∉ (P.toBetaDiagram.matrix i j).vars := by
  constructor
  · change complete (P.xi r - P.zeta r) = MvPolynomial.X a
    rw [P.xi_sub_zeta, hr]
    exact complete_nat a
  · intro i j hij hm
    have he : (a.val : ℤ) = P.xi i - P.zeta j := (mem_vars_complete_iff _ a).mp hm
    rcases lt_trichotomy i j with hij' | rfl | hji
    · have hc := P.zeta_strictAnti hij'
      have hd := P.xi_sub_zeta i
      have hr := hmin i
      omega
    · have hd := P.xi_sub_zeta i
      have hr : P.r i = a.val := by omega
      have hi := hunique i hr
      exact hij.elim (fun h => h hi) (fun h => h hi)
    · by_cases hfar : j.val + 1 < i.val
      · have hn := hP.hessenberg i j hfar
        have ha := a.pos
        omega
      · let s : Fin n := ⟨j.val, by
          have := i.isLt
          change j.val < i.val at hji
          omega⟩
        have hs0 : s.castSucc = j := Fin.ext rfl
        have hs1 : s.succ = i := by
          apply Fin.ext
          change s.val + 1 = i.val
          dsimp [s]
          change j.val < i.val at hji
          omega
        have hv := P.xi_succ_sub_zeta_castSucc s
        rw [hs0, hs1] at hv
        exact hg s (by omega)

/-- The private shortest-row coefficient is the whole first-row deletion when that row is first. -/
theorem shortest_first_row_coefficient {n : ℕ} (P : Profile n)
    (hP : SkewJacobiNegative.Staircase.Thick P) (a : ℕ+)
    (hr : P.r 0 = a.val) (hmin : ∀ i, a.val ≤ P.r i)
    (hunique : ∀ i, P.r i = a.val → i = 0) (hg : ∀ j, P.g j ≠ a.val) :
    MvPolynomial.pderiv a P.toBetaDiagram.schur =
      (firstRowTail P.toBetaDiagram).schur := by
  obtain ⟨he, hp⟩ := shortest_row_private P hP a 0 hr hmin hunique hg
  have hd := pderiv_det_private P.toBetaDiagram.matrix a 0 0 he hp
  have hm : (firstRowTail P.toBetaDiagram).matrix =
      P.toBetaDiagram.matrix.submatrix Fin.succ Fin.succ := rfl
  rw [BetaDiagram.schur, BetaDiagram.schur, hm]
  simpa only [Fin.val_zero, zero_add, pow_zero, one_mul, Fin.succAbove_zero] using hd

end SkewClassInflation
