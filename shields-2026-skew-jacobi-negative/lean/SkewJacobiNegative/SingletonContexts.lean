/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.BorderCoefficients
import SkewJacobiNegative.ComponentCuts
import SkewJacobiNegative.SchurClasses

/-!
# Actual singleton contexts

The beta lists and full determinant identity of `eq:singleton-context` and
`eq:singleton-polynomial` in `shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
variable {n m : ℕ}

/-- The genuine minimum-square initial polynomial has coefficient one. -/
theorem square_initial_monomial (D : BetaDiagram n) :
    Base.initialForm Base.squareWeight.generatorWeight D.schur =
      MvPolynomial.monomial D.diagonalExponent 1 := by
  rw [D.schur_eq_integerLift, integerLift_initialForm]
  unfold integerSchur diagonalExponent
  rw [D.integerMatrix_eq_staircase,
    Base.monge_minor_initialForm Base.squareWeight D.neg_row_strictMono
      D.neg_col_strictMono D.neg_diagonal_feasible,
    Base.increasing_product_eq_monomial _ _ D.neg_diagonal_feasible]
  simp [integerLift, MvPolynomial.map_monomial]

/-- A nonzero scalar preserves the actual support minimum. -/
theorem initialForm_rat_smul (w : ℕ+ → ℝ) (p : CompleteRing) (q : ℚ)
    (_hp : p ≠ 0) (hq : q ≠ 0) :
    Base.initialForm w (q • p) = q • Base.initialForm w p := by
  classical
  have hs : (q • p).support = p.support := by
    ext d
    simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul,
      smul_eq_mul, ne_eq, mul_eq_zero, hq, false_or]
  have hl : Base.leastWeight w (q • p) = Base.leastWeight w p := by
    unfold Base.leastWeight
    rw [hs]
  unfold Base.initialForm
  rw [hl]
  exact map_smul (MvPolynomial.weightedHomogeneousComponent w (Base.leastWeight w p)) q p

/-- Coefficient-one leaders remove the scalar without assuming equal row counts. -/
theorem schur_eq_of_proportional (E : BetaDiagram n) (F : BetaDiagram m) (q : ℚ)
    (he : E.schur = q • F.schur) : E.schur = F.schur := by
  classical
  have hq : q ≠ 0 := by
    intro h
    apply E.schur_ne_zero
    simpa [h] using he
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [initialForm_rat_smul _ _ _ F.schur_ne_zero hq,
    E.square_initial_monomial, F.square_initial_monomial] at hi
  have hc := congrArg (fun p : CompleteRing => p.coeff E.diagonalExponent) hi
  by_cases hd : E.diagonalExponent = F.diagonalExponent
  · have hq1 : q = 1 := by simpa [hd] using hc.symm
    simpa [hq1] using he
  · have : (1 : ℚ) = 0 := by
      simp [MvPolynomial.coeff_monomial, Ne.symm hd] at hc
    exact False.elim (one_ne_zero this)

/-- Polynomial association of actual Schur functions is equality, not a chosen scalar. -/
theorem schur_eq_of_associated (E : BetaDiagram n) (F : BetaDiagram m)
    (h : Associated E.schur F.schur) : E.schur = F.schur := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨q, _, hq⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  apply Eq.symm
  apply F.schur_eq_of_proportional E q
  rw [MvPolynomial.smul_eq_C_mul, ← hq, mul_comm]
  exact hu.symm

/-- Common translation of both actual beta lists. -/
def shifted (D : BetaDiagram n) (c : ℤ) : BetaDiagram n where
  row i := D.row i + c
  col i := D.col i + c
  row_strictAnti := by
    intro i j h
    have hh := D.row_strictAnti h
    change D.row j + c < D.row i + c
    omega
  col_strictAnti := by
    intro i j h
    have hh := D.col_strictAnti h
    change D.col j + c < D.col i + c
    omega
  row_nonempty := by
    intro i
    have hh := D.row_nonempty i
    omega

@[simp] theorem shifted_matrix (D : BetaDiagram n) (c : ℤ) :
    (D.shifted c).matrix = D.matrix := by
  ext i j
  simp [matrix, shifted]

@[simp] theorem shifted_schur (D : BetaDiagram n) (c : ℤ) :
    (D.shifted c).schur = D.schur := by
  unfold schur
  rw [shifted_matrix]

/-- The disconnected maximal cofactor: one nonempty row followed by the core. -/
def singletonCore (Q : BetaDiagram (n + 1)) (s g : ℤ)
    (hs : 0 < s) (hg : 0 < g) : BetaDiagram (n + 2) where
  row := Fin.cons (Q.row 0 + g + s) Q.row
  col := Fin.cons (Q.row 0 + g) Q.col
  row_strictAnti := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        have h := Q.row_strictAnti.antitone (Fin.zero_le j)
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        simpa only [Fin.cons_succ] using Q.row_strictAnti
          (show i < j by simpa only [Fin.succ_lt_succ_iff] using hij)
  col_strictAnti := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        have h := Q.col_strictAnti.antitone (Fin.zero_le j)
        have h0 := Q.row_nonempty 0
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        simpa only [Fin.cons_succ] using Q.col_strictAnti
          (show i < j by simpa only [Fin.succ_lt_succ_iff] using hij)
  row_nonempty := by
    intro i
    cases i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; omega
    | succ i => simpa only [Fin.cons_succ] using Q.row_nonempty i

/-- The manuscript's parent, including its final zero beta after normalization. -/
def singletonContext (Q : BetaDiagram (n + 1)) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    BetaDiagram (n + 3) :=
  ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).shifted v

@[simp] theorem singletonContext_row_zero (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row 0 = Q.row 0 + v + g + s + u := by
  simp [singletonContext, shifted, singletonCore]
  ring

@[simp] theorem singletonContext_row_one (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row (0 : Fin (n + 2)).succ =
      Q.row 0 + v + g + s := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row
    (0 : Fin (n + 2)).succ + v = _
  rw [positiveBorder_row_succ]
  simp only [singletonCore, Fin.cons_zero]
  ring

@[simp] theorem singletonContext_row_core (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (i : Fin (n + 1)) :
    (Q.singletonContext s u v g hs hu hv hg).row i.succ.succ = v + Q.row i := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row i.succ.succ + v = _
  rw [positiveBorder_row_succ]
  simp only [singletonCore, Fin.cons_succ]
  omega

@[simp] theorem singletonContext_col_zero (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).col 0 = v + Q.row 0 + g := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col
    (0 : Fin (n + 2)).castSucc + v = _
  rw [positiveBorder_col_castSucc]
  simp only [singletonCore, Fin.cons_zero]
  ring

@[simp] theorem singletonContext_col_core (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (i : Fin (n + 1)) :
    (Q.singletonContext s u v g hs hu hv hg).col i.succ.castSucc = v + Q.col i := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col i.succ.castSucc + v = _
  rw [positiveBorder_col_castSucc]
  simp only [singletonCore, Fin.cons_succ]
  omega

@[simp] theorem singletonContext_col_last (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2)) =
      Q.col (Fin.last n) := by
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col
    (Fin.last (n + 2)) + v = _
  rw [positiveBorder_col_last]
  simp only [singletonCore, Fin.cons_last]
  omega

/-- The singleton context is connected even though its maximal cofactor is not. -/
theorem singletonContext_connected (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).Connected := by
  have h := (Q.singletonCore s g hs hg).positiveBorder_connected u v hu hv
  refine ⟨h.1, ?_⟩
  intro i hi
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col i + v ≤
    ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row ⟨i.val + 1, hi⟩ + v
  have hh := h.2 i hi
  omega

/-- Every entry of the singleton's lower-left rectangle is strictly negative. -/
theorem singletonCore_lower_negative (Q : BetaDiagram (n + 1))
    (s g : ℤ) (hs : 0 < s) (hg : 0 < g) (i : Fin (n + 1)) :
    (Q.singletonCore s g hs hg).row i.succ -
      (Q.singletonCore s g hs hg).col 0 < 0 := by
  have h := Q.row_strictAnti.antitone (Fin.zero_le i)
  simp only [singletonCore, Fin.cons_zero, Fin.cons_succ]
  omega

/-- Common translation preserves absence of common beta entries. -/
theorem shifted_zeroFree (D : BetaDiagram n) (hD : D.ZeroFree) (c : ℤ) :
    (D.shifted c).ZeroFree := by
  intro i j h
  apply hD i j
  exact add_right_cancel h

/-- A positive border introduces no common beta entries. -/
theorem positiveBorder_zeroFree (D : BetaDiagram (n + 1)) (hD : D.ZeroFree)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).ZeroFree := by
  intro i j he
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.lastCases with
    | last =>
      have hr := D.row_strictAnti.antitone (Fin.le_last (0 : Fin (n + 1)))
      have hd := D.row_nonempty (Fin.last n)
      simp only [positiveBorder_row_zero, positiveBorder_col_last] at he
      omega
    | cast j =>
      have hr := D.row_strictAnti.antitone (Fin.zero_le j)
      have hd := D.row_nonempty j
      simp only [positiveBorder_row_zero, positiveBorder_col_castSucc] at he
      omega
  | succ i =>
    cases j using Fin.lastCases with
    | last =>
      have hc := D.col_strictAnti.antitone (Fin.le_last i)
      have hd := D.row_nonempty i
      simp only [positiveBorder_row_succ, positiveBorder_col_last] at he
      omega
    | cast j =>
      apply hD i j
      simpa only [positiveBorder_row_succ, positiveBorder_col_castSucc] using he

/-- The separated singleton core inherits zero-freeness only from its actual core. -/
theorem singletonCore_zeroFree (Q : BetaDiagram (n + 1)) (hQ : Q.ZeroFree)
    (s g : ℤ) (hs : 0 < s) (hg : 0 < g) :
    (Q.singletonCore s g hs hg).ZeroFree := by
  intro i j he
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp only [singletonCore, Fin.cons_zero] at he
      omega
    | succ j =>
      have hc := Q.col_strictAnti.antitone (Fin.zero_le j)
      have hd := Q.row_nonempty 0
      simp only [singletonCore, Fin.cons_zero, Fin.cons_succ] at he
      omega
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have hn := Q.singletonCore_lower_negative s g hs hg i
      simp only [he, sub_self] at hn
      omega
    | succ j =>
      apply hQ i j
      simpa only [singletonCore, Fin.cons_succ] using he

/-- The source zero-free hypothesis propagates through the actual singleton construction. -/
theorem singletonContext_zeroFree (Q : BetaDiagram (n + 1)) (hQ : Q.ZeroFree)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).ZeroFree :=
  ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).shifted_zeroFree
    ((Q.singletonCore s g hs hg).positiveBorder_zeroFree
      (Q.singletonCore_zeroFree hQ s g hs hg) u v hu hv) v

/-- The actual maximal cofactor factors as the singleton generator times the core. -/
theorem singletonCore_schur (Q : BetaDiagram (n + 1))
    (s g : ℤ) (hs : 0 < s) (hg : 0 < g) :
    (Q.singletonCore s g hs hg).schur = complete s * Q.schur := by
  classical
  unfold schur
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hm : (Q.singletonCore s g hs hg).matrix.submatrix Fin.succ Fin.succ =
      Q.matrix := by
    apply Matrix.ext
    intro i j
    simp [matrix, singletonCore]
  simp only [Fin.succAbove_zero] at ⊢
  rw [hm]
  have hz : ∀ i : Fin (n + 1), (Q.singletonCore s g hs hg).matrix i.succ 0 = 0 := by
    intro i
    exact complete_of_neg (Q.singletonCore_lower_negative s g hs hg i)
  simp only [Fin.val_zero, pow_zero, one_mul, hz, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 1
  simp [matrix, singletonCore]

/-- Removing the first parent row and first column gives precisely the first border. -/
theorem singletonContext_first_minor (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).matrix.submatrix Fin.succ Fin.succ =
      (Q.positiveBorder (s + g) v (by omega) hv).matrix := by
  apply Matrix.ext
  intro i j
  change complete ((Q.singletonContext s u v g hs hu hv hg).row i.succ -
    (Q.singletonContext s u v g hs hu hv hg).col j.succ) =
    complete ((Q.positiveBorder (s + g) v (by omega) hv).row i -
      (Q.positiveBorder (s + g) v (by omega) hv).col j)
  apply congrArg complete
  cases i using Fin.cases <;> cases j using Fin.lastCases <;>
    simp only [singletonContext_row_one, singletonContext_row_core,
      ← Fin.castSucc_succ, singletonContext_col_core, singletonContext_col_last, Fin.succ_last,
      positiveBorder_row_zero, positiveBorder_row_succ,
      positiveBorder_col_castSucc, positiveBorder_col_last] <;> ring

/-- Removing the second parent row and first column gives precisely the second border. -/
theorem singletonContext_second_minor (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).matrix.submatrix
      ((0 : Fin (n + 2)).succ).succAbove Fin.succ =
      (Q.positiveBorder (s + g + u) v (by omega) hv).matrix := by
  apply Matrix.ext
  intro i j
  change complete ((Q.singletonContext s u v g hs hu hv hg).row
      (((0 : Fin (n + 2)).succ).succAbove i) -
    (Q.singletonContext s u v g hs hu hv hg).col j.succ) =
    complete ((Q.positiveBorder (s + g + u) v (by omega) hv).row i -
      (Q.positiveBorder (s + g + u) v (by omega) hv).col j)
  apply congrArg complete
  cases i using Fin.cases <;> cases j using Fin.lastCases <;>
    simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.zero_succAbove,
      singletonContext_row_zero, singletonContext_row_core,
      ← Fin.castSucc_succ, singletonContext_col_core, singletonContext_col_last, Fin.succ_last,
      positiveBorder_row_zero, positiveBorder_row_succ,
      positiveBorder_col_castSucc, positiveBorder_col_last] <;> ring

/-- The full determinant identity, not a coefficient certificate (`eq:singleton-polynomial`). -/
theorem singletonContext_schur (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).schur =
      complete (s + u) * (Q.positiveBorder (s + g) v (by omega) hv).schur -
      complete s * (Q.positiveBorder (s + g + u) v (by omega) hv).schur := by
  classical
  unfold schur
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero]
  rw [singletonContext_first_minor, singletonContext_second_minor]
  have h0 : (Q.singletonContext s u v g hs hu hv hg).matrix 0 0 =
      complete (s + u) := by
    simp only [matrix, Matrix.of_apply, singletonContext_row_zero,
      singletonContext_col_zero]
    congr 1
    ring
  have h1 : (Q.singletonContext s u v g hs hu hv hg).matrix
      (0 : Fin (n + 2)).succ 0 = complete s := by
    simp only [matrix, Matrix.of_apply, singletonContext_row_one,
      singletonContext_col_zero]
    congr 1
    ring
  have hz : ∀ i : Fin (n + 1),
      (Q.singletonContext s u v g hs hu hv hg).matrix i.succ.succ 0 = 0 := by
    intro i
    have h := Q.row_strictAnti.antitone (Fin.zero_le i)
    apply complete_of_neg
    simp only [singletonContext_row_core, singletonContext_col_zero]
    omega
  simp only [h0, h1, hz, Fin.val_zero, Fin.val_succ, pow_zero, pow_one,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- The corner coefficient is the actual product, with the common sign retained. -/
theorem singletonContext_corner_coefficient (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    MvPolynomial.pderiv
      (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).borderLargestGenerator)
      (Q.singletonContext s u v g hs hu hv hg).schur =
      (-1) ^ (n + 2) * (complete s * Q.schur) := by
  simp only [singletonContext, shifted_schur]
  rw [positiveBorder_corner_coefficient, singletonCore_schur]

/-- A genuine singleton-first cut reconstructs the entire parent's literal beta
lists, not merely a factorization or a proposed context certificate. -/
theorem singleton_parent_of_first_cut (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner)
    (hcut : D.row (0 : Fin (n + 1)).succ.succ < D.col 0) :
    let Q := (D.cornerDiagram hP).tail
    ∃ (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.singletonContext s u v g hs hu hv hg) := by
  dsimp only
  let Q := (D.cornerDiagram hP).tail
  let s := D.row (0 : Fin (n + 2)).succ - D.col 0
  let g := D.col 0 - D.row (0 : Fin (n + 1)).succ.succ
  have hs : 0 < s := by
    have hh := hP (0 : Fin (n + 2))
    change D.col 0 < D.row (0 : Fin (n + 2)).succ at hh
    exact sub_pos.mpr hh
  have hg : 0 < g := sub_pos.mpr hcut
  refine ⟨s, D.topMargin, D.bottomMargin, g, hs, D.topMargin_pos,
    D.bottomMargin_pos, hg, -D.bottomMargin, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [singletonContext_row_zero]
      simp only [Q, tail, cornerDiagram, s, g, topMargin]
      ring
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        rw [singletonContext_row_one]
        simp only [Q, tail, cornerDiagram, s, g]
        ring
      | succ i =>
        rw [singletonContext_row_core]
        simp only [Q, tail, cornerDiagram]
        ring
  · intro j
    cases j using Fin.lastCases with
    | last =>
      rw [singletonContext_col_last]
      simp only [Q, tail, cornerDiagram, bottomMargin, Fin.succ_last]
      ring
    | cast j =>
      cases j using Fin.cases with
      | zero =>
        rw [Fin.castSucc_zero, singletonContext_col_zero]
        simp only [Q, tail, cornerDiagram, g]
        ring
      | succ j =>
        rw [singletonContext_col_core]
        simp only [Q, tail, cornerDiagram]
        ring

/-- Rotating the core interchanges the two actual positive border margins. -/
theorem positiveBorder_rotate_schur (Q : BetaDiagram (n + 1))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) :
    (Q.rotate.positiveBorder w v hw hv).schur =
      (Q.positiveBorder v w hv hw).schur := by
  let A := Q.rotate.positiveBorder w v hw hv
  let B := Q.positiveBorder v w hv hw
  have hm : A.matrix = B.rotate.matrix := by
    apply Matrix.ext
    intro i j
    change complete (A.row i - A.col j) =
      complete (B.rotate.row i - B.rotate.col j)
    apply congrArg complete
    cases i using Fin.cases <;> cases j using Fin.lastCases <;>
      simp only [A, B, rotate, positiveBorder, Fin.cons_zero, Fin.cons_succ,
        Fin.snoc_castSucc, Fin.snoc_last, Fin.rev_zero, Fin.rev_last,
        Fin.rev_succ, Fin.rev_castSucc] <;> ring
  change A.matrix.det = B.schur
  rw [hm]
  exact B.rotate_schur

/-- Every first-order last-column complementary determinant has actual nonempty
beta rows when the maximal complementary diagonal is strictly positive. -/
def lastColumnDiagram (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner)
    (r : Fin (n + 1)) : BetaDiagram n where
  row i := D.row (r.succAbove i)
  col i := D.col i.castSucc
  row_strictAnti := D.row_strictAnti.comp_strictMono (Fin.strictMono_succAbove r)
  col_strictAnti := D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc
  row_nonempty := by
    intro i
    have hi : r.succAbove i ≤ i.succ := by
      unfold Fin.succAbove
      split_ifs
      · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        omega
      · exact le_rfl
    exact lt_of_lt_of_le (hP i) (D.row_strictAnti.antitone hi)

/-- This is the genuine complementary matrix, not a polynomial substitute. -/
theorem lastColumnDiagram_matrix (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner)
    (r : Fin (n + 1)) :
    (D.lastColumnDiagram hP r).matrix =
      D.matrix.submatrix r.succAbove (Fin.last n).succAbove := by
  apply Matrix.ext
  intro i j
  simp only [matrix, Matrix.of_apply, Matrix.submatrix_apply, lastColumnDiagram,
    Fin.succAbove_last]

/-- The constructed diagram's polynomial equals the whole unsigned cofactor. -/
theorem lastColumnDiagram_schur (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner)
    (r : Fin (n + 1)) :
    (D.lastColumnDiagram hP r).schur =
      (D.matrix.submatrix r.succAbove (Fin.last n).succAbove).det := by
  unfold schur
  rw [lastColumnDiagram_matrix]

/-- Nonempty actual core rows produce the whole parent's positive corner diagonal. -/
theorem singletonContext_positiveCorner (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).PositiveCorner := by
  intro i
  change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col i.castSucc + v <
    ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row i.succ + v
  have hh := (Q.singletonCore s g hs hg).positiveBorder_positiveCorner u v hu hv i
  omega

/-- The separator's complementary determinant is connected from its actual
subdiagonal labels, including every core overlap rather than a density premise. -/
theorem singleton_separator_diagram_connected (Q : BetaDiagram (n + 1))
    (hQ : Q.Connected) (hZ : Q.ZeroFree)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((Q.singletonContext s u v g hs hu hv hg).lastColumnDiagram
      (Q.singletonContext_positiveCorner s u v g hs hu hv hg)
      (0 : Fin (n + 1)).succ.succ).Connected := by
  let P := Q.singletonContext s u v g hs hu hv hg
  let r : Fin (n + 3) := (0 : Fin (n + 1)).succ.succ
  refine ⟨by omega, ?_⟩
  intro i hi
  change P.col i.castSucc ≤ P.row (r.succAbove ⟨i.val + 1, hi⟩)
  cases i using Fin.cases with
  | zero =>
    have he : r.succAbove (⟨1, hi⟩ : Fin (n + 2)) = (0 : Fin (n + 2)).succ := by
      rw [Fin.succAbove_of_castSucc_lt _ _
        (show (⟨1, hi⟩ : Fin (n + 2)).castSucc < r by
          simp only [r, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
          omega)]
      apply Fin.ext
      rfl
    change P.col (0 : Fin (n + 2)).castSucc ≤
      P.row (r.succAbove (⟨1, hi⟩ : Fin (n + 2)))
    rw [he]
    simp only [P, Fin.castSucc_zero, singletonContext_col_zero, singletonContext_row_one]
    omega
  | succ j =>
    let l : Fin (n + 1) := ⟨j.val + 1, by
      simp only [Fin.val_succ] at hi
      omega⟩
    have he : r.succAbove (⟨j.succ.val + 1, hi⟩ : Fin (n + 2)) = l.succ.succ := by
      rw [Fin.succAbove_of_le_castSucc _ _
        (show r ≤ (⟨j.succ.val + 1, hi⟩ : Fin (n + 2)).castSucc by
          simp only [r, Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
          omega)]
      apply Fin.ext
      simp only [l, Fin.val_succ]
    rw [he]
    simp only [P, singletonContext_col_core, singletonContext_row_core]
    have hweak : Q.col j ≤ Q.row l := hQ.2 j (by
      simp only [Fin.val_succ] at hi
      omega)
    have hneq := hZ l j
    omega

/-- The upper separator cofactor is literally the singleton times the actual
bottom endpoint extension of the core (`eq:margin-separator`). -/
theorem singleton_top_separator_minor (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.singletonContext s u v g hs hu hv hg
    (P.matrix.submatrix Fin.succ (Fin.last (n + 1)).castSucc.succAbove).det =
      complete s * (Q.extendBottom v hv).schur := by
  classical
  dsimp only
  let P := Q.singletonContext s u v g hs hu hv hg
  let p : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let M := P.matrix.submatrix Fin.succ p.succAbove
  have hp0 : p.succAbove (0 : Fin (n + 2)) = 0 := by
    apply Fin.succAbove_ne_zero_zero
    intro h
    have hh := congrArg Fin.val h
    simp only [p, Fin.val_castSucc, Fin.val_last, Fin.val_zero] at hh
    omega
  have hblock : M.submatrix Fin.succ Fin.succ = (Q.extendBottom v hv).matrix := by
    apply Matrix.ext
    intro i j
    change complete (P.row i.succ.succ - P.col (p.succAbove j.succ)) =
      complete ((Q.extendBottom v hv).row i - (Q.extendBottom v hv).col j)
    apply congrArg complete
    cases j using Fin.lastCases with
    | last =>
      simp only [p, Fin.succ_last, Fin.succAbove_castSucc_self,
        P, singletonContext_row_core, singletonContext_col_last, extendBottom, ite_true]
      ring
    | cast j =>
      have hj : p.succAbove j.castSucc.succ = j.castSucc.succ.castSucc := by
        apply Fin.succAbove_of_castSucc_lt
        simp only [p, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
        omega
      rw [hj]
      simp only [P, singletonContext_row_core, singletonContext_col_core,
        extendBottom, Fin.castSucc_ne_last, ite_false]
      ring
  have h0 : M 0 0 = complete s := by
    change complete (P.row (0 : Fin (n + 2)).succ - P.col (p.succAbove 0)) = _
    rw [hp0]
    simp only [P, singletonContext_row_one, singletonContext_col_zero]
    congr 1
    ring
  have hz : ∀ i : Fin (n + 1), M i.succ 0 = 0 := by
    intro i
    change complete (P.row i.succ.succ - P.col (p.succAbove 0)) = 0
    rw [hp0]
    apply complete_of_neg
    simp only [P, singletonContext_row_core, singletonContext_col_zero]
    have hh := Q.row_strictAnti.antitone (Fin.zero_le i)
    omega
  change M.det = complete s * (Q.extendBottom v hv).matrix.det
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero, hblock, h0, hz, Fin.val_zero, pow_zero,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

@[simp] theorem borderLargestGenerator_int (D : BetaDiagram (n + 1)) :
    (D.borderLargestGenerator.val : ℤ) = D.largestLabel := by
  change ((D.largestLabel.toNat : ℕ) : ℤ) = D.largestLabel
  have h := D.largestLabel_pos
  omega

@[simp] theorem borderSecondGenerator_int (D : BetaDiagram (n + 2)) :
    (D.borderSecondGenerator.val : ℤ) = D.secondLabel := by
  change ((D.secondLabel.toNat : ℕ) : ℤ) = D.secondLabel
  have h := D.secondLabel_pos
  omega

/-- The penultimate-column separator is a private generator when it lies above
the third-row last-column label, despite the two larger last-column labels. -/
theorem separator_top_private (D : BetaDiagram (n + 3))
    (hgap : D.topMargin < D.bottomMargin)
    (hside : D.row (0 : Fin (n + 1)).succ.succ - D.col (Fin.last (n + 2)) <
      D.row 0 - D.col (Fin.last (n + 1)).castSucc) :
    let t := D.row 0 - D.col (Fin.last (n + 1)).castSucc
    ∃ ht : 0 < t,
      MvPolynomial.pderiv (⟨t.toNat, by omega⟩ : ℕ+) D.schur =
        D.cofactor 0 (Fin.last (n + 1)).castSucc := by
  dsimp only
  let p : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let r1 : Fin (n + 3) := (0 : Fin (n + 2)).succ
  let r2 : Fin (n + 3) := (0 : Fin (n + 1)).succ.succ
  let t := D.row 0 - D.col p
  have ht : 0 < t := by
    have hd := D.row_nonempty 0
    have hc := D.col_strictAnti.antitone (Fin.zero_le p)
    dsimp [t]
    omega
  refine ⟨ht, ?_⟩
  let k : ℕ+ := ⟨t.toNat, by omega⟩
  have hk : (k.val : ℤ) = t := by dsimp [k]; omega
  have hprivate : ∀ i j, i ≠ 0 ∨ j ≠ p → k ∉ (D.matrix i j).vars := by
    intro i j hsite
    change k ∉ (complete (D.row i - D.col j)).vars
    rw [mem_vars_complete_iff]
    intro he
    change (k.val : ℤ) = D.row i - D.col j at he
    by_cases hi0 : i = 0
    · subst i
      by_cases hjlast : j = Fin.last (n + 2)
      · subst j
        have hc := D.col_strictAnti (show p < Fin.last (n + 2) by
          exact Fin.castSucc_lt_last _)
        dsimp [t] at hk
        omega
      · have hjp : j ≠ p := by simpa using hsite
        have hjle : j ≤ p := by
          have hh := Fin.lt_last_iff_ne_last.mpr hjlast
          simp only [p, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
          omega
        have hjlt : j < p := lt_of_le_of_ne hjle hjp
        have hc := D.col_strictAnti hjlt
        dsimp [t] at hk
        omega
    · by_cases hi1 : i = r1
      · subst i
        by_cases hjlast : j = Fin.last (n + 2)
        · subst j
          change D.row 0 - D.row r1 <
            D.col p - D.col (Fin.last (n + 2)) at hgap
          dsimp [t] at hk
          omega
        · have hjle : j ≤ p := by
            have hh := Fin.lt_last_iff_ne_last.mpr hjlast
            simp only [p, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
            omega
          have hc := D.col_strictAnti.antitone hjle
          have hr := D.row_strictAnti (show (0 : Fin (n + 3)) < r1 by
            simp only [r1, Fin.lt_def, Fin.val_zero, Fin.val_succ]; omega)
          dsimp [t] at hk
          omega
      · have hir : r2 ≤ i := by
          have h0 := Fin.pos_iff_ne_zero.mpr hi0
          have h1 : i.val ≠ 1 := by
            intro h
            apply hi1
            apply Fin.ext
            simpa only [r1, Fin.val_succ, Fin.val_zero] using h
          simp only [r2, Fin.le_def, Fin.val_succ, Fin.val_zero]
          omega
        have hr := D.row_strictAnti.antitone hir
        have hc := D.col_strictAnti.antitone (Fin.le_last j)
        change D.row r2 - D.col (Fin.last (n + 2)) < D.row 0 - D.col p at hside
        dsimp [t] at hk
        omega
  have hentry : D.matrix 0 p = MvPolynomial.X k := by
    change complete t = MvPolynomial.X k
    exact complete_of_pos ht
  change MvPolynomial.pderiv k D.matrix.det = D.cofactor 0 p
  simpa only [cofactor] using pderiv_det_private D.matrix k 0 p hentry hprivate

/-- The third-row last-column separator is private when it exceeds every
nonlast-column entry; the larger first two last-column entries remain harmless. -/
theorem separator_bottom_private (D : BetaDiagram (n + 3))
    (hside : D.row 0 - D.col (Fin.last (n + 1)).castSucc <
      D.row (0 : Fin (n + 1)).succ.succ - D.col (Fin.last (n + 2))) :
    let r := (0 : Fin (n + 1)).succ.succ
    let t := D.row r - D.col (Fin.last (n + 2))
    ∃ ht : 0 < t,
      MvPolynomial.pderiv (⟨t.toNat, by omega⟩ : ℕ+) D.schur =
        D.cofactor r (Fin.last (n + 2)) := by
  dsimp only
  let r : Fin (n + 3) := (0 : Fin (n + 1)).succ.succ
  let p : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let t := D.row r - D.col (Fin.last (n + 2))
  have ht : 0 < t := by
    have hd := D.row_nonempty r
    have hc := D.col_strictAnti.antitone (Fin.le_last r)
    dsimp [t]
    omega
  refine ⟨ht, ?_⟩
  let k : ℕ+ := ⟨t.toNat, by omega⟩
  have hk : (k.val : ℤ) = t := by dsimp [k]; omega
  have hprivate : ∀ i j, i ≠ r ∨ j ≠ Fin.last (n + 2) →
      k ∉ (D.matrix i j).vars := by
    intro i j hsite
    change k ∉ (complete (D.row i - D.col j)).vars
    rw [mem_vars_complete_iff]
    intro he
    change (k.val : ℤ) = D.row i - D.col j at he
    by_cases hjlast : j = Fin.last (n + 2)
    · subst j
      have hrows : D.row i = D.row r := by dsimp [t] at hk; omega
      have hi := D.row_strictAnti.injective hrows
      exact (by simpa using hsite : i ≠ r) hi
    · have hjle : j ≤ p := by
        have hh := Fin.lt_last_iff_ne_last.mpr hjlast
        simp only [p, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
        omega
      have hc := D.col_strictAnti.antitone hjle
      have hr := D.row_strictAnti.antitone (Fin.zero_le i)
      change D.row 0 - D.col p < D.row r - D.col (Fin.last (n + 2)) at hside
      dsimp [t] at hk
      omega
  have hentry : D.matrix r (Fin.last (n + 2)) = MvPolynomial.X k := by
    change complete t = MvPolynomial.X k
    exact complete_of_pos ht
  change MvPolynomial.pderiv k D.matrix.det = D.cofactor r (Fin.last (n + 2))
  simpa only [cofactor] using
    pderiv_det_private D.matrix k r (Fin.last (n + 2)) hentry hprivate

/-- Extraction at the larger top separator yields the full product coefficient,
with its actual cofactor sign, rather than an irreducibility assumption. -/
theorem singleton_top_separator_coefficient (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hgap : u < v)
    (hside : (Q.singletonContext s u v g hs hu hv hg).row
        (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2)) <
      (Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc) :
    let P := Q.singletonContext s u v g hs hu hv hg
    let t := P.row 0 - P.col (Fin.last (n + 1)).castSucc
    ∃ ht : 0 < t,
      MvPolynomial.pderiv (⟨t.toNat, by omega⟩ : ℕ+) P.schur =
        (-1 : CompleteRing) ^ (n + 1) * (complete s * (Q.extendBottom v hv).schur) := by
  dsimp only
  let P := Q.singletonContext s u v g hs hu hv hg
  have hmargin : P.topMargin < P.bottomMargin := by
    change (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).shifted v).topMargin <
      (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).shifted v).bottomMargin
    have ht : P.topMargin = u := by
      change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row 0 + v -
        (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).row
          (0 : Fin (n + 2)).succ + v) = u
      rw [positiveBorder_row_zero, positiveBorder_row_succ]
      ring
    have hb : P.bottomMargin = v := by
      change ((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col
          (Fin.last (n + 1)).castSucc + v -
        (((Q.singletonCore s g hs hg).positiveBorder u v hu hv).col
          (Fin.last (n + 2)) + v) = v
      rw [positiveBorder_col_castSucc, positiveBorder_col_last]
      ring
    change P.topMargin < P.bottomMargin
    rw [ht, hb]
    exact hgap
  obtain ⟨ht, hc⟩ := P.separator_top_private hmargin hside
  refine ⟨ht, ?_⟩
  rw [hc]
  unfold cofactor
  simp only [Fin.val_zero, Fin.val_castSucc, Fin.val_last, zero_add]
  simp only [Fin.succAbove_zero]
  change (-1 : CompleteRing) ^ (n + 1) *
      ((Q.singletonContext s u v g hs hu hv hg).matrix.submatrix Fin.succ
        (Fin.last (n + 1)).castSucc.succAbove).det =
    (-1 : CompleteRing) ^ (n + 1) * (complete s * (Q.extendBottom v hv).schur)
  rw [singleton_top_separator_minor]

/-- Extraction at the other strict separator yields the actual connected
complementary determinant used in `eq:margin-separator`. -/
theorem singleton_bottom_separator_coefficient (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hside : (Q.singletonContext s u v g hs hu hv hg).row 0 -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 1)).castSucc <
      (Q.singletonContext s u v g hs hu hv hg).row
        (0 : Fin (n + 1)).succ.succ -
        (Q.singletonContext s u v g hs hu hv hg).col (Fin.last (n + 2))) :
    let P := Q.singletonContext s u v g hs hu hv hg
    let r := (0 : Fin (n + 1)).succ.succ
    let t := P.row r - P.col (Fin.last (n + 2))
    ∃ ht : 0 < t,
      MvPolynomial.pderiv (⟨t.toNat, by omega⟩ : ℕ+) P.schur =
        (-1 : CompleteRing) ^ (n + 2) *
          (P.lastColumnDiagram (Q.singletonContext_positiveCorner s u v g hs hu hv hg) r).schur := by
  dsimp only
  let P := Q.singletonContext s u v g hs hu hv hg
  obtain ⟨ht, hc⟩ := P.separator_bottom_private hside
  refine ⟨ht, ?_⟩
  rw [hc]
  unfold cofactor
  simp only [Fin.val_succ, Fin.val_zero, Fin.val_last]
  rw [lastColumnDiagram_schur]
  have hsign : (-1 : CompleteRing) ^ (0 + 1 + 1 + (n + 2)) = (-1) ^ (n + 2) := by
    simp only [show 0 + 1 + 1 + (n + 2) = (n + 2) + 2 by omega, pow_add]
    norm_num
  rw [hsign]

/-- The first-column identity after removing the actual private corner variable. -/
theorem singletonContext_erased (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let A := Q.positiveBorder (s + g) v (by omega) hv
    let B := Q.positiveBorder (s + g + u) v (by omega) hv
    eraseGenerator B.borderLargestGenerator
      (Q.singletonContext s u v g hs hu hv hg).schur =
      complete (s + u) * A.schur -
        complete s * eraseGenerator B.borderLargestGenerator B.schur := by
  dsimp only
  let B := Q.positiveBorder (s + g + u) v (by omega) hv
  have hN : (B.borderLargestGenerator.val : ℤ) = Q.largestLabel + s + g + u + v := by
    rw [borderLargestGenerator_int]
    simp only [B, positiveBorder_largestLabel]
    ring
  have hS := Q.largestLabel_pos
  have hs0 : B.borderLargestGenerator ∉ (complete s).vars := by
    rw [mem_vars_complete_iff]
    omega
  have hsu0 : B.borderLargestGenerator ∉ (complete (s + u)).vars := by
    rw [mem_vars_complete_iff]
    omega
  have hA : B.borderLargestGenerator ∉
      (Q.positiveBorder (s + g) v (by omega) hv).schur.vars := by
    intro h
    have hh := (Q.positiveBorder (s + g) v (by omega) hv).vars_le_largestLabel _ h
    rw [positiveBorder_largestLabel] at hh
    omega
  rw [singletonContext_schur, map_sub, map_mul, map_mul,
    eraseGenerator_eq_self _ _ hsu0, eraseGenerator_eq_self _ _ hs0,
    eraseGenerator_eq_self _ _ hA]

/-- The moving marker as a true positive complete-generator index. -/
def singletonMarker (Q : BetaDiagram (n + 1)) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) : ℕ+ :=
  ⟨(Q.largestLabel + s + g + u + v - min u v).toNat, by
    have hS := Q.largestLabel_pos
    have hm := min_le_left u v
    omega⟩

/-- The whole strict top marker in `eq:singleton-marker`. -/
theorem singletonContext_top_marker (Q : BetaDiagram (n + 2))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (h : u < v) :
    let B := Q.positiveBorder (s + g + u) v (by omega) hv
    MvPolynomial.pderiv (Q.singletonMarker s u v g hs hu hv hg)
      (eraseGenerator B.borderLargestGenerator
        (Q.singletonContext s u v g hs hu hv hg).schur) =
      (-1) ^ (n + 2) * (complete (s + u) * Q.schur) := by
  dsimp only
  let k := Q.singletonMarker s u v g hs hu hv hg
  let A := Q.positiveBorder (s + g) v (by omega) hv
  let B := Q.positiveBorder (s + g + u) v (by omega) hv
  have hk : (k.val : ℤ) = Q.largestLabel + s + g + v := by
    have hS := Q.largestLabel_pos
    dsimp [k, singletonMarker]
    rw [min_eq_left h.le]
    omega
  have hka : k = A.borderLargestGenerator := by
    apply Subtype.ext
    have he : (k.val : ℤ) = (A.borderLargestGenerator.val : ℤ) := by
      rw [borderLargestGenerator_int]
      simp only [A, positiveBorder_largestLabel]
      omega
    exact Int.ofNat.inj he
  have hs0 : k ∉ (complete s).vars := by
    rw [mem_vars_complete_iff]
    have := Q.largestLabel_pos
    omega
  have hsu0 : k ∉ (complete (s + u)).vars := by
    rw [mem_vars_complete_iff]
    have := Q.largestLabel_pos
    omega
  have hB : k ∉ (eraseGenerator B.borderLargestGenerator B.schur).vars := by
    intro hvk
    have hb := B.vars_le_secondLabel k hvk
    simp only [B, positiveBorder_secondLabel] at hb
    have ha : u < s + g + u := by omega
    have hm : u < min (s + g + u) v := lt_min ha h
    omega
  rw [singletonContext_erased, map_sub, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hs0,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hsu0,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hB]
  have hA : MvPolynomial.pderiv k A.schur = (-1) ^ (n + 2) * Q.schur := by
    rw [hka]
    exact Q.positiveBorder_corner_coefficient (s + g) v (by omega) hv
  rw [hA]
  ring

/-- The whole strict bottom marker in `eq:singleton-marker`. -/
theorem singletonContext_bottom_marker (Q : BetaDiagram (n + 2))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (h : v < u) :
    let B := Q.positiveBorder (s + g + u) v (by omega) hv
    MvPolynomial.pderiv (Q.singletonMarker s u v g hs hu hv hg)
      (eraseGenerator B.borderLargestGenerator
        (Q.singletonContext s u v g hs hu hv hg).schur) =
      (-1) ^ (n + 2) * (complete s * (Q.extendBottom v hv).schur) := by
  dsimp only
  let k := Q.singletonMarker s u v g hs hu hv hg
  let A := Q.positiveBorder (s + g) v (by omega) hv
  let B := Q.positiveBorder (s + g + u) v (by omega) hv
  have hk : (k.val : ℤ) = Q.largestLabel + s + g + u := by
    have hS := Q.largestLabel_pos
    dsimp [k, singletonMarker]
    rw [min_eq_right h.le]
    omega
  have hbv : v < s + g + u := by omega
  have hkb : k = B.borderSecondGenerator := by
    apply Subtype.ext
    have he : (k.val : ℤ) = (B.borderSecondGenerator.val : ℤ) := by
      rw [borderSecondGenerator_int]
      simp only [B, positiveBorder_secondLabel, min_eq_right hbv.le]
      omega
    exact Int.ofNat.inj he
  have hs0 : k ∉ (complete s).vars := by
    rw [mem_vars_complete_iff]
    have := Q.largestLabel_pos
    omega
  have hsu0 : k ∉ (complete (s + u)).vars := by
    rw [mem_vars_complete_iff]
    have := Q.largestLabel_pos
    omega
  have hA : k ∉ A.schur.vars := by
    intro hvk
    have ha := A.vars_le_largestLabel k hvk
    simp only [A, positiveBorder_largestLabel] at ha
    omega
  rw [singletonContext_erased, map_sub, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hs0,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hsu0,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hA]
  have hB : MvPolynomial.pderiv k (eraseGenerator B.borderLargestGenerator B.schur) =
      (-1) ^ (n + 3) * (Q.extendBottom v hv).schur := by
    rw [hkb]
    exact Q.positiveBorder_bottom_coefficient (s + g + u) v (by omega) hv hbv
  rw [hB]
  simp only [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  ring

/-- The tied marker retains both actual contributions with their common sign. -/
theorem singletonContext_tied_marker (Q : BetaDiagram (n + 2))
    (s q g : ℤ) (hs : 0 < s) (hq : 0 < q) (hg : 0 < g) :
    let B := Q.positiveBorder (s + g + q) q (by omega) hq
    MvPolynomial.pderiv (Q.singletonMarker s q q g hs hq hq hg)
      (eraseGenerator B.borderLargestGenerator
        (Q.singletonContext s q q g hs hq hq hg).schur) =
      (-1) ^ (n + 2) *
        (complete (s + q) * Q.schur + complete s * (Q.extendBottom q hq).schur) := by
  dsimp only
  let k := Q.singletonMarker s q q g hs hq hq hg
  let A := Q.positiveBorder (s + g) q (by omega) hq
  let B := Q.positiveBorder (s + g + q) q (by omega) hq
  have hk : (k.val : ℤ) = Q.largestLabel + s + g + q := by
    have hS := Q.largestLabel_pos
    dsimp [k, singletonMarker]
    rw [min_self]
    omega
  have hka : k = A.borderLargestGenerator := by
    apply Subtype.ext
    have he : (k.val : ℤ) = (A.borderLargestGenerator.val : ℤ) := by
      rw [borderLargestGenerator_int]
      simp only [A, positiveBorder_largestLabel]
      omega
    exact Int.ofNat.inj he
  have hkb : k = B.borderSecondGenerator := by
    apply Subtype.ext
    have he : (k.val : ℤ) = (B.borderSecondGenerator.val : ℤ) := by
      rw [borderSecondGenerator_int]
      simp only [B, positiveBorder_secondLabel,
        min_eq_right (show q ≤ s + g + q by omega)]
      omega
    exact Int.ofNat.inj he
  have hs0 : k ∉ (complete s).vars := by
    rw [mem_vars_complete_iff]
    have := Q.largestLabel_pos
    omega
  have hsq0 : k ∉ (complete (s + q)).vars := by
    rw [mem_vars_complete_iff]
    have := Q.largestLabel_pos
    omega
  rw [singletonContext_erased, map_sub, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hs0,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hsq0]
  have hA : MvPolynomial.pderiv k A.schur = (-1) ^ (n + 2) * Q.schur := by
    rw [hka]
    exact Q.positiveBorder_corner_coefficient (s + g) q (by omega) hq
  have hB : MvPolynomial.pderiv k (eraseGenerator B.borderLargestGenerator B.schur) =
      (-1) ^ (n + 3) * (Q.extendBottom q hq).schur := by
    rw [hkb]
    exact Q.positiveBorder_bottom_coefficient (s + g + q) q (by omega) hq (by omega)
  rw [hA, hB]
  simp only [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  ring

end SkewJacobiNegative.BetaDiagram
