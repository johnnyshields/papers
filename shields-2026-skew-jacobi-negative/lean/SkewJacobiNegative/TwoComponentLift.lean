/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SingletonLift

/-!
# Actual two-component contexts

The ordered beta lists of `eq:two-component-lists` and the nonzero actual
complementary determinant in `eq:two-component-tie-table` of
`shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative.BetaDiagram
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p r : ℕ}

/-- Translation placing the last column of the first component above the second span. -/
def componentOffset (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) : ℤ := R.row 0 + g - Q.col (Fin.last p)

/-- The two actual component lists, with their genuine negative rectangular cut. -/
def separatedComponents (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) : BetaDiagram ((p + 1) + (r + 1)) where
  row := Fin.append (fun i => Q.row i + Q.componentOffset R g) R.row
  col := Fin.append (fun i => Q.col i + Q.componentOffset R g) R.col
  row_strictAnti := by
    intro i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        have hh := Q.row_strictAnti (show i < j by
          change i.val < j.val
          change i.val < j.val at hij
          exact hij)
        omega
      | right j =>
        have hQ := Q.row_strictAnti.antitone (Fin.le_last i)
        have hQ0 := Q.row_nonempty (Fin.last p)
        have hR := R.row_strictAnti.antitone (Fin.zero_le j)
        simp only [Fin.append_left, Fin.append_right, componentOffset]
        omega
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have h : ¬ i.natAdd (p + 1) < j.castAdd (r + 1) := by
          simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
          omega
        exact (h hij).elim
      | right j =>
        simpa only [Fin.append_right] using R.row_strictAnti (by simpa using hij)
  col_strictAnti := by
    intro i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        have hh := Q.col_strictAnti (show i < j by
          change i.val < j.val
          change i.val < j.val at hij
          exact hij)
        omega
      | right j =>
        have hQ := Q.col_strictAnti.antitone (Fin.le_last i)
        have hR := R.col_strictAnti.antitone (Fin.zero_le j)
        have hR0 := R.row_nonempty 0
        simp only [Fin.append_left, Fin.append_right, componentOffset]
        omega
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have h : ¬ i.natAdd (p + 1) < j.castAdd (r + 1) := by
          simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
          omega
        exact (h hij).elim
      | right j =>
        simpa only [Fin.append_right] using R.col_strictAnti (by simpa using hij)
  row_nonempty := by
    intro i
    cases i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      have hh := Q.row_nonempty i
      omega
    | right i => simpa only [Fin.append_right] using R.row_nonempty i

/-- Every cell in the lower-left block is strictly negative. -/
theorem separatedComponents_lower_negative
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) (i : Fin (r + 1)) (j : Fin (p + 1)) :
    (Q.separatedComponents R g hg).row (i.natAdd (p + 1)) <
      (Q.separatedComponents R g hg).col (j.castAdd (r + 1)) := by
  have hR := R.row_strictAnti.antitone (Fin.zero_le i)
  have hQ := Q.col_strictAnti.antitone (Fin.le_last j)
  simp only [separatedComponents, Fin.append_left, Fin.append_right, componentOffset]
  omega

/-- The whole determinant is the true product, including equal component functions. -/
theorem separatedComponents_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) :
    (Q.separatedComponents R g hg).schur = Q.schur * R.schur := by
  let D := Q.separatedComponents R g hg
  have hcut : D.row ⟨p + 1, by omega⟩ < D.col ⟨p + 1 - 1, by omega⟩ := by
    convert Q.separatedComponents_lower_negative R g hg 0 (Fin.last p) using 1 <;>
      congr 1 <;> apply Fin.ext <;> simp
  rw [D.schur_factor_at_cut (by omega) (by omega) hcut]
  have hleft : D.betaPrefix.matrix = Q.matrix := by
    apply Matrix.ext
    intro i j
    simp [D, matrix, betaPrefix, separatedComponents]
  have hright : D.suffix.matrix = R.matrix := by
    apply Matrix.ext
    intro i j
    simp [D, matrix, suffix, separatedComponents]
  change D.betaPrefix.matrix.det * D.suffix.matrix.det = Q.matrix.det * R.matrix.det
  rw [hleft, hright]

/-- No new index zero occurs anywhere in the separated component board. -/
theorem separatedComponents_zeroFree
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.ZeroFree) (hR : R.ZeroFree) (g : ℤ) (hg : 0 < g) :
    (Q.separatedComponents R g hg).ZeroFree := by
  intro i j he
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j =>
      apply hQ i j
      exact add_right_cancel (by simpa only [separatedComponents, Fin.append_left] using he)
    | right j =>
      have hQrow := Q.row_strictAnti.antitone (Fin.le_last i)
      have hQdiag := Q.row_nonempty (Fin.last p)
      have hRcol := R.col_strictAnti.antitone (Fin.zero_le j)
      have hRdiag := R.row_nonempty 0
      simp only [separatedComponents, Fin.append_left, Fin.append_right,
        componentOffset] at he
      omega
  | right i =>
    cases j using Fin.addCases with
    | left j =>
      have hn := Q.separatedComponents_lower_negative R g hg i j
      rw [he] at hn
      exact (lt_irrefl _ hn).elim
    | right j =>
      apply hR i j
      simpa only [separatedComponents, Fin.append_right] using he

/-- Cast only the produced natural-number order equality required by the border operation. -/
def twoComponentCore (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) : BetaDiagram (p + r + 2) :=
  (Q.separatedComponents R g hg).reindexOrder (by omega)

/-- The actual connected parent of the two ordered nonlinear components. -/
def twoComponentContext (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    BetaDiagram (p + r + 3) :=
  ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).shifted
    (v - R.col (Fin.last r))

@[simp] theorem twoComponentCore_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) :
    (Q.twoComponentCore R g hg).schur = Q.schur * R.schur := by
  rw [twoComponentCore, reindexOrder_schur, separatedComponents_schur]

/-- The harmless produced order cast retains actual zero-freeness. -/
theorem twoComponentCore_zeroFree
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.ZeroFree) (hR : R.ZeroFree) (g : ℤ) (hg : 0 < g) :
    (Q.twoComponentCore R g hg).ZeroFree := by
  intro i j he
  exact Q.separatedComponents_zeroFree R hQ hR g hg _ _ he

/-- The full constructed parent is zero-free, not merely its component factors. -/
theorem twoComponentContext_zeroFree
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.ZeroFree) (hR : R.ZeroFree)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).ZeroFree :=
  ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).shifted_zeroFree
    ((Q.twoComponentCore R g hg).positiveBorder_zeroFree
      (Q.twoComponentCore_zeroFree R hQ hR g hg) u v hu hv) _

/-- The context has connected nonempty actual beta lists. -/
theorem twoComponentContext_connected
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).Connected := by
  have h := (Q.twoComponentCore R g hg).positiveBorder_connected u v hu hv
  refine ⟨h.1, ?_⟩
  intro i hi
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col i +
      (v - R.col (Fin.last r)) ≤
    ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row ⟨i.val + 1, hi⟩ +
      (v - R.col (Fin.last r))
  have hh := h.2 i hi
  omega

/-- Differentiation recovers the full product, with its actual common cofactor sign. -/
theorem twoComponentContext_corner_coefficient
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    MvPolynomial.pderiv
      (((Q.twoComponentCore R g hg).positiveBorder u v hu hv).borderLargestGenerator)
      (Q.twoComponentContext R u v g hu hv hg).schur =
      (-1) ^ (p + r + 2) * (Q.schur * R.schur) := by
  simp only [twoComponentContext, shifted_schur]
  rw [positiveBorder_corner_coefficient, twoComponentCore_schur]

/-- The determinant called `B_Q` is the actual maximal complementary board. -/
noncomputable def twoComponentTieMinor (Q : BetaDiagram (p + 2)) : CompleteRing :=
  (Q.matrix.submatrix Fin.succ (Fin.last (p + 1)).succAbove).det

/-- Its sorted diagonal is strictly positive, produced from connectedness and zero-freeness. -/
theorem twoComponentTieMinor_ne_zero (Q : BetaDiagram (p + 2))
    (hC : Q.Connected) (hZ : Q.ZeroFree) : Q.twoComponentTieMinor ≠ 0 := by
  let hP := Q.positiveCorner_of_connected_zeroFree hC hZ
  have he : Q.matrix.submatrix Fin.succ (Fin.last (p + 1)).succAbove =
      (Q.cornerDiagram hP).matrix := by
    apply Matrix.ext
    intro i j
    simp [matrix, cornerDiagram]
  change (Q.matrix.submatrix Fin.succ (Fin.last (p + 1)).succAbove).det ≠ 0
  rw [he]
  exact (Q.cornerDiagram hP).schur_ne_zero

/-- The moving top coefficient of the actual `A₁` is precisely the signed `B_Q`
in `eq:two-component-tie-table`, with no normalization or row-order restriction. -/
theorem twoComponent_top_extension_coefficient (Q : BetaDiagram (p + 2))
    (u : ℤ) (hu : 0 < u) :
    MvPolynomial.pderiv (Q.extendTop u hu).borderLargestGenerator
      (Q.extendTop u hu).schur = (-1) ^ (p + 1) * Q.twoComponentTieMinor := by
  have hd := (Q.extendTop u hu).pderiv_schur_largest
  have hcorner : (Q.extendTop u hu).cornerPolynomial = Q.twoComponentTieMinor := by
    unfold cornerPolynomial twoComponentTieMinor
    congr 1
    apply Matrix.ext
    intro i j
    have hi : (i.succ : Fin (p + 2)) ≠ 0 := Fin.succ_ne_zero i
    simp [cornerBoard, betaBoard, matrix, extendTop, hi]
  change MvPolynomial.pderiv (Q.extendTop u hu).borderLargestGenerator
    (Q.extendTop u hu).schur = (Q.extendTop u hu).cornerCoefficient at hd
  rw [hd, cornerCoefficient, hcorner]

/-- The coefficient factor used in all three tie regimes is genuinely nonzero. -/
theorem twoComponent_tie_coefficient_ne_zero (Q : BetaDiagram (p + 2))
    (hC : Q.Connected) (hZ : Q.ZeroFree) (c : CompleteRing) (hc : c ≠ 0) :
    Q.twoComponentTieMinor * c ≠ 0 :=
  mul_ne_zero (Q.twoComponentTieMinor_ne_zero hC hZ) hc

/-- The actual `Aᵢ` diagram obtained by deleting row `i` from the increased
top-row list and retaining all original columns.  The auxiliary bottom margin
is deleted, so it contributes no entry to this diagram. -/
def twoComponentLeftMinor (Q : BetaDiagram (p + 1))
    (u : ℤ) (hu : 0 < u) (i : Fin (p + 2)) : BetaDiagram (p + 1) :=
  (Q.positiveBorder u 1 hu (by norm_num)).lastColumnDiagram
    (Q.positiveBorder_positiveCorner u 1 hu (by norm_num)) i

@[simp] theorem twoComponentLeftMinor_zero (Q : BetaDiagram (p + 1))
    (u : ℤ) (hu : 0 < u) :
    (Q.twoComponentLeftMinor u hu 0).schur = Q.schur := by
  have hm : (Q.twoComponentLeftMinor u hu 0).matrix = Q.matrix := by
    apply Matrix.ext
    intro i j
    change complete ((Q.positiveBorder u 1 hu (by norm_num)).row ((0 : Fin (p + 2)).succAbove i) -
      (Q.positiveBorder u 1 hu (by norm_num)).col j.castSucc) =
      complete (Q.row i - Q.col j)
    simp only [Fin.zero_succAbove, positiveBorder_row_succ, positiveBorder_col_castSucc]
  unfold schur
  rw [hm]

@[simp] theorem twoComponentLeftMinor_one (Q : BetaDiagram (p + 1))
    (u : ℤ) (hu : 0 < u) :
    (Q.twoComponentLeftMinor u hu (0 : Fin (p + 1)).succ).schur =
      (Q.extendTop u hu).schur := by
  have hm : (Q.twoComponentLeftMinor u hu (0 : Fin (p + 1)).succ).matrix =
      (Q.extendTop u hu).matrix := by
    apply Matrix.ext
    intro i j
    change complete ((Q.positiveBorder u 1 hu (by norm_num)).row
        (((0 : Fin (p + 1)).succ).succAbove i) -
      (Q.positiveBorder u 1 hu (by norm_num)).col j.castSucc) =
      complete ((Q.extendTop u hu).row i - (Q.extendTop u hu).col j)
    cases i using Fin.cases <;>
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.zero_succAbove,
        positiveBorder_row_zero, positiveBorder_row_succ, positiveBorder_col_castSucc,
        extendTop, Fin.succ_ne_zero, ite_true, ite_false]
  unfold schur
  rw [hm]

/-- Every actual left coefficient is nonzero by its produced nonempty beta rows. -/
theorem twoComponentLeftMinor_ne_zero (Q : BetaDiagram (p + 1))
    (u : ℤ) (hu : 0 < u) (i : Fin (p + 2)) :
    (Q.twoComponentLeftMinor u hu i).schur ≠ 0 :=
  (Q.twoComponentLeftMinor u hu i).schur_ne_zero

/-- No actual left determinant has a generator beyond the enlarged top span. -/
theorem twoComponentLeftMinor_vars_le (Q : BetaDiagram (p + 1))
    (u : ℤ) (hu : 0 < u) (i : Fin (p + 2)) (k : ℕ+)
    (hk : k ∈ (Q.twoComponentLeftMinor u hu i).schur.vars) :
    (k.val : ℤ) ≤ Q.largestLabel + u := by
  let A := Q.twoComponentLeftMinor u hu i
  let P := Q.positiveBorder u 1 hu (by norm_num)
  have hb := A.vars_le_largestLabel k hk
  have hr := P.row_strictAnti.antitone (Fin.zero_le (i.succAbove 0))
  rw [positiveBorder_row_zero] at hr
  have hc : A.col (Fin.last p) = Q.col (Fin.last p) := by
    change P.col (Fin.last p).castSucc = _
    exact Q.positiveBorder_col_castSucc u 1 hu (by norm_num) (Fin.last p)
  change (k.val : ℤ) ≤ A.row 0 - A.col (Fin.last p) at hb
  rw [hc] at hb
  change P.row (i.succAbove 0) ≤ Q.row 0 + u at hr
  change (k.val : ℤ) ≤ Q.row 0 - Q.col (Fin.last p) + u
  change (k.val : ℤ) ≤ P.row (i.succAbove 0) - Q.col (Fin.last p) at hb
  omega

/-- The entire coefficient at the enlarged top generator has labels strictly
below the original span, for every actual deleted-row minor. -/
theorem twoComponentLeftMinor_corner_labels (Q : BetaDiagram (p + 2))
    (u : ℤ) (hu : 0 < u) (r : Fin (p + 3)) :
    LabelsBelow (Q.twoComponentLeftMinor u hu r).cornerPolynomial Q.largestLabel := by
  intro k hk
  by_contra hlt
  have hge : Q.row 0 - Q.col (Fin.last (p + 1)) ≤ (k.val : ℤ) := by
    change Q.largestLabel ≤ (k.val : ℤ)
    omega
  let A := Q.twoComponentLeftMinor u hu r
  let P := Q.positiveBorder u 1 hu (by norm_num)
  apply (not_mem_vars_det A.cornerBoard k ?_) hk
  intro i j
  change k ∉ (complete (P.row (r.succAbove i.succ) - P.col j.castSucc.castSucc)).vars
  rw [positiveBorder_col_castSucc]
  rw [mem_vars_complete_iff]
  intro he
  change (k.val : ℤ) = P.row (r.succAbove i.succ) - Q.col j.castSucc at he
  have hpos := Fin.succAbove_pos r i.succ (show 0 < i.succ by
    simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ]
    omega)
  have hidx : (0 : Fin (p + 2)).succ ≤ r.succAbove i.succ := by
    simp only [Fin.lt_def, Fin.val_zero] at hpos
    simp only [Fin.le_def, Fin.val_succ, Fin.val_zero]
    omega
  have hr := P.row_strictAnti.antitone hidx
  rw [positiveBorder_row_succ] at hr
  have hc := Q.col_strictAnti (Fin.castSucc_lt_last j)
  omega

/-- Every noninitial actual left minor has the same enlarged top span. -/
theorem twoComponentLeftMinor_largestLabel (Q : BetaDiagram (p + 1))
    (u : ℤ) (hu : 0 < u) (r : Fin (p + 2)) (hr : r ≠ 0) :
    (Q.twoComponentLeftMinor u hu r).largestLabel = Q.largestLabel + u := by
  change (Q.positiveBorder u 1 hu (by norm_num)).row (r.succAbove 0) -
    (Q.positiveBorder u 1 hu (by norm_num)).col (Fin.last p).castSucc =
    Q.row 0 - Q.col (Fin.last p) + u
  rw [Fin.succAbove_ne_zero_zero hr, positiveBorder_row_zero, positiveBorder_col_castSucc]
  ring

/-- The coefficient at that common moving generator is the whole actual
complementary determinant, not a supplied leading certificate. -/
theorem twoComponentLeftMinor_top_coefficient (Q : BetaDiagram (p + 2))
    (u : ℤ) (hu : 0 < u) (r : Fin (p + 3)) (hr : r ≠ 0) :
    MvPolynomial.pderiv (Q.extendTop u hu).borderLargestGenerator
      (Q.twoComponentLeftMinor u hu r).schur =
      (-1 : CompleteRing) ^ (p + 1) *
        (Q.twoComponentLeftMinor u hu r).cornerPolynomial := by
  let A := Q.twoComponentLeftMinor u hu r
  have hg : A.borderLargestGenerator = (Q.extendTop u hu).borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (A.borderLargestGenerator.val : ℤ) =
      ((Q.extendTop u hu).borderLargestGenerator.val : ℤ)
    rw [borderLargestGenerator_int, borderLargestGenerator_int,
      twoComponentLeftMinor_largestLabel, border_extendTop_largestLabel]
    exact hr
  have hd := A.pderiv_schur_largest
  change MvPolynomial.pderiv A.borderLargestGenerator A.schur = A.cornerCoefficient at hd
  rw [hg] at hd
  simpa only [cornerCoefficient] using hd

/-- The actual moving shifts are positive, without a normalization hypothesis. -/
def twoComponentShift (Q : BetaDiagram (p + 1)) (g : ℤ) (i : Fin (p + 1)) : ℤ :=
  g + Q.row i - Q.col (Fin.last p)

theorem twoComponentShift_pos (Q : BetaDiagram (p + 1))
    (g : ℤ) (hg : 0 < g) (i : Fin (p + 1)) : 0 < Q.twoComponentShift g i := by
  have hd := Q.row_nonempty i
  have hc := Q.col_strictAnti.antitone (Fin.le_last i)
  unfold twoComponentShift
  omega

@[simp] theorem twoComponentShift_zero (Q : BetaDiagram (p + 1)) (g : ℤ) :
    Q.twoComponentShift g 0 = g + Q.largestLabel := by
  unfold twoComponentShift largestLabel
  ring

theorem twoComponentShift_lt_zero (Q : BetaDiagram (p + 1)) (g : ℤ)
    (i : Fin (p + 1)) (hi : i ≠ 0) :
    Q.twoComponentShift g i < Q.twoComponentShift g 0 := by
  have hr := Q.row_strictAnti (Fin.pos_iff_ne_zero.mpr hi)
  unfold twoComponentShift
  omega

/-- The full actual Laplace sum at the outer-margin tie
(`eq:two-component-tie`), with every left determinant retained. -/
noncomputable def twoComponentTieSum (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 1))
    (u g : ℤ) (hu : 0 < u) (hg : 0 < g) : CompleteRing :=
  ∑ i : Fin (p + 2), (-1 : CompleteRing) ^ (p + 1 - i.val) *
    (Q.twoComponentLeftMinor u hu i.succ).schur *
    R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)

private theorem pderiv_sign_pow (k : ℕ+) (e : ℕ) :
    MvPolynomial.pderiv k ((-1 : CompleteRing) ^ e) = 0 := by
  have he : (-1 : CompleteRing) ^ e = MvPolynomial.C ((-1 : ℚ) ^ e) := by
    simp only [map_pow, map_neg, map_one]
  rw [he]
  simp

/-- The actual left determinants are linear in the common top generator. -/
theorem twoComponentLeftMinor_second_derivative (Q : BetaDiagram (p + 2))
    (u : ℤ) (hu : 0 < u) (r : Fin (p + 3)) (hr : r ≠ 0) :
    let k := (Q.extendTop u hu).borderLargestGenerator
    MvPolynomial.pderiv k (MvPolynomial.pderiv k
      (Q.twoComponentLeftMinor u hu r).schur) = 0 := by
  dsimp only
  let k := (Q.extendTop u hu).borderLargestGenerator
  have hk : (k.val : ℤ) = Q.largestLabel + u := by
    simp only [k, borderLargestGenerator_int, border_extendTop_largestLabel]
  have hn : k ∉ (Q.twoComponentLeftMinor u hu r).cornerPolynomial.vars := by
    intro h
    have hb := Q.twoComponentLeftMinor_corner_labels u hu r k h
    omega
  rw [twoComponentLeftMinor_top_coefficient Q u hu r hr,
    MvPolynomial.pderiv_mul, pderiv_sign_pow,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hn]
  ring

/-- The first strict row of `eq:two-component-tie-table`: the actual first
left minor carries the only moving endpoint generator above every left span. -/
private theorem twoComponentTieSum_above_of_split (Q : BetaDiagram (p + 2))
    (R : BetaDiagram (r + 1)) (κ : ℤ) (hκ : 0 < κ) (c : CompleteRing)
    (hd : ∀ (t : ℤ) (ht : 0 < t), ∃ z : CompleteRing,
      R.endpointDifference t ht = complete (κ + t) * c + z ∧
        LabelsBelow c (κ + t) ∧ LabelsBelow z (κ + t)) :
    ∀ (u g : ℤ) (hu : 0 < u) (hg : 0 < g),
      Q.largestLabel + u < κ + g + Q.largestLabel →
      ∃ ht : 0 < κ + g + Q.largestLabel,
        MvPolynomial.pderiv (⟨(κ + g + Q.largestLabel).toNat, by omega⟩ : ℕ+)
          (Q.twoComponentTieSum R u g hu hg) =
          (-1 : CompleteRing) ^ (p + 1) * (Q.extendTop u hu).schur * c := by
  intro u g hu hg hcase
  let t0 := κ + g + Q.largestLabel
  have ht : 0 < t0 := by
    have hS := Q.largestLabel_pos
    dsimp [t0]
    omega
  refine ⟨ht, ?_⟩
  let k : ℕ+ := ⟨t0.toNat, by omega⟩
  have hk : (k.val : ℤ) = t0 := by dsimp [k]; omega
  let A (i : Fin (p + 2)) := (Q.twoComponentLeftMinor u hu i.succ).schur
  let E (i : Fin (p + 2)) :=
    R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)
  let b (i : Fin (p + 2)) := (-1 : CompleteRing) ^ (p + 1 - i.val)
  have hAzero : ∀ i, MvPolynomial.pderiv k (A i) = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hi
    have hb := Q.twoComponentLeftMinor_vars_le u hu i.succ k hi
    dsimp [t0] at hk
    omega
  have hEzero : ∀ i : Fin (p + 2), i ≠ 0 → MvPolynomial.pderiv k (E i) = 0 := by
    intro i hi
    obtain ⟨z, hz, hcl, hzl⟩ := hd (Q.twoComponentShift g i)
      (Q.twoComponentShift_pos g hg i)
    have hr := Q.row_strictAnti (Fin.pos_iff_ne_zero.mpr hi)
    have hlevel : κ + Q.twoComponentShift g i < t0 := by
      dsimp [twoComponentShift, t0, largestLabel]
      omega
    have hbelow : LabelsBelow (E i) t0 := by
      change LabelsBelow
        (R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)) t0
      rw [hz]
      apply LabelsBelow.add
      · apply LabelsBelow.mul (LabelsBelow.complete hlevel)
        intro j hj
        have hh := hcl j hj
        omega
      · intro j hj
        have hh := hzl j hj
        omega
    exact MvPolynomial.pderiv_eq_zero_of_notMem_vars (hbelow.not_mem k hk)
  have hlevel0 : κ + Q.twoComponentShift g 0 = t0 := by
    dsimp [twoComponentShift, t0]
    unfold largestLabel
    ring
  have hE0 : MvPolynomial.pderiv k (E 0) = c := by
    obtain ⟨z, hz, hcl, hzl⟩ := hd (Q.twoComponentShift g 0)
      (Q.twoComponentShift_pos g hg 0)
    have hX : complete (κ + Q.twoComponentShift g 0) = (MvPolynomial.X k : CompleteRing) := by
      rw [hlevel0]
      exact complete_of_pos ht
    have hk0 : (k.val : ℤ) = κ + Q.twoComponentShift g 0 := hk.trans hlevel0.symm
    change MvPolynomial.pderiv k
      (R.endpointDifference (Q.twoComponentShift g 0) (Q.twoComponentShift_pos g hg 0)) = c
    rw [hz, hX, map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hcl.not_mem k hk0),
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hzl.not_mem k hk0)]
    ring
  have hbzero : ∀ i, MvPolynomial.pderiv k (b i) = 0 := by
    intro i
    exact pderiv_sign_pow k _
  change MvPolynomial.pderiv k (∑ i : Fin (p + 2), b i * A i * E i) =
    (-1 : CompleteRing) ^ (p + 1) * (Q.extendTop u hu).schur * c
  rw [map_sum, Fin.sum_univ_succ]
  have htail : ∀ i : Fin (p + 1),
      MvPolynomial.pderiv k (b i.succ * A i.succ * E i.succ) = 0 := by
    intro i
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      hbzero, hAzero, hEzero i.succ (Fin.succ_ne_zero i)]
    ring
  simp only [htail, Finset.sum_const_zero, add_zero]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, hbzero, hAzero, hE0]
  simp only [A, b, Fin.val_zero, Nat.sub_zero, twoComponentLeftMinor_one]
  ring

/-- The equal-index row of `eq:two-component-tie-table`, expressed as the exact
second derivative (twice the square coefficient).  Both leaders are produced
from the actual left minor and the stipulated endpoint-leading property. -/
private theorem twoComponentTieSum_equal_of_split (Q : BetaDiagram (p + 2))
    (R : BetaDiagram (r + 1)) (κ : ℤ) (hκ : 0 < κ) (c : CompleteRing)
    (hd : ∀ (t : ℤ) (ht : 0 < t), ∃ z : CompleteRing,
      R.endpointDifference t ht = complete (κ + t) * c + z ∧
        LabelsBelow c (κ + t) ∧ LabelsBelow z (κ + t)) :
    ∀ (u g : ℤ) (hu : 0 < u) (hg : 0 < g),
      κ + g + Q.largestLabel = Q.largestLabel + u →
      let k := (Q.extendTop u hu).borderLargestGenerator
      MvPolynomial.pderiv k (MvPolynomial.pderiv k
        (Q.twoComponentTieSum R u g hu hg)) =
        (2 : CompleteRing) * Q.twoComponentTieMinor * c := by
  intro u g hu hg heq
  dsimp only
  let k := (Q.extendTop u hu).borderLargestGenerator
  have hk : (k.val : ℤ) = Q.largestLabel + u := by
    simp only [k, borderLargestGenerator_int, border_extendTop_largestLabel]
  let A (i : Fin (p + 2)) := (Q.twoComponentLeftMinor u hu i.succ).schur
  let E (i : Fin (p + 2)) :=
    R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)
  let b (i : Fin (p + 2)) := (-1 : CompleteRing) ^ (p + 1 - i.val)
  have hk0 : (k.val : ℤ) = κ + Q.twoComponentShift g 0 := by
    rw [twoComponentShift_zero]
    omega
  obtain ⟨z0, hz0, hcl0, hzl0⟩ := hd (Q.twoComponentShift g 0)
    (Q.twoComponentShift_pos g hg 0)
  have hE0 : MvPolynomial.pderiv k (E 0) = c := by
    have hX : complete (κ + Q.twoComponentShift g 0) = (MvPolynomial.X k : CompleteRing) := by
      rw [← hk0]
      exact complete_nat k
    change MvPolynomial.pderiv k
      (R.endpointDifference (Q.twoComponentShift g 0) (Q.twoComponentShift_pos g hg 0)) = c
    rw [hz0, hX, map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hcl0.not_mem k hk0),
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hzl0.not_mem k hk0)]
    ring
  have hEzero : ∀ i : Fin (p + 2), i ≠ 0 → MvPolynomial.pderiv k (E i) = 0 := by
    intro i hi
    obtain ⟨z, hz, hcl, hzl⟩ := hd (Q.twoComponentShift g i)
      (Q.twoComponentShift_pos g hg i)
    have hshift := Q.twoComponentShift_lt_zero g i hi
    have hbelow : LabelsBelow (E i) (k.val : ℤ) := by
      change LabelsBelow
        (R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)) (k.val : ℤ)
      rw [hz]
      apply LabelsBelow.add
      · apply LabelsBelow.mul (LabelsBelow.complete (by omega))
        intro j hj
        have hh := hcl j hj
        omega
      · intro j hj
        have hh := hzl j hj
        omega
    exact MvPolynomial.pderiv_eq_zero_of_notMem_vars (hbelow.not_mem k rfl)
  have hEsecond : ∀ i, MvPolynomial.pderiv k (MvPolynomial.pderiv k (E i)) = 0 := by
    intro i
    by_cases hi : i = 0
    · subst i
      rw [hE0, MvPolynomial.pderiv_eq_zero_of_notMem_vars (hcl0.not_mem k hk0)]
    · rw [hEzero i hi, map_zero]
  have hAsecond : ∀ i, MvPolynomial.pderiv k (MvPolynomial.pderiv k (A i)) = 0 := by
    intro i
    exact Q.twoComponentLeftMinor_second_derivative u hu i.succ (Fin.succ_ne_zero i)
  have hbzero : ∀ i, MvPolynomial.pderiv k (b i) = 0 := by
    intro i
    exact pderiv_sign_pow k _
  have hA0 : MvPolynomial.pderiv k (A 0) =
      (-1 : CompleteRing) ^ (p + 1) * Q.twoComponentTieMinor := by
    change MvPolynomial.pderiv k
      (Q.twoComponentLeftMinor u hu (0 : Fin (p + 2)).succ).schur = _
    rw [twoComponentLeftMinor_one]
    exact Q.twoComponent_top_extension_coefficient u hu
  change MvPolynomial.pderiv k (MvPolynomial.pderiv k
      (∑ i : Fin (p + 2), b i * A i * E i)) =
    (2 : CompleteRing) * Q.twoComponentTieMinor * c
  rw [map_sum, map_sum, Fin.sum_univ_succ]
  have htail : ∀ i : Fin (p + 1),
      MvPolynomial.pderiv k (MvPolynomial.pderiv k
        (b i.succ * A i.succ * E i.succ)) = 0 := by
    intro i
    rw [pderiv_twice_three_mul k _ _ _ (hbzero i.succ) (hAsecond i.succ)
      (hEsecond i.succ), hEzero i.succ (Fin.succ_ne_zero i)]
    ring
  simp only [htail, Finset.sum_const_zero, add_zero]
  rw [pderiv_twice_three_mul k _ _ _ (hbzero 0) (hAsecond 0) (hEsecond 0), hA0, hE0]
  simp only [b, Fin.val_zero, Nat.sub_zero]
  have hsquare : (-1 : CompleteRing) ^ (p + 1) * (-1 : CompleteRing) ^ (p + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : CompleteRing) * (-1) ^ (p + 1) *
        ((-1) ^ (p + 1) * Q.twoComponentTieMinor) * c =
        2 * ((-1) ^ (p + 1) * (-1) ^ (p + 1)) * Q.twoComponentTieMinor * c := by ring
    _ = 2 * Q.twoComponentTieMinor * c := by rw [hsquare]; ring

/-- The lower-index row of `eq:two-component-tie-table`: mixed extraction at
the enlarged left span and the moving right endpoint index gives `B_Q c_R`. -/
private theorem twoComponentTieSum_below_of_split (Q : BetaDiagram (p + 2))
    (R : BetaDiagram (r + 1)) (κ : ℤ) (hκ : 0 < κ) (c : CompleteRing)
    (hd : ∀ (t : ℤ) (ht : 0 < t), ∃ z : CompleteRing,
      R.endpointDifference t ht = complete (κ + t) * c + z ∧
        LabelsBelow c (κ + t) ∧ LabelsBelow z (κ + t)) :
    ∀ (u g : ℤ) (hu : 0 < u) (hg : 0 < g),
      κ + g + Q.largestLabel < Q.largestLabel + u →
      ∃ ht : 0 < κ + g + Q.largestLabel,
        let j := (⟨(κ + g + Q.largestLabel).toNat, by omega⟩ : ℕ+)
        let k := (Q.extendTop u hu).borderLargestGenerator
        MvPolynomial.pderiv j (MvPolynomial.pderiv k
          (Q.twoComponentTieSum R u g hu hg)) = Q.twoComponentTieMinor * c := by
  intro u g hu hg hcase
  let t0 := κ + g + Q.largestLabel
  have ht : 0 < t0 := by
    have hs := Q.largestLabel_pos
    dsimp [t0]
    omega
  refine ⟨ht, ?_⟩
  dsimp only
  let j : ℕ+ := ⟨t0.toNat, by omega⟩
  let k := (Q.extendTop u hu).borderLargestGenerator
  have hj : (j.val : ℤ) = t0 := by dsimp [j]; omega
  have hk : (k.val : ℤ) = Q.largestLabel + u := by
    simp only [k, borderLargestGenerator_int, border_extendTop_largestLabel]
  have hlevel0 : κ + Q.twoComponentShift g 0 = t0 := by
    rw [twoComponentShift_zero]
    dsimp [t0]
    ring
  let A (i : Fin (p + 2)) := (Q.twoComponentLeftMinor u hu i.succ).schur
  let E (i : Fin (p + 2)) :=
    R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)
  let b (i : Fin (p + 2)) := (-1 : CompleteRing) ^ (p + 1 - i.val)
  have hEk : ∀ i, MvPolynomial.pderiv k (E i) = 0 := by
    intro i
    obtain ⟨z, hz, hcl, hzl⟩ := hd (Q.twoComponentShift g i)
      (Q.twoComponentShift_pos g hg i)
    have hr := Q.row_strictAnti.antitone (Fin.zero_le i)
    have hshift : Q.twoComponentShift g i ≤ Q.twoComponentShift g 0 := by
      unfold twoComponentShift
      omega
    have hbelow : LabelsBelow (E i) (k.val : ℤ) := by
      change LabelsBelow
        (R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)) (k.val : ℤ)
      rw [hz]
      apply LabelsBelow.add
      · apply LabelsBelow.mul (LabelsBelow.complete (by dsimp [t0] at hlevel0; omega))
        intro v hv
        have hh := hcl v hv
        dsimp [t0] at hlevel0
        omega
      · intro v hv
        have hh := hzl v hv
        dsimp [t0] at hlevel0
        omega
    exact MvPolynomial.pderiv_eq_zero_of_notMem_vars (hbelow.not_mem k rfl)
  have hEj : ∀ i : Fin (p + 2), i ≠ 0 → MvPolynomial.pderiv j (E i) = 0 := by
    intro i hi
    obtain ⟨z, hz, hcl, hzl⟩ := hd (Q.twoComponentShift g i)
      (Q.twoComponentShift_pos g hg i)
    have hshift := Q.twoComponentShift_lt_zero g i hi
    have hbelow : LabelsBelow (E i) t0 := by
      change LabelsBelow
        (R.endpointDifference (Q.twoComponentShift g i) (Q.twoComponentShift_pos g hg i)) t0
      rw [hz]
      apply LabelsBelow.add
      · apply LabelsBelow.mul (LabelsBelow.complete (by omega))
        intro v hv
        have hh := hcl v hv
        omega
      · intro v hv
        have hh := hzl v hv
        omega
    exact MvPolynomial.pderiv_eq_zero_of_notMem_vars (hbelow.not_mem j hj)
  have hE0 : MvPolynomial.pderiv j (E 0) = c := by
    obtain ⟨z, hz, hcl, hzl⟩ := hd (Q.twoComponentShift g 0)
      (Q.twoComponentShift_pos g hg 0)
    have hX : complete (κ + Q.twoComponentShift g 0) = (MvPolynomial.X j : CompleteRing) := by
      rw [hlevel0]
      exact complete_of_pos ht
    have hj0 : (j.val : ℤ) = κ + Q.twoComponentShift g 0 := hj.trans hlevel0.symm
    change MvPolynomial.pderiv j
      (R.endpointDifference (Q.twoComponentShift g 0) (Q.twoComponentShift_pos g hg 0)) = c
    rw [hz, hX, map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hcl.not_mem j hj0),
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hzl.not_mem j hj0)]
    ring
  have hAmix : ∀ i, MvPolynomial.pderiv j (MvPolynomial.pderiv k (A i)) = 0 := by
    intro i
    have hn : j ∉ (Q.twoComponentLeftMinor u hu i.succ).cornerPolynomial.vars := by
      intro hv
      have hb := Q.twoComponentLeftMinor_corner_labels u hu i.succ j hv
      dsimp [t0] at hj
      omega
    rw [twoComponentLeftMinor_top_coefficient Q u hu i.succ (Fin.succ_ne_zero i),
      MvPolynomial.pderiv_mul, pderiv_sign_pow,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hn]
    ring
  have hA0 : MvPolynomial.pderiv k (A 0) =
      (-1 : CompleteRing) ^ (p + 1) * Q.twoComponentTieMinor := by
    change MvPolynomial.pderiv k
      (Q.twoComponentLeftMinor u hu (0 : Fin (p + 2)).succ).schur = _
    rw [twoComponentLeftMinor_one]
    exact Q.twoComponent_top_extension_coefficient u hu
  have hterm : ∀ i : Fin (p + 2),
      MvPolynomial.pderiv j (MvPolynomial.pderiv k (b i * A i * E i)) =
        b i * MvPolynomial.pderiv k (A i) * MvPolynomial.pderiv j (E i) := by
    intro i
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      pderiv_sign_pow, hEk]
    simp only [zero_mul, zero_add, mul_zero, add_zero]
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      pderiv_sign_pow, hAmix]
    ring
  change MvPolynomial.pderiv j (MvPolynomial.pderiv k
      (∑ i : Fin (p + 2), b i * A i * E i)) = Q.twoComponentTieMinor * c
  rw [map_sum, map_sum]
  simp only [hterm]
  rw [Fin.sum_univ_succ]
  have htail : ∀ i : Fin (p + 1),
      b i.succ * MvPolynomial.pderiv k (A i.succ) * MvPolynomial.pderiv j (E i.succ) = 0 := by
    intro i
    rw [hEj i.succ (Fin.succ_ne_zero i), mul_zero]
  simp only [htail, Finset.sum_const_zero, add_zero, hA0, hE0,
    b, Fin.val_zero, Nat.sub_zero]
  have hsquare : (-1 : CompleteRing) ^ (p + 1) * (-1 : CompleteRing) ^ (p + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : CompleteRing) ^ (p + 1) *
        ((-1) ^ (p + 1) * Q.twoComponentTieMinor) * c =
        ((-1) ^ (p + 1) * (-1) ^ (p + 1)) * Q.twoComponentTieMinor * c := by ring
    _ = Q.twoComponentTieMinor * c := by rw [hsquare]; ring

/-- All three rows of the actual tie table share the same endpoint offset and
nonzero coefficient supplied by the legitimate fixed-leading-property premise. -/
theorem twoComponentTieSum_table (Q : BetaDiagram (p + 2))
    (R : BetaDiagram (r + 1)) (hR : R.EndpointLeader) :
    ∃ (κ : ℤ) (hκ : 0 < κ), κ < R.largestLabel ∧
      ∃ c : CompleteRing, c ≠ 0 ∧ ∀ (u g : ℤ) (hu : 0 < u) (hg : 0 < g),
        (Q.largestLabel + u < κ + g + Q.largestLabel →
          ∃ ht : 0 < κ + g + Q.largestLabel,
            MvPolynomial.pderiv (⟨(κ + g + Q.largestLabel).toNat, by omega⟩ : ℕ+)
              (Q.twoComponentTieSum R u g hu hg) =
              (-1 : CompleteRing) ^ (p + 1) * (Q.extendTop u hu).schur * c) ∧
        (κ + g + Q.largestLabel = Q.largestLabel + u →
          let k := (Q.extendTop u hu).borderLargestGenerator
          MvPolynomial.pderiv k (MvPolynomial.pderiv k
            (Q.twoComponentTieSum R u g hu hg)) =
            (2 : CompleteRing) * Q.twoComponentTieMinor * c) ∧
        (κ + g + Q.largestLabel < Q.largestLabel + u →
          ∃ ht : 0 < κ + g + Q.largestLabel,
            let j := (⟨(κ + g + Q.largestLabel).toNat, by omega⟩ : ℕ+)
            let k := (Q.extendTop u hu).borderLargestGenerator
            MvPolynomial.pderiv j (MvPolynomial.pderiv k
              (Q.twoComponentTieSum R u g hu hg)) = Q.twoComponentTieMinor * c) := by
  obtain ⟨κ, hκ, hκS, c, hc, hd⟩ := hR
  refine ⟨κ, hκ, hκS, c, hc, ?_⟩
  intro u g hu hg
  exact ⟨twoComponentTieSum_above_of_split Q R κ hκ c hd u g hu hg,
    twoComponentTieSum_equal_of_split Q R κ hκ c hd u g hu hg,
    twoComponentTieSum_below_of_split Q R κ hκ c hd u g hu hg⟩

/-- The actual outer-margin tie sum cannot vanish.  Its complementary diagonal
and all three alternative coefficient extractions have genuine producers. -/
theorem twoComponentTieSum_ne_zero (Q : BetaDiagram (p + 2))
    (R : BetaDiagram (r + 1)) (hQ : Q.Connected) (hZ : Q.ZeroFree)
    (hR : R.EndpointLeader) (u g : ℤ) (hu : 0 < u) (hg : 0 < g) :
    Q.twoComponentTieSum R u g hu hg ≠ 0 := by
  obtain ⟨κ, hκ, _, c, hc, hd⟩ := Q.twoComponentTieSum_table R hR
  obtain ⟨ha, he, hb⟩ := hd u g hu hg
  have hB := Q.twoComponentTieMinor_ne_zero hQ hZ
  intro hz
  rcases lt_trichotomy (Q.largestLabel + u) (κ + g + Q.largestLabel) with h | h | h
  · obtain ⟨ht, hd⟩ := ha h
    rw [hz, map_zero] at hd
    exact (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : CompleteRing) ≠ 0)))
      (Q.extendTop u hu).schur_ne_zero) hc) hd.symm
  · have hd := he h.symm
    dsimp only at hd
    rw [hz, map_zero, map_zero] at hd
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : CompleteRing) ≠ 0) hB) hc) hd.symm
  · obtain ⟨ht, hd⟩ := hb h
    dsimp only at hd
    rw [hz, map_zero, map_zero] at hd
    exact (mul_ne_zero hB hc) hd.symm

/-- Arbitrary connected mates recover both genuine component functions, with
their multiplicities even when the factors are equal. -/
theorem twoComponent_mate_components {m : ℕ}
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hZQ : Q.ZeroFree) (hZR : R.ZeroFree)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (E : BetaDiagram m) (hE : E.Connected)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur = E.schur) :
    ∃ hrow : m = p + r + 3,
      let F := E.castOrder hrow
      ∃ hP : F.PositiveCorner, F.ZeroFree ∧
        ∀ K : ComponentDecomposition (F.cornerDiagram hP),
          Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.schur = Y.2.schur)
            ([(⟨p + 1, Q⟩ : Σ k : ℕ, BetaDiagram k),
              (⟨r + 1, R⟩ : Σ k : ℕ, BetaDiagram k)] : Multiset (Σ k : ℕ, BetaDiagram k))
            (K.components : Multiset _) := by
  let P := Q.twoComponentContext R u v g hu hv hg
  have hPconn := Q.twoComponentContext_connected R u v g hu hv hg
  have hPzero := Q.twoComponentContext_zeroFree R hZQ hZR u v g hu hv hg
  have hrow : m = p + r + 3 := (P.row_count_of_schur_eq E he).symm
  refine ⟨hrow, ?_⟩
  let F := E.castOrder hrow
  have hFconn : F.Connected := (E.castOrder_connected hrow).mpr hE
  have hFeq : P.schur = F.schur := by simpa only [F, castOrder_schur] using he
  have hFzero := P.zeroFree_of_schur_eq F hPconn hFconn hPzero hFeq
  let hPF := F.positiveCorner_of_connected_zeroFree hFconn hFzero
  refine ⟨hPF, hFzero, ?_⟩
  intro K
  apply (F.cornerDiagram hPF).component_matching_of_product K
    [⟨p + 1, Q⟩, ⟨r + 1, R⟩]
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact hQ
    · exact hR
  · have hcorner := P.cornerPolynomial_eq_of_schur_eq F hPconn hFconn hFeq
    have hprod : P.cornerPolynomial = Q.schur * R.schur := by
      simp only [P, twoComponentContext]
      have hm : (((Q.twoComponentCore R g hg).positiveBorder u v hu hv).shifted
          (v - R.col (Fin.last r))).cornerBoard =
          ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).cornerBoard := by
        apply Matrix.ext
        intro i j
        simp [cornerBoard, betaBoard, shifted]
      rw [cornerPolynomial, hm, ← cornerPolynomial,
        positiveBorder_cornerPolynomial, twoComponentCore_schur]
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, cornerDiagram_schur] using hprod.symm.trans hcorner

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/RestorationPaths.lean
private theorem pderiv_finset_prod {ι : Type*} [DecidableEq ι] (k : ℕ+)
    (s : Finset ι) (f : ι → CompleteRing) :
    MvPolynomial.pderiv k (∏ i ∈ s, f i) =
      ∑ j ∈ s, ∏ i ∈ s, if i = j then MvPolynomial.pderiv k (f i) else f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul, ih, Finset.sum_insert ha]
    have hhead : (∏ i ∈ insert a s,
        if i = a then MvPolynomial.pderiv k (f i) else f i) =
        MvPolynomial.pderiv k (f a) * ∏ i ∈ s, f i := by
      rw [Finset.prod_insert ha]
      simp only [ite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [ite_eq_right (by intro h; subst i; exact ha hi)]
    have htail : (∑ j ∈ s, ∏ i ∈ insert a s,
        if i = j then MvPolynomial.pderiv k (f i) else f i) =
        f a * ∑ j ∈ s, ∏ i ∈ s,
          if i = j then MvPolynomial.pderiv k (f i) else f i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.prod_insert ha, ite_eq_right (by intro h; subst j; exact ha hj)]
    rw [hhead, htail]

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/RestorationPaths.lean
private theorem pderiv_det_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ+) (M : Matrix ι ι CompleteRing) :
    MvPolynomial.pderiv k M.det =
      ∑ j : ι, (M.updateCol j (fun i => MvPolynomial.pderiv k (M i j))).det := by
  have hdet : ∀ A : Matrix ι ι CompleteRing, A.det =
      ∑ σ : Equiv.Perm ι, MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℚ)) *
        ∏ i, A (σ i) i := by
    intro A
    simpa only [map_intCast] using Matrix.det_apply' A
  rw [hdet M, map_sum]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, pderiv_finset_prod,
    zero_mul, zero_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hdet (M.updateCol j (fun i => MvPolynomial.pderiv k (M i j)))]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hij : i = j
  · subst i
    simp
  · simp [Matrix.updateCol_apply, hij]

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/RestorationPaths.lean
private theorem pderiv_det_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ+) (M : Matrix ι ι CompleteRing) :
    MvPolynomial.pderiv k M.det =
      ∑ j : ι, ∑ i : ι, M.adjugate j i * MvPolynomial.pderiv k (M i j) := by
  rw [pderiv_det_columns]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- The full first derivative at the two actual exterior sites retains both
cofactors, including their common moving entry at a tied margin. -/
private theorem pderiv_det_exterior_pair {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) CompleteRing) (k : ℕ+)
    (ht : M 0 (Fin.last n).castSucc = MvPolynomial.X k)
    (hb : M (0 : Fin (n + 1)).succ (Fin.last (n + 1)) = MvPolynomial.X k)
    (hprivate : ∀ i j,
      (i ≠ 0 ∨ j ≠ (Fin.last n).castSucc) →
      (i ≠ (0 : Fin (n + 1)).succ ∨ j ≠ Fin.last (n + 1)) →
      MvPolynomial.pderiv k (M i j) = 0) :
    MvPolynomial.pderiv k M.det =
      (-1 : CompleteRing) ^ n *
          (M.submatrix Fin.succ (Fin.last n).castSucc.succAbove).det +
        (-1 : CompleteRing) ^ (n + 2) *
          (M.submatrix (0 : Fin (n + 1)).succ.succAbove
            (Fin.last (n + 1)).succAbove).det := by
  have hentry : ∀ i j,
      MvPolynomial.pderiv k (M i j) =
        (if i = 0 ∧ j = (Fin.last n).castSucc then 1 else 0) +
          (if i = (0 : Fin (n + 1)).succ ∧ j = Fin.last (n + 1) then 1 else 0) := by
    intro i j
    by_cases hT : i = 0 ∧ j = (Fin.last n).castSucc
    · obtain ⟨rfl, rfl⟩ := hT
      rw [ht, MvPolynomial.pderiv_X_self]
      simp
    · by_cases hB : i = (0 : Fin (n + 1)).succ ∧ j = Fin.last (n + 1)
      · obtain ⟨rfl, rfl⟩ := hB
        rw [hb, MvPolynomial.pderiv_X_self]
        simp
      · rw [hprivate i j (by tauto) (by tauto)]
        simp only [hT, hB, ite_false, add_zero]
  rw [pderiv_det_contraction]
  simp only [hentry, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.succAbove_zero, Fin.val_zero, Fin.val_castSucc, Fin.val_last, Fin.val_succ, zero_add]
  have he : 1 + (n + 1) = n + 2 := by omega
  simp only [he]

/-- The tied positive-border derivative keeps both whole actual endpoint
extensions.  This is valid for arbitrary negative core boards as well. -/
theorem positiveBorder_tied_first_derivative {n : ℕ} (D : BetaDiagram (n + 2))
    (q : ℤ) (hq : 0 < q) :
    let P := D.positiveBorder q q hq hq
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) =
      (-1 : CompleteRing) ^ (n + 3) *
        ((D.extendTop q hq).schur + (D.extendBottom q hq).schur) := by
  classical
  dsimp only
  let P := D.positiveBorder q q hq hq
  let N := P.borderLargestGenerator
  let k := P.borderSecondGenerator
  let A := P.matrix.map (eraseGenerator N)
  let hP := D.positiveBorder_positiveCorner q q hq hq
  have hN : (N.val : ℤ) = P.largestLabel := borderLargestGenerator_int P
  have hk : (k.val : ℤ) = P.secondLabel := borderSecondGenerator_int P
  have hNV : N ≠ k := by
    intro he
    have hh := congrArg (fun x : ℕ+ => (x.val : ℤ)) he
    simp only [P, positiveBorder_largestLabel, positiveBorder_secondLabel, min_self] at hN hk
    omega
  have hgap : P.topMargin = P.bottomMargin := by
    simp only [P, positiveBorder_topMargin, positiveBorder_bottomMargin]
  have ht : A 0 (Fin.last (n + 1)).castSucc = MvPolynomial.X k := by
    change eraseGenerator N (complete (P.row 0 - P.col (Fin.last (n + 1)).castSucc)) =
      (MvPolynomial.X k : CompleteRing)
    have hl : P.row 0 - P.col (Fin.last (n + 1)).castSucc = (k.val : ℤ) := by
      rw [P.exterior_candidate_labels.2, hk]
      simp only [secondLabel, P, positiveBorder_topMargin, positiveBorder_bottomMargin, min_self]
    rw [hl, complete_nat k]
    simp [eraseGenerator, hNV, Ne.symm hNV]
  have hb : A (0 : Fin (n + 2)).succ (Fin.last (n + 2)) = MvPolynomial.X k := by
    change eraseGenerator N
      (complete (P.row (0 : Fin (n + 2)).succ - P.col (Fin.last (n + 2)))) =
      (MvPolynomial.X k : CompleteRing)
    have hl : P.row (0 : Fin (n + 2)).succ - P.col (Fin.last (n + 2)) = (k.val : ℤ) := by
      rw [P.exterior_candidate_labels.1, hk]
      simp only [secondLabel, P, positiveBorder_topMargin, positiveBorder_bottomMargin, min_self]
    rw [hl, complete_nat k]
    simp [eraseGenerator, hNV, Ne.symm hNV]
  have hprivate : ∀ i j,
      (i ≠ 0 ∨ j ≠ (Fin.last (n + 1)).castSucc) →
      (i ≠ (0 : Fin (n + 2)).succ ∨ j ≠ Fin.last (n + 2)) →
      MvPolynomial.pderiv k (A i j) = 0 := by
    intro i j htop hbottom
    by_cases hcorner : i = 0 ∧ j = Fin.last (n + 2)
    · obtain ⟨rfl, rfl⟩ := hcorner
      change MvPolynomial.pderiv k (eraseGenerator N (complete P.largestLabel)) = 0
      have he : complete P.largestLabel = (MvPolynomial.X N : CompleteRing) :=
        complete_of_pos P.largestLabel_pos
      rw [he]
      simp [eraseGenerator]
    · have hl := P.tied_margin_private hgap i j (by tauto) htop hbottom
      have hn : k ∉ (complete (P.row i - P.col j)).vars := by
        rw [mem_vars_complete_iff]
        change ¬ (k.val : ℤ) = P.row i - P.col j
        simp only [secondLabel, hgap, min_self] at hk
        omega
      change MvPolynomial.pderiv k
        (eraseGenerator N (complete (P.row i - P.col j))) = 0
      rw [eraseGenerator_complete]
      split_ifs
      · simp
      · exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hn
  have htopM : A.submatrix Fin.succ (Fin.last (n + 1)).castSucc.succAbove =
      P.matrix.submatrix Fin.succ (Fin.last (n + 1)).castSucc.succAbove := by
    apply Matrix.ext
    intro i j
    change eraseGenerator N
      (complete (P.row i.succ - P.col ((Fin.last (n + 1)).castSucc.succAbove j))) =
      complete (P.row i.succ - P.col ((Fin.last (n + 1)).castSucc.succAbove j))
    apply eraseGenerator_eq_self
    rw [mem_vars_complete_iff]
    have hl := P.index_lt_largestLabel i.succ
      ((Fin.last (n + 1)).castSucc.succAbove j) (Or.inl (Fin.succ_ne_zero i))
    change ¬ (N.val : ℤ) = _
    omega
  have hbottomM : A.submatrix (0 : Fin (n + 2)).succ.succAbove (Fin.last (n + 2)).succAbove =
      P.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove (Fin.last (n + 2)).succAbove := by
    apply Matrix.ext
    intro i j
    change eraseGenerator N
      (complete (P.row (((0 : Fin (n + 2)).succ).succAbove i) -
        P.col ((Fin.last (n + 2)).succAbove j))) =
      complete (P.row (((0 : Fin (n + 2)).succ).succAbove i) -
        P.col ((Fin.last (n + 2)).succAbove j))
    apply eraseGenerator_eq_self
    rw [mem_vars_complete_iff]
    have hl := P.index_lt_largestLabel (((0 : Fin (n + 2)).succ).succAbove i)
      ((Fin.last (n + 2)).succAbove j) (Or.inr (Fin.succAbove_ne _ _))
    change ¬ (N.val : ℤ) = _
    omega
  have htopDet : (P.matrix.submatrix Fin.succ (Fin.last (n + 1)).castSucc.succAbove).det =
      (D.extendBottom q hq).schur := by
    have hh := P.endpoint_top_minor hP
    simpa only [unsignedMinor, Fin.succAbove_zero, P, hP, positiveBorder_cornerDiagram,
      positiveBorder_bottomMargin] using hh
  have hbottomDet :
      (P.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove (Fin.last (n + 2)).succAbove).det =
      (D.extendTop q hq).schur := by
    have hh := P.endpoint_bottom_minor hP
    simpa only [unsignedMinor, P, hP, positiveBorder_cornerDiagram, positiveBorder_topMargin] using hh
  change MvPolynomial.pderiv k (eraseGenerator N P.matrix.det) = _
  rw [eraseGenerator_det]
  change MvPolynomial.pderiv k A.det = _
  rw [pderiv_det_exterior_pair A k ht hb hprivate, htopM, hbottomM, htopDet, hbottomDet]
  have hsign : (-1 : CompleteRing) ^ (n + 1) = (-1) ^ (n + 3) := by
    simp only [show n + 3 = (n + 1) + 2 by omega, pow_add]
    norm_num
  rw [hsign]
  ring

private theorem reindexOrder_extendTop_schur {a b : ℕ} (D : BetaDiagram (a + 1))
    (h : b + 1 = a + 1) (u : ℤ) (hu : 0 < u) :
    ((D.reindexOrder h).extendTop u hu).schur = (D.extendTop u hu).schur := by
  have hab : b = a := by omega
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem reindexOrder_extendBottom_schur {a b : ℕ} (D : BetaDiagram (a + 1))
    (h : b + 1 = a + 1) (v : ℤ) (hv : 0 < v) :
    ((D.reindexOrder h).extendBottom v hv).schur = (D.extendBottom v hv).schur := by
  have hab : b = a := by omega
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

/-- Extending the actual first component row changes only its first factor. -/
theorem separatedComponents_extendTop_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g u : ℤ) (hg : 0 < g) (hu : 0 < u) :
    ((Q.separatedComponents R g hg).extendTop u hu).schur =
      (Q.extendTop u hu).schur * R.schur := by
  have hm : ((Q.separatedComponents R g hg).extendTop u hu).matrix =
      ((Q.extendTop u hu).separatedComponents R g hg).matrix := by
    apply Matrix.ext
    intro i j
    change complete (((Q.separatedComponents R g hg).extendTop u hu).row i -
      ((Q.separatedComponents R g hg).extendTop u hu).col j) =
      complete (((Q.extendTop u hu).separatedComponents R g hg).row i -
        ((Q.extendTop u hu).separatedComponents R g hg).col j)
    apply congrArg complete
    cases i using Fin.addCases (m := p + 1) (n := r + 1) with
    | left i =>
      have hi : i.castAdd (r + 1) = 0 ↔ i = 0 := by
        constructor
        · intro h
          apply Fin.ext
          have hh := congrArg Fin.val h
          simpa only [Fin.val_castAdd, Fin.val_zero] using hh
        · rintro rfl
          rfl
      cases j using Fin.addCases (m := p + 1) (n := r + 1) <;>
        simp only [extendTop, separatedComponents, componentOffset,
          Fin.append_left, Fin.append_right, hi] <;>
        split_ifs <;> ring
    | right i =>
      have hi : i.natAdd (p + 1) ≠ 0 := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_zero] at hh
        omega
      cases j using Fin.addCases (m := p + 1) (n := r + 1) <;>
        simp only [extendTop, separatedComponents, componentOffset,
          Fin.append_left, Fin.append_right, hi, ite_false]
  change ((Q.separatedComponents R g hg).extendTop u hu).matrix.det = _
  rw [hm]
  exact (Q.extendTop u hu).separatedComponents_schur R g hg

/-- Extending the actual last component column changes only its last factor. -/
theorem separatedComponents_extendBottom_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g v : ℤ) (hg : 0 < g) (hv : 0 < v) :
    ((Q.separatedComponents R g hg).extendBottom v hv).schur =
      Q.schur * (R.extendBottom v hv).schur := by
  have hm : ((Q.separatedComponents R g hg).extendBottom v hv).matrix =
      (Q.separatedComponents (R.extendBottom v hv) g hg).matrix := by
    apply Matrix.ext
    intro i j
    change complete (((Q.separatedComponents R g hg).extendBottom v hv).row i -
      ((Q.separatedComponents R g hg).extendBottom v hv).col j) =
      complete ((Q.separatedComponents (R.extendBottom v hv) g hg).row i -
        (Q.separatedComponents (R.extendBottom v hv) g hg).col j)
    apply congrArg complete
    cases j using Fin.addCases (m := p + 1) (n := r + 1) with
    | left j =>
      have hj : j.castAdd (r + 1) ≠ Fin.last ((p + 1) + r) := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_last] at hh
        omega
      cases i using Fin.addCases (m := p + 1) (n := r + 1) <;>
        simp only [extendBottom, separatedComponents, componentOffset,
          Fin.append_left, Fin.append_right] <;>
        split_ifs with h <;> first | exact (hj h).elim | rfl
    | right j =>
      have hj : j.natAdd (p + 1) = Fin.last ((p + 1) + r) ↔ j = Fin.last r := by
        constructor
        · intro h
          apply Fin.ext
          have hh := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_last] at hh ⊢
          omega
        · rintro rfl
          apply Fin.ext
          simp only [Fin.val_natAdd, Fin.val_last]
      by_cases hlast : j = Fin.last r
      · subst j
        have he : (Fin.natAdd (p + 1) (Fin.last r) :
            Fin ((p + 1) + (r + 1))) = Fin.last ((p + 1) + r) := by
          apply Fin.ext
          simp only [Fin.val_natAdd, Fin.val_last]
        cases i using Fin.addCases (m := p + 1) (n := r + 1) <;>
          simp only [extendBottom, separatedComponents, componentOffset,
            Fin.append_left, Fin.append_right, ← he, ite_true] <;>
          split_ifs with hh <;>
          first
          | exfalso
            apply hh
            apply Fin.ext
            rfl
          | ring
      · have hglobal : j.natAdd (p + 1) ≠ Fin.last ((p + 1) + r) := by
          intro h
          exact hlast (hj.mp h)
        cases i using Fin.addCases (m := p + 1) (n := r + 1) <;>
          simp only [extendBottom, separatedComponents, componentOffset,
            Fin.append_left, Fin.append_right] <;>
          split_ifs with h <;>
          first | exact (hglobal h).elim | exact (hlast h).elim | rfl
  change ((Q.separatedComponents R g hg).extendBottom v hv).matrix.det = _
  rw [hm]
  exact Q.separatedComponents_schur (R.extendBottom v hv) g hg

/-- The produced order cast does not alter the true endpoint-factor product. -/
theorem twoComponentCore_extendTop_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g u : ℤ) (hg : 0 < g) (hu : 0 < u) :
    ((Q.twoComponentCore R g hg).extendTop u hu).schur =
      (Q.extendTop u hu).schur * R.schur := by
  rw [twoComponentCore, reindexOrder_extendTop_schur]
  exact Q.separatedComponents_extendTop_schur R g u hg hu

theorem twoComponentCore_extendBottom_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g v : ℤ) (hg : 0 < g) (hv : 0 < v) :
    ((Q.twoComponentCore R g hg).extendBottom v hv).schur =
      Q.schur * (R.extendBottom v hv).schur := by
  rw [twoComponentCore, reindexOrder_extendBottom_schur]
  exact Q.separatedComponents_extendBottom_schur R g v hg hv

/-- The geometric area increment of an actual top extension. -/
theorem endpoint_extendTop_area (Q : BetaDiagram (p + 1)) (t : ℤ) (ht : 0 < t) :
    (Q.extendTop t ht).area = Q.area + t := by
  simp only [area, extendTop, Fin.sum_univ_succ, Fin.succ_ne_zero, ite_true, ite_false]
  ring

/-- The geometric area increment of an actual bottom extension. -/
theorem endpoint_extendBottom_area (Q : BetaDiagram (p + 1)) (t : ℤ) (ht : 0 < t) :
    (Q.extendBottom t ht).area = Q.area + t := by
  simp only [area, extendBottom, Fin.sum_univ_castSucc, Fin.castSucc_ne_last,
    ite_true, ite_false]
  ring

/-- Equal actual Schur functions have equal weighted degree and therefore equal area. -/
theorem endpoint_area_eq_of_schur_eq (Q W : BetaDiagram (p + 1)) (he : Q.schur = W.schur) :
    Q.area = W.area := by
  have hW : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight Q.schur (-(W.area : ℝ)) := by
    rw [he]
    exact W.schur_reverse_homogeneous
  have hd := MvPolynomial.IsWeightedHomogeneous.inj_right Q.schur_ne_zero
    Q.schur_reverse_homogeneous hW
  have ha : (Q.area : ℝ) = (W.area : ℝ) := by linarith
  exact_mod_cast ha

/-- Reduction modulo an old factor in the tied marker equates the actual endpoint
extensions.  A nonzero divisible difference would have a scalar quotient of the
wrong weighted degree, since the positive extension changes area. -/
theorem endpoint_top_eq_of_old_factor_dvd (Q W : BetaDiagram (p + 1))
    (hcore : Q.schur = W.schur) (t : ℤ) (ht : 0 < t)
    (hdiv : Q.schur ∣ (Q.extendTop t ht).schur - (W.extendTop t ht).schur) :
    (Q.extendTop t ht).schur = (W.extendTop t ht).schur := by
  classical
  apply sub_eq_zero.mp
  by_contra hn
  let E := (Q.extendTop t ht).schur - (W.extendTop t ht).schur
  have hE : E ≠ 0 := hn
  obtain ⟨f, hf⟩ := hdiv
  have hproduct : E = Q.schur * f := hf
  have hfn : f ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hproduct
    exact hE hproduct
  have hdegree : E.totalDegree ≤ p + 1 := by
    have hd := MvPolynomial.totalDegree_sub (Q.extendTop t ht).schur (W.extendTop t ht).schur
    simpa only [schur_totalDegree, max_self] using hd
  rw [hproduct, MvPolynomial.totalDegree_mul_of_isDomain Q.schur_ne_zero hfn,
    schur_totalDegree] at hdegree
  have hfdegree : f.totalDegree = 0 := by omega
  have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hfdegree
  let c := f.coeff 0
  have hscalar : E = c • Q.schur := by
    rw [hproduct, hconstant, MvPolynomial.smul_eq_C_mul]
    exact mul_comm _ _
  have harea := endpoint_area_eq_of_schur_eq Q W hcore
  have hQt := (Q.extendTop t ht).schur_reverse_homogeneous
  have hWt := (W.extendTop t ht).schur_reverse_homogeneous
  rw [endpoint_extendTop_area] at hQt
  rw [endpoint_extendTop_area, ← harea] at hWt
  have hweighted : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight E
      (-((Q.area + t : ℤ) : ℝ)) := hQt.sub hWt
  have hscalarWeighted : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight E
      (-(Q.area : ℝ)) := by
    rw [hscalar]
    exact (MvPolynomial.weightedHomogeneousSubmodule ℚ reverseIndexWeight (-(Q.area : ℝ))).smul_mem
      c Q.schur_reverse_homogeneous
  have hweights := MvPolynomial.IsWeightedHomogeneous.inj_right hE hweighted hscalarWeighted
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  simp only [Int.cast_add] at hweights
  linarith

/-- The corresponding bottom endpoint assertion follows by actual literal rotation. -/
theorem endpoint_bottom_eq_of_old_factor_dvd (Q W : BetaDiagram (p + 1))
    (hcore : Q.schur = W.schur) (t : ℤ) (ht : 0 < t)
    (hdiv : Q.schur ∣ (Q.extendBottom t ht).schur - (W.extendBottom t ht).schur) :
    (Q.extendBottom t ht).schur = (W.extendBottom t ht).schur := by
  have hr : Q.rotate.schur = W.rotate.schur := Q.rotate_schur.trans (hcore.trans W.rotate_schur.symm)
  have hd : Q.rotate.schur ∣
      (Q.rotate.extendTop t ht).schur - (W.rotate.extendTop t ht).schur := by
    simpa only [rotate_schur, rotate_extendTop_schur] using hdiv
  have he := endpoint_top_eq_of_old_factor_dvd Q.rotate W.rotate hr t ht hd
  simpa only [rotate_extendTop_schur] using he

/-- An old connected factor cannot divide its positive endpoint extension. -/
theorem endpoint_old_factor_not_dvd_top (Q : BetaDiagram (p + 1)) (hQ : Q.Connected)
    (t : ℤ) (ht : 0 < t) : ¬ Q.schur ∣ (Q.extendTop t ht).schur := by
  intro h
  have he := Q.schur_eq_of_connected_dvd (Q.extendTop t ht)
    hQ (Q.extendTop_connected hQ t ht) h
  have hs := Q.largestLabel_eq_of_schur_eq (Q.extendTop t ht)
    hQ (Q.extendTop_connected hQ t ht) he
  rw [border_extendTop_largestLabel] at hs
  omega

theorem endpoint_old_factor_not_dvd_bottom (Q : BetaDiagram (p + 1)) (hQ : Q.Connected)
    (t : ℤ) (ht : 0 < t) : ¬ Q.schur ∣ (Q.extendBottom t ht).schur := by
  intro h
  have he := Q.schur_eq_of_connected_dvd (Q.extendBottom t ht)
    hQ (Q.extendBottom_connected hQ t ht) h
  have hs := Q.largestLabel_eq_of_schur_eq (Q.extendBottom t ht)
    hQ (Q.extendBottom_connected hQ t ht) he
  rw [border_extendBottom_largestLabel] at hs
  omega

/-- The actual separated span is the sum of intrinsic component spans and the gap. -/
theorem twoComponentCore_span (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) :
    (Q.twoComponentCore R g hg).largestLabel = Q.largestLabel + R.largestLabel + g := by
  let horder : p + r + 2 = (p + 1) + (r + 1) := by omega
  have h0 : Fin.cast horder (0 : Fin (p + r + 2)) =
      (0 : Fin (p + 1)).castAdd (r + 1) := by
    apply Fin.ext
    rfl
  have hlast : Fin.cast horder (Fin.last (p + r + 1)) =
      (Fin.last r).natAdd (p + 1) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last, Fin.val_natAdd]
    omega
  change (Q.separatedComponents R g hg).row (Fin.cast horder 0) -
    (Q.separatedComponents R g hg).col (Fin.cast horder (Fin.last (p + r + 1))) = _
  rw [h0, hlast]
  simp only [separatedComponents, Fin.append_left, Fin.append_right, componentOffset, largestLabel]
  ring

/-- The strict top marker is the actual extended first factor times the old last factor. -/
theorem twoComponentContext_top_marker
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (h : u < v) :
    let B := (Q.twoComponentCore R g hg).positiveBorder u v hu hv
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.twoComponentContext R u v g hu hv hg).schur) =
      (-1 : CompleteRing) ^ (p + r + 3) * ((Q.extendTop u hu).schur * R.schur) := by
  dsimp only
  simp only [twoComponentContext, shifted_schur]
  rw [positiveBorder_top_coefficient (Q.twoComponentCore R g hg) u v hu hv h,
    twoComponentCore_extendTop_schur]

/-- The strict bottom marker is the actual old first factor times the extended last factor. -/
theorem twoComponentContext_bottom_marker
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (h : v < u) :
    let B := (Q.twoComponentCore R g hg).positiveBorder u v hu hv
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.twoComponentContext R u v g hu hv hg).schur) =
      (-1 : CompleteRing) ^ (p + r + 3) * (Q.schur * (R.extendBottom v hv).schur) := by
  dsimp only
  simp only [twoComponentContext, shifted_schur]
  rw [positiveBorder_bottom_coefficient (Q.twoComponentCore R g hg) u v hu hv h,
    twoComponentCore_extendBottom_schur]

/-- At a tied margin both actual endpoint-factor contributions have the same sign. -/
theorem twoComponentContext_tied_marker
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (q g : ℤ) (hq : 0 < q) (hg : 0 < g) :
    let B := (Q.twoComponentCore R g hg).positiveBorder q q hq hq
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.twoComponentContext R q q g hq hq hg).schur) =
      (-1 : CompleteRing) ^ (p + r + 3) *
        ((Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur) := by
  dsimp only
  simp only [twoComponentContext, shifted_schur]
  rw [positiveBorder_tied_first_derivative, twoComponentCore_extendTop_schur,
    twoComponentCore_extendBottom_schur]

/-- The full tied marker is nonzero, including equal old factors; coefficient-one
normalization excludes an opposite-sign cancellation of the two actual Schur functions. -/
theorem two_component_tied_marker_ne_zero
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected) (q : ℤ) (hq : 0 < q) :
    (Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur ≠ 0 := by
  by_cases he : Q.schur = R.schur
  · have hf : (Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur =
        Q.schur * ((Q.extendTop q hq).schur + (R.extendBottom q hq).schur) := by
      rw [← he]
      ring
    rw [hf]
    exact mul_ne_zero Q.schur_ne_zero
      (schur_add_schur_ne_zero (Q.extendTop q hq) (R.extendBottom q hq))
  · intro hz
    have hp : Prime Q.schur :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hQ)
    have hsum : Q.schur ∣ (Q.extendTop q hq).schur * R.schur +
        Q.schur * (R.extendBottom q hq).schur := by
      rw [hz]
      exact dvd_zero _
    have hfirst : Q.schur ∣ (Q.extendTop q hq).schur * R.schur := by
      have hh := dvd_sub hsum (dvd_mul_right Q.schur (R.extendBottom q hq).schur)
      simpa only [add_sub_cancel_right] using hh
    obtain ht | hr := hp.dvd_mul.mp hfirst
    · exact Q.endpoint_old_factor_not_dvd_top hQ q hq ht
    · exact he (Q.schur_eq_of_connected_dvd R hQ hR hr)

/-- For distinct old factors, strict and tied markers have their stated exact
divisibility pattern; no profile assumption is made on endpoint representatives. -/
theorem two_component_marker_divisibility_distinct
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hne : Q.schur ≠ R.schur)
    (q : ℤ) (hq : 0 < q) :
    (¬ Q.schur ∣ (Q.extendTop q hq).schur * R.schur) ∧
      (R.schur ∣ (Q.extendTop q hq).schur * R.schur) ∧
      (Q.schur ∣ Q.schur * (R.extendBottom q hq).schur) ∧
      (¬ R.schur ∣ Q.schur * (R.extendBottom q hq).schur) ∧
      (¬ Q.schur ∣ (Q.extendTop q hq).schur * R.schur +
        Q.schur * (R.extendBottom q hq).schur) ∧
      (¬ R.schur ∣ (Q.extendTop q hq).schur * R.schur +
        Q.schur * (R.extendBottom q hq).schur) := by
  have hpQ : Prime Q.schur :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hQ)
  have hpR : Prime R.schur :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (R.schur_irreducible hR)
  have hnQR : ¬ Q.schur ∣ R.schur := by
    intro h
    exact hne (Q.schur_eq_of_connected_dvd R hQ hR h)
  have hnRQ : ¬ R.schur ∣ Q.schur := by
    intro h
    exact hne (R.schur_eq_of_connected_dvd Q hR hQ h).symm
  have htop : ¬ Q.schur ∣ (Q.extendTop q hq).schur * R.schur := by
    intro h
    obtain h | h := hpQ.dvd_mul.mp h
    · exact Q.endpoint_old_factor_not_dvd_top hQ q hq h
    · exact hnQR h
  have hbottom : ¬ R.schur ∣ Q.schur * (R.extendBottom q hq).schur := by
    intro h
    obtain h | h := hpR.dvd_mul.mp h
    · exact hnRQ h
    · exact R.endpoint_old_factor_not_dvd_bottom hR q hq h
  refine ⟨htop, dvd_mul_left _ _, dvd_mul_right _ _, hbottom, ?_, ?_⟩
  · intro h
    apply htop
    have hh := dvd_sub h (dvd_mul_right Q.schur (R.extendBottom q hq).schur)
    simpa only [add_sub_cancel_right] using hh
  · intro h
    apply hbottom
    have hh := dvd_sub h (dvd_mul_left R.schur (Q.extendTop q hq).schur)
    simpa only [add_sub_cancel_left] using hh

/-- The full top endpoint coefficient is the old signed maximal cofactor. -/
theorem endpoint_top_corner_derivative (Q : BetaDiagram (p + 1))
    (q : ℤ) (hq : 0 < q) :
    MvPolynomial.pderiv (Q.extendTop q hq).borderLargestGenerator (Q.extendTop q hq).schur =
      (-1 : CompleteRing) ^ p * Q.cornerPolynomial := by
  have hc : (Q.extendTop q hq).cornerPolynomial = Q.cornerPolynomial := by
    unfold cornerPolynomial
    congr 1
  have hd := (Q.extendTop q hq).pderiv_schur_largest
  change MvPolynomial.pderiv (Q.extendTop q hq).borderLargestGenerator
    (Q.extendTop q hq).schur = (Q.extendTop q hq).cornerCoefficient at hd
  simpa only [cornerCoefficient, hc] using hd

/-- The bottom endpoint has the same old signed maximal cofactor. -/
theorem endpoint_bottom_corner_derivative (Q : BetaDiagram (p + 1))
    (q : ℤ) (hq : 0 < q) :
    MvPolynomial.pderiv (Q.extendBottom q hq).borderLargestGenerator (Q.extendBottom q hq).schur =
      (-1 : CompleteRing) ^ p * Q.cornerPolynomial := by
  have hc : (Q.extendBottom q hq).cornerPolynomial = Q.cornerPolynomial := by
    unfold cornerPolynomial
    congr 1
    apply Matrix.ext
    intro i j
    simp only [cornerBoard, betaBoard, Matrix.of_apply, extendBottom,
      Fin.castSucc_ne_last, ite_false]
  have hd := (Q.extendBottom q hq).pderiv_schur_largest
  change MvPolynomial.pderiv (Q.extendBottom q hq).borderLargestGenerator
    (Q.extendBottom q hq).schur = (Q.extendBottom q hq).cornerCoefficient at hd
  simpa only [cornerCoefficient, hc] using hd

/-- With equal old factors, a tied marker contributes twice the common endpoint
leader, while an actual strict candidate contributes once.  The coefficient is
nonzero by the real old corner determinant. -/
theorem equal_factor_tied_sum_ne_top (Q R W : BetaDiagram (p + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur)
    (q : ℤ) (hq : 0 < q) :
    (Q.extendTop q hq).schur + (R.extendBottom q hq).schur ≠ (W.extendTop q hq).schur := by
  let k := (Q.extendTop q hq).borderLargestGenerator
  have hSR := Q.largestLabel_eq_of_schur_eq R hQ hR hQR
  have hSW := Q.largestLabel_eq_of_schur_eq W hQ hW hQW
  have hCR := Q.cornerPolynomial_eq_of_schur_eq R hQ hR hQR
  have hCW := Q.cornerPolynomial_eq_of_schur_eq W hQ hW hQW
  have hkR : k = (R.extendBottom q hq).borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) = ((R.extendBottom q hq).borderLargestGenerator.val : ℤ)
    simp only [k, borderLargestGenerator_int, border_extendTop_largestLabel,
      border_extendBottom_largestLabel, hSR]
  have hkW : k = (W.extendTop q hq).borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) = ((W.extendTop q hq).borderLargestGenerator.val : ℤ)
    simp only [k, borderLargestGenerator_int, border_extendTop_largestLabel, hSW]
  have hRderiv : MvPolynomial.pderiv k (R.extendBottom q hq).schur =
      (-1 : CompleteRing) ^ p * Q.cornerPolynomial := by
    rw [hkR, endpoint_bottom_corner_derivative, ← hCR]
  have hWderiv : MvPolynomial.pderiv k (W.extendTop q hq).schur =
      (-1 : CompleteRing) ^ p * Q.cornerPolynomial := by
    rw [hkW, endpoint_top_corner_derivative, ← hCW]
  intro he
  have hd := congrArg (MvPolynomial.pderiv k) he
  rw [map_add, endpoint_top_corner_derivative, hRderiv, hWderiv] at hd
  have hz : (-1 : CompleteRing) ^ p * Q.cornerPolynomial = 0 := by
    linear_combination hd
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Q.cornerPolynomial_ne_zero hQ)) hz

theorem equal_factor_tied_sum_ne_bottom (Q R W : BetaDiagram (p + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur)
    (q : ℤ) (hq : 0 < q) :
    (Q.extendTop q hq).schur + (R.extendBottom q hq).schur ≠ (W.extendBottom q hq).schur := by
  have hRQr : R.rotate.schur = Q.rotate.schur :=
    R.rotate_schur.trans (hQR.symm.trans Q.rotate_schur.symm)
  have hRWr : R.rotate.schur = W.rotate.schur :=
    R.rotate_schur.trans (hQR.symm.trans (hQW.trans W.rotate_schur.symm))
  have hn := equal_factor_tied_sum_ne_top R.rotate Q.rotate W.rotate
    (R.rotate_connected hR) (Q.rotate_connected hQ) (W.rotate_connected hW)
    hRQr hRWr q hq
  simpa only [rotate_extendTop_schur, rotate_extendBottom_schur, add_comm] using hn

/-- The actual first-block index in the canonical component order. -/
def twoLeftIndex (i : Fin (p + 1)) : Fin (p + r + 2) := ⟨i.val, by omega⟩

/-- The actual second-block index in the same order. -/
def twoRightIndex (j : Fin (r + 1)) : Fin (p + r + 2) := ⟨p + 1 + j.val, by omega⟩

theorem twoComponentCore_row_left (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) (i : Fin (p + 1)) :
    (Q.twoComponentCore R g hg).row (twoLeftIndex (r := r) i) =
      Q.row i + Q.componentOffset R g := by
  let horder : p + r + 2 = (p + 1) + (r + 1) := by omega
  have hi : Fin.cast horder (twoLeftIndex (r := r) i) = i.castAdd (r + 1) := by
    apply Fin.ext
    rfl
  change (Q.separatedComponents R g hg).row (Fin.cast horder (twoLeftIndex i)) = _
  rw [hi]
  simp only [separatedComponents, Fin.append_left]

theorem twoComponentCore_col_left (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) (i : Fin (p + 1)) :
    (Q.twoComponentCore R g hg).col (twoLeftIndex (r := r) i) =
      Q.col i + Q.componentOffset R g := by
  let horder : p + r + 2 = (p + 1) + (r + 1) := by omega
  have hi : Fin.cast horder (twoLeftIndex (r := r) i) = i.castAdd (r + 1) := by
    apply Fin.ext
    rfl
  change (Q.separatedComponents R g hg).col (Fin.cast horder (twoLeftIndex i)) = _
  rw [hi]
  simp only [separatedComponents, Fin.append_left]

theorem twoComponentCore_row_right (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) (j : Fin (r + 1)) :
    (Q.twoComponentCore R g hg).row (twoRightIndex (p := p) j) = R.row j := by
  let horder : p + r + 2 = (p + 1) + (r + 1) := by omega
  have hj : Fin.cast horder (twoRightIndex (p := p) j) = j.natAdd (p + 1) := by
    apply Fin.ext
    rfl
  change (Q.separatedComponents R g hg).row (Fin.cast horder (twoRightIndex j)) = _
  rw [hj]
  simp only [separatedComponents, Fin.append_right]

theorem twoComponentCore_col_right (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (g : ℤ) (hg : 0 < g) (j : Fin (r + 1)) :
    (Q.twoComponentCore R g hg).col (twoRightIndex (p := p) j) = R.col j := by
  let horder : p + r + 2 = (p + 1) + (r + 1) := by omega
  have hj : Fin.cast horder (twoRightIndex (p := p) j) = j.natAdd (p + 1) := by
    apply Fin.ext
    rfl
  change (Q.separatedComponents R g hg).col (Fin.cast horder (twoRightIndex j)) = _
  rw [hj]
  simp only [separatedComponents, Fin.append_right]

/-- The new top row in `eq:two-component-lists`. -/
theorem twoComponentContext_row_zero (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).row 0 =
      Q.row 0 + Q.componentOffset R g + u + v - R.col (Fin.last r) := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row 0 +
    (v - R.col (Fin.last r)) = _
  rw [positiveBorder_row_zero]
  have h0 : (0 : Fin (p + r + 2)) = twoLeftIndex (r := r) (0 : Fin (p + 1)) := rfl
  rw [h0, twoComponentCore_row_left]
  ring

theorem twoComponentContext_row_left (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i : Fin (p + 1)) :
    (Q.twoComponentContext R u v g hu hv hg).row (twoLeftIndex (r := r) i).succ =
      Q.row i + Q.componentOffset R g + v - R.col (Fin.last r) := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row (twoLeftIndex i).succ +
    (v - R.col (Fin.last r)) = _
  rw [positiveBorder_row_succ, twoComponentCore_row_left]
  ring

theorem twoComponentContext_col_left (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i : Fin (p + 1)) :
    (Q.twoComponentContext R u v g hu hv hg).col (twoLeftIndex (r := r) i).castSucc =
      Q.col i + Q.componentOffset R g + v - R.col (Fin.last r) := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col (twoLeftIndex i).castSucc +
    (v - R.col (Fin.last r)) = _
  rw [positiveBorder_col_castSucc, twoComponentCore_col_left]
  ring

theorem twoComponentContext_row_right (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (j : Fin (r + 1)) :
    (Q.twoComponentContext R u v g hu hv hg).row (twoRightIndex (p := p) j).succ =
      R.row j + v - R.col (Fin.last r) := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row (twoRightIndex j).succ +
    (v - R.col (Fin.last r)) = _
  rw [positiveBorder_row_succ, twoComponentCore_row_right]
  ring

theorem twoComponentContext_col_right (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (j : Fin (r + 1)) :
    (Q.twoComponentContext R u v g hu hv hg).col (twoRightIndex (p := p) j).castSucc =
      R.col j + v - R.col (Fin.last r) := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col (twoRightIndex j).castSucc +
    (v - R.col (Fin.last r)) = _
  rw [positiveBorder_col_castSucc, twoComponentCore_col_right]
  ring

@[simp] theorem twoComponentContext_col_last (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).col (Fin.last (p + r + 2)) = 0 := by
  have hj : twoRightIndex (p := p) (Fin.last r) = Fin.last (p + r + 1) := by
    apply Fin.ext
    simp only [twoRightIndex, Fin.val_last]
    omega
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col (Fin.last (p + r + 2)) +
    (v - R.col (Fin.last r)) = 0
  rw [positiveBorder_col_last, ← hj, twoComponentCore_col_right]
  ring

/-- The actual row index in the enlarged first component block. -/
def twoParentLeftRow (i : Fin (p + 2)) : Fin (p + r + 3) := ⟨i.val, by omega⟩

/-- The actual row index in the unchanged second component block. -/
def twoParentRightRow (j : Fin (r + 1)) : Fin (p + r + 3) := ⟨p + 2 + j.val, by omega⟩

theorem twoComponentContext_row_left_full (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i : Fin (p + 2)) :
    (Q.twoComponentContext R u v g hu hv hg).row (twoParentLeftRow (r := r) i) =
      (Q.positiveBorder u 1 hu (by norm_num)).row i +
        Q.componentOffset R g + v - R.col (Fin.last r) := by
  cases i using Fin.cases with
  | zero =>
    change (Q.twoComponentContext R u v g hu hv hg).row 0 = _
    rw [twoComponentContext_row_zero, positiveBorder_row_zero]
    ring
  | succ i =>
    have hi : twoParentLeftRow (r := r) i.succ = (twoLeftIndex (r := r) i).succ := by
      apply Fin.ext
      rfl
    rw [hi, twoComponentContext_row_left, positiveBorder_row_succ]

theorem twoComponentContext_row_right_full (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (j : Fin (r + 1)) :
    (Q.twoComponentContext R u v g hu hv hg).row (twoParentRightRow (p := p) j) =
      R.row j + v - R.col (Fin.last r) := by
  have hj : twoParentRightRow (p := p) j = (twoRightIndex (p := p) j).succ := by
    apply Fin.ext
    simp only [twoParentRightRow, twoRightIndex, Fin.val_succ]
    omega
  rw [hj, twoComponentContext_row_right]

/-- Deleting a left-block row agrees with deletion within the actual left list. -/
theorem two_left_row_deletion (i : Fin (p + 2)) (j : Fin (p + 1)) :
    (twoParentLeftRow (r := r) i).succAbove (twoLeftIndex (r := r) j) =
      twoParentLeftRow (r := r) (i.succAbove j) := by
  apply Fin.ext
  unfold Fin.succAbove
  simp only [twoParentLeftRow, twoLeftIndex, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> rfl

/-- The same deletion shifts each right-block row once, as its actual index requires. -/
theorem two_right_row_deletion (i : Fin (p + 2)) (j : Fin (r + 1)) :
    (twoParentLeftRow (r := r) i).succAbove (twoRightIndex (p := p) j) =
      twoParentRightRow (p := p) j := by
  rw [Fin.succAbove_of_le_castSucc _ _
    (show twoParentLeftRow (r := r) i ≤ (twoRightIndex (p := p) j).castSucc by
      simp only [twoParentLeftRow, twoRightIndex, Fin.le_def, Fin.val_castSucc]
      omega)]
  apply Fin.ext
  simp only [twoParentRightRow, twoRightIndex, Fin.val_succ]
  omega

/-- The actual connected parent's complementary diagonal is positive. -/
theorem twoComponentContext_positiveCorner (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).PositiveCorner := by
  intro i
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col i.castSucc +
      (v - R.col (Fin.last r)) <
    ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row i.succ +
      (v - R.col (Fin.last r))
  have hh := (Q.twoComponentCore R g hg).positiveBorder_positiveCorner u v hu hv i
  omega

/-- Each actual left-block last-column cofactor has its full `A_i s_R` product,
obtained from literal beta lists and a genuine separated-component determinant. -/
theorem twoComponentContext_left_cofactor_product
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i : Fin (p + 2)) :
    let P := Q.twoComponentContext R u v g hu hv hg
    (P.matrix.submatrix (twoParentLeftRow (r := r) i).succAbove
      (Fin.last (p + r + 2)).succAbove).det =
      (Q.twoComponentLeftMinor u hu i).schur * R.schur := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let Ai := Q.twoComponentLeftMinor u hu i
  let hp := Q.twoComponentContext_positiveCorner R u v g hu hv hg
  let M := P.lastColumnDiagram hp (twoParentLeftRow (r := r) i)
  let B := Ai.twoComponentCore R g hg
  have hoffset : Ai.componentOffset R g = Q.componentOffset R g := by
    change R.row 0 + g -
      (Q.positiveBorder u 1 hu (by norm_num)).col (Fin.last p).castSucc =
      R.row 0 + g - Q.col (Fin.last p)
    rw [positiveBorder_col_castSucc]
  have hT : M.TranslationEquivalent B := by
    refine ⟨v - R.col (Fin.last r), ?_, ?_⟩
    · intro j
      by_cases hj : j.val < p + 1
      · let a : Fin (p + 1) := ⟨j.val, hj⟩
        have he : j = twoLeftIndex (r := r) a := by apply Fin.ext; rfl
        change P.row ((twoParentLeftRow (r := r) i).succAbove j) =
          B.row j + (v - R.col (Fin.last r))
        rw [he, two_left_row_deletion, twoComponentContext_row_left_full,
          twoComponentCore_row_left, hoffset]
        change (Q.positiveBorder u 1 hu (by norm_num)).row (i.succAbove a) +
            Q.componentOffset R g + v - R.col (Fin.last r) =
          (Q.positiveBorder u 1 hu (by norm_num)).row (i.succAbove a) +
            Q.componentOffset R g + (v - R.col (Fin.last r))
        ring
      · let a : Fin (r + 1) := ⟨j.val - (p + 1), by omega⟩
        have he : j = twoRightIndex (p := p) a := by
          apply Fin.ext
          simp only [a, twoRightIndex]
          omega
        change P.row ((twoParentLeftRow (r := r) i).succAbove j) =
          B.row j + (v - R.col (Fin.last r))
        rw [he, two_right_row_deletion, twoComponentContext_row_right_full,
          twoComponentCore_row_right]
        ring
    · intro j
      by_cases hj : j.val < p + 1
      · let a : Fin (p + 1) := ⟨j.val, hj⟩
        have he : j = twoLeftIndex (r := r) a := by apply Fin.ext; rfl
        change P.col j.castSucc = B.col j + (v - R.col (Fin.last r))
        rw [he, twoComponentContext_col_left, twoComponentCore_col_left, hoffset]
        change Q.col a + Q.componentOffset R g + v - R.col (Fin.last r) =
          (Q.positiveBorder u 1 hu (by norm_num)).col a.castSucc +
            Q.componentOffset R g + (v - R.col (Fin.last r))
        rw [positiveBorder_col_castSucc]
        ring
      · let a : Fin (r + 1) := ⟨j.val - (p + 1), by omega⟩
        have he : j = twoRightIndex (p := p) a := by
          apply Fin.ext
          simp only [a, twoRightIndex]
          omega
        change P.col j.castSucc = B.col j + (v - R.col (Fin.last r))
        rw [he, twoComponentContext_col_right, twoComponentCore_col_right]
        ring
  dsimp only
  rw [← lastColumnDiagram_schur P hp (twoParentLeftRow (r := r) i)]
  exact hT.schur_eq.trans (Ai.twoComponentCore_schur R g hg)

private theorem two_parent_sum (f : Fin (p + r + 3) → CompleteRing) :
    (∑ i, f i) =
      (∑ i : Fin (p + 2), f (twoParentLeftRow (r := r) i)) +
        ∑ j : Fin (r + 1), f (twoParentRightRow (p := p) j) := by
  let horder : (p + 2) + (r + 1) = p + r + 3 := by omega
  rw [← Fin.sum_congr' f horder, Fin.sum_univ_add]
  congr 1

/-- The entire initial last-column part, expressed using actual left minors and
the old right factor.  It includes every left-block row, not only two terms. -/
noncomputable def twoComponentInitialColumnPart
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) : CompleteRing :=
  ∑ i : Fin (p + 2), (-1 : CompleteRing) ^ (i.val + (p + r + 2)) *
    complete ((Q.positiveBorder u 1 hu (by norm_num)).row i +
      Q.componentOffset R g + v - R.col (Fin.last r)) *
    ((Q.twoComponentLeftMinor u hu i).schur * R.schur)

/-- The complementary right-block last-column part contains the actual unsigned
last-column diagrams, with no proposed context or cofactor certificate. -/
noncomputable def twoComponentResidualColumnPart
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) : CompleteRing :=
  let P := Q.twoComponentContext R u v g hu hv hg
  ∑ j : Fin (r + 1), (-1 : CompleteRing) ^ ((p + 2 + j.val) + (p + r + 2)) *
    complete (R.row j + v - R.col (Fin.last r)) *
    (P.lastColumnDiagram (Q.twoComponentContext_positiveCorner R u v g hu hv hg)
      (twoParentRightRow (p := p) j)).schur

/-- Full actual Laplace expansion, separating the shared initial block from the
part used by `eq:two-component-separator`. -/
theorem twoComponentContext_column_expansion
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).schur =
      Q.twoComponentInitialColumnPart R u v g hu hv hg +
        Q.twoComponentResidualColumnPart R u v g hu hv hg := by
  let P := Q.twoComponentContext R u v g hu hv hg
  change P.matrix.det = _
  rw [Matrix.det_succ_column P.matrix (Fin.last (p + r + 2)), two_parent_sum]
  unfold twoComponentInitialColumnPart twoComponentResidualColumnPart
  apply congrArg₂ (fun x y : CompleteRing => x + y)
  · apply Finset.sum_congr rfl
    intro i hi
    have hentry : P.matrix (twoParentLeftRow (r := r) i) (Fin.last (p + r + 2)) =
        complete ((Q.positiveBorder u 1 hu (by norm_num)).row i +
          Q.componentOffset R g + v - R.col (Fin.last r)) := by
      change complete (P.row (twoParentLeftRow i) - P.col (Fin.last (p + r + 2))) = _
      rw [twoComponentContext_col_last, twoComponentContext_row_left_full, sub_zero]
    change (-1 : CompleteRing) ^ ((twoParentLeftRow (r := r) i).val + (p + r + 2)) *
        P.matrix (twoParentLeftRow i) (Fin.last (p + r + 2)) *
        (P.matrix.submatrix (twoParentLeftRow i).succAbove
          (Fin.last (p + r + 2)).succAbove).det = _
    rw [hentry, twoComponentContext_left_cofactor_product]
    rfl
  · apply Finset.sum_congr rfl
    intro j hj
    have hentry : P.matrix (twoParentRightRow (p := p) j) (Fin.last (p + r + 2)) =
        complete (R.row j + v - R.col (Fin.last r)) := by
      change complete (P.row (twoParentRightRow j) - P.col (Fin.last (p + r + 2))) = _
      rw [twoComponentContext_col_last, twoComponentContext_row_right_full, sub_zero]
    change (-1 : CompleteRing) ^ ((twoParentRightRow (p := p) j).val + (p + r + 2)) *
        P.matrix (twoParentRightRow j) (Fin.last (p + r + 2)) *
        (P.matrix.submatrix (twoParentRightRow j).succAbove
          (Fin.last (p + r + 2)).succAbove).det = _
    rw [hentry, lastColumnDiagram_schur]
    rfl

/-- The literal last-column remainder after suppressing the entire shared left
block.  Its determinant is proved to equal the actual Laplace remainder. -/
noncomputable def twoComponentResidualMatrix
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    Matrix (Fin (p + r + 3)) (Fin (p + r + 3)) CompleteRing :=
  let P := Q.twoComponentContext R u v g hu hv hg
  P.matrix.updateCol (Fin.last (p + r + 2))
    (fun i => if i.val < p + 2 then 0 else P.matrix i (Fin.last (p + r + 2)))

/-- Last-column complementary matrices are unchanged by that exact column operation. -/
theorem twoComponentResidualMatrix_minor
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (i : Fin (p + r + 3)) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg).submatrix i.succAbove
      (Fin.last (p + r + 2)).succAbove =
      (Q.twoComponentContext R u v g hu hv hg).matrix.submatrix i.succAbove
        (Fin.last (p + r + 2)).succAbove := by
  apply Matrix.ext
  intro a b
  simp only [twoComponentResidualMatrix, Matrix.submatrix_apply,
    Matrix.updateCol_apply, Fin.succAbove_ne, ite_false]

/-- The filtered matrix is precisely the actual residual polynomial, not a
replacement determinant supplied as an assumption. -/
theorem twoComponentResidualMatrix_det
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg).det =
      Q.twoComponentResidualColumnPart R u v g hu hv hg := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let M := Q.twoComponentResidualMatrix R u v g hu hv hg
  rw [Matrix.det_succ_column M (Fin.last (p + r + 2)), two_parent_sum]
  have hleft : ∀ i : Fin (p + 2),
      M (twoParentLeftRow (r := r) i) (Fin.last (p + r + 2)) = 0 := by
    intro i
    simp only [M, twoComponentResidualMatrix, Matrix.updateCol_apply, ite_true,
      twoParentLeftRow, i.isLt]
  simp only [hleft, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  unfold twoComponentResidualColumnPart
  apply Finset.sum_congr rfl
  intro j hj
  have hright : M (twoParentRightRow (p := p) j) (Fin.last (p + r + 2)) =
      P.matrix (twoParentRightRow (p := p) j) (Fin.last (p + r + 2)) := by
    simp only [M, twoComponentResidualMatrix, Matrix.updateCol_apply, ite_true]
    rw [ite_eq_right (show ¬(twoParentRightRow (p := p) j).val < p + 2 by
      simp only [twoParentRightRow]; omega)]
  rw [hright, twoComponentResidualMatrix_minor]
  have hentry : P.matrix (twoParentRightRow (p := p) j) (Fin.last (p + r + 2)) =
      complete (R.row j + v - R.col (Fin.last r)) := by
    change complete (P.row (twoParentRightRow (p := p) j) - P.col (Fin.last (p + r + 2))) = _
    rw [twoComponentContext_col_last, twoComponentContext_row_right_full, sub_zero]
  change (-1 : CompleteRing) ^ ((twoParentRightRow (p := p) j).val + (p + r + 2)) *
      P.matrix (twoParentRightRow (p := p) j) (Fin.last (p + r + 2)) *
      (P.matrix.submatrix (twoParentRightRow (p := p) j).succAbove
        (Fin.last (p + r + 2)).succAbove).det = _
  rw [hentry, lastColumnDiagram_schur]
  rfl

/-- The initial part depends only on the common parent span, the oriented left
component, the top margin, and the old right function. -/
theorem twoComponentInitialColumnPart_eq_of_span
    (Q : BetaDiagram (p + 1)) (R W : BetaDiagram (r + 1))
    (hR : R.Connected) (hW : W.Connected) (hRW : R.schur = W.schur)
    (u vm vp gm gp : ℤ)
    (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp) (hgm : 0 < gm) (hgp : 0 < gp)
    (hspan : (Q.twoComponentCore R gm hgm).largestLabel + u + vm =
      (Q.twoComponentCore W gp hgp).largestLabel + u + vp) :
    Q.twoComponentInitialColumnPart R u vm gm hu hvm hgm =
      Q.twoComponentInitialColumnPart W u vp gp hu hvp hgp := by
  have hs := R.largestLabel_eq_of_schur_eq W hR hW hRW
  rw [twoComponentCore_span, twoComponentCore_span] at hspan
  have hsum : gm + vm = gp + vp := by omega
  have hoffset : Q.componentOffset R gm + vm - R.col (Fin.last r) =
      Q.componentOffset W gp + vp - W.col (Fin.last r) := by
    unfold componentOffset
    change R.row 0 - R.col (Fin.last r) = W.row 0 - W.col (Fin.last r) at hs
    omega
  unfold twoComponentInitialColumnPart
  apply Finset.sum_congr rfl
  intro i hi
  rw [hRW]
  have hlabel : (Q.positiveBorder u 1 hu (by norm_num)).row i +
      Q.componentOffset R gm + vm - R.col (Fin.last r) =
      (Q.positiveBorder u 1 hu (by norm_num)).row i +
      Q.componentOffset W gp + vp - W.col (Fin.last r) := by omega
  rw [hlabel]

/-- Equality of the shared initial part reduces the full actual comparison to
the two literal residual determinants used by the margin separator. -/
theorem twoComponentContext_difference_residual
    (Q : BetaDiagram (p + 1)) (R W : BetaDiagram (r + 1))
    (hR : R.Connected) (hW : W.Connected) (hRW : R.schur = W.schur)
    (u vm vp gm gp : ℤ)
    (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp) (hgm : 0 < gm) (hgp : 0 < gp)
    (hspan : (Q.twoComponentCore R gm hgm).largestLabel + u + vm =
      (Q.twoComponentCore W gp hgp).largestLabel + u + vp) :
    (Q.twoComponentContext W u vp gp hu hvp hgp).schur -
        (Q.twoComponentContext R u vm gm hu hvm hgm).schur =
      (Q.twoComponentResidualMatrix W u vp gp hu hvp hgp).det -
        (Q.twoComponentResidualMatrix R u vm gm hu hvm hgm).det := by
  rw [twoComponentContext_column_expansion, twoComponentContext_column_expansion,
    twoComponentResidualMatrix_det, twoComponentResidualMatrix_det,
    twoComponentInitialColumnPart_eq_of_span Q R W hR hW hRW
      u vm vp gm gp hu hvm hvp hgm hgp hspan]
  ring

theorem twoComponentContext_span (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).largestLabel =
      Q.largestLabel + R.largestLabel + g + u + v := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row 0 +
      (v - R.col (Fin.last r)) -
    (((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col (Fin.last (p + r + 2)) +
      (v - R.col (Fin.last r))) = _
  rw [positiveBorder_row_zero, positiveBorder_col_last]
  have hs := Q.twoComponentCore_span R g hg
  change (Q.twoComponentCore R g hg).row 0 -
    (Q.twoComponentCore R g hg).col (Fin.last (p + r + 1)) =
      Q.largestLabel + R.largestLabel + g at hs
  linarith

/-- The largest nonlast-column index of the actual context. -/
theorem twoComponentContext_upper_separator (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).row 0 -
      (Q.twoComponentContext R u v g hu hv hg).col (Fin.last (p + r + 1)).castSucc =
      Q.largestLabel + R.largestLabel + g + u := by
  change ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).row 0 +
      (v - R.col (Fin.last r)) -
    (((Q.twoComponentCore R g hg).positiveBorder u v hu hv).col
      (Fin.last (p + r + 1)).castSucc + (v - R.col (Fin.last r))) = _
  rw [positiveBorder_row_zero, positiveBorder_col_castSucc]
  have hs := Q.twoComponentCore_span R g hg
  change (Q.twoComponentCore R g hg).row 0 -
    (Q.twoComponentCore R g hg).col (Fin.last (p + r + 1)) =
      Q.largestLabel + R.largestLabel + g at hs
  linarith

/-- A generator above both literal residual levels is absent from the residual
determinant; all left-block last-column entries were exactly removed. -/
theorem twoComponentResidualMatrix_above_levels_zero
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (k : ℕ+) (hupper : Q.largestLabel + R.largestLabel + g + u < (k.val : ℤ))
    (hlower : R.largestLabel + v < (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.twoComponentResidualMatrix R u v g hu hv hg).det = 0 := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let M := Q.twoComponentResidualMatrix R u v g hu hv hg
  apply pderiv_det_eq_zero
  intro i j
  by_cases hjlast : j = Fin.last (p + r + 2)
  · subst j
    simp only [twoComponentResidualMatrix, Matrix.updateCol_apply, ite_true]
    change MvPolynomial.pderiv k
      (if i.val < p + 2 then 0 else P.matrix i (Fin.last (p + r + 2))) = 0
    by_cases hi : i.val < p + 2
    · rw [ite_eq_left hi, map_zero]
    · rw [ite_eq_right hi]
      let a : Fin (r + 1) := ⟨i.val - (p + 2), by omega⟩
      have he : i = twoParentRightRow (p := p) a := by
        apply Fin.ext
        simp only [a, twoParentRightRow]
        omega
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      change k ∉ (complete (P.row i - P.col (Fin.last (p + r + 2)))).vars
      rw [he, twoComponentContext_row_right_full, twoComponentContext_col_last, sub_zero,
        mem_vars_complete_iff]
      have hr := R.row_strictAnti.antitone (Fin.zero_le a)
      change ¬ (k.val : ℤ) = R.row a + v - R.col (Fin.last r)
      change R.row 0 - R.col (Fin.last r) + v < (k.val : ℤ) at hlower
      omega
  · have hjle : j ≤ (Fin.last (p + r + 1)).castSucc := by
      have hh := Fin.lt_last_iff_ne_last.mpr hjlast
      simp only [Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
      omega
    have hc := P.col_strictAnti.antitone hjle
    have hr := P.row_strictAnti.antitone (Fin.zero_le i)
    have hl := Q.twoComponentContext_upper_separator R u v g hu hv hg
    change P.row 0 - P.col (Fin.last (p + r + 1)).castSucc =
      Q.largestLabel + R.largestLabel + g + u at hl
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    change k ∉ (M i j).vars
    have he : M i j = P.matrix i j := by
      simp only [M, twoComponentResidualMatrix, Matrix.updateCol_apply, hjlast, ite_false]
      rfl
    rw [he]
    change k ∉ (complete (P.row i - P.col j)).vars
    rw [mem_vars_complete_iff]
    change ¬ (k.val : ℤ) = P.row i - P.col j
    omega

/-- The bottom separator's actual complementary diagram is connected.  Its
left subdiagonal consists of old nonempty diagonal rows, while its right
subdiagonal consists of the produced strict overlaps of the right core. -/
theorem twoComponent_separator_diagram_connected
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hR : R.Connected) (hZR : R.ZeroFree)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((Q.twoComponentContext R u v g hu hv hg).lastColumnDiagram
      (Q.twoComponentContext_positiveCorner R u v g hu hv hg)
      (twoParentRightRow (p := p) (0 : Fin (r + 1)))).Connected := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let row := twoParentRightRow (p := p) (0 : Fin (r + 1))
  refine ⟨by omega, ?_⟩
  intro j hj
  change P.col j.castSucc ≤ P.row (row.succAbove ⟨j.val + 1, hj⟩)
  by_cases hleft : j.val < p + 1
  · let a : Fin (p + 1) := ⟨j.val, hleft⟩
    have hjidx : j = twoLeftIndex (r := r) a := by apply Fin.ext; rfl
    have hrow : row.succAbove (⟨j.val + 1, hj⟩ : Fin (p + r + 2)) =
        (twoLeftIndex (r := r) a).succ := by
      rw [Fin.succAbove_of_castSucc_lt _ _
        (show (⟨j.val + 1, hj⟩ : Fin (p + r + 2)).castSucc < row by
          simp only [row, twoParentRightRow, Fin.lt_def, Fin.val_castSucc, Fin.val_zero]
          omega)]
      apply Fin.ext
      simp only [twoLeftIndex, a, Fin.val_castSucc, Fin.val_succ]
    rw [hrow, hjidx, twoComponentContext_col_left, twoComponentContext_row_left]
    have hd := Q.row_nonempty a
    omega
  · let a : Fin (r + 1) := ⟨j.val - (p + 1), by omega⟩
    let b : Fin (r + 1) := ⟨a.val + 1, by
      dsimp [a]
      omega⟩
    have hjidx : j = twoRightIndex (p := p) a := by
      apply Fin.ext
      simp only [twoRightIndex, a]
      omega
    have hrow : row.succAbove (⟨j.val + 1, hj⟩ : Fin (p + r + 2)) =
        twoParentRightRow (p := p) b := by
      rw [Fin.succAbove_of_le_castSucc _ _
        (show row ≤ (⟨j.val + 1, hj⟩ : Fin (p + r + 2)).castSucc by
          simp only [row, twoParentRightRow, Fin.le_def, Fin.val_zero, Fin.val_castSucc]
          omega)]
      apply Fin.ext
      simp only [twoParentRightRow, b, a, Fin.val_succ]
      omega
    rw [hrow, hjidx, twoComponentContext_col_right, twoComponentContext_row_right_full]
    have ho : R.col a ≤ R.row b := hR.2 a (by
      dsimp [a]
      omega)
    have hn := hZR b a
    omega

/-- At a strict upper residual maximum the only surviving generator occurrence
is the actual top-row penultimate-column site. -/
theorem twoComponentResidualMatrix_top_private
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (k : ℕ+) (hk : (k.val : ℤ) = Q.largestLabel + R.largestLabel + g + u)
    (hside : R.largestLabel + v < (k.val : ℤ)) :
    let M := Q.twoComponentResidualMatrix R u v g hu hv hg
    MvPolynomial.pderiv k M.det =
      (-1 : CompleteRing) ^ (p + r + 1) *
        (M.submatrix Fin.succ (Fin.last (p + r + 1)).castSucc.succAbove).det := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let M := Q.twoComponentResidualMatrix R u v g hu hv hg
  let col : Fin (p + r + 3) := (Fin.last (p + r + 1)).castSucc
  have hl := Q.twoComponentContext_upper_separator R u v g hu hv hg
  change P.row 0 - P.col col = Q.largestLabel + R.largestLabel + g + u at hl
  have hentry : M 0 col = (MvPolynomial.X k : CompleteRing) := by
    have hc : col ≠ Fin.last (p + r + 2) := Fin.castSucc_ne_last _
    change (P.matrix.updateCol (Fin.last (p + r + 2))
      (fun i => if i.val < p + 2 then 0 else P.matrix i (Fin.last (p + r + 2)))) 0 col = _
    rw [Matrix.updateCol_apply, ite_eq_right hc]
    change complete (P.row 0 - P.col col) = _
    rw [hl, ← hk]
    exact complete_nat k
  have hprivate : ∀ i j, i ≠ 0 ∨ j ≠ col → k ∉ (M i j).vars := by
    intro i j hsite
    by_cases hjlast : j = Fin.last (p + r + 2)
    · subst j
      simp only [M, twoComponentResidualMatrix, Matrix.updateCol_apply, ite_true]
      change k ∉ (if i.val < p + 2 then 0 else P.matrix i (Fin.last (p + r + 2))).vars
      by_cases hi : i.val < p + 2
      · rw [ite_eq_left hi]
        simp
      · rw [ite_eq_right hi]
        let a : Fin (r + 1) := ⟨i.val - (p + 2), by omega⟩
        have he : i = twoParentRightRow (p := p) a := by
          apply Fin.ext
          simp only [a, twoParentRightRow]
          omega
        change k ∉ (complete (P.row i - P.col (Fin.last (p + r + 2)))).vars
        rw [he, twoComponentContext_row_right_full, twoComponentContext_col_last, sub_zero,
          mem_vars_complete_iff]
        have hr := R.row_strictAnti.antitone (Fin.zero_le a)
        change ¬ (k.val : ℤ) = R.row a + v - R.col (Fin.last r)
        change R.row 0 - R.col (Fin.last r) + v < (k.val : ℤ) at hside
        omega
    · have he : M i j = P.matrix i j := by
        simp only [M, twoComponentResidualMatrix, Matrix.updateCol_apply, hjlast, ite_false]
        rfl
      rw [he]
      change k ∉ (complete (P.row i - P.col j)).vars
      rw [mem_vars_complete_iff]
      intro h
      change (k.val : ℤ) = P.row i - P.col j at h
      have hjle : j ≤ col := by
        have hh := Fin.lt_last_iff_ne_last.mpr hjlast
        simp only [col, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
        omega
      have hc := P.col_strictAnti.antitone hjle
      have hr := P.row_strictAnti.antitone (Fin.zero_le i)
      by_cases hi : i = 0
      · subst i
        have hn : j ≠ col := by simpa using hsite
        have hc' := P.col_strictAnti (lt_of_le_of_ne hjle hn)
        omega
      · have hr' := P.row_strictAnti (Fin.pos_iff_ne_zero.mpr hi)
        omega
  dsimp only
  have hd := pderiv_det_private M k 0 col hentry hprivate
  simpa only [M, col, Fin.val_zero, Fin.val_castSucc, Fin.val_last, zero_add,
    Fin.succAbove_zero] using hd

private def topCofactorIndex (p r : ℕ) :
    Fin (p + 1) ⊕ Fin (r + 1) ≃ Fin (p + r + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem topCofactorIndex_inl (i : Fin (p + 1)) :
    ((topCofactorIndex p r) (Sum.inl i)).val = i.val := by simp [topCofactorIndex]

private theorem topCofactorIndex_inr (j : Fin (r + 1)) :
    ((topCofactorIndex p r) (Sum.inr j)).val = p + 1 + j.val := by
  simp [topCofactorIndex, Fin.val_natAdd]

private theorem topColumn_val (k : Fin (p + r + 2)) :
    ((Fin.last (p + r + 1)).castSucc.succAbove k).val =
      if k.val < p + r + 1 then k.val else k.val + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last, Fin.val_succ]
  split_ifs <;> rfl

private theorem residual_apply_of_ne (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (a b : Fin (p + r + 3))
    (hb : b ≠ Fin.last (p + r + 2)) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg) a b =
      (Q.twoComponentContext R u v g hu hv hg).matrix a b := by
  simp only [twoComponentResidualMatrix, Matrix.updateCol_apply, hb, ite_false]

private theorem residual_apply_last (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (a : Fin (p + r + 3))
    (ha : p + 2 ≤ a.val) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg) a (Fin.last (p + r + 2)) =
      (Q.twoComponentContext R u v g hu hv hg).matrix a (Fin.last (p + r + 2)) := by
  have hn : ¬ a.val < p + 2 := by omega
  simp only [twoComponentResidualMatrix, Matrix.updateCol_apply, ite_true, hn, ite_false]

private theorem residual_entry_left (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i j : Fin (p + 1)) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg) (twoParentLeftRow (r := r) i.succ)
      (twoLeftIndex (r := r) j).castSucc = Q.matrix i j := by
  rw [residual_apply_of_ne Q R u v g hu hv hg _ _ (Fin.castSucc_ne_last _)]
  change complete ((Q.twoComponentContext R u v g hu hv hg).row (twoParentLeftRow i.succ) -
      (Q.twoComponentContext R u v g hu hv hg).col (twoLeftIndex j).castSucc) =
    complete (Q.row i - Q.col j)
  rw [twoComponentContext_row_left_full, twoComponentContext_col_left, positiveBorder_row_succ]
  apply congrArg complete
  ring

private theorem residual_entry_lower_left (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i : Fin (r + 1)) (j : Fin (p + 1)) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg) (twoParentRightRow (p := p) i)
      (twoLeftIndex (r := r) j).castSucc = 0 := by
  rw [residual_apply_of_ne Q R u v g hu hv hg _ _ (Fin.castSucc_ne_last _)]
  change complete ((Q.twoComponentContext R u v g hu hv hg).row (twoParentRightRow i) -
    (Q.twoComponentContext R u v g hu hv hg).col (twoLeftIndex j).castSucc) = 0
  rw [twoComponentContext_row_right_full, twoComponentContext_col_left]
  apply complete_of_neg
  have hQ := Q.col_strictAnti.antitone (Fin.le_last j)
  have hR := R.row_strictAnti.antitone (Fin.zero_le i)
  unfold componentOffset
  omega

private theorem residual_entry_right (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i j : Fin (r + 1))
    (hj : j ≠ Fin.last r) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg) (twoParentRightRow (p := p) i)
      (twoRightIndex (p := p) j).castSucc = (R.extendBottom v hv).matrix i j := by
  rw [residual_apply_of_ne Q R u v g hu hv hg _ _ (Fin.castSucc_ne_last _)]
  change complete ((Q.twoComponentContext R u v g hu hv hg).row (twoParentRightRow i) -
      (Q.twoComponentContext R u v g hu hv hg).col (twoRightIndex j).castSucc) =
    complete (R.row i - (R.extendBottom v hv).col j)
  rw [twoComponentContext_row_right_full, twoComponentContext_col_right]
  simp only [extendBottom, hj, ite_false]
  apply congrArg complete
  ring

private theorem residual_entry_right_last (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (i : Fin (r + 1)) :
    (Q.twoComponentResidualMatrix R u v g hu hv hg) (twoParentRightRow (p := p) i)
      (Fin.last (p + r + 2)) = (R.extendBottom v hv).matrix i (Fin.last r) := by
  rw [residual_apply_last Q R u v g hu hv hg _ (by
    simp only [twoParentRightRow]; omega)]
  change complete ((Q.twoComponentContext R u v g hu hv hg).row (twoParentRightRow i) -
      (Q.twoComponentContext R u v g hu hv hg).col (Fin.last (p + r + 2))) =
    complete (R.row i - (R.extendBottom v hv).col (Fin.last r))
  rw [twoComponentContext_row_right_full, twoComponentContext_col_last]
  simp only [sub_zero, extendBottom, ite_true]
  apply congrArg complete
  ring

private theorem det_eq_of_lower_left_zero {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (X : Matrix (a ⊕ b) (a ⊕ b) CompleteRing)
    (h : X.toBlocks₂₁ = 0) :
    X.det = X.toBlocks₁₁.det * X.toBlocks₂₂.det := by
  have hX := Matrix.fromBlocks_toBlocks X
  rw [h] at hX
  rw [← hX, Matrix.det_fromBlocks_zero₂₁]
  rfl

/-- The strict upper separator cofactor has its actual nonlinear-factor product. -/
theorem twoComponentResidualMatrix_top_cofactor
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    ((Q.twoComponentResidualMatrix R u v g hu hv hg).submatrix Fin.succ
      (Fin.last (p + r + 1)).castSucc.succAbove).det =
      Q.schur * (R.extendBottom v hv).schur := by
  have hrowR : ∀ i : Fin (r + 1), (topCofactorIndex p r (Sum.inr i)).succ =
      twoParentRightRow (p := p) i := by
    intro i
    apply Fin.ext
    rw [Fin.val_succ, topCofactorIndex_inr]
    simp only [twoParentRightRow]
    omega
  have hrowL : ∀ i : Fin (p + 1), (topCofactorIndex p r (Sum.inl i)).succ =
      twoParentLeftRow (r := r) i.succ := by
    intro i
    apply Fin.ext
    rw [Fin.val_succ, topCofactorIndex_inl]
    rfl
  have hcolL : ∀ j : Fin (p + 1),
      (Fin.last (p + r + 1)).castSucc.succAbove (topCofactorIndex p r (Sum.inl j)) =
        (twoLeftIndex (r := r) j).castSucc := by
    intro j
    have hlt : j.val < p + r + 1 := by omega
    apply Fin.ext
    simp only [topColumn_val, topCofactorIndex_inl, twoLeftIndex, Fin.val_castSucc, ite_eq_left hlt]
  have hcolR : ∀ j : Fin (r + 1), j ≠ Fin.last r →
      (Fin.last (p + r + 1)).castSucc.succAbove (topCofactorIndex p r (Sum.inr j)) =
        (twoRightIndex (p := p) j).castSucc := by
    intro j hj
    have hneq : j.val ≠ r := by intro h; exact hj (Fin.ext h)
    have hlt : p + 1 + j.val < p + r + 1 := by omega
    apply Fin.ext
    simp only [topColumn_val, topCofactorIndex_inr, twoRightIndex, Fin.val_castSucc, ite_eq_left hlt]
  have hcolLast : (Fin.last (p + r + 1)).castSucc.succAbove
      (topCofactorIndex p r (Sum.inr (Fin.last r))) = Fin.last (p + r + 2) := by
    apply Fin.ext
    rw [topColumn_val, topCofactorIndex_inr, Fin.val_last]
    rw [ite_eq_right (show ¬ p + 1 + r < p + r + 1 by omega)]
    simp only [Fin.val_last]
    omega
  rw [← Matrix.det_submatrix_equiv_self (topCofactorIndex p r)]
  refine (det_eq_of_lower_left_zero _ ?_).trans ?_
  · apply Matrix.ext
    intro i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    rw [hrowR i, hcolL j]
    exact residual_entry_lower_left Q R u v g hu hv hg i j
  · change _ * _ = Q.matrix.det * (R.extendBottom v hv).matrix.det
    apply congrArg₂ (fun x y : CompleteRing => x * y)
    · apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply]
      rw [hrowL i, hcolL j]
      exact residual_entry_left Q R u v g hu hv hg i j
    · apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply]
      by_cases hj : j = Fin.last r
      · subst j
        rw [hrowR i, hcolLast]
        exact residual_entry_right_last Q R u v g hu hv hg i
      · rw [hrowR i, hcolR j hj]
        exact residual_entry_right Q R u v g hu hv hg i j hj

private theorem ext_of_row_col {m : ℕ} {A B : BetaDiagram m}
    (hr : A.row = B.row) (hc : A.col = B.col) : A = B := by
  cases A
  cases B
  cases hr
  cases hc
  rfl

/-- The actual maximal corner with its produced two-block order. -/
def twoCutCore (D : BetaDiagram (p + r + 3)) (hP : D.PositiveCorner) :
    BetaDiagram ((p + 1) + (r + 1)) :=
  (D.cornerDiagram hP).reindexOrder (by omega)

private theorem componentOffset_cut (C : BetaDiagram ((p + 1) + (r + 1))) :
    C.betaPrefix.componentOffset C.suffix
      (C.betaPrefix.col (Fin.last p) - C.suffix.row 0) = 0 := by
  unfold componentOffset
  ring

/-- Rejoining the two actual restrictions at the actual cut returns the core. -/
theorem separatedComponents_cut (C : BetaDiagram ((p + 1) + (r + 1)))
    (hg : 0 < C.betaPrefix.col (Fin.last p) - C.suffix.row 0) :
    C.betaPrefix.separatedComponents C.suffix
      (C.betaPrefix.col (Fin.last p) - C.suffix.row 0) hg = C := by
  have hoff := componentOffset_cut C
  apply ext_of_row_col
  · funext i
    cases i using Fin.addCases (m := p + 1) (n := r + 1) with
    | left i =>
      simp only [separatedComponents, Fin.append_left]
      rw [hoff, add_zero]
      rfl
    | right i =>
      simp only [separatedComponents, Fin.append_right, suffix]
  · funext i
    cases i using Fin.addCases (m := p + 1) (n := r + 1) with
    | left i =>
      simp only [separatedComponents, Fin.append_left]
      rw [hoff, add_zero]
      rfl
    | right i =>
      simp only [separatedComponents, Fin.append_right, suffix]

private theorem twoComponentCore_cut_row (D : BetaDiagram (p + r + 3)) (hP : D.PositiveCorner)
    (hg : 0 < (D.twoCutCore hP).betaPrefix.col (Fin.last p) - (D.twoCutCore hP).suffix.row 0)
    (j : Fin (p + r + 2)) :
    ((D.twoCutCore hP).betaPrefix.twoComponentCore (D.twoCutCore hP).suffix
      ((D.twoCutCore hP).betaPrefix.col (Fin.last p) - (D.twoCutCore hP).suffix.row 0) hg).row j =
      D.row j.succ := by
  unfold twoComponentCore
  rw [separatedComponents_cut]
  rfl

private theorem twoComponentCore_cut_col (D : BetaDiagram (p + r + 3)) (hP : D.PositiveCorner)
    (hg : 0 < (D.twoCutCore hP).betaPrefix.col (Fin.last p) - (D.twoCutCore hP).suffix.row 0)
    (j : Fin (p + r + 2)) :
    ((D.twoCutCore hP).betaPrefix.twoComponentCore (D.twoCutCore hP).suffix
      ((D.twoCutCore hP).betaPrefix.col (Fin.last p) - (D.twoCutCore hP).suffix.row 0) hg).col j =
      D.col j.castSucc := by
  unfold twoComponentCore
  rw [separatedComponents_cut]
  rfl

/-- A genuine two-component maximal-cofactor cut reconstructs the whole actual
parent lists and produces every margin and gap.  No context shape is assumed. -/
theorem parent_twoComponentContext_of_cut (D : BetaDiagram (p + r + 3)) (hP : D.PositiveCorner)
    (hcut : (D.twoCutCore hP).row ⟨p + 1, by omega⟩ <
      (D.twoCutCore hP).col ⟨p + 1 - 1, by omega⟩) :
    ∃ hg : 0 < (D.twoCutCore hP).betaPrefix.col (Fin.last p) - (D.twoCutCore hP).suffix.row 0,
      D.TranslationEquivalent
        ((D.twoCutCore hP).betaPrefix.twoComponentContext (D.twoCutCore hP).suffix
          D.topMargin D.bottomMargin
          ((D.twoCutCore hP).betaPrefix.col (Fin.last p) - (D.twoCutCore hP).suffix.row 0)
          D.topMargin_pos D.bottomMargin_pos hg) := by
  have hQc : (D.twoCutCore hP).betaPrefix.col (Fin.last p) =
      (D.twoCutCore hP).col ⟨p + 1 - 1, by omega⟩ := rfl
  have hRr : (D.twoCutCore hP).suffix.row 0 =
      (D.twoCutCore hP).row ⟨p + 1, by omega⟩ := rfl
  have hg : 0 < (D.twoCutCore hP).betaPrefix.col (Fin.last p) -
      (D.twoCutCore hP).suffix.row 0 := by
    rw [hQc, hRr]
    exact sub_pos.mpr hcut
  refine ⟨hg, (D.twoCutCore hP).suffix.col (Fin.last r) - D.bottomMargin, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      change D.row 0 =
        (((D.twoCutCore hP).betaPrefix.twoComponentCore (D.twoCutCore hP).suffix _ hg).positiveBorder
          D.topMargin D.bottomMargin D.topMargin_pos D.bottomMargin_pos).row 0 +
        (D.bottomMargin - (D.twoCutCore hP).suffix.col (Fin.last r)) +
        ((D.twoCutCore hP).suffix.col (Fin.last r) - D.bottomMargin)
      rw [positiveBorder_row_zero, twoComponentCore_cut_row D hP hg 0]
      unfold topMargin
      ring
    | succ j =>
      change D.row j.succ =
        (((D.twoCutCore hP).betaPrefix.twoComponentCore (D.twoCutCore hP).suffix _ hg).positiveBorder
          D.topMargin D.bottomMargin D.topMargin_pos D.bottomMargin_pos).row j.succ +
        (D.bottomMargin - (D.twoCutCore hP).suffix.col (Fin.last r)) +
        ((D.twoCutCore hP).suffix.col (Fin.last r) - D.bottomMargin)
      rw [positiveBorder_row_succ, twoComponentCore_cut_row D hP hg j]
      ring
  · intro i
    cases i using Fin.lastCases with
    | last =>
      change D.col (Fin.last (p + r + 2)) =
        (((D.twoCutCore hP).betaPrefix.twoComponentCore (D.twoCutCore hP).suffix _ hg).positiveBorder
          D.topMargin D.bottomMargin D.topMargin_pos D.bottomMargin_pos).col (Fin.last (p + r + 2)) +
        (D.bottomMargin - (D.twoCutCore hP).suffix.col (Fin.last r)) +
        ((D.twoCutCore hP).suffix.col (Fin.last r) - D.bottomMargin)
      rw [positiveBorder_col_last, twoComponentCore_cut_col D hP hg (Fin.last (p + r + 1))]
      unfold bottomMargin
      ring
    | cast j =>
      change D.col j.castSucc =
        (((D.twoCutCore hP).betaPrefix.twoComponentCore (D.twoCutCore hP).suffix _ hg).positiveBorder
          D.topMargin D.bottomMargin D.topMargin_pos D.bottomMargin_pos).col j.castSucc +
        (D.bottomMargin - (D.twoCutCore hP).suffix.col (Fin.last r)) +
        ((D.twoCutCore hP).suffix.col (Fin.last r) - D.bottomMargin)
      rw [positiveBorder_col_castSucc, twoComponentCore_cut_col D hP hg j]
      ring

private theorem pderiv_complete_indicator (k : ℕ+) (z : ℤ) :
    MvPolynomial.pderiv k (complete z) =
      if (k.val : ℤ) = z then (1 : CompleteRing) else 0 := by
  by_cases h : (k.val : ℤ) = z
  · rw [ite_eq_left h, ← h, complete_nat, MvPolynomial.pderiv_X_self]
  · rw [ite_eq_right h]
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    simpa only [mem_vars_complete_iff] using h

private theorem pderiv_det_two_sites {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing) (k : ℕ+)
    (a b c d : Fin (n + 1)) (hbd : b ≠ d) (x y : CompleteRing)
    (hentry : ∀ i j, MvPolynomial.pderiv k (M i j) =
      (if i = a ∧ j = b then x else 0) + (if i = c ∧ j = d then y else 0)) :
    MvPolynomial.pderiv k M.det =
      (-1 : CompleteRing) ^ (a.val + b.val) *
          (M.submatrix a.succAbove b.succAbove).det * x +
        (-1 : CompleteRing) ^ (c.val + d.val) *
          (M.submatrix c.succAbove d.succAbove).det * y := by
  rw [pderiv_det_contraction]
  simp only [hentry, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, ite_and]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.adjugate_fin_succ_eq_det_submatrix]

/-- The residual derivative at the maximum of its two literal levels retains
both actual cofactors when the levels coincide (`eq:two-component-separator`). -/
theorem twoComponentResidualMatrix_separator
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (k : ℕ+) (hupper : Q.largestLabel + R.largestLabel + g + u ≤ (k.val : ℤ))
    (hlower : R.largestLabel + v ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.twoComponentResidualMatrix R u v g hu hv hg).det =
      (-1 : CompleteRing) ^ (p + r + 1) *
          (Q.schur * (R.extendBottom v hv).schur) *
          (if (k.val : ℤ) = Q.largestLabel + R.largestLabel + g + u then 1 else 0) +
        (-1 : CompleteRing) ^ (p + 2 + (p + r + 2)) *
          ((Q.twoComponentContext R u v g hu hv hg).lastColumnDiagram
            (Q.twoComponentContext_positiveCorner R u v g hu hv hg)
            (twoParentRightRow (p := p) (0 : Fin (r + 1)))).schur *
          (if (k.val : ℤ) = R.largestLabel + v then 1 else 0) := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let M := Q.twoComponentResidualMatrix R u v g hu hv hg
  let col : Fin (p + r + 3) := (Fin.last (p + r + 1)).castSucc
  let row := twoParentRightRow (p := p) (0 : Fin (r + 1))
  let x : CompleteRing :=
    if (k.val : ℤ) = Q.largestLabel + R.largestLabel + g + u then 1 else 0
  let y : CompleteRing := if (k.val : ℤ) = R.largestLabel + v then 1 else 0
  have htop : MvPolynomial.pderiv k (M 0 col) = x := by
    dsimp only [M, col]
    rw [residual_apply_of_ne Q R u v g hu hv hg _ _ (Fin.castSucc_ne_last _)]
    change MvPolynomial.pderiv k (complete (P.row 0 - P.col col)) = x
    rw [Q.twoComponentContext_upper_separator R u v g hu hv hg]
    exact pderiv_complete_indicator k _
  have hbottom : MvPolynomial.pderiv k (M row (Fin.last (p + r + 2))) = y := by
    dsimp only [M, row]
    rw [residual_apply_last Q R u v g hu hv hg _ (by
      simp only [row, twoParentRightRow, Fin.val_zero]; omega)]
    change MvPolynomial.pderiv k
      (complete (P.row row - P.col (Fin.last (p + r + 2)))) = y
    rw [twoComponentContext_row_right_full, twoComponentContext_col_last, sub_zero]
    have he : R.row 0 + v - R.col (Fin.last r) = R.largestLabel + v := by
      unfold largestLabel
      ring
    rw [he]
    exact pderiv_complete_indicator k _
  have hprivate : ∀ i j, (i ≠ 0 ∨ j ≠ col) →
      (i ≠ row ∨ j ≠ Fin.last (p + r + 2)) →
      MvPolynomial.pderiv k (M i j) = 0 := by
    intro i j ht hb
    by_cases hjlast : j = Fin.last (p + r + 2)
    · subst j
      have hirow : i ≠ row := by simpa using hb
      simp only [M, twoComponentResidualMatrix, Matrix.updateCol_apply, ite_true]
      by_cases hleft : i.val < p + 2
      · rw [ite_eq_left hleft, map_zero]
      · rw [ite_eq_right hleft]
        let a : Fin (r + 1) := ⟨i.val - (p + 2), by omega⟩
        have he : i = twoParentRightRow (p := p) a := by
          apply Fin.ext
          simp only [a, twoParentRightRow]
          omega
        have ha : a ≠ 0 := by
          intro h
          apply hirow
          simpa only [row, h] using he
        have hr := R.row_strictAnti (Fin.pos_iff_ne_zero.mpr ha)
        apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
        change k ∉ (complete (P.row i - P.col (Fin.last (p + r + 2)))).vars
        rw [he, twoComponentContext_row_right_full, twoComponentContext_col_last,
          sub_zero, mem_vars_complete_iff]
        change R.row 0 - R.col (Fin.last r) + v ≤ (k.val : ℤ) at hlower
        omega
    · dsimp only [M]
      rw [residual_apply_of_ne Q R u v g hu hv hg i j hjlast]
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      change k ∉ (complete (P.row i - P.col j)).vars
      rw [mem_vars_complete_iff]
      intro h
      have hjle : j ≤ col := by
        have hh := Fin.lt_last_iff_ne_last.mpr hjlast
        simp only [col, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at *
        omega
      have hc := P.col_strictAnti.antitone hjle
      have hr := P.row_strictAnti.antitone (Fin.zero_le i)
      have hl := Q.twoComponentContext_upper_separator R u v g hu hv hg
      change P.row 0 - P.col col = _ at hl
      by_cases hi : i = 0
      · subst i
        have hn : j ≠ col := by simpa using ht
        have hc' := P.col_strictAnti (lt_of_le_of_ne hjle hn)
        omega
      · have hr' := P.row_strictAnti (Fin.pos_iff_ne_zero.mpr hi)
        omega
  have hentry : ∀ i j, MvPolynomial.pderiv k (M i j) =
      (if i = 0 ∧ j = col then x else 0) +
        (if i = row ∧ j = Fin.last (p + r + 2) then y else 0) := by
    intro i j
    by_cases ht : i = 0 ∧ j = col
    · obtain ⟨rfl, rfl⟩ := ht
      rw [htop]
      simp only [col, eq_self, true_and, ite_true, Fin.castSucc_ne_last,
        and_false, ite_false, add_zero]
    · by_cases hb : i = row ∧ j = Fin.last (p + r + 2)
      · obtain ⟨rfl, rfl⟩ := hb
        rw [hbottom]
        simp only [ht, ite_false, eq_self, true_and, ite_true, zero_add]
      · rw [hprivate i j (by tauto) (by tauto)]
        simp only [ht, hb, ite_false, add_zero]
  have hd := pderiv_det_two_sites M k 0 col row (Fin.last (p + r + 2))
    (Fin.castSucc_ne_last _) x y hentry
  dsimp only [M, col, row] at hd
  rw [Fin.succAbove_zero, twoComponentResidualMatrix_top_cofactor,
    twoComponentResidualMatrix_minor, ← lastColumnDiagram_schur] at hd
  simpa only [Fin.val_zero, Fin.val_castSucc, Fin.val_last, zero_add,
    twoParentRightRow, Fin.val_zero] using hd

private theorem signed_product_connected_ne_zero {a b c : ℕ}
    (E : BetaDiagram a) (F : BetaDiagram b) (T : BetaDiagram c)
    (ha : 0 < a) (hb : 0 < b) (hT : T.Connected) (i j : ℕ) :
    (-1 : CompleteRing) ^ i * (E.schur * F.schur) +
      (-1 : CompleteRing) ^ j * T.schur ≠ 0 := by
  intro hz
  have hs : (-1 : CompleteRing) ^ j * (-1 : CompleteRing) ^ j = 1 := by
    rw [← mul_pow]
    simp
  have hh := congrArg (fun z : CompleteRing => (-1) ^ j * z) hz
  rw [mul_add, ← mul_assoc ((-1 : CompleteRing) ^ j)
    ((-1 : CompleteRing) ^ j) T.schur, hs, one_mul, mul_zero] at hh
  have he : T.schur =
      ((-((-1 : CompleteRing) ^ j * (-1) ^ i)) * E.schur) * F.schur := by
    linear_combination hh
  obtain hE | hF := (T.schur_irreducible hT).isUnit_or_isUnit he
  · exact E.schur_not_isUnit ha (isUnit_of_mul_isUnit_right hE)
  · exact F.schur_not_isUnit hb hF

/-- Unequal bottom margins give a nonzero full-parent difference after the
shared initial Laplace terms are removed.  This includes the mixed-sign tied
separator, where connected irreducibility, not a positivity convention, decides
noncancellation (`eq:two-component-separator`). -/
theorem twoComponent_margin_comparison_ne
    (Q : BetaDiagram (p + 1)) (R W : BetaDiagram (r + 1))
    (hR : R.Connected) (hW : W.Connected) (hZW : W.ZeroFree)
    (hRW : R.schur = W.schur)
    (u vm vp gm gp : ℤ)
    (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp) (hgm : 0 < gm) (hgp : 0 < gp)
    (hincrease : vm < vp)
    (hspan : (Q.twoComponentContext R u vm gm hu hvm hgm).largestLabel =
      (Q.twoComponentContext W u vp gp hu hvp hgp).largestLabel) :
    (Q.twoComponentContext R u vm gm hu hvm hgm).schur ≠
      (Q.twoComponentContext W u vp gp hu hvp hgp).schur := by
  let Um := Q.largestLabel + R.largestLabel + gm + u
  let Up := Q.largestLabel + W.largestLabel + gp + u
  let Vm := R.largestLabel + vm
  let Vp := W.largestLabel + vp
  let K := max Um Vp
  have hs := R.largestLabel_eq_of_schur_eq W hR hW hRW
  have hsp := hspan
  rw [twoComponentContext_span, twoComponentContext_span] at hsp
  have hup : Up < Um := by dsimp [Up, Um]; omega
  have hlow : Vm < Vp := by dsimp [Vm, Vp]; omega
  have hpos : 0 < K := by
    have hq := Q.largestLabel_pos
    have hr := R.largestLabel_pos
    have hh := le_max_left Um Vp
    dsimp [K, Um] at *
    omega
  let k : ℕ+ := ⟨K.toNat, by omega⟩
  have hk : (k.val : ℤ) = K := by dsimp [k]; omega
  have hm := Q.twoComponentResidualMatrix_separator R u vm gm hu hvm hgm k
    (by change Um ≤ (k.val : ℤ); rw [hk]; exact le_max_left _ _)
    (by change Vm ≤ (k.val : ℤ); rw [hk]; exact hlow.le.trans (le_max_right _ _))
  have hp := Q.twoComponentResidualMatrix_separator W u vp gp hu hvp hgp k
    (by change Up ≤ (k.val : ℤ); rw [hk]; exact hup.le.trans (le_max_left _ _))
    (by change Vp ≤ (k.val : ℤ); rw [hk]; exact le_max_right _ _)
  let T := (Q.twoComponentContext W u vp gp hu hvp hgp).lastColumnDiagram
    (Q.twoComponentContext_positiveCorner W u vp gp hu hvp hgp)
    (twoParentRightRow (p := p) (0 : Fin (r + 1)))
  have hT : T.Connected :=
    Q.twoComponent_separator_diagram_connected W hW hZW u vp gp hu hvp hgp
  have hkm : ¬ (k.val : ℤ) = Vm := by rw [hk]; dsimp [K]; omega
  have hkp : ¬ (k.val : ℤ) = Up := by rw [hk]; dsimp [K]; omega
  change MvPolynomial.pderiv k (Q.twoComponentResidualMatrix R u vm gm hu hvm hgm).det =
    (-1 : CompleteRing) ^ (p + r + 1) * (Q.schur * (R.extendBottom vm hvm).schur) *
      (if (k.val : ℤ) = Um then 1 else 0) +
    (-1 : CompleteRing) ^ (p + 2 + (p + r + 2)) * _ *
      (if (k.val : ℤ) = Vm then 1 else 0) at hm
  change MvPolynomial.pderiv k (Q.twoComponentResidualMatrix W u vp gp hu hvp hgp).det =
    (-1 : CompleteRing) ^ (p + r + 1) * _ *
      (if (k.val : ℤ) = Up then 1 else 0) +
    (-1 : CompleteRing) ^ (p + 2 + (p + r + 2)) * T.schur *
      (if (k.val : ℤ) = Vp then 1 else 0) at hp
  rw [ite_eq_right hkm, mul_zero, add_zero] at hm
  rw [ite_eq_right hkp, mul_zero, zero_add] at hp
  have hactual := Q.twoComponentContext_difference_residual R W hR hW hRW
    u vm vp gm gp hu hvm hvp hgm hgp (by
      rw [twoComponentCore_span, twoComponentCore_span]
      exact hsp)
  intro he
  have hz : (Q.twoComponentResidualMatrix W u vp gp hu hvp hgp).det -
      (Q.twoComponentResidualMatrix R u vm gm hu hvm hgm).det = 0 := by
    rw [← hactual, he, sub_self]
  have hd := congrArg (MvPolynomial.pderiv k) hz
  rw [map_sub, map_zero, hp, hm] at hd
  rcases lt_trichotomy Um Vp with hlt | heq | hgt
  · have hkv : (k.val : ℤ) = Vp := hk.trans (max_eq_right hlt.le)
    have hku : ¬ (k.val : ℤ) = Um := by omega
    rw [ite_eq_left hkv, ite_eq_right hku, mul_one, mul_zero, sub_zero] at hd
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) T.schur_ne_zero hd
  · have hku : (k.val : ℤ) = Um := hk.trans (max_eq_left heq.symm.le)
    have hkv : (k.val : ℤ) = Vp := hku.trans heq
    rw [ite_eq_left hkv, ite_eq_left hku, mul_one, mul_one] at hd
    have hn := signed_product_connected_ne_zero Q (R.extendBottom vm hvm) T
      (by omega) (by omega) hT (p + r + 2) (p + 2 + (p + r + 2))
    apply hn
    have hsign : (-1 : CompleteRing) ^ (p + r + 2) =
        -((-1 : CompleteRing) ^ (p + r + 1)) := by
      rw [show p + r + 2 = (p + r + 1) + 1 by omega, pow_succ]
      ring
    rw [hsign]
    linear_combination hd
  · have hku : (k.val : ℤ) = Um := hk.trans (max_eq_left hgt.le)
    have hkv : ¬ (k.val : ℤ) = Vp := by omega
    rw [ite_eq_right hkv, ite_eq_left hku, mul_zero, mul_one, zero_sub] at hd
    exact (neg_ne_zero.mpr (mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero Q.schur_ne_zero (R.extendBottom vm hvm).schur_ne_zero))) hd

/-- Two connected factors are recovered with multiplicity, even when they are
equal.  Their row counts are not hypotheses on a competing factorization. -/
theorem connected_two_product_matching {a b c d : ℕ}
    (Q : BetaDiagram a) (R : BetaDiagram b) (W : BetaDiagram c) (T : BetaDiagram d)
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (he : Q.schur * R.schur = W.schur * T.schur) :
    (Q.schur = W.schur ∧ R.schur = T.schur ∧ a = c ∧ b = d) ∨
      (Q.schur = T.schur ∧ R.schur = W.schur ∧ a = d ∧ b = c) := by
  have hp : Prime Q.schur :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hQ)
  have hd : Q.schur ∣ W.schur * T.schur := by
    rw [← he]
    exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with h | h
  · have hQW := Q.schur_eq_of_connected_dvd W hQ hW h
    have hRT : R.schur = T.schur := by
      rw [← hQW] at he
      exact mul_left_cancel₀ Q.schur_ne_zero he
    exact Or.inl ⟨hQW, hRT, Q.row_count_of_schur_eq W hQW,
      R.row_count_of_schur_eq T hRT⟩
  · have hQT := Q.schur_eq_of_connected_dvd T hQ hT h
    have hRW : R.schur = W.schur := by
      rw [← hQT, mul_comm W.schur Q.schur] at he
      exact mul_left_cancel₀ Q.schur_ne_zero he
    exact Or.inr ⟨hQT, hRW, Q.row_count_of_schur_eq T hQT,
      R.row_count_of_schur_eq W hRW⟩

/-- An arbitrary connected Schur-equal mate has precisely one actual maximal
cofactor cut, with the two actual connected restrictions equal to the old
factors in one of their two orders.  Scalar associates have already been fixed
by the actual coefficient-one normalization. -/
theorem twoComponent_mate_cut_inventory {m : ℕ}
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hZQ : Q.ZeroFree) (hZR : R.ZeroFree)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (E : BetaDiagram m) (hE : E.Connected)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur = E.schur) :
    ∃ hrow : m = p + r + 3,
      let F := E.castOrder hrow
      ∃ (hP : F.PositiveCorner) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
        (horder : a + b = p + r + 2),
        let C := (F.cornerDiagram hP).reindexOrder horder
        F.ZeroFree ∧
        C.row ⟨a, by omega⟩ < C.col ⟨a - 1, by omega⟩ ∧
        C.betaPrefix.Connected ∧ C.suffix.Connected ∧
        ((Q.schur = C.betaPrefix.schur ∧ R.schur = C.suffix.schur ∧
            p + 1 = a ∧ r + 1 = b) ∨
          (Q.schur = C.suffix.schur ∧ R.schur = C.betaPrefix.schur ∧
            p + 1 = b ∧ r + 1 = a)) := by
  obtain ⟨hrow, hP, hZF, hmatching⟩ :=
    Q.twoComponent_mate_components R hQ hR hZQ hZR u v g hu hv hg E hE he
  let F := E.castOrder hrow
  let D := F.cornerDiagram hP
  obtain ⟨K⟩ := D.exists_componentDecomposition
  have hrel := hmatching K
  have hcard := Multiset.card_eq_card_of_rel hrel
  have hlen : K.components.length = 2 := by
    simpa only [Multiset.coe_card, List.length_cons, List.length_nil] using hcard.symm
  obtain ⟨a, b, ha, hb, horder, hcut, hLC, hRC, hlist⟩ :=
    D.component_list_two_cut K hlen
  have hfunctions :
      (([(⟨p + 1, Q⟩ : Σ k : ℕ, BetaDiagram k),
        (⟨r + 1, R⟩ : Σ k : ℕ, BetaDiagram k)] : Multiset _).map
          (fun X : Σ k : ℕ, BetaDiagram k => X.2.schur)) =
      (K.components : Multiset _).map (fun X : Σ k : ℕ, BetaDiagram k => X.2.schur) :=
    Multiset.rel_eq.mp (Multiset.rel_map.mpr hrel)
  have hprod := congrArg Multiset.prod hfunctions
  have heprod : Q.schur * R.schur =
      (D.reindexOrder horder).betaPrefix.schur * (D.reindexOrder horder).suffix.schur := by
    simpa only [Multiset.map_coe, List.map_cons, List.map_nil, Multiset.prod_coe,
      List.prod_cons, List.prod_nil, mul_one, hlist] using hprod
  refine ⟨hrow, hP, a, b, ha, hb, horder, hZF, hcut, hLC, hRC, ?_⟩
  exact connected_two_product_matching Q R _ _ hQ hR hLC hRC heprod

/-- Normalized parent lists are unchanged by independent translations of their
actual ordered components. -/
theorem twoComponentContext_eq_of_core_translations
    (Q W : BetaDiagram (p + 1)) (R T : BetaDiagram (r + 1))
    (hQW : Q.TranslationEquivalent W) (hRT : R.TranslationEquivalent T)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    Q.twoComponentContext R u v g hu hv hg = W.twoComponentContext T u v g hu hv hg := by
  obtain ⟨a, hqr, hqc⟩ := hQW
  obtain ⟨b, hrr, hrc⟩ := hRT
  have hoff : Q.componentOffset R g = W.componentOffset T g + b - a := by
    unfold componentOffset
    rw [hrr 0, hqc (Fin.last p)]
    ring
  have hleft : ∀ i : Fin (p + 2),
      (Q.positiveBorder u 1 hu (by norm_num)).row i =
        (W.positiveBorder u 1 hu (by norm_num)).row i + a := by
    intro i
    cases i using Fin.cases with
    | zero =>
      rw [positiveBorder_row_zero, positiveBorder_row_zero, hqr 0]
      ring
    | succ i =>
      rw [positiveBorder_row_succ, positiveBorder_row_succ, hqr i]
  apply ext_of_row_col
  · funext i
    by_cases hi : i.val < p + 2
    · let j : Fin (p + 2) := ⟨i.val, hi⟩
      have he : i = twoParentLeftRow (r := r) j := by apply Fin.ext; rfl
      rw [he, twoComponentContext_row_left_full, twoComponentContext_row_left_full,
        hleft j, hoff, hrc (Fin.last r)]
      ring
    · let j : Fin (r + 1) := ⟨i.val - (p + 2), by omega⟩
      have he : i = twoParentRightRow (p := p) j := by
        apply Fin.ext
        simp only [j, twoParentRightRow]
        omega
      rw [he, twoComponentContext_row_right_full, twoComponentContext_row_right_full,
        hrr j, hrc (Fin.last r)]
      ring
  · funext i
    cases i using Fin.lastCases with
    | last => rw [twoComponentContext_col_last, twoComponentContext_col_last]
    | cast j =>
      by_cases hj : j.val < p + 1
      · let k : Fin (p + 1) := ⟨j.val, hj⟩
        have he : j = twoLeftIndex (r := r) k := by apply Fin.ext; rfl
        rw [he, twoComponentContext_col_left, twoComponentContext_col_left,
          hqc k, hoff, hrc (Fin.last r)]
        ring
      · let k : Fin (r + 1) := ⟨j.val - (p + 1), by omega⟩
        have he : j = twoRightIndex (p := p) k := by
          apply Fin.ext
          simp only [k, twoRightIndex]
          omega
        rw [he, twoComponentContext_col_right, twoComponentContext_col_right,
          hrc k, hrc (Fin.last r)]
        ring

/-- The actual row offsets for the almost-square left block. -/
def twoComponentWeight (Q : BetaDiagram (p + 1))
    (u g : ℤ) (hu : 0 < u) (i : Fin (p + 2)) : ℤ :=
  g + (Q.positiveBorder u 1 hu (by norm_num)).row i - Q.col (Fin.last p)

@[simp] theorem twoComponentWeight_zero (Q : BetaDiagram (p + 1))
    (u g : ℤ) (hu : 0 < u) :
    Q.twoComponentWeight u g hu 0 = g + Q.largestLabel + u := by
  unfold twoComponentWeight largestLabel
  rw [positiveBorder_row_zero]
  ring

@[simp] theorem twoComponentWeight_succ (Q : BetaDiagram (p + 1))
    (u g : ℤ) (hu : 0 < u) (i : Fin (p + 1)) :
    Q.twoComponentWeight u g hu i.succ = Q.twoComponentShift g i := by
  unfold twoComponentWeight twoComponentShift
  rw [positiveBorder_row_succ]

theorem twoComponentWeight_pos (Q : BetaDiagram (p + 1))
    (u g : ℤ) (hu : 0 < u) (hg : 0 < g) (i : Fin (p + 2)) :
    0 < Q.twoComponentWeight u g hu i := by
  cases i using Fin.cases with
  | zero =>
    rw [twoComponentWeight_zero]
    have hs := Q.largestLabel_pos
    omega
  | succ i =>
    rw [twoComponentWeight_succ]
    exact Q.twoComponentShift_pos g hg i

theorem twoComponentWeight_lt_zero (Q : BetaDiagram (p + 1))
    (u g : ℤ) (hu : 0 < u) (i : Fin (p + 2)) (hi : i ≠ 0) :
    Q.twoComponentWeight u g hu i < Q.twoComponentWeight u g hu 0 := by
  have hr := (Q.positiveBorder u 1 hu (by norm_num)).row_strictAnti
    (Fin.pos_iff_ne_zero.mpr hi)
  unfold twoComponentWeight
  omega

/-- Every border difference in the source's full orientation sum, including
the outer top row, is retained. -/
noncomputable def twoComponentOrientationSum
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) : CompleteRing :=
  ∑ i : Fin (p + 3), (-1 : CompleteRing) ^ (p + 2 - i.val) *
    (Q.twoComponentLeftMinor u hu i).schur *
    R.borderDifference (Q.twoComponentWeight u g hu i) v
      (Q.twoComponentWeight_pos u g hu hg i) hv

private theorem borderDifference_coefficient_at_of_lt (R : BetaDiagram (r + 2))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) (h : w < v)
    (k : ℕ+) (hk : (k.val : ℤ) = R.largestLabel + v) :
    MvPolynomial.pderiv k (R.borderDifference w v hw hv) =
      (-1) ^ (r + 3) * R.endpointDifference w hw := by
  have hi : R.borderDifferenceGenerator w v hw hv = k := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change ((R.borderDifferenceGenerator w v hw hv).val : ℤ) = (k.val : ℤ)
    rw [borderDifferenceGenerator_int, max_eq_right h.le, hk]
  rw [← hi]
  exact R.borderDifference_coefficient_of_lt w v hw hv h

private theorem borderDifference_coefficient_at_of_gt (R : BetaDiagram (r + 2))
    (w v : ℤ) (hw : 0 < w) (hv : 0 < v) (h : v < w)
    (k : ℕ+) (hk : (k.val : ℤ) = R.largestLabel + w) :
    MvPolynomial.pderiv k (R.borderDifference w v hw hv) =
      (-1) ^ (r + 2) * R.endpointDifference v hv := by
  have hi : R.borderDifferenceGenerator w v hw hv = k := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change ((R.borderDifferenceGenerator w v hw hv).val : ℤ) = (k.val : ℤ)
    rw [borderDifferenceGenerator_int, max_eq_left h.le, hk]
  rw [← hi]
  exact R.borderDifference_coefficient_of_gt w v hw hv h

/-- Below the outer top weight, its private border generator extracts the old
left determinant times the actual endpoint difference at the bottom margin. -/
theorem twoComponentOrientationSum_ne_zero_of_lt
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2)) (hR : R.EndpointLeader)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (h : v < g + Q.largestLabel + u) :
    Q.twoComponentOrientationSum R u v g hu hv hg ≠ 0 := by
  let w := g + Q.largestLabel + u
  let K := R.largestLabel + w
  have hpos : 0 < K := by
    have hs := R.largestLabel_pos
    dsimp [K, w]
    omega
  let k : ℕ+ := ⟨K.toNat, by omega⟩
  have hk : (k.val : ℤ) = K := by dsimp [k]; omega
  have hleft : ∀ i : Fin (p + 3),
      MvPolynomial.pderiv k (Q.twoComponentLeftMinor u hu i).schur = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := Q.twoComponentLeftMinor_vars_le u hu i k hm
    have hs := R.largestLabel_pos
    dsimp [K, w] at hk
    omega
  have hrest : ∀ i : Fin (p + 2),
      MvPolynomial.pderiv k
        (R.borderDifference (Q.twoComponentWeight u g hu i.succ) v
          (Q.twoComponentWeight_pos u g hu hg i.succ) hv) = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := R.borderDifference_vars_le
      (Q.twoComponentWeight u g hu i.succ) v
      (Q.twoComponentWeight_pos u g hu hg i.succ) hv k hm
    have hw := Q.twoComponentWeight_lt_zero u g hu i.succ (Fin.succ_ne_zero _)
    rw [twoComponentWeight_zero] at hw
    dsimp [K, w] at hk
    omega
  have htop := borderDifference_coefficient_at_of_gt R
    (Q.twoComponentWeight u g hu 0) v (Q.twoComponentWeight_pos u g hu hg 0) hv
    (by simpa only [twoComponentWeight_zero] using h) k
    (by simpa only [K, w, twoComponentWeight_zero] using hk)
  intro hz
  have hd := congrArg (MvPolynomial.pderiv k) hz
  rw [twoComponentOrientationSum, Fin.sum_univ_succ, map_add,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, pderiv_sign_pow,
    hleft, htop, map_sum, map_zero] at hd
  have htail : (∑ i : Fin (p + 2), MvPolynomial.pderiv k
      ((-1 : CompleteRing) ^ (p + 2 - i.succ.val) *
        (Q.twoComponentLeftMinor u hu i.succ).schur *
        R.borderDifference (Q.twoComponentWeight u g hu i.succ) v
          (Q.twoComponentWeight_pos u g hu hg i.succ) hv)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      pderiv_sign_pow, hleft, hrest]
    ring
  rw [htail, twoComponentLeftMinor_zero] at hd
  have hn := mul_ne_zero (pow_ne_zero (p + 2) (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero Q.schur_ne_zero
      (mul_ne_zero (pow_ne_zero (r + 2) (neg_ne_zero.mpr one_ne_zero))
        (EndpointLeader.difference_ne_zero R hR v hv)))
  apply hn
  simpa only [Fin.val_zero, Nat.sub_zero, zero_mul, mul_zero, zero_add, add_zero,
    mul_assoc] using hd

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/SingletonLift.lean
-- The support-reading argument is adapted to actual two-component parents.

@[simp] theorem twoComponentContext_topMargin
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).topMargin = u := by
  let B := (Q.twoComponentCore R g hg).positiveBorder u v hu hv
  change B.row 0 + (v - R.col (Fin.last r)) -
    (B.row (0 : Fin (p + r + 2)).succ + (v - R.col (Fin.last r))) = u
  have h := (Q.twoComponentCore R g hg).positiveBorder_topMargin u v hu hv
  change B.row 0 - B.row (0 : Fin (p + r + 2)).succ = u at h
  omega

@[simp] theorem twoComponentContext_bottomMargin
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).bottomMargin = v := by
  let B := (Q.twoComponentCore R g hg).positiveBorder u v hu hv
  change B.col (Fin.last (p + r + 1)).castSucc + (v - R.col (Fin.last r)) -
    (B.col (Fin.last (p + r + 2)) + (v - R.col (Fin.last r))) = v
  have h := (Q.twoComponentCore R g hg).positiveBorder_bottomMargin u v hu hv
  change B.col (Fin.last (p + r + 1)).castSucc -
    B.col (Fin.last (p + r + 2)) = v at h
  omega

@[simp] theorem twoComponentContext_secondLabel
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).secondLabel =
      Q.largestLabel + R.largestLabel + g + u + v - min u v := by
  simp only [secondLabel, twoComponentContext_span,
    twoComponentContext_topMargin, twoComponentContext_bottomMargin]

/-- The normalized context retains the actual border's largest generator. -/
theorem twoComponentContext_largest_generator
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).borderLargestGenerator =
      ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).borderLargestGenerator := by
  apply Subtype.ext
  apply Int.ofNat.inj
  change (((Q.twoComponentContext R u v g hu hv hg).borderLargestGenerator).val : ℤ) =
    ((((Q.twoComponentCore R g hg).positiveBorder u v hu hv).borderLargestGenerator).val : ℤ)
  rw [borderLargestGenerator_int, borderLargestGenerator_int,
    twoComponentContext_span, positiveBorder_largestLabel, twoComponentCore_span]

/-- The second generator is unchanged by the normalization translation. -/
theorem twoComponentContext_second_generator
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).borderSecondGenerator =
      ((Q.twoComponentCore R g hg).positiveBorder u v hu hv).borderSecondGenerator := by
  apply Subtype.ext
  apply Int.ofNat.inj
  change (((Q.twoComponentContext R u v g hu hv hg).borderSecondGenerator).val : ℤ) =
    ((((Q.twoComponentCore R g hg).positiveBorder u v hu hv).borderSecondGenerator).val : ℤ)
  rw [borderSecondGenerator_int, borderSecondGenerator_int,
    twoComponentContext_secondLabel, positiveBorder_secondLabel, twoComponentCore_span]

/-- Both endpoint contributions are retained in the tied regime. -/
noncomputable def twoComponentRegimeCoefficient
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) : CompleteRing :=
  if u < v then (Q.extendTop u hu).schur * R.schur
  else if v < u then Q.schur * (R.extendBottom v hv).schur
  else (Q.extendTop u hu).schur * R.schur + Q.schur * (R.extendBottom u hu).schur

/-- This is a coefficient of the full actual parent, not an assumed marker. -/
theorem twoComponentRegimeCoefficient_identity
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.twoComponentContext R u v g hu hv hg
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) =
      (-1 : CompleteRing) ^ (p + r + 3) * Q.twoComponentRegimeCoefficient R u v hu hv := by
  dsimp only
  rw [twoComponentContext_second_generator, twoComponentContext_largest_generator]
  rcases lt_trichotomy u v with h | h | h
  · rw [twoComponentContext_top_marker Q R u v g hu hv hg h]
    simp only [twoComponentRegimeCoefficient, h, ite_true]
  · subst v
    rw [twoComponentContext_tied_marker Q R u g hu hg]
    simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false]
  · rw [twoComponentContext_bottom_marker Q R u v g hu hv hg h]
    simp only [twoComponentRegimeCoefficient, lt_asymm h, ite_false, h, ite_true]

/-- Nonvanishing is produced in all three regimes, including equal old factors. -/
theorem twoComponentRegimeCoefficient_ne_zero
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    Q.twoComponentRegimeCoefficient R u v hu hv ≠ 0 := by
  rcases lt_trichotomy u v with h | h | h
  · simp only [twoComponentRegimeCoefficient, h, ite_true]
    exact mul_ne_zero (Q.extendTop u hu).schur_ne_zero R.schur_ne_zero
  · subst v
    simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false]
    exact two_component_tied_marker_ne_zero Q R hQ hR u hu
  · simp only [twoComponentRegimeCoefficient, lt_asymm h, ite_false, h, ite_true]
    exact mul_ne_zero Q.schur_ne_zero (R.extendBottom v hv).schur_ne_zero

theorem twoComponent_secondLabel_derivative_ne_zero
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.twoComponentContext R u v g hu hv hg
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) ≠ (0 : CompleteRing) := by
  dsimp only
  rw [twoComponentRegimeCoefficient_identity]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Q.twoComponentRegimeCoefficient_ne_zero R hQ hR u v hu hv)

/-- The second generator actually occurs after corner erasure. -/
theorem twoComponent_secondLabel_mem_vars
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.twoComponentContext R u v g hu hv hg
    P.borderSecondGenerator ∈ (eraseGenerator P.borderLargestGenerator P.schur).vars := by
  dsimp only
  by_contra hn
  exact Q.twoComponent_secondLabel_derivative_ne_zero R hQ hR u v g hu hv hg
    (MvPolynomial.pderiv_eq_zero_of_notMem_vars hn)

/-- Occurrence and the entrywise support bound identify the largest remaining variable. -/
theorem twoComponent_secondLabel_support_reading
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let P := Q.twoComponentContext R u v g hu hv hg
    P.borderSecondGenerator ∈ (eraseGenerator P.borderLargestGenerator P.schur).vars ∧
      ∀ k ∈ (eraseGenerator P.borderLargestGenerator P.schur).vars,
        (k.val : ℤ) ≤ P.secondLabel := by
  dsimp only
  exact ⟨Q.twoComponent_secondLabel_mem_vars R hQ hR u v g hu hv hg,
    fun k hk => (Q.twoComponentContext R u v g hu hv hg).vars_le_secondLabel k hk⟩

private theorem largestLabel_eq_of_schur_eq_of_order_reading {n m : ℕ}
    (D : BetaDiagram (n + 1)) (E : BetaDiagram (m + 1))
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    D.largestLabel = E.largestLabel := by
  have hn : n = m := by have hh := D.row_count_of_schur_eq E he; omega
  subst m
  exact D.largestLabel_eq_of_schur_eq E hD hE he

/-- Full equality reads the second label without assuming a shared component profile,
component order, gap, or margin.  The comparison component sizes are independent. -/
theorem twoComponent_secondLabel_eq_of_schur_eq {a b : ℕ}
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (W : BetaDiagram (a + 1)) (T : BetaDiagram (b + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    (Q.twoComponentContext R u v g hu hv hg).secondLabel =
      (W.twoComponentContext T U V G hU hV hG).secondLabel := by
  let Pm := Q.twoComponentContext R u v g hu hv hg
  let Pp := W.twoComponentContext T U V G hU hV hG
  have hN := largestLabel_eq_of_schur_eq_of_order_reading Pm Pp
    (Q.twoComponentContext_connected R u v g hu hv hg)
    (W.twoComponentContext_connected T U V G hU hV hG) he
  have hgen : Pm.borderLargestGenerator = Pp.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (Pm.borderLargestGenerator.val : ℤ) = (Pp.borderLargestGenerator.val : ℤ)
    rw [borderLargestGenerator_int, borderLargestGenerator_int, hN]
  have hmm := Q.twoComponent_secondLabel_mem_vars R hQ hR u v g hu hv hg
  have hmp := W.twoComponent_secondLabel_mem_vars T hW hT U V G hU hV hG
  change Pm.borderSecondGenerator ∈ (eraseGenerator Pm.borderLargestGenerator Pm.schur).vars at hmm
  change Pp.borderSecondGenerator ∈ (eraseGenerator Pp.borderLargestGenerator Pp.schur).vars at hmp
  rw [hgen, he] at hmm
  rw [← hgen, ← he] at hmp
  have hb1 := Pp.vars_le_secondLabel Pm.borderSecondGenerator hmm
  have hb2 := Pm.vars_le_secondLabel Pp.borderSecondGenerator hmp
  rw [borderSecondGenerator_int] at hb1 hb2
  exact le_antisymm hb1 hb2

/-- The minimum margin is a reading of the full parent polynomial. -/
theorem twoComponent_min_margin_eq_of_schur_eq {a b : ℕ}
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (W : BetaDiagram (a + 1)) (T : BetaDiagram (b + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    min u v = min U V := by
  have hN := largestLabel_eq_of_schur_eq_of_order_reading
    (Q.twoComponentContext R u v g hu hv hg)
    (W.twoComponentContext T U V G hU hV hG)
    (Q.twoComponentContext_connected R u v g hu hv hg)
    (W.twoComponentContext_connected T U V G hU hV hG) he
  have hM := twoComponent_secondLabel_eq_of_schur_eq Q R W T hQ hR hW hT
    u v g U V G hu hv hg hU hV hG he
  simp only [twoComponentContext_span] at hN
  simp only [twoComponentContext_secondLabel] at hM
  omega

/-- Equality of full parents yields equality of the full regime polynomials.
The common cofactor sign is recovered from ordinary degree, even when the
comparison's component sizes are independently specified. -/
theorem twoComponentRegimeCoefficient_eq_of_schur_eq {a b : ℕ}
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (W : BetaDiagram (a + 1)) (T : BetaDiagram (b + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    Q.twoComponentRegimeCoefficient R u v hu hv =
      W.twoComponentRegimeCoefficient T U V hU hV := by
  let Pm := Q.twoComponentContext R u v g hu hv hg
  let Pp := W.twoComponentContext T U V G hU hV hG
  have hN := largestLabel_eq_of_schur_eq_of_order_reading Pm Pp
    (Q.twoComponentContext_connected R u v g hu hv hg)
    (W.twoComponentContext_connected T U V G hU hV hG) he
  have hM := twoComponent_secondLabel_eq_of_schur_eq Q R W T hQ hR hW hT
    u v g U V G hu hv hg hU hV hG he
  have hNgen : Pm.borderLargestGenerator = Pp.borderLargestGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (Pm.borderLargestGenerator.val : ℤ) = (Pp.borderLargestGenerator.val : ℤ)
    rw [borderLargestGenerator_int, borderLargestGenerator_int, hN]
  have hMgen : Pm.borderSecondGenerator = Pp.borderSecondGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (Pm.borderSecondGenerator.val : ℤ) = (Pp.borderSecondGenerator.val : ℤ)
    rw [borderSecondGenerator_int, borderSecondGenerator_int]
    exact hM
  have hn : p + r + 3 = a + b + 3 := Pm.row_count_of_schur_eq Pp he
  have hs : (-1 : CompleteRing) ^ (p + r + 3) =
      (-1 : CompleteRing) ^ (a + b + 3) := congrArg (fun k : ℕ => (-1 : CompleteRing) ^ k) hn
  have hd := congrArg (fun f : CompleteRing =>
    MvPolynomial.pderiv Pm.borderSecondGenerator (eraseGenerator Pm.borderLargestGenerator f)) he
  have hm := Q.twoComponentRegimeCoefficient_identity R u v g hu hv hg
  have hp := W.twoComponentRegimeCoefficient_identity T U V G hU hV hG
  have hc : (-1 : CompleteRing) ^ (p + r + 3) * Q.twoComponentRegimeCoefficient R u v hu hv =
      (-1 : CompleteRing) ^ (p + r + 3) * W.twoComponentRegimeCoefficient T U V hU hV := by
    calc
      (-1 : CompleteRing) ^ (p + r + 3) * Q.twoComponentRegimeCoefficient R u v hu hv =
          MvPolynomial.pderiv Pm.borderSecondGenerator
            (eraseGenerator Pm.borderLargestGenerator Pm.schur) := hm.symm
      _ = MvPolynomial.pderiv Pm.borderSecondGenerator
          (eraseGenerator Pm.borderLargestGenerator Pp.schur) := hd
      _ = MvPolynomial.pderiv Pp.borderSecondGenerator
          (eraseGenerator Pp.borderLargestGenerator Pp.schur) := by rw [hMgen, hNgen]
      _ = (-1 : CompleteRing) ^ (a + b + 3) *
          W.twoComponentRegimeCoefficient T U V hU hV := hp
      _ = (-1 : CompleteRing) ^ (p + r + 3) *
          W.twoComponentRegimeCoefficient T U V hU hV := by rw [hs]
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc

/-- For distinct old factors their divisibility tests recover the two strict regimes. -/
theorem twoComponentRegimeCoefficient_divisibility_distinct
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hne : Q.schur ≠ R.schur)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (Q.schur ∣ Q.twoComponentRegimeCoefficient R u v hu hv ↔ v < u) ∧
      (R.schur ∣ Q.twoComponentRegimeCoefficient R u v hu hv ↔ u < v) := by
  rcases lt_trichotomy u v with h | h | h
  · have hd := two_component_marker_divisibility_distinct Q R hQ hR hne u hu
    simp only [twoComponentRegimeCoefficient, h, ite_true]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hh; exact (hd.1 hh).elim
    · intro hh; omega
    · intro _; trivial
    · intro _; exact hd.2.1
  · subst v
    have hd := two_component_marker_divisibility_distinct Q R hQ hR hne u hu
    simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hh; exact (hd.2.2.2.2.1 hh).elim
    · intro hh; exact hh.elim
    · intro hh; exact (hd.2.2.2.2.2 hh).elim
    · intro hh; exact hh.elim
  · have hd := two_component_marker_divisibility_distinct Q R hQ hR hne v hv
    simp only [twoComponentRegimeCoefficient, lt_asymm h, ite_false, h, ite_true]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro _; trivial
    · intro _; exact hd.2.2.1
    · intro hh; exact (hd.2.2.2.1 hh).elim
    · intro hh; exact hh.elim

/-- Aligned distinct old factors and full equality identify all three regimes. -/
theorem twoComponent_regimes_eq_of_schur_eq_distinct {a b : ℕ}
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (W : BetaDiagram (a + 1)) (T : BetaDiagram (b + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (hne : Q.schur ≠ R.schur) (hQW : Q.schur = W.schur) (hRT : R.schur = T.schur)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    (u < v ↔ U < V) ∧ (v < u ↔ V < U) ∧ (u = v ↔ U = V) := by
  have hWT : W.schur ≠ T.schur := by
    rw [← hQW, ← hRT]
    exact hne
  have hm := twoComponentRegimeCoefficient_eq_of_schur_eq Q R W T hQ hR hW hT
    u v g U V G hu hv hg hU hV hG he
  have hd := twoComponentRegimeCoefficient_divisibility_distinct Q R hQ hR hne u v hu hv
  have hp := twoComponentRegimeCoefficient_divisibility_distinct W T hW hT hWT U V hU hV
  have htop : u < v ↔ U < V := by
    rw [← hd.2, ← hp.2, hRT, hm]
  have hbottom : v < u ↔ V < U := by
    rw [← hd.1, ← hp.1, hQW, hm]
  exact ⟨htop, hbottom, by omega⟩

/-- Cancellation of the common old factor excludes a tied marker equaling a strict
marker; the existing endpoint derivative theorem supplies the factor-of-two obstruction. -/
theorem two_component_equal_factor_tied_marker_ne_top
    (Q R W T : BetaDiagram (p + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur) (hQT : Q.schur = T.schur)
    (q : ℤ) (hq : 0 < q) :
    (Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur ≠
      (W.extendTop q hq).schur * T.schur := by
  intro he
  have hc : Q.schur * ((Q.extendTop q hq).schur + (R.extendBottom q hq).schur) =
      Q.schur * (W.extendTop q hq).schur := by
    calc
      Q.schur * ((Q.extendTop q hq).schur + (R.extendBottom q hq).schur) =
          (Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur := by
            rw [← hQR]
            ring
      _ = (W.extendTop q hq).schur * T.schur := he
      _ = Q.schur * (W.extendTop q hq).schur := by rw [← hQT]; ring
  exact equal_factor_tied_sum_ne_top Q R W hQ hR hW hQR hQW q hq
    (mul_left_cancel₀ Q.schur_ne_zero hc)

theorem two_component_equal_factor_tied_marker_ne_bottom
    (Q R W T : BetaDiagram (p + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hT : T.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur) (hQT : Q.schur = T.schur)
    (q : ℤ) (hq : 0 < q) :
    (Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur ≠
      W.schur * (T.extendBottom q hq).schur := by
  intro he
  have hc : Q.schur * ((Q.extendTop q hq).schur + (R.extendBottom q hq).schur) =
      Q.schur * (T.extendBottom q hq).schur := by
    calc
      Q.schur * ((Q.extendTop q hq).schur + (R.extendBottom q hq).schur) =
          (Q.extendTop q hq).schur * R.schur + Q.schur * (R.extendBottom q hq).schur := by
            rw [← hQR]
            ring
      _ = W.schur * (T.extendBottom q hq).schur := he
      _ = Q.schur * (T.extendBottom q hq).schur := by rw [← hQW]
  exact equal_factor_tied_sum_ne_bottom Q R T hQ hR hT hQR hQT q hq
    (mul_left_cancel₀ Q.schur_ne_zero hc)

/-- With equal old factors the minimum-margin reading and the factor-of-two
obstruction distinguish tied from strict full parents. -/
theorem twoComponent_tied_eq_of_schur_eq_equal
    (Q R W T : BetaDiagram (p + 1))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur) (hQT : Q.schur = T.schur)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    u = v ↔ U = V := by
  have one_way : ∀ (A B C D : BetaDiagram (p + 1)),
      A.Connected → B.Connected → C.Connected → D.Connected →
      A.schur = B.schur → A.schur = C.schur → A.schur = D.schur →
      ∀ (q x y gm gp : ℤ) (hq : 0 < q) (hx : 0 < x) (hy : 0 < y)
        (hgm : 0 < gm) (hgp : 0 < gp),
      (A.twoComponentContext B q q gm hq hq hgm).schur =
        (C.twoComponentContext D x y gp hx hy hgp).schur → x = y := by
    intro A B C D hA hB hC hD hAB hAC hAD q x y gm gp hq hx hy hgm hgp hh
    have hmin := twoComponent_min_margin_eq_of_schur_eq A B C D hA hB hC hD
      q q gm x y gp hq hq hgm hx hy hgp hh
    have hm := twoComponentRegimeCoefficient_eq_of_schur_eq A B C D hA hB hC hD
      q q gm x y gp hq hq hgm hx hy hgp hh
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hxq : x = q := by rw [min_self, min_eq_left hxy.le] at hmin; omega
      subst x
      simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false,
        hxy, ite_true] at hm
      exact (two_component_equal_factor_tied_marker_ne_top A B C D
        hA hB hC hAB hAC hAD q hq hm).elim
    · exact hxy
    · have hyq : y = q := by rw [min_self, min_eq_right hyx.le] at hmin; omega
      subst y
      simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false,
        lt_asymm hyx, hyx, ite_true] at hm
      exact (two_component_equal_factor_tied_marker_ne_bottom A B C D
        hA hB hD hAB hAC hAD q hq hm).elim
  constructor
  · intro huv
    subst v
    exact one_way Q R W T hQ hR hW hT hQR hQW hQT u U V g G hu hU hV hg hG he
  · intro hUV
    subst V
    have hWT : W.schur = T.schur := hQW.symm.trans hQT
    have hWQ : W.schur = Q.schur := hQW.symm
    have hWR : W.schur = R.schur := hQW.symm.trans hQR
    exact one_way W T Q R hW hT hQ hR hWT hWQ hWR U u v G g hU hu hv hG hg he.symm


section AlmostSquareBlock

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The actual square matrix with blocks of sizes `(a+1)×a`,
`(a+1)×(b+1)`, `b×a`, and `b×(b+1)`, with zero lower-left block.
The row and column indices are the ordinary increasing `Fin` indices. -/
def almostSquareBlock {a b : ℕ}
    (L : Matrix (Fin (a + 1)) (Fin a) R)
    (B : Matrix (Fin (a + 1)) (Fin (b + 1)) R)
    (C : Matrix (Fin b) (Fin (b + 1)) R) :
    Matrix (Fin (a + b + 1)) (Fin (a + b + 1)) R :=
  fun i j =>
    if hi : i.val < a + 1 then
      if hj : j.val < a then
        L ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else
        B ⟨i.val, hi⟩ ⟨j.val - a, by omega⟩
    else
      if hj : j.val < a then
        0
      else
        C ⟨i.val - (a + 1), by omega⟩ ⟨j.val - a, by omega⟩

private theorem almostSquare_drop_right_left {a b : ℕ}
    (j : Fin (b + 2)) (k : Fin a) :
    (j.natAdd a).succAbove (k.castAdd (b + 1)) =
      k.castAdd (b + 2) := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd,
      Fin.val_natAdd]
    omega

private theorem almostSquare_drop_right_right {a b : ℕ}
    (j : Fin (b + 2)) (k : Fin (b + 1)) :
    (j.natAdd a).succAbove (k.natAdd a) =
      (j.succAbove k).natAdd a := by
  unfold Fin.succAbove
  split_ifs <;> apply Fin.ext <;>
    simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
      Fin.val_natAdd] <;> omega

/-- Deleting the last bottom row and a right-block column leaves the
same almost-square block shape, with exactly those deletions in `B` and `C`. -/
private theorem almostSquareBlock_last_right_minor {a b : ℕ}
    (L : Matrix (Fin (a + 1)) (Fin a) R)
    (B : Matrix (Fin (a + 1)) (Fin (b + 2)) R)
    (C : Matrix (Fin (b + 1)) (Fin (b + 2)) R)
    (j : Fin (b + 2)) :
    (almostSquareBlock L B C).submatrix Fin.castSucc
        (j.natAdd a).succAbove =
      almostSquareBlock L (B.submatrix id j.succAbove)
        (C.submatrix Fin.castSucc j.succAbove) := by
  ext x y
  cases y using Fin.addCases with
  | left y =>
      rw [Matrix.submatrix_apply, almostSquare_drop_right_left]
      simp only [almostSquareBlock, Fin.val_castSucc,
        Fin.val_castAdd, y.isLt, dif_pos,
        Matrix.submatrix_apply] <;> split_ifs <;> rfl
  | right y =>
      rw [Matrix.submatrix_apply, almostSquare_drop_right_right]
      have hy : ¬ a + y.val < a := by omega
      have hz : ¬ a + (j.succAbove y).val < a := by omega
      simp only [almostSquareBlock, Fin.val_castSucc,
        Fin.val_natAdd, hy, hz, dif_neg,
        Nat.add_sub_cancel_left, Matrix.submatrix_apply] <;>
        split_ifs <;> first | contradiction | rfl

private theorem almostSquare_cons_last_minor {a b : ℕ}
    (B : Matrix (Fin (a + 1)) (Fin (b + 2)) R)
    (C : Matrix (Fin (b + 1)) (Fin (b + 2)) R)
    (i : Fin (a + 1)) (j : Fin (b + 2)) :
    Matrix.submatrix
      (Matrix.vecCons (B i) C : Matrix (Fin (b + 2)) (Fin (b + 2)) R)
        (Fin.last (b + 1)).succAbove j.succAbove =
      (Matrix.vecCons ((B.submatrix id j.succAbove) i)
        (C.submatrix Fin.castSucc j.succAbove) :
          Matrix (Fin (b + 1)) (Fin (b + 1)) R) := by
  ext x y
  rw [Fin.succAbove_last]
  cases x using Fin.cases with
  | zero =>
      simp [Matrix.submatrix_apply]
  | succ x =>
      have hx : x.succ.castSucc = x.castSucc.succ := by
        apply Fin.ext
        rfl
      simp only [Matrix.vecCons, Matrix.submatrix_apply, hx, Fin.cons_succ]

/-- The genuine almost-square block expansion.  Its hypotheses consist
only of the three input blocks; the zero lower-left block is built into
`almostSquareBlock`.  The proof expands actual determinants, not supplied
expansion identities. -/
theorem det_almostSquareBlock {a b : ℕ}
    (L : Matrix (Fin (a + 1)) (Fin a) R)
    (B : Matrix (Fin (a + 1)) (Fin (b + 1)) R)
    (C : Matrix (Fin b) (Fin (b + 1)) R) :
    (almostSquareBlock L B C).det =
      ∑ i : Fin (a + 1),
        (-1 : R) ^ (i.val + a) *
          (L.submatrix i.succAbove id).det *
          Matrix.det
            (Matrix.vecCons (B i) C : Matrix (Fin (b + 1)) (Fin (b + 1)) R) := by
  classical
  induction b with
  | zero =>
      have hentry (i : Fin (a + 1)) :
          almostSquareBlock L B C i (Fin.last a) = B i 0 := by
        simp [almostSquareBlock, i.isLt, Fin.val_last]
      have hminor (i : Fin (a + 1)) :
          (almostSquareBlock L B C).submatrix i.succAbove
              (Fin.last a).succAbove =
            L.submatrix i.succAbove id := by
        ext x y
        rw [Matrix.submatrix_apply, Fin.succAbove_last]
        simp [almostSquareBlock, (i.succAbove x).isLt, y.isLt,
          Matrix.submatrix_apply]
      have h := Matrix.det_succ_column
        (almostSquareBlock L B C) (Fin.last a)
      rw [h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hentry, hminor]
      simp only [Fin.val_last, Matrix.det_unique,
        Fin.default_eq_zero, Matrix.vecCons, Fin.cons_zero]
      ring
  | succ b ih =>
      have hrow : ¬ a + b + 1 < a + 1 := by omega
      have hbottom : (a + b + 1) - (a + 1) = b := by omega
      have hleft (k : Fin a) :
          almostSquareBlock L B C (Fin.last (a + b + 1))
              (k.castAdd (b + 2)) = 0 := by
        simp [almostSquareBlock, Fin.val_last, hrow, k.isLt]
      have hright (j : Fin (b + 2)) :
          almostSquareBlock L B C (Fin.last (a + b + 1))
              (j.natAdd a) = C (Fin.last b) j := by
        have hj : ¬ a + j.val < a := by omega
        simp [almostSquareBlock, Fin.val_last, hrow, hbottom, hj]
        rfl
      have hsign (j : Fin (b + 2)) :
          (-1 : R) ^ ((a + b + 1) + (a + j.val)) =
            (-1 : R) ^ (b + 1 + j.val) := by
        calc
          (-1 : R) ^ ((a + b + 1) + (a + j.val)) =
              (-1 : R) ^ (2 * a + (b + 1 + j.val)) := by
                congr 1
                omega
          _ = (-1 : R) ^ (b + 1 + j.val) := by
                rw [pow_add, pow_mul]
                simp
      have hstep :
          (almostSquareBlock L B C).det =
            ∑ j : Fin (b + 2),
              (-1 : R) ^ (b + 1 + j.val) * C (Fin.last b) j *
                (almostSquareBlock L (B.submatrix id j.succAbove)
                  (C.submatrix Fin.castSucc j.succAbove)).det := by
        let M : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) R :=
          almostSquareBlock L B C
        let f : Fin (a + (b + 2)) → R := fun j =>
          (-1 : R) ^ ((Fin.last (a + b + 1)).val + j.val) *
            M (Fin.last (a + b + 1)) j *
              Matrix.det (Matrix.submatrix M (Fin.last (a + b + 1)).succAbove j.succAbove)
        have hd : Matrix.det M = ∑ j, f j :=
          Matrix.det_succ_row M (Fin.last (a + b + 1))
        have hs : (∑ j, f j) =
            (∑ k : Fin a, f (k.castAdd (b + 2))) +
              ∑ j : Fin (b + 2), f (j.natAdd a) :=
          Fin.sum_univ_add f
        have hl (k : Fin a) : f (k.castAdd (b + 2)) = 0 := by
          dsimp only [f]
          have he : M (Fin.last (a + b + 1)) (k.castAdd (b + 2)) = 0 := hleft k
          rw [he, mul_zero, zero_mul]
        have hr (j : Fin (b + 2)) :
            f (j.natAdd a) =
              (-1 : R) ^ (b + 1 + j.val) * C (Fin.last b) j *
                (almostSquareBlock L (B.submatrix id j.succAbove)
                  (C.submatrix Fin.castSucc j.succAbove)).det := by
          have he : M (Fin.last (a + b + 1)) (j.natAdd a) = C (Fin.last b) j := hright j
          have hm : Matrix.submatrix M (Fin.last (a + b + 1)).succAbove
                (j.natAdd a).succAbove =
              almostSquareBlock L (B.submatrix id j.succAbove)
                (C.submatrix Fin.castSucc j.succAbove) := by
            simpa only [M, Fin.succAbove_last] using
              almostSquareBlock_last_right_minor L B C j
          dsimp only [f]
          rw [he, hm, Fin.val_last, Fin.val_natAdd, hsign]
        exact hd.trans (hs.trans (by
          simp only [hl, Finset.sum_const_zero, zero_add, hr]))
      have hcons (i : Fin (a + 1)) :
          Matrix.det
            (Matrix.vecCons (B i) C : Matrix (Fin (b + 2)) (Fin (b + 2)) R) =
            ∑ j : Fin (b + 2),
              (-1 : R) ^ (b + 1 + j.val) * C (Fin.last b) j *
                Matrix.det
                  (Matrix.vecCons ((B.submatrix id j.succAbove) i)
                    (C.submatrix Fin.castSucc j.succAbove) :
                      Matrix (Fin (b + 1)) (Fin (b + 1)) R) := by
        let N : Matrix (Fin (b + 2)) (Fin (b + 2)) R := Matrix.vecCons (B i) C
        have hentry (j : Fin (b + 2)) : N (Fin.last (b + 1)) j =
            C (Fin.last b) j := by
          simp only [N, Matrix.vecCons, Fin.cons_last]
        have hminor (j : Fin (b + 2)) :
            Matrix.submatrix N (Fin.last (b + 1)).succAbove j.succAbove =
              (Matrix.vecCons ((B.submatrix id j.succAbove) i)
                (C.submatrix Fin.castSucc j.succAbove) :
                  Matrix (Fin (b + 1)) (Fin (b + 1)) R) :=
          almostSquare_cons_last_minor B C i j
        change Matrix.det N = _
        rw [Matrix.det_succ_row N (Fin.last (b + 1))]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hentry, hminor]
        simp only [Fin.val_last]
      rw [hstep]
      simp_rw [ih, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcons, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end AlmostSquareBlock
private def twoParentRightCol (j : Fin (r + 2)) : Fin (p + r + 3) :=
  ⟨p + 1 + j.val, by omega⟩

private theorem twoComponentContext_right_column
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g w : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) (hw : 0 < w)
    (j : Fin (r + 2)) :
    (Q.twoComponentContext R u v g hu hv hg).col (twoParentRightCol (p := p) j) =
      (R.positiveBorder w v hw hv).col j + v - R.col (Fin.last r) := by
  cases j using Fin.lastCases with
  | last =>
    have he : twoParentRightCol (p := p) (Fin.last (r + 1)) =
        Fin.last (p + r + 2) := by
      apply Fin.ext
      simp only [twoParentRightCol, Fin.val_last]
      omega
    rw [he, twoComponentContext_col_last, positiveBorder_col_last]
    ring
  | cast j =>
    have he : twoParentRightCol (p := p) j.castSucc =
        (twoRightIndex (p := p) j).castSucc := by apply Fin.ext; rfl
    rw [he, twoComponentContext_col_right, positiveBorder_col_castSucc]

private theorem twoComponentContext_top_right_entry
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (i : Fin (p + 2)) (j : Fin (r + 2)) :
    (Q.twoComponentContext R u v g hu hv hg).matrix
        (twoParentLeftRow (r := r) i) (twoParentRightCol (p := p) j) =
      (R.positiveBorder (Q.twoComponentWeight u g hu i) v
        (Q.twoComponentWeight_pos u g hu hg i) hv).matrix 0 j := by
  change complete (_ - _) = complete (_ - _)
  rw [twoComponentContext_row_left_full,
    twoComponentContext_right_column Q R u v g (Q.twoComponentWeight u g hu i)
      hu hv hg (Q.twoComponentWeight_pos u g hu hg i) j,
    positiveBorder_row_zero]
  apply congrArg complete
  unfold componentOffset twoComponentWeight
  ring

private theorem twoComponentContext_bottom_right_entry
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (i : Fin (r + 1)) (j : Fin (r + 2)) :
    (Q.twoComponentContext R u v g hu hv hg).matrix
        (twoParentRightRow (p := p) i) (twoParentRightCol (p := p) j) =
      (R.positiveBorder 1 v (by norm_num) hv).matrix i.succ j := by
  change complete (_ - _) = complete (_ - _)
  rw [twoComponentContext_row_right_full,
    twoComponentContext_right_column Q R u v g 1 hu hv hg (by norm_num) j,
    positiveBorder_row_succ]
  apply congrArg complete
  ring

private theorem neg_one_pow_add_eq_sub (a i : ℕ) (hi : i ≤ a) :
    (-1 : CompleteRing) ^ (i + a) = (-1) ^ (a - i) := by
  rw [show i + a = (a - i) + 2 * i by omega, pow_add, pow_mul]
  simp

/-- Full almost-square block expansion of the actual normalized parent:
all original left cofactors and all genuine right borders are present
(`lem:two-component-lift`). -/
theorem twoComponentContext_left_expansion
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).schur =
      ∑ i : Fin (p + 2), (-1 : CompleteRing) ^ (p + 1 - i.val) *
        (Q.twoComponentLeftMinor u hu i).schur *
        (R.positiveBorder (Q.twoComponentWeight u g hu i) v
          (Q.twoComponentWeight_pos u g hu hg i) hv).schur := by
  let P := Q.twoComponentContext R u v g hu hv hg
  let L : Matrix (Fin (p + 2)) (Fin (p + 1)) CompleteRing :=
    fun i j => complete ((Q.positiveBorder u 1 hu (by norm_num)).row i - Q.col j)
  let B : Matrix (Fin (p + 2)) (Fin (r + 2)) CompleteRing :=
    fun i j => (R.positiveBorder (Q.twoComponentWeight u g hu i) v
      (Q.twoComponentWeight_pos u g hu hg i) hv).matrix 0 j
  let C : Matrix (Fin (r + 1)) (Fin (r + 2)) CompleteRing :=
    fun i j => (R.positiveBorder 1 v (by norm_num) hv).matrix i.succ j
  let ho : (p + 1) + (r + 1) + 1 = p + r + 3 := by omega
  have hM : P.matrix.submatrix (finCongr ho) (finCongr ho) = almostSquareBlock L B C := by
    apply Matrix.ext
    intro i j
    unfold almostSquareBlock
    split_ifs with hi hj hj
    · have hr : finCongr ho i = twoParentLeftRow (r := r) ⟨i.val, hi⟩ := by
        apply Fin.ext
        rfl
      have hc : finCongr ho j = (twoLeftIndex (r := r) ⟨j.val, hj⟩).castSucc := by
        apply Fin.ext
        rfl
      change P.matrix (finCongr ho i) (finCongr ho j) = _
      rw [hr, hc]
      change complete (_ - _) = complete (_ - _)
      rw [twoComponentContext_row_left_full, twoComponentContext_col_left]
      apply congrArg complete
      ring
    · have hr : finCongr ho i = twoParentLeftRow (r := r) ⟨i.val, hi⟩ := by
        apply Fin.ext
        rfl
      have hc : finCongr ho j =
          twoParentRightCol (p := p) ⟨j.val - (p + 1), by omega⟩ := by
        apply Fin.ext
        change j.val = p + 1 + (j.val - (p + 1))
        omega
      change P.matrix (finCongr ho i) (finCongr ho j) = _
      rw [hr, hc]
      exact twoComponentContext_top_right_entry Q R u v g hu hv hg _ _
    · have hr : finCongr ho i =
          twoParentRightRow (p := p) ⟨i.val - (p + 2), by omega⟩ := by
        apply Fin.ext
        change i.val = p + 2 + (i.val - (p + 2))
        omega
      have hc : finCongr ho j = (twoLeftIndex (r := r) ⟨j.val, hj⟩).castSucc := by
        apply Fin.ext
        rfl
      change P.matrix (finCongr ho i) (finCongr ho j) = 0
      rw [hr, hc]
      rw [← residual_apply_of_ne Q R u v g hu hv hg _ _ (Fin.castSucc_ne_last _)]
      exact residual_entry_lower_left Q R u v g hu hv hg _ _
    · have hr : finCongr ho i =
          twoParentRightRow (p := p) ⟨i.val - (p + 2), by omega⟩ := by
        apply Fin.ext
        change i.val = p + 2 + (i.val - (p + 2))
        omega
      have hc : finCongr ho j =
          twoParentRightCol (p := p) ⟨j.val - (p + 1), by omega⟩ := by
        apply Fin.ext
        change j.val = p + 1 + (j.val - (p + 1))
        omega
      change P.matrix (finCongr ho i) (finCongr ho j) = _
      rw [hr, hc]
      exact twoComponentContext_bottom_right_entry Q R u v g hu hv hg _ _
  have hdet : P.schur = (almostSquareBlock L B C).det := by
    rw [← hM, Matrix.det_submatrix_equiv_self]
    rfl
  rw [hdet, det_almostSquareBlock]
  apply Finset.sum_congr rfl
  intro i hi
  have hL : L.submatrix i.succAbove id = (Q.twoComponentLeftMinor u hu i).matrix := by
    apply Matrix.ext
    intro a b
    change complete ((Q.positiveBorder u 1 hu (by norm_num)).row (i.succAbove a) - Q.col b) =
      complete ((Q.positiveBorder u 1 hu (by norm_num)).row (i.succAbove a) -
        (Q.positiveBorder u 1 hu (by norm_num)).col b.castSucc)
    rw [positiveBorder_col_castSucc]
  have hR : Matrix.vecCons (B i) C =
      (R.positiveBorder (Q.twoComponentWeight u g hu i) v
        (Q.twoComponentWeight_pos u g hu hg i) hv).matrix := by
    apply Matrix.ext
    intro a b
    cases a using Fin.cases with
    | zero => rfl
    | succ a =>
      change complete (R.row a - _) = complete (R.row a - _)
      cases b using Fin.lastCases <;>
        simp only [positiveBorder_col_last, positiveBorder_col_castSucc]
  rw [hL, hR, neg_one_pow_add_eq_sub (p + 1) i.val (by omega)]
  rfl

/-- The full parent reflection difference is exactly the source's finite
almost-square cofactor sum, not an orientation certificate. -/
theorem twoComponentContext_reflection_difference
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).schur -
      (Q.twoComponentContext R.rotate u v g hu hv hg).schur =
        Q.twoComponentOrientationSum R u v g hu hv hg := by
  rw [twoComponentContext_left_expansion, twoComponentContext_left_expansion,
    ← Finset.sum_sub_distrib]
  unfold twoComponentOrientationSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [positiveBorder_rotate_schur]
  unfold borderDifference
  ring

/-- At the outer top tie its vanishing border term is deleted, and the
remaining actual derivative is the full sum in `eq:two-component-tie`. -/
theorem twoComponentOrientationSum_tied_derivative
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (h : v = g + Q.largestLabel + u)
    (k : ℕ+) (hk : (k.val : ℤ) = R.largestLabel + v) :
    MvPolynomial.pderiv k (Q.twoComponentOrientationSum R u v g hu hv hg) =
      (-1 : CompleteRing) ^ (r + 3) * Q.twoComponentTieSum R u g hu hg := by
  have hleft : ∀ i : Fin (p + 3),
      MvPolynomial.pderiv k (Q.twoComponentLeftMinor u hu i).schur = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := Q.twoComponentLeftMinor_vars_le u hu i k hm
    have hs := R.largestLabel_pos
    omega
  have hzero : R.borderDifference (Q.twoComponentWeight u g hu 0) v
      (Q.twoComponentWeight_pos u g hu hg 0) hv = 0 := by
    have hw : Q.twoComponentWeight u g hu 0 = v := by
      rw [twoComponentWeight_zero, h]
    simp only [hw, borderDifference, sub_self]
  rw [twoComponentOrientationSum, Fin.sum_univ_succ, hzero, mul_zero, zero_add, map_sum]
  unfold twoComponentTieSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hw := Q.twoComponentWeight_lt_zero u g hu i.succ (Fin.succ_ne_zero _)
  rw [twoComponentWeight_zero, ← h] at hw
  have hd := borderDifference_coefficient_at_of_lt R
    (Q.twoComponentWeight u g hu i.succ) v
    (Q.twoComponentWeight_pos u g hu hg i.succ) hv hw k hk
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, pderiv_sign_pow, hleft, hd]
  simp only [zero_mul, mul_zero, zero_add, twoComponentWeight_succ]
  have he : p + 2 - i.succ.val = p + 1 - i.val := by
    simp only [Fin.val_succ]
    omega
  rw [he]
  ring

/-- The three actual derivative regimes for the full tie sum prohibit the
remaining reflection at the outer top tie. -/
theorem twoComponentOrientationSum_ne_zero_of_eq
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hZQ : Q.ZeroFree) (hR : R.EndpointLeader)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (h : v = g + Q.largestLabel + u) :
    Q.twoComponentOrientationSum R u v g hu hv hg ≠ 0 := by
  let K := R.largestLabel + v
  have hpos : 0 < K := by
    have hs := R.largestLabel_pos
    dsimp [K]
    omega
  let k : ℕ+ := ⟨K.toNat, by omega⟩
  have hk : (k.val : ℤ) = R.largestLabel + v := by dsimp [k, K]; omega
  intro hz
  have hd := congrArg (MvPolynomial.pderiv k) hz
  rw [twoComponentOrientationSum_tied_derivative Q R u v g hu hv hg h k hk, map_zero] at hd
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Q.twoComponentTieSum_ne_zero R hQ hZQ hR u g hu hg) hd

private noncomputable def twoComponentFullEndpointSum
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (u g : ℤ) (hu : 0 < u) (hg : 0 < g) : CompleteRing :=
  ∑ i : Fin (p + 3), (-1 : CompleteRing) ^ (p + 2 - i.val) *
    (Q.twoComponentLeftMinor u hu i).schur *
    R.endpointDifference (Q.twoComponentWeight u g hu i)
      (Q.twoComponentWeight_pos u g hu hg i)

private theorem twoComponentFullEndpointSum_ne_zero
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2)) (hR : R.EndpointLeader)
    (u g : ℤ) (hu : 0 < u) (hg : 0 < g) :
    Q.twoComponentFullEndpointSum R u g hu hg ≠ 0 := by
  obtain ⟨κ, hκ, hκS, c, hc, hd⟩ := R.endpointLeader_maxLabel hR
  let w := Q.twoComponentWeight u g hu 0
  have hw : 0 < w := Q.twoComponentWeight_pos u g hu hg 0
  let k : ℕ+ := ⟨(κ + w).toNat, by omega⟩
  have hk : (k.val : ℤ) = κ + w := by dsimp [k]; omega
  have hleft : ∀ i : Fin (p + 3),
      MvPolynomial.pderiv k (Q.twoComponentLeftMinor u hu i).schur = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := Q.twoComponentLeftMinor_vars_le u hu i k hm
    have hw0 := Q.twoComponentWeight_zero u g hu
    change w = g + Q.largestLabel + u at hw0
    omega
  have htop : MvPolynomial.pderiv k
      (R.endpointDifference (Q.twoComponentWeight u g hu 0)
        (Q.twoComponentWeight_pos u g hu hg 0)) = c := by
    exact (hd w hw).1
  have hrest : ∀ i : Fin (p + 2), MvPolynomial.pderiv k
      (R.endpointDifference (Q.twoComponentWeight u g hu i.succ)
        (Q.twoComponentWeight_pos u g hu hg i.succ)) = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := (hd (Q.twoComponentWeight u g hu i.succ)
      (Q.twoComponentWeight_pos u g hu hg i.succ)).2.2 k hm
    have ht := Q.twoComponentWeight_lt_zero u g hu i.succ (Fin.succ_ne_zero _)
    change Q.twoComponentWeight u g hu i.succ < w at ht
    omega
  intro hz
  have he := congrArg (MvPolynomial.pderiv k) hz
  rw [twoComponentFullEndpointSum, Fin.sum_univ_succ, map_add, map_sum, map_zero,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, pderiv_sign_pow, hleft, htop] at he
  have htail : (∑ i : Fin (p + 2), MvPolynomial.pderiv k
      ((-1 : CompleteRing) ^ (p + 2 - i.succ.val) *
        (Q.twoComponentLeftMinor u hu i.succ).schur *
        R.endpointDifference (Q.twoComponentWeight u g hu i.succ)
          (Q.twoComponentWeight_pos u g hu hg i.succ))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, pderiv_sign_pow, hleft, hrest]
    ring
  rw [htail, twoComponentLeftMinor_zero] at he
  have hn := mul_ne_zero (pow_ne_zero (p + 2) (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero Q.schur_ne_zero hc)
  apply hn
  simpa only [Fin.val_zero, Nat.sub_zero, zero_mul, mul_zero, zero_add, add_zero,
    mul_assoc] using he

/-- Above the outer top weight, the common first border derivative is the
full endpoint sum; its outer row has a strictly private fixed-leader index. -/
theorem twoComponentOrientationSum_ne_zero_of_gt
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2)) (hR : R.EndpointLeader)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (h : g + Q.largestLabel + u < v) :
    Q.twoComponentOrientationSum R u v g hu hv hg ≠ 0 := by
  let K := R.largestLabel + v
  have hpos : 0 < K := by
    have hs := R.largestLabel_pos
    dsimp [K]
    omega
  let k : ℕ+ := ⟨K.toNat, by omega⟩
  have hk : (k.val : ℤ) = R.largestLabel + v := by dsimp [k, K]; omega
  have hleft : ∀ i : Fin (p + 3),
      MvPolynomial.pderiv k (Q.twoComponentLeftMinor u hu i).schur = 0 := by
    intro i
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := Q.twoComponentLeftMinor_vars_le u hu i k hm
    have hs := R.largestLabel_pos
    omega
  have hweight : ∀ i : Fin (p + 3), Q.twoComponentWeight u g hu i < v := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [twoComponentWeight_zero] using h
    · have hw := Q.twoComponentWeight_lt_zero u g hu i hi
      rw [twoComponentWeight_zero] at hw
      omega
  have hder : MvPolynomial.pderiv k (Q.twoComponentOrientationSum R u v g hu hv hg) =
      (-1 : CompleteRing) ^ (r + 3) * Q.twoComponentFullEndpointSum R u g hu hg := by
    rw [twoComponentOrientationSum, map_sum, twoComponentFullEndpointSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, pderiv_sign_pow, hleft,
      borderDifference_coefficient_at_of_lt R _ v
        (Q.twoComponentWeight_pos u g hu hg i) hv (hweight i) k hk]
    ring
  intro hz
  have hd := congrArg (MvPolynomial.pderiv k) hz
  rw [hder, map_zero] at hd
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Q.twoComponentFullEndpointSum_ne_zero R hR u g hu hg) hd

/-- All three actual outer-weight regimes exclude the remaining reflection;
the equality case uses the full three-way `B_Q c_R` coefficient table. -/
theorem twoComponentOrientationSum_ne_zero
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hZQ : Q.ZeroFree) (hR : R.EndpointLeader)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    Q.twoComponentOrientationSum R u v g hu hv hg ≠ 0 := by
  rcases lt_trichotomy v (g + Q.largestLabel + u) with h | h | h
  · exact Q.twoComponentOrientationSum_ne_zero_of_lt R hR u v g hu hv hg h
  · exact Q.twoComponentOrientationSum_ne_zero_of_eq R hQ hZQ hR u v g hu hv hg h
  · exact Q.twoComponentOrientationSum_ne_zero_of_gt R hR u v g hu hv hg h

/-- The actual two-component parent changes when only its nonsymmetric right
core is reflected. -/
theorem twoComponentContext_reflected_right_ne
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hZQ : Q.ZeroFree) (hR : R.EndpointLeader)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).schur ≠
      (Q.twoComponentContext R.rotate u v g hu hv hg).schur := by
  intro he
  apply Q.twoComponentOrientationSum_ne_zero R hQ hZQ hR u v g hu hv hg
  rw [← twoComponentContext_reflection_difference, he, sub_self]

/-- Once the literal left orientation and top margin are read, the actual
bottom separator reads the bottom margin and the full span reads the gap.
The last possible right-core reflection is then excluded by its fixed leader. -/
theorem twoComponent_rigidity_between_right_contexts
    (Q : BetaDiagram (p + 2)) (R W : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hZQ : Q.ZeroFree)
    (hR : R.Connected) (hW : W.Connected) (hZR : R.ZeroFree) (hZW : W.ZeroFree)
    (hcore : R.schur = W.schur) (hRR : R.RotationRigid)
    (hLeader : ¬ R.Symmetric → R.EndpointLeader)
    (u vm vp gm gp : ℤ)
    (hu : 0 < u) (hvm : 0 < vm) (hvp : 0 < vp) (hgm : 0 < gm) (hgp : 0 < gp)
    (he : (Q.twoComponentContext R u vm gm hu hvm hgm).schur =
      (Q.twoComponentContext W u vp gp hu hvp hgp).schur) :
    vm = vp ∧ gm = gp ∧ R.TranslationEquivalent W := by
  have hspan := (Q.twoComponentContext R u vm gm hu hvm hgm).largestLabel_eq_of_schur_eq
    (Q.twoComponentContext W u vp gp hu hvp hgp)
    (Q.twoComponentContext_connected R u vm gm hu hvm hgm)
    (Q.twoComponentContext_connected W u vp gp hu hvp hgp) he
  have hv : vm = vp := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Q.twoComponent_margin_comparison_ne R W hR hW hZW hcore
        u vm vp gm gp hu hvm hvp hgm hgp h hspan he
    · exact Q.twoComponent_margin_comparison_ne W R hW hR hZR hcore.symm
        u vp vm gp gm hu hvp hvm hgp hgm h hspan.symm he.symm
  have hs := R.largestLabel_eq_of_schur_eq W hR hW hcore
  have hg : gm = gp := by
    rw [twoComponentContext_span, twoComponentContext_span] at hspan
    omega
  refine ⟨hv, hg, ?_⟩
  subst vp
  subst gp
  obtain hT | hRot := (R.rotationRigid_iff_same_order.mp hRR) W hW hcore.symm
  · exact hT
  · by_cases hS : R.Symmetric
    · exact R.translation_of_rotation_of_symmetric W hS hRot
    · have hTW := R.rotated_core_translation W hRot
      have hQQ : Q.TranslationEquivalent Q :=
        ⟨0, (fun i => by ring), (fun i => by ring)⟩
      have hparent := Q.twoComponentContext_eq_of_core_translations Q W R.rotate
        hQQ hTW u vm gm hu hvm hgm
      rw [hparent] at he
      exact (Q.twoComponentContext_reflected_right_ne R hQ hZQ (hLeader hS)
        u vm gm hu hvm hgm he).elim

/-- Equality of actual top extensions fixes the old core orientation from
core rigidity and its fixed-leader-or-symmetry dichotomy alone. -/
theorem core_translation_of_top_extension_eq
    (Q W : BetaDiagram (p + 2)) (hW : W.Connected)
    (hcore : Q.schur = W.schur) (hRQ : Q.RotationRigid)
    (hLeader : ¬ Q.Symmetric → Q.EndpointLeader)
    (q : ℤ) (hq : 0 < q)
    (he : (Q.extendTop q hq).schur = (W.extendTop q hq).schur) :
    Q.TranslationEquivalent W := by
  obtain hT | hR := (Q.rotationRigid_iff_same_order.mp hRQ) W hW hcore.symm
  · exact hT
  · by_cases hS : Q.Symmetric
    · exact Q.translation_of_rotation_of_symmetric W hS hR
    · have hR' : W.RotationEquivalent Q := by
        obtain ⟨c, hr, hc⟩ := hR
        refine ⟨c, ?_, ?_⟩
        · intro i
          have hh := hc i.rev
          simp only [Fin.rev_rev] at hh
          omega
        · intro i
          have hh := hr i.rev
          simp only [Fin.rev_rev] at hh
          omega
      have hh := W.extendTop_schur_eq_extendBottom_of_rotation Q hR' q hq
      have hz : Q.endpointDifference q hq = 0 := by
        unfold endpointDifference
        rw [he, hh, sub_self]
      exact (EndpointLeader.difference_ne_zero Q (hLeader hS) q hq hz).elim

/-- In two actual strict-top contexts, the marker fixes the enlarged left
factor and its orientation.  No common gap, bottom margin, or orientation of
the competing right core is assumed. -/
theorem twoComponent_strict_top_contexts_comparison
    (Q W : BetaDiagram (p + 2)) (R T : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hR : R.Connected) (hT : T.Connected)
    (hZQ : Q.ZeroFree) (hZR : R.ZeroFree) (hZT : T.ZeroFree)
    (hQW : Q.schur = W.schur) (hRT : R.schur = T.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (htop : u < v) (hTop : U < V)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    u = U ∧ v = V ∧ g = G ∧ Q.TranslationEquivalent W ∧ R.TranslationEquivalent T := by
  have hmin := twoComponent_min_margin_eq_of_schur_eq Q R W T hQ hR hW hT
    u v g U V G hu hv hg hU hV hG he
  rw [min_eq_left htop.le, min_eq_left hTop.le] at hmin
  subst U
  have hm := twoComponentRegimeCoefficient_eq_of_schur_eq Q R W T hQ hR hW hT
    u v g u V G hu hv hg hU hV hG he
  simp only [twoComponentRegimeCoefficient, htop, hTop, ite_true] at hm
  rw [← hRT] at hm
  have hendpoint : (Q.extendTop u hu).schur = (W.extendTop u hu).schur :=
    mul_right_cancel₀ R.schur_ne_zero hm
  have hleft := core_translation_of_top_extension_eq Q W hW hQW hRQ hLeaderQ
    u hu hendpoint
  have hTT : T.TranslationEquivalent T :=
    ⟨0, (fun i => by ring), (fun i => by ring)⟩
  have hparent := Q.twoComponentContext_eq_of_core_translations W T T hleft hTT
    u V G hu hV hG
  rw [← hparent] at he
  obtain ⟨hvV, hgG, hright⟩ := Q.twoComponent_rigidity_between_right_contexts R T
    hQ hZQ hR hT hZR hZT hRT hRR hLeaderR u v V g G hu hv hV hg hG he
  exact ⟨rfl, hvV, hgG, hleft, hright⟩

/-- Reduction of the tied marker modulo its first old irreducible factor
produces equality of the actual top extensions.  Weighted area prevents a
nonzero scalar quotient. -/
theorem twoComponent_tied_top_extension_eq_distinct
    (Q W : BetaDiagram (p + 2)) (R T : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hR : R.Connected)
    (hQW : Q.schur = W.schur) (hRT : R.schur = T.schur)
    (hne : Q.schur ≠ R.schur) (q : ℤ) (hq : 0 < q)
    (hm : (Q.extendTop q hq).schur * R.schur +
        Q.schur * (R.extendBottom q hq).schur =
      (W.extendTop q hq).schur * T.schur +
        W.schur * (T.extendBottom q hq).schur) :
    (Q.extendTop q hq).schur = (W.extendTop q hq).schur := by
  have hp : Prime Q.schur :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hQ)
  have hn : ¬ Q.schur ∣ R.schur := by
    intro h
    exact hne (Q.schur_eq_of_connected_dvd R hQ hR h)
  rw [← hQW, ← hRT] at hm
  have hd : Q.schur ∣
      ((Q.extendTop q hq).schur - (W.extendTop q hq).schur) * R.schur := by
    refine ⟨(T.extendBottom q hq).schur - (R.extendBottom q hq).schur, ?_⟩
    linear_combination hm
  have hd' := (hp.dvd_mul.mp hd).resolve_right hn
  exact Q.endpoint_top_eq_of_old_factor_dvd W hQW q hq hd'

/-- Distinct aligned old factors in actual tied-margin parents determine
both component orientations and the actual gap. -/
theorem twoComponent_tied_contexts_comparison_distinct
    (Q W : BetaDiagram (p + 2)) (R T : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hR : R.Connected) (hT : T.Connected)
    (hZQ : Q.ZeroFree) (hZR : R.ZeroFree) (hZT : T.ZeroFree)
    (hQW : Q.schur = W.schur) (hRT : R.schur = T.schur)
    (hne : Q.schur ≠ R.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (q t g G : ℤ) (hq : 0 < q) (ht : 0 < t) (hg : 0 < g) (hG : 0 < G)
    (he : (Q.twoComponentContext R q q g hq hq hg).schur =
      (W.twoComponentContext T t t G ht ht hG).schur) :
    q = t ∧ g = G ∧ Q.TranslationEquivalent W ∧ R.TranslationEquivalent T := by
  have hmarg := twoComponent_min_margin_eq_of_schur_eq Q R W T hQ hR hW hT
    q q g t t G hq hq hg ht ht hG he
  simp only [min_self] at hmarg
  subst t
  have hm := twoComponentRegimeCoefficient_eq_of_schur_eq Q R W T hQ hR hW hT
    q q g q q G hq hq hg ht ht hG he
  simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false] at hm
  have hext := Q.twoComponent_tied_top_extension_eq_distinct W R T hQ hR
    hQW hRT hne q hq hm
  have hleft := core_translation_of_top_extension_eq Q W hW hQW hRQ hLeaderQ q hq hext
  have hTT : T.TranslationEquivalent T :=
    ⟨0, (fun i => by ring), (fun i => by ring)⟩
  have hparent := Q.twoComponentContext_eq_of_core_translations W T T hleft hTT q q G hq hq hG
  rw [← hparent] at he
  obtain ⟨_, hgG, hright⟩ := Q.twoComponent_rigidity_between_right_contexts R T
    hQ hZQ hR hT hZR hZT hRT hRR hLeaderR q q q g G hq hq hq hg hG he
  exact ⟨rfl, hgG, hleft, hright⟩


-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/PositiveBorders.lean
private theorem positiveBorder_rotation_of_rotation {n : ℕ}
    {D E : BetaDiagram (n + 1)} (h : D.RotationEquivalent E)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).RotationEquivalent
      (E.positiveBorder v u hv hu) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      have h := hr 0
      rw [Fin.rev_zero] at h
      simp only [positiveBorder_row_zero, Fin.rev_zero, positiveBorder_col_last]
      omega
    | succ i =>
      simpa only [positiveBorder_row_succ, Fin.rev_succ,
        positiveBorder_col_castSucc] using hr i
  · intro i
    cases i using Fin.lastCases with
    | last =>
      have h := hc (Fin.last n)
      rw [Fin.rev_last] at h
      simp only [positiveBorder_col_last, Fin.rev_last, positiveBorder_row_zero]
      omega
    | cast i =>
      simpa only [positiveBorder_col_castSucc, Fin.rev_castSucc,
        positiveBorder_row_succ] using hc i

private theorem shifted_rotation_of_rotation {n : ℕ}
    {D E : BetaDiagram n} (h : D.RotationEquivalent E) (a b : ℤ) :
    (D.shifted a).RotationEquivalent (E.shifted b) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c + a + b, ?_, ?_⟩
  · intro i
    change D.row i + a = c + a + b - (E.col i.rev + b)
    rw [hr i]
    ring
  · intro i
    change D.col i + a = c + a + b - (E.row i.rev + b)
    rw [hc i]
    ring

private theorem reindexOrder_positiveBorder_shifted {a b : ℕ}
    (E : BetaDiagram (b + 1)) (h : a + 1 = b + 1)
    (h' : a + 2 = b + 2) (u v s : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (((E.reindexOrder h).positiveBorder u v hu hv).shifted s) =
      (((E.positiveBorder u v hu hv).shifted s).reindexOrder h') := by
  have hab : a = b := by omega
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  have hh' : h' = rfl := Subsingleton.elim _ _
  rw [hh, hh']
  rfl

theorem componentOffset_rotate_swap (Q : BetaDiagram (p + 1))
    (R : BetaDiagram (r + 1)) (g : ℤ) :
    Q.componentOffset R g = R.rotate.componentOffset Q.rotate g := by
  simp only [componentOffset, rotate, Fin.rev_zero, Fin.rev_last]
  ring

private theorem twoCore_cast_rev_left (i : Fin (p + 1))
    (h : p + r + 2 = r + p + 2) :
    Fin.cast h (twoLeftIndex (r := r) i).rev =
      twoRightIndex (p := r) i.rev := by
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_rev, twoLeftIndex, twoRightIndex]
  omega

private theorem twoCore_cast_rev_right (j : Fin (r + 1))
    (h : p + r + 2 = r + p + 2) :
    Fin.cast h (twoRightIndex (p := p) j).rev =
      twoLeftIndex (r := p) j.rev := by
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_rev, twoLeftIndex, twoRightIndex]
  omega

theorem twoComponentCore_rotate_swap (Q : BetaDiagram (p + 1))
    (R : BetaDiagram (r + 1)) (g : ℤ) (hg : 0 < g)
    (hCore : p + r + 2 = r + p + 2) :
    (Q.twoComponentCore R g hg).RotationEquivalent
      ((R.rotate.twoComponentCore Q.rotate g hg).reindexOrder hCore) := by
  have hoff := Q.componentOffset_rotate_swap R g
  refine ⟨Q.componentOffset R g, ?_, ?_⟩
  · intro k
    by_cases hk : k.val < p + 1
    · let i : Fin (p + 1) := ⟨k.val, hk⟩
      have he : k = twoLeftIndex (r := r) i := by
        apply Fin.ext
        rfl
      rw [he, twoComponentCore_row_left]
      change Q.row i + Q.componentOffset R g =
        Q.componentOffset R g -
          (R.rotate.twoComponentCore Q.rotate g hg).col
            (Fin.cast hCore (twoLeftIndex (r := r) i).rev)
      rw [twoCore_cast_rev_left, twoComponentCore_col_right]
      simp only [rotate, Fin.rev_rev]
      ring
    · let j : Fin (r + 1) := ⟨k.val - (p + 1), by omega⟩
      have he : k = twoRightIndex (p := p) j := by
        apply Fin.ext
        simp only [twoRightIndex, j]
        omega
      rw [he, twoComponentCore_row_right]
      change R.row j = Q.componentOffset R g -
        (R.rotate.twoComponentCore Q.rotate g hg).col
          (Fin.cast hCore (twoRightIndex (p := p) j).rev)
      rw [twoCore_cast_rev_right, twoComponentCore_col_left, ← hoff]
      simp only [rotate, Fin.rev_rev]
      ring
  · intro k
    by_cases hk : k.val < p + 1
    · let i : Fin (p + 1) := ⟨k.val, hk⟩
      have he : k = twoLeftIndex (r := r) i := by
        apply Fin.ext
        rfl
      rw [he, twoComponentCore_col_left]
      change Q.col i + Q.componentOffset R g =
        Q.componentOffset R g -
          (R.rotate.twoComponentCore Q.rotate g hg).row
            (Fin.cast hCore (twoLeftIndex (r := r) i).rev)
      rw [twoCore_cast_rev_left, twoComponentCore_row_right]
      simp only [rotate, Fin.rev_rev]
      ring
    · let j : Fin (r + 1) := ⟨k.val - (p + 1), by omega⟩
      have he : k = twoRightIndex (p := p) j := by
        apply Fin.ext
        simp only [twoRightIndex, j]
        omega
      rw [he, twoComponentCore_col_right]
      change R.col j = Q.componentOffset R g -
        (R.rotate.twoComponentCore Q.rotate g hg).row
          (Fin.cast hCore (twoRightIndex (p := p) j).rev)
      rw [twoCore_cast_rev_right, twoComponentCore_row_left, ← hoff]
      simp only [rotate, Fin.rev_rev]
      ring

theorem twoComponentContext_rotate_swap (Q : BetaDiagram (p + 1))
    (R : BetaDiagram (r + 1)) (u v g : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let hParent : p + r + 3 = r + p + 3 := by omega
    (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent
      ((R.rotate.twoComponentContext Q.rotate v u g hv hu hg).reindexOrder hParent) := by
  dsimp only
  let hCore : p + r + 2 = r + p + 2 := by omega
  let hParent : p + r + 3 = r + p + 3 := by omega
  have h := positiveBorder_rotation_of_rotation
    (Q.twoComponentCore_rotate_swap R g hg hCore) u v hu hv
  have hs := shifted_rotation_of_rotation h
    (v - R.col (Fin.last r)) (u - Q.rotate.col (Fin.last p))
  rw [reindexOrder_positiveBorder_shifted
    (a := p + r + 1) (b := r + p + 1)
    (R.rotate.twoComponentCore Q.rotate g hg) hCore hParent
    v u (u - Q.rotate.col (Fin.last p)) hv hu] at hs
  exact hs


private theorem tied_equal_rotation_symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.RotationEquivalent E) : E.RotationEquivalent D := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    have hh := hc i.rev
    simp only [Fin.rev_rev] at hh
    omega
  · intro i
    have hh := hr i.rev
    simp only [Fin.rev_rev] at hh
    omega

private theorem tied_equal_translation_symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : E.TranslationEquivalent D := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨-c, ?_, ?_⟩ <;> intro i
  · have hh := hr i
    omega
  · have hh := hc i
    omega

private theorem tied_equal_translation_rotation {n : ℕ}
    {D E F : BetaDiagram n}
    (hDE : D.TranslationEquivalent E) (hEF : E.RotationEquivalent F) :
    D.RotationEquivalent F := by
  obtain ⟨a, hDr, hDc⟩ := hDE
  obtain ⟨b, hEr, hEc⟩ := hEF
  refine ⟨a + b, ?_, ?_⟩ <;> intro i
  · have hd := hDr i
    have he := hEr i
    omega
  · have hd := hDc i
    have he := hEc i
    omega

private theorem tied_equal_rotation_endpoints {n : ℕ}
    (D E : BetaDiagram (n + 1)) (h : D.RotationEquivalent E)
    (q : ℤ) (hq : 0 < q) :
    (D.extendTop q hq).schur = (E.extendBottom q hq).schur ∧
      (D.extendBottom q hq).schur = (E.extendTop q hq).schur := by
  exact ⟨D.extendTop_schur_eq_extendBottom_of_rotation E h q hq,
    (E.extendTop_schur_eq_extendBottom_of_rotation D
      (tied_equal_rotation_symm h) q hq).symm⟩

private theorem tied_equal_symmetric_of_difference_zero {n : ℕ}
    (D : BetaDiagram (n + 1))
    (hLeader : ¬ D.Symmetric → D.EndpointLeader)
    (q : ℤ) (hq : 0 < q) (hz : D.endpointDifference q hq = 0) :
    D.Symmetric := by
  by_contra hn
  exact EndpointLeader.difference_ne_zero D (hLeader hn) q hq hz

/-- Cancellation of the common old factor in the actual tied marker fixes
both core orientations up to the simultaneous swapped reflection. -/
theorem twoComponent_tied_core_orientations_equal
    (Q R W T : BetaDiagram (p + 2))
    (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur)
    (hQT : Q.schur = T.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (q : ℤ) (hq : 0 < q)
    (hm : (Q.extendTop q hq).schur * R.schur +
        Q.schur * (R.extendBottom q hq).schur =
      (W.extendTop q hq).schur * T.schur +
        W.schur * (T.extendBottom q hq).schur) :
    (Q.TranslationEquivalent W ∧ R.TranslationEquivalent T) ∨
      (Q.RotationEquivalent T ∧ R.RotationEquivalent W) := by
  have hs : (Q.extendTop q hq).schur + (R.extendBottom q hq).schur =
      (W.extendTop q hq).schur + (T.extendBottom q hq).schur := by
    rw [← hQR, ← hQW, ← hQT] at hm
    have hc : Q.schur *
        ((Q.extendTop q hq).schur + (R.extendBottom q hq).schur) =
      Q.schur *
        ((W.extendTop q hq).schur + (T.extendBottom q hq).schur) := by
      calc
        _ = (Q.extendTop q hq).schur * Q.schur +
            Q.schur * (R.extendBottom q hq).schur := by ring
        _ = (W.extendTop q hq).schur * Q.schur +
            Q.schur * (T.extendBottom q hq).schur := hm
        _ = _ := by ring
    exact mul_left_cancel₀ Q.schur_ne_zero hc
  have hRT : R.schur = T.schur := hQR.symm.trans hQT
  obtain hQWtr | hQWrot :=
    (Q.rotationRigid_iff_same_order.mp hRQ) W hW hQW.symm
  · obtain hRTtr | hRTrot :=
      (R.rotationRigid_iff_same_order.mp hRR) T hT hRT.symm
    · exact Or.inl ⟨hQWtr, hRTtr⟩
    · have htop := Q.extendTop_schur_eq_of_translation W hQWtr q hq
      have hrot := tied_equal_rotation_endpoints R T hRTrot q hq
      have hz : R.endpointDifference q hq = 0 := by
        unfold endpointDifference
        rw [← htop, ← hrot.1] at hs
        linear_combination -hs
      have hsym := tied_equal_symmetric_of_difference_zero R hLeaderR q hq hz
      exact Or.inl ⟨hQWtr, R.translation_of_rotation_of_symmetric T hsym hRTrot⟩
  · obtain hRTtr | hRTrot :=
      (R.rotationRigid_iff_same_order.mp hRR) T hT hRT.symm
    · have hbot := R.extendBottom_schur_eq_of_translation T hRTtr q hq
      have hrot := tied_equal_rotation_endpoints Q W hQWrot q hq
      have hz : Q.endpointDifference q hq = 0 := by
        unfold endpointDifference
        rw [← hbot, ← hrot.2] at hs
        linear_combination hs
      have hsym := tied_equal_symmetric_of_difference_zero Q hLeaderQ q hq hz
      exact Or.inl ⟨Q.translation_of_rotation_of_symmetric W hsym hQWrot, hRTtr⟩
    · have hQends := tied_equal_rotation_endpoints Q W hQWrot q hq
      have hRends := tied_equal_rotation_endpoints R T hRTrot q hq
      have hd : Q.endpointDifference q hq = R.endpointDifference q hq := by
        unfold endpointDifference
        rw [← hQends.2, ← hRends.1] at hs
        linear_combination hs
      have hQRtr : Q.TranslationEquivalent R := by
        obtain htr | hrot :=
          (Q.rotationRigid_iff_same_order.mp hRQ) R hR hQR.symm
        · exact htr
        · have hends := tied_equal_rotation_endpoints Q R hrot q hq
          have hopp : Q.endpointDifference q hq = -R.endpointDifference q hq := by
            unfold endpointDifference
            rw [hends.1, hends.2]
            ring
          have hz : Q.endpointDifference q hq = 0 := by
            have hz2 : (2 : CompleteRing) * Q.endpointDifference q hq = 0 := by
              linear_combination hd + hopp
            exact (mul_eq_zero.mp hz2).resolve_left (by norm_num)
          have hsym := tied_equal_symmetric_of_difference_zero Q hLeaderQ q hq hz
          exact Q.translation_of_rotation_of_symmetric R hsym hrot
      exact Or.inr ⟨tied_equal_translation_rotation hQRtr hRTrot,
        tied_equal_translation_rotation (tied_equal_translation_symm hQRtr) hQWrot⟩

/-- Actual Schur equality of tied-margin parents with equal old factors reads
the gap and yields either aligned translations or swapped core rotations. -/
theorem twoComponent_tied_contexts_comparison_equal
    (Q R W T : BetaDiagram (p + 2))
    (hQ : Q.Connected) (hR : R.Connected)
    (hW : W.Connected) (hT : T.Connected)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur)
    (hQT : Q.schur = T.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (q g G : ℤ) (hq : 0 < q) (hg : 0 < g) (hG : 0 < G)
    (he : (Q.twoComponentContext R q q g hq hq hg).schur =
      (W.twoComponentContext T q q G hq hq hG).schur) :
    g = G ∧ ((Q.TranslationEquivalent W ∧ R.TranslationEquivalent T) ∨
      (Q.RotationEquivalent T ∧ R.RotationEquivalent W)) := by
  have hRT : R.schur = T.schur := hQR.symm.trans hQT
  have hspan :=
    (Q.twoComponentContext R q q g hq hq hg).largestLabel_eq_of_schur_eq
      (W.twoComponentContext T q q G hq hq hG)
      (Q.twoComponentContext_connected R q q g hq hq hg)
      (W.twoComponentContext_connected T q q G hq hq hG) he
  have hQspan := Q.largestLabel_eq_of_schur_eq W hQ hW hQW
  have hRspan := R.largestLabel_eq_of_schur_eq T hR hT hRT
  have hgap : g = G := by
    rw [twoComponentContext_span, twoComponentContext_span] at hspan
    omega
  have hm := twoComponentRegimeCoefficient_eq_of_schur_eq Q R W T hQ hR hW hT
    q q g q q G hq hq hg hq hq hG he
  simp only [twoComponentRegimeCoefficient, lt_self_iff_false, ite_false] at hm
  exact ⟨hgap, twoComponent_tied_core_orientations_equal Q R W T hR hW hT
    hQR hQW hQT hRQ hRR hLeaderQ hLeaderR q hq hm⟩
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ThreeComponentContexts.lean
private theorem twoCore_zeroFree_rotate {n : ℕ} (D : BetaDiagram n) (h : D.ZeroFree) :
    D.rotate.ZeroFree := by
  intro i j he
  apply h j.rev i.rev
  change -D.col i.rev = -D.row j.rev at he
  omega

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ThreeComponentContexts.lean
private theorem twoCore_rotationRigid_rotate {n : ℕ}
    (D : BetaDiagram n) (hD : D.RotationRigid) : D.rotate.RotationRigid := by
  rw [rotationRigid_iff_same_order] at hD ⊢
  intro E hE he
  have hp : E.schur = D.schur := by simpa only [rotate_schur] using he
  rcases hD E hE hp with ⟨t, hr, hc⟩ | ⟨t, hr, hc⟩
  · refine Or.inr ⟨-t, ?_, ?_⟩
    · intro i
      change -D.col i.rev = -t - E.col i.rev
      rw [hc i.rev]
      ring
    · intro i
      change -D.row i.rev = -t - E.row i.rev
      rw [hr i.rev]
      ring
  · refine Or.inl ⟨-t, ?_, ?_⟩
    · intro i
      have hh := hc i.rev
      simp only [Fin.rev_rev] at hh
      change -D.col i.rev = E.row i + (-t)
      omega
    · intro i
      have hh := hr i.rev
      simp only [Fin.rev_rev] at hh
      change -D.row i.rev = E.col i + (-t)
      omega

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/FiveEndpointLeader.lean
private theorem twoCore_symmetric_of_rotate {n : ℕ}
    (D : BetaDiagram n) (h : D.rotate.Symmetric) : D.Symmetric := by
  obtain ⟨k, hr, hc⟩ := h
  refine ⟨-k, ?_, ?_⟩
  · intro i
    have hh := hc i.rev
    simp only [rotate, Fin.rev_rev] at hh
    omega
  · intro i
    have hh := hr i.rev
    simp only [rotate, Fin.rev_rev] at hh
    omega

private theorem twoCore_symmetric_rotate {n : ℕ}
    (D : BetaDiagram n) (h : D.Symmetric) : D.rotate.Symmetric := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨-c, ?_, ?_⟩
  · intro i
    have hh := hc i.rev
    simp only [Fin.rev_rev] at hh
    simp only [rotate, Fin.rev_rev]
    omega
  · intro i
    have hh := hr i.rev
    simp only [Fin.rev_rev] at hh
    simp only [rotate, Fin.rev_rev]
    omega

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/FiveEndpointLeader.lean
private theorem twoCore_endpointLeader_rotate {n : ℕ}
    (D : BetaDiagram (n + 1)) (h : D.EndpointLeader) : D.rotate.EndpointLeader := by
  obtain ⟨κ, hκ, hκS, c, hc, hd⟩ := h
  refine ⟨κ, hκ, by simpa only [D.rotate_largestLabel] using hκS,
    -c, neg_ne_zero.mpr hc, ?_⟩
  intro t ht
  obtain ⟨z, he, hcl, hzl⟩ := hd t ht
  refine ⟨-z, ?_, hcl.neg, hzl.neg⟩
  rw [D.endpointDifference_rotate t ht, he]
  ring

private theorem reindexOrder_self {n : ℕ} (D : BetaDiagram n) (h : n = n) :
    D.reindexOrder h = D := by
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

private theorem rotation_schur_eq {n : ℕ} {D E : BetaDiagram n}
    (h : D.RotationEquivalent E) : D.schur = E.schur :=
  ((D.translation_rotate_iff_rotation E).mpr h).schur_eq.trans E.rotate_schur

private theorem rotations_same_target_translation {n : ℕ}
    {D E F : BetaDiagram n} (hD : D.RotationEquivalent F) (hE : E.RotationEquivalent F) :
    D.TranslationEquivalent E := by
  obtain ⟨a, hrD, hcD⟩ := hD
  obtain ⟨b, hrE, hcE⟩ := hE
  refine ⟨a - b, ?_, ?_⟩
  · intro i
    rw [hrD i, hrE i]
    ring
  · intro i
    rw [hcD i, hcE i]
    ring

theorem twoComponentContext_rotate_swap_schur
    (Q : BetaDiagram (p + 1)) (R : BetaDiagram (r + 1))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).schur =
      (R.rotate.twoComponentContext Q.rotate v u g hv hu hg).schur := by
  have he := rotation_schur_eq (Q.twoComponentContext_rotate_swap R u v g hu hv hg)
  simpa only [reindexOrder_schur] using he

private theorem translation_of_eq {n : ℕ} {D E : BetaDiagram n} (he : D = E) :
    D.TranslationEquivalent E := by
  subst E
  exact ⟨0, (fun i => by ring), (fun i => by ring)⟩

/-- Distinct aligned old factors force equality of the actual full context
lists.  Both strict regimes and the tied regime are read from the polynomial,
not imposed on the competing context. -/
theorem twoComponent_rigidity_between_contexts_distinct
    (Q W : BetaDiagram (p + 2)) (R T : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hR : R.Connected) (hT : T.Connected)
    (hZQ : Q.ZeroFree) (hZW : W.ZeroFree) (hZR : R.ZeroFree) (hZT : T.ZeroFree)
    (hQW : Q.schur = W.schur) (hRT : R.schur = T.schur) (hne : Q.schur ≠ R.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    (Q.twoComponentContext R u v g hu hv hg).TranslationEquivalent
      (W.twoComponentContext T U V G hU hV hG) := by
  have hreg := twoComponent_regimes_eq_of_schur_eq_distinct Q R W T hQ hR hW hT
    hne hQW hRT u v g U V G hu hv hg hU hV hG he
  rcases lt_trichotomy u v with htop | htie | hbottom
  · have hTop := hreg.1.mp htop
    obtain ⟨huU, hvV, hgG, hleft, hright⟩ :=
      twoComponent_strict_top_contexts_comparison Q W R T hQ hW hR hT
        hZQ hZR hZT hQW hRT hRQ hRR hLeaderQ hLeaderR
        u v g U V G hu hv hg hU hV hG htop hTop he
    subst U
    subst V
    subst G
    exact translation_of_eq (Q.twoComponentContext_eq_of_core_translations W R T
      hleft hright u v g hu hv hg)
  · have hTie := hreg.2.2.mp htie
    subst v
    subst V
    obtain ⟨huU, hgG, hleft, hright⟩ :=
      twoComponent_tied_contexts_comparison_distinct Q W R T hQ hW hR hT
        hZQ hZR hZT hQW hRT hne hRQ hRR hLeaderQ hLeaderR
        u U g G hu hU hg hG he
    subst U
    subst G
    exact translation_of_eq (Q.twoComponentContext_eq_of_core_translations W R T
      hleft hright u u g hu hu hg)
  · have hBottom := hreg.2.1.mp hbottom
    have hswap :
        (R.rotate.twoComponentContext Q.rotate v u g hv hu hg).schur =
          (T.rotate.twoComponentContext W.rotate V U G hV hU hG).schur :=
      (Q.twoComponentContext_rotate_swap_schur R u v g hu hv hg).symm.trans
        (he.trans (W.twoComponentContext_rotate_swap_schur T U V G hU hV hG))
    obtain ⟨hvV, huU, hgG, hleft, hright⟩ :=
      twoComponent_strict_top_contexts_comparison R.rotate T.rotate Q.rotate W.rotate
        (R.rotate_connected hR) (T.rotate_connected hT)
        (Q.rotate_connected hQ) (W.rotate_connected hW)
        (twoCore_zeroFree_rotate R hZR) (twoCore_zeroFree_rotate Q hZQ)
        (twoCore_zeroFree_rotate W hZW)
        (by simpa only [rotate_schur] using hRT)
        (by simpa only [rotate_schur] using hQW)
        (twoCore_rotationRigid_rotate R hRR) (twoCore_rotationRigid_rotate Q hRQ)
        (fun hn => twoCore_endpointLeader_rotate R
          (hLeaderR (fun hs => hn (twoCore_symmetric_rotate R hs))))
        (fun hn => twoCore_endpointLeader_rotate Q
          (hLeaderQ (fun hs => hn (twoCore_symmetric_rotate Q hs))))
        v u g V U G hv hu hg hV hU hG hbottom hBottom hswap
    subst U
    subst V
    subst G
    have hctx := R.rotate.twoComponentContext_eq_of_core_translations T.rotate
      Q.rotate W.rotate hleft hright v u g hv hu hg
    have hsource := Q.twoComponentContext_rotate_swap R u v g hu hv hg
    have hmate := W.twoComponentContext_rotate_swap T u v g hu hv hg
    rw [hctx] at hsource
    exact rotations_same_target_translation hsource hmate

private theorem rotation_translation {n : ℕ} {D E F : BetaDiagram n}
    (hD : D.RotationEquivalent E) (hE : E.TranslationEquivalent F) :
    D.RotationEquivalent F := by
  obtain ⟨a, hrD, hcD⟩ := hD
  obtain ⟨b, hrE, hcE⟩ := hE
  refine ⟨a - b, ?_, ?_⟩
  · intro i
    rw [hrD i, hcE i.rev]
    ring
  · intro i
    rw [hcD i, hrE i.rev]
    ring

private theorem motion_of_double_rotations {n : ℕ} {D E A B : BetaDiagram n}
    (hDA : D.RotationEquivalent A) (hEB : E.RotationEquivalent B)
    (hAB : A.TranslationEquivalent B ∨ A.RotationEquivalent B) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  rcases hAB with hT | hR
  · exact Or.inl (rotations_same_target_translation (rotation_translation hDA hT) hEB)
  · have hDB := rotations_same_target_translation hDA (tied_equal_rotation_symm hR)
    exact Or.inr (tied_equal_translation_rotation hDB (tied_equal_rotation_symm hEB))

/-- Swapped core rotations give the actual margin-swapped parent rotation,
with its produced order cast. -/
theorem twoComponentContext_rotation_of_swapped_cores
    (Q T : BetaDiagram (p + 1)) (R W : BetaDiagram (r + 1))
    (hQT : Q.RotationEquivalent T) (hRW : R.RotationEquivalent W)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    let hParent : p + r + 3 = r + p + 3 := by omega
    (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent
      ((W.twoComponentContext T v u g hv hu hg).reindexOrder hParent) := by
  have hW := R.rotated_core_translation W hRW
  have hT := Q.rotated_core_translation T hQT
  have hctx := W.twoComponentContext_eq_of_core_translations R.rotate T Q.rotate
    hW hT v u g hv hu hg
  have hrot := Q.twoComponentContext_rotate_swap R u v g hu hv hg
  rw [← hctx] at hrot
  exact hrot

private theorem twoComponentContext_rotate_swap_same_order
    (Q R : BetaDiagram (p + 2))
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent
      (R.rotate.twoComponentContext Q.rotate v u g hv hu hg) := by
  have hrot := Q.twoComponentContext_rotate_swap R u v g hu hv hg
  simpa only [reindexOrder_self] using hrot

/-- For equal old factors in a strict-top source, the factor-of-two marker
excludes a tied mate.  A strict-bottom mate is rotated by its actual lists
before the same strict-top comparison is applied. -/
theorem twoComponent_strict_top_equal_contexts
    (Q R W T : BetaDiagram (p + 2))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (hZQ : Q.ZeroFree) (hZR : R.ZeroFree) (hZW : W.ZeroFree) (hZT : T.ZeroFree)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur) (hQT : Q.schur = T.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (htop : u < v)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    (Q.twoComponentContext R u v g hu hv hg).TranslationEquivalent
        (W.twoComponentContext T U V G hU hV hG) ∨
      (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent
        (W.twoComponentContext T U V G hU hV hG) := by
  have hRT : R.schur = T.schur := hQR.symm.trans hQT
  have htied := twoComponent_tied_eq_of_schur_eq_equal Q R W T hQ hR hW hT
    hQR hQW hQT u v g U V G hu hv hg hU hV hG he
  rcases lt_trichotomy U V with hTop | hTie | hBottom
  · obtain ⟨huU, hvV, hgG, hleft, hright⟩ :=
      twoComponent_strict_top_contexts_comparison Q W R T hQ hW hR hT
        hZQ hZR hZT hQW hRT hRQ hRR hLeaderQ hLeaderR
        u v g U V G hu hv hg hU hV hG htop hTop he
    subst U
    subst V
    subst G
    exact Or.inl (translation_of_eq
      (Q.twoComponentContext_eq_of_core_translations W R T hleft hright u v g hu hv hg))
  · exact (ne_of_lt htop (htied.mpr hTie)).elim
  · have hrot := twoComponentContext_rotate_swap_same_order W T U V G hU hV hG
    have hswap := he.trans (rotation_schur_eq hrot)
    obtain ⟨huV, hvU, hgG, hleft, hright⟩ :=
      twoComponent_strict_top_contexts_comparison Q T.rotate R W.rotate
        hQ (T.rotate_connected hT) hR (W.rotate_connected hW)
        hZQ hZR (twoCore_zeroFree_rotate W hZW)
        (by simpa only [rotate_schur] using hQT)
        (by simpa only [rotate_schur] using hQR.symm.trans hQW)
        hRQ hRR hLeaderQ hLeaderR
        u v g V U G hu hv hg hV hU hG htop hBottom hswap
    subst V
    subst U
    subst G
    have hctx := Q.twoComponentContext_eq_of_core_translations T.rotate R W.rotate
      hleft hright u v g hu hv hg
    exact Or.inr (tied_equal_translation_rotation (translation_of_eq hctx)
      (tied_equal_rotation_symm hrot))

/-- Equal old factors retain all multiplicities and all strict/tied marker
regimes.  The only surviving simultaneous reflection is the actual global
parent rotation with the two cores exchanged. -/
theorem twoComponent_rigidity_between_contexts_equal
    (Q R W T : BetaDiagram (p + 2))
    (hQ : Q.Connected) (hR : R.Connected) (hW : W.Connected) (hT : T.Connected)
    (hZQ : Q.ZeroFree) (hZR : R.ZeroFree) (hZW : W.ZeroFree) (hZT : T.ZeroFree)
    (hQR : Q.schur = R.schur) (hQW : Q.schur = W.schur) (hQT : Q.schur = T.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    (Q.twoComponentContext R u v g hu hv hg).TranslationEquivalent
        (W.twoComponentContext T U V G hU hV hG) ∨
      (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent
        (W.twoComponentContext T U V G hU hV hG) := by
  rcases lt_trichotomy u v with htop | htie | hbottom
  · exact twoComponent_strict_top_equal_contexts Q R W T hQ hR hW hT
      hZQ hZR hZW hZT hQR hQW hQT hRQ hRR hLeaderQ hLeaderR
      u v g U V G hu hv hg hU hV hG htop he
  · have hTie := (twoComponent_tied_eq_of_schur_eq_equal Q R W T hQ hR hW hT
      hQR hQW hQT u v g U V G hu hv hg hU hV hG he).mp htie
    subst v
    subst V
    have hmin := twoComponent_min_margin_eq_of_schur_eq Q R W T hQ hR hW hT
      u u g U U G hu hu hg hU hU hG he
    simp only [min_self] at hmin
    subst U
    obtain ⟨hgG, hmotion⟩ := twoComponent_tied_contexts_comparison_equal Q R W T
      hQ hR hW hT hQR hQW hQT hRQ hRR hLeaderQ hLeaderR u g G hu hg hG he
    subst G
    rcases hmotion with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · exact Or.inl (translation_of_eq
        (Q.twoComponentContext_eq_of_core_translations W R T hleft hright u u g hu hu hg))
    · have hparent := Q.twoComponentContext_rotation_of_swapped_cores T R W
        hleft hright u u g hu hu hg
      exact Or.inr (by simpa only [reindexOrder_self] using hparent)
  · have hsource := twoComponentContext_rotate_swap_same_order Q R u v g hu hv hg
    have hmate := twoComponentContext_rotate_swap_same_order W T U V G hU hV hG
    have hswap := (rotation_schur_eq hsource).symm.trans
      (he.trans (rotation_schur_eq hmate))
    have hbetween := twoComponent_strict_top_equal_contexts
      R.rotate Q.rotate T.rotate W.rotate
      (R.rotate_connected hR) (Q.rotate_connected hQ)
      (T.rotate_connected hT) (W.rotate_connected hW)
      (twoCore_zeroFree_rotate R hZR) (twoCore_zeroFree_rotate Q hZQ)
      (twoCore_zeroFree_rotate T hZT) (twoCore_zeroFree_rotate W hZW)
      (by simpa only [rotate_schur] using hQR.symm)
      (by simpa only [rotate_schur] using hQR.symm.trans hQT)
      (by simpa only [rotate_schur] using hQR.symm.trans hQW)
      (twoCore_rotationRigid_rotate R hRR) (twoCore_rotationRigid_rotate Q hRQ)
      (fun hn => twoCore_endpointLeader_rotate R
        (hLeaderR (fun hs => hn (twoCore_symmetric_rotate R hs))))
      (fun hn => twoCore_endpointLeader_rotate Q
        (hLeaderQ (fun hs => hn (twoCore_symmetric_rotate Q hs))))
      v u g V U G hv hu hg hV hU hG hbottom hswap
    exact motion_of_double_rotations hsource hmate hbetween

/-- Aligned component-function inventory is enough: no component profile,
mate margins, or mate orientations are assumed. -/
theorem twoComponent_rigidity_between_contexts_aligned
    (Q W : BetaDiagram (p + 2)) (R T : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hW : W.Connected) (hR : R.Connected) (hT : T.Connected)
    (hZQ : Q.ZeroFree) (hZW : W.ZeroFree) (hZR : R.ZeroFree) (hZT : T.ZeroFree)
    (hQW : Q.schur = W.schur) (hRT : R.schur = T.schur)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (u v g U V G : ℤ)
    (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur =
      (W.twoComponentContext T U V G hU hV hG).schur) :
    (Q.twoComponentContext R u v g hu hv hg).TranslationEquivalent
        (W.twoComponentContext T U V G hU hV hG) ∨
      (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent
        (W.twoComponentContext T U V G hU hV hG) := by
  by_cases hQR : Q.schur = R.schur
  · have hr : p = r := by have hh := Q.row_count_of_schur_eq R hQR; omega
    subst r
    exact twoComponent_rigidity_between_contexts_equal Q R W T hQ hR hW hT
      hZQ hZR hZW hZT hQR hQW (hQR.trans hRT) hRQ hRR hLeaderQ hLeaderR
      u v g U V G hu hv hg hU hV hG he
  · exact Or.inl (twoComponent_rigidity_between_contexts_distinct Q W R T
      hQ hW hR hT hZQ hZW hZR hZT hQW hRT hQR hRQ hRR hLeaderQ hLeaderR
      u v g U V G hu hv hg hU hV hG he)

private theorem rotated_cut_prefix {a b : ℕ} (C : BetaDiagram (a + b))
    (h : b + a = a + b) :
    (C.rotate.reindexOrder h).betaPrefix = C.suffix.rotate := by
  apply ext_of_row_col
  · funext i
    change -C.col ((Fin.cast h (i.castAdd a)).rev) =
      -C.col (i.rev.natAdd a)
    apply congrArg (fun j => -C.col j)
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · funext i
    change -C.row ((Fin.cast h (i.castAdd a)).rev) =
      -C.row (i.rev.natAdd a)
    apply congrArg (fun j => -C.row j)
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    omega

private theorem rotated_cut_suffix {a b : ℕ} (C : BetaDiagram (a + b))
    (h : b + a = a + b) :
    (C.rotate.reindexOrder h).suffix = C.betaPrefix.rotate := by
  apply ext_of_row_col
  · funext i
    change -C.col ((Fin.cast h (i.natAdd b)).rev) =
      -C.col (i.rev.castAdd b)
    apply congrArg (fun j => -C.col j)
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · funext i
    change -C.row ((Fin.cast h (i.natAdd b)).rev) =
      -C.row (i.rev.castAdd b)
    apply congrArg (fun j => -C.row j)
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    omega

private theorem rotated_cut_strict {a b : ℕ} (C : BetaDiagram (a + b))
    (ha : 0 < a) (hb : 0 < b) (h : b + a = a + b)
    (hc : C.row ⟨a, by omega⟩ < C.col ⟨a - 1, by omega⟩) :
    (C.rotate.reindexOrder h).row ⟨b, by omega⟩ <
      (C.rotate.reindexOrder h).col ⟨b - 1, by omega⟩ := by
  have hi : (Fin.cast h (⟨b, by omega⟩ : Fin (b + a))).rev =
      (⟨a - 1, by omega⟩ : Fin (a + b)) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_rev]
    omega
  have hj : (Fin.cast h (⟨b - 1, by omega⟩ : Fin (b + a))).rev =
      (⟨a, by omega⟩ : Fin (a + b)) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_rev]
    omega
  change -C.col _ < -C.row _
  rw [hi, hj]
  omega

private theorem twoCutCore_rotate_from_corner {a b p r : ℕ}
    (F : BetaDiagram (p + r + 3)) (hP : F.PositiveCorner)
    (ho : a + b = p + r + 2) (h : (p + 1) + (r + 1) = a + b) :
    F.rotate.twoCutCore (F.rotate_positiveCorner hP) =
      (((F.cornerDiagram hP).reindexOrder ho).rotate.reindexOrder h) := by
  apply ext_of_row_col
  · funext i
    change -F.col _ = -F.col _
    apply congrArg (fun j => -F.col j)
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
    omega
  · funext i
    change -F.row _ = -F.row _
    apply congrArg (fun j => -F.row j)
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
    omega

/-- Function matching of the arbitrary mate chooses an actual left-to-right
cut, possibly after a literal parent rotation.  The component orders and the
choice of side are produced, not supplied. -/
theorem twoComponent_mate_aligned_cut
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hR : R.Connected) (hZQ : Q.ZeroFree) (hZR : R.ZeroFree)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (F : BetaDiagram ((p + 1) + (r + 1) + 3)) (hF : F.Connected)
    (he : (Q.twoComponentContext R u v g hu hv hg).schur = F.schur) :
    ∃ (D : BetaDiagram ((p + 1) + (r + 1) + 3)) (hP : D.PositiveCorner),
      (D = F ∨ D = F.rotate) ∧ D.Connected ∧ D.ZeroFree ∧
      (D.twoCutCore hP).row ⟨p + 2, by omega⟩ <
        (D.twoCutCore hP).col ⟨p + 2 - 1, by omega⟩ ∧
      (D.twoCutCore hP).betaPrefix.Connected ∧ (D.twoCutCore hP).suffix.Connected ∧
      Q.schur = (D.twoCutCore hP).betaPrefix.schur ∧
        R.schur = (D.twoCutCore hP).suffix.schur := by
  obtain ⟨hn, hP, a, b, ha, hb, ho, hZF, hcut, hLC, hRC, hmatch⟩ :=
    Q.twoComponent_mate_cut_inventory R hQ hR hZQ hZR u v g hu hv hg F hF he
  have hnr : hn = rfl := Subsingleton.elim _ _
  cases hnr
  rcases hmatch with ⟨hQL, hRR, hpa, hrb⟩ | ⟨hQR, hRL, hpb, hra⟩
  · subst a
    subst b
    exact ⟨F, hP, Or.inl rfl, hF, hZF, hcut, hLC, hRC, hQL, hRR⟩
  · subst a
    subst b
    let C := (F.cornerDiagram hP).reindexOrder ho
    let hs : (p + 2) + (r + 2) = (r + 2) + (p + 2) := by omega
    have hcore := twoCutCore_rotate_from_corner F hP ho hs
    have hpref : (F.rotate.twoCutCore (F.rotate_positiveCorner hP)).betaPrefix =
        C.suffix.rotate := by
      rw [hcore]
      exact rotated_cut_prefix C hs
    have hsuff : (F.rotate.twoCutCore (F.rotate_positiveCorner hP)).suffix =
        C.betaPrefix.rotate := by
      rw [hcore]
      exact rotated_cut_suffix C hs
    refine ⟨F.rotate, F.rotate_positiveCorner hP, Or.inr rfl, F.rotate_connected hF,
      twoCore_zeroFree_rotate F hZF, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcore]
      exact rotated_cut_strict C (by omega) (by omega) hs hcut
    · rw [hpref]
      exact C.suffix.rotate_connected hRC
    · rw [hsuff]
      exact C.betaPrefix.rotate_connected hLC
    · rw [hpref, rotate_schur]
      exact hQR
    · rw [hsuff, rotate_schur]
      exact hRL

private theorem translation_trans {n : ℕ} {D E F : BetaDiagram n}
    (hD : D.TranslationEquivalent E) (hE : E.TranslationEquivalent F) :
    D.TranslationEquivalent F := by
  obtain ⟨a, hrD, hcD⟩ := hD
  obtain ⟨b, hrE, hcE⟩ := hE
  refine ⟨a + b, ?_, ?_⟩
  · intro i
    rw [hrD i, hrE i]
    ring
  · intro i
    rw [hcD i, hcE i]
    ring

/-- Generic arbitrary-mate lifting for two actual nonlinear components
(`lem:two-component-lift`).  Row count, zero-freeness, the genuine component
cut, factor multiplicities, every margin, and every orientation are produced
from full Schur equality.  Endpoint isolation is derived from the fixed
leader-or-symmetry premises and is not an additional input. -/
theorem twoComponentContext_rotationRigid
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (hQ : Q.Connected) (hR : R.Connected) (hZQ : Q.ZeroFree) (hZR : R.ZeroFree)
    (hRQ : Q.RotationRigid) (hRR : R.RotationRigid)
    (hLeaderQ : ¬ Q.Symmetric → Q.EndpointLeader)
    (hLeaderR : ¬ R.Symmetric → R.EndpointLeader)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).RotationRigid := by
  rw [rotationRigid_iff_same_order]
  intro F hF he
  obtain ⟨D, hPD, hchoice, hD, hZD, hcut, hW, hT, hQW, hRT⟩ :=
    Q.twoComponent_mate_aligned_cut R hQ hR hZQ hZR u v g hu hv hg F hF he.symm
  let C := D.twoCutCore hPD
  let W := C.betaPrefix
  let T := C.suffix
  have hZW : W.ZeroFree := by
    intro i j hz
    exact hZD _ _ hz
  have hZT : T.ZeroFree := by
    intro i j hz
    exact hZD _ _ hz
  obtain ⟨hG, hparent⟩ := D.parent_twoComponentContext_of_cut hPD hcut
  have hpolyD : (Q.twoComponentContext R u v g hu hv hg).schur = D.schur := by
    rcases hchoice with rfl | rfl
    · exact he.symm
    · exact he.symm.trans F.rotate_schur.symm
  have hbetween := twoComponent_rigidity_between_contexts_aligned Q W R T
    hQ hW hR hT hZQ hZW hZR hZT hQW hRT hRQ hRR hLeaderQ hLeaderR
    u v g D.topMargin D.bottomMargin
      (C.betaPrefix.col (Fin.last (p + 1)) - C.suffix.row 0)
    hu hv hg D.topMargin_pos D.bottomMargin_pos hG (hpolyD.trans hparent.schur_eq)
  have hmotion :
      (Q.twoComponentContext R u v g hu hv hg).TranslationEquivalent D ∨
        (Q.twoComponentContext R u v g hu hv hg).RotationEquivalent D := by
    rcases hbetween with htr | hrot
    · exact Or.inl (translation_trans htr (tied_equal_translation_symm hparent))
    · exact Or.inr (rotation_translation hrot (tied_equal_translation_symm hparent))
  rcases hchoice with rfl | rfl
  · exact hmotion
  · rcases hmotion with htr | hrot
    · exact Or.inr (((Q.twoComponentContext R u v g hu hv hg).translation_rotate_iff_rotation F).mp htr)
    · exact Or.inl (((Q.twoComponentContext R u v g hu hv hg).rotation_rotate_iff_translation F).mp hrot)

/-- Dense nonlinear cores supply all standing inputs of the full arbitrary
mate theorem, including the two-by-two cores of a five-row parent. -/
theorem twoComponentContext_rotationRigid_of_dense
    (Q : BetaDiagram (p + 2)) (R : BetaDiagram (r + 2))
    (hDQ : Q.Dense) (hDR : R.Dense)
    (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.twoComponentContext R u v g hu hv hg).RotationRigid := by
  have hQ := hDQ.connected (by omega)
  have hR := hDR.connected (by omega)
  exact Q.twoComponentContext_rotationRigid R hQ hR hDQ.zeroFree hDR.zeroFree
    (Q.rotationRigid_of_nonnegative hQ hDQ.nonnegative)
    (R.rotationRigid_of_nonnegative hR hDR.nonnegative)
    (fun hS => Q.endpointLeader_dense hDQ hS)
    (fun hS => R.endpointLeader_dense hDR hS) u v g hu hv hg

end SkewJacobiNegative.BetaDiagram
