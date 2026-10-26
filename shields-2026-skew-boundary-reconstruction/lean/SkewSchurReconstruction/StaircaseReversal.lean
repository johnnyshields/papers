/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.RatioNormalization
import SkewSchurReconstruction.TwoSeriesReversal
import SkewSchurReconstruction.BoundarySeparation

/-!
# Staircase word diagrams

Actual staircase diagrams for "Reversal pairs on the locus"
(`subsec:locus-family`, `prop:staircase-reversal`).
Formal word reversal produces the ratio identity; actual boundary separation
proves skew-Schur inequivalence.  Prefix-times-tail cofactor factorization and
the exact square-weight cofactor increment apply uniformly to binary words.
Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

variable {N : ℕ}

/-- The staircase inner boundary `(N-1, …, 0)`. -/
def staircaseInner (N : ℕ) (i : Fin N) : ℕ := N - 1 - i.val

/-- Actual diagram obtained by adding a binary row-length word to the staircase. -/
def staircaseDiagram (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) : Diagram N where
  outer i := staircaseInner N i + w i
  inner := staircaseInner N
  outer_antitone := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hwi := hw i
    have hwj := hw j
    by_cases he : i = j
    · subst j
      exact le_rfl
    · have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
      have hval : i.val < j.val := lt_of_le_of_ne (show i.val ≤ j.val from hij) hne
      change (N - 1 - j.val) + w j ≤ (N - 1 - i.val) + w i
      rcases hwi with hwi | hwi <;> rcases hwj with hwj | hwj <;> omega
  inner_antitone := by
    intro i j hij
    change N - 1 - j.val ≤ N - 1 - i.val
    have hval : i.val ≤ j.val := hij
    omega
  row_nonempty := by
    intro i
    rcases hw i with h | h <;> simp [h]

theorem staircase_rowLength (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) (i : Fin N) :
    (staircaseDiagram w hw).rowLength i = w i := by
  simp [Diagram.rowLength, staircaseDiagram]

theorem staircase_connected (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) : (staircaseDiagram w hw).Connected := by
  refine ⟨hN, ?_⟩
  intro i hi
  have hib := i.isLt
  have hw' := hw ⟨i.val + 1, hi⟩
  change N - 1 - i.val < (N - 1 - (i.val + 1)) + w ⟨i.val + 1, hi⟩
  rcases hw' with h | h <;> omega

theorem staircase_overlap (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (i : Fin N) (hi : i.val + 1 < N) :
    (staircaseDiagram w hw).overlap i hi = (w ⟨i.val + 1, hi⟩ : ℤ) - 1 := by
  have ho : (staircaseDiagram w hw).outer ⟨i.val + 1, hi⟩ =
      (N - 1 - (i.val + 1)) + w ⟨i.val + 1, hi⟩ := rfl
  have hm : (staircaseDiagram w hw).inner i = N - 1 - i.val := rfl
  rw [Diagram.overlap, ho, hm]
  have hib := i.isLt
  omega

theorem staircase_top (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) : (staircaseDiagram w hw).top = N + 1 := by
  rw [Diagram.top_of_pos _ hN]
  change N - 1 - 0 + w ⟨0, hN⟩ = N + 1
  rw [hfirst]
  omega

theorem staircase_rowParam (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) (i : Fin N) :
    (staircaseDiagram w hw).rowParam i = 2 * (i.val : ℤ) + 2 - w i := by
  have hi := i.isLt
  unfold Diagram.rowParam
  rw [staircase_top w hw hN hfirst]
  change ((N + 1 : ℕ) : ℤ) - ((N - 1 - i.val + w i : ℕ) : ℤ) + i.val = _
  omega

theorem staircase_capShift (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) (j : Fin (N + 1)) :
    (staircaseDiagram w hw).capShift j = 2 * (j.val : ℤ) := by
  cases j using Fin.cases with
  | zero => simp
  | succ i =>
    have hi := i.isLt
    rw [Diagram.capShift_succ, staircase_top w hw hN hfirst]
    change ((N + 1 : ℕ) : ℤ) - ((N - 1 - i.val : ℕ) : ℤ) + i.val = 2 * (i.val + 1 : ℕ)
    omega

/-- Complete-generator word determinant `D(rho)` from the manuscript. -/
noncomputable def completeWordMatrix (rho : Fin N → ℕ) : Matrix (Fin N) (Fin N) CompleteRing :=
  Matrix.of fun i j => complete ((rho i : ℤ) + 2 * ((j.val : ℤ) - i.val))

theorem staircase_schurFunction (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) :
    (staircaseDiagram w hw).schurFunction = (completeWordMatrix w).det := by
  rw [Diagram.schurFunction_eq_det_ordinaryMatrix]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [Diagram.ordinaryMatrix, staircaseMatrix, Matrix.of_apply,
    staircase_capShift w hw hN hfirst, staircase_rowParam w hw hN hfirst, completeWordMatrix,
    Fin.val_succ]
  apply congrArg complete
  push_cast
  ring

/-- The capped function is the determinant with an actual prefixed positive row. -/
theorem staircase_capPolynomial (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) (r : ℕ) (hr : 0 < r) :
    (staircaseDiagram w hw).capPolynomial r = (completeWordMatrix (Fin.cases r w)).det := by
  rw [← Diagram.schurFunction_extendNortheast _ r hr,
    Diagram.schurFunction_eq_det_ordinaryMatrix]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
    simp only [Diagram.ordinaryMatrix, staircaseMatrix, Matrix.of_apply,
      Diagram.extendNortheast_rowParam_zero, Diagram.extendNortheast_capShift_succ,
      staircase_capShift w hw hN hfirst, completeWordMatrix, Fin.cases_zero,
      Fin.val_zero, sub_zero]
    apply congrArg complete
    ring
  | succ i =>
    simp only [Diagram.ordinaryMatrix, staircaseMatrix, Matrix.of_apply,
      Diagram.extendNortheast_rowParam_succ, Diagram.extendNortheast_capShift_succ,
      staircase_capShift w hw hN hfirst, staircase_rowParam w hw hN hfirst,
      completeWordMatrix, Fin.cases_succ, Fin.val_succ]
    apply congrArg complete
    push_cast
    ring

/-- Reversing a natural word. -/
def reversedWord (w : Fin N → ℕ) (i : Fin N) : ℕ := w i.rev

theorem reversedWord_binary (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) :
    ∀ i, reversedWord w i = 2 ∨ reversedWord w i = 3 := fun i => hw i.rev

theorem staircase_common_inner (w v : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hv : ∀ i, v i = 2 ∨ v i = 3) :
    (staircaseDiagram w hw).inner = (staircaseDiagram v hv).inner := rfl

theorem staircase_common_cap (w v : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hv : ∀ i, v i = 2 ∨ v i = 3)
    (hN : 0 < N) (hw0 : w ⟨0, hN⟩ = 2) (hv0 : v ⟨0, hN⟩ = 2) :
    (staircaseDiagram w hw).capShift = (staircaseDiagram v hv).capShift := by
  funext j
  rw [staircase_capShift w hw hN hw0, staircase_capShift v hv hN hv0]

/-- Distinct words give distinct actual diagrams, not merely distinct coordinate presentations. -/
theorem staircase_ne_of_word_ne (w v : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hv : ∀ i, v i = 2 ∨ v i = 3) (h : w ≠ v) :
    staircaseDiagram w hw ≠ staircaseDiagram v hv := by
  intro he
  apply h
  funext i
  have hh := congrArg (fun X : Diagram N => X.rowLength i) he
  simpa only [staircase_rowLength] using hh

/-- Common-inner staircase diagrams are translates only when their words coincide. -/
theorem staircase_not_translationEquivalent (w v : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hv : ∀ i, v i = 2 ∨ v i = 3)
    (hN : 0 < N) (h : w ≠ v) :
    ¬ TranslationEquivalent (staircaseDiagram w hw) (staircaseDiagram v hv) := by
  rintro ⟨_, t, ht⟩
  have hz := (ht ⟨0, hN⟩ ⟨0, hN⟩ rfl).2
  change ((N - 1 : ℕ) : ℤ) = ((N - 1 : ℕ) : ℤ) + t at hz
  have ht0 : t = 0 := by omega
  apply h
  funext i
  have ho := (ht i i rfl).1
  change ((staircaseInner N i + w i : ℕ) : ℤ) =
    ((staircaseInner N i + v i : ℕ) : ℤ) + t at ho
  omega

/-- Binary word as positive row lengths, with true denoting a length-three row. -/
def binaryLength (x : Fin N → Bool) (i : Fin N) : ℕ := if x i then 3 else 2

theorem binaryLength_binary (x : Fin N → Bool) :
    ∀ i, binaryLength x i = 2 ∨ binaryLength x i = 3 := by
  intro i
  cases h : x i <;> simp [binaryLength, h]

/-- The even formal complete series, with constant coefficient one. -/
noncomputable def evenCompleteSeries : PowerSeries CompleteRing :=
  PowerSeries.mk fun i => complete (2 * (i : ℤ))

/-- The odd formal complete series. -/
noncomputable def oddCompleteSeries : PowerSeries CompleteRing :=
  PowerSeries.mk fun i => complete (2 * (i : ℤ) + 1)

theorem evenCompleteSeries_constant : PowerSeries.constantCoeff evenCompleteSeries = 1 := by
  simp [evenCompleteSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]


theorem shifted_evenCompleteSeries {M : ℕ} (s : ℕ) (j : Fin M) :
    TwoSeries.shiftedRow evenCompleteSeries s j =
      complete (2 * ((j.val : ℤ) - s)) := by
  by_cases hs : s ≤ j.val
  · simp only [TwoSeries.shiftedRow, ite_eq_left hs, evenCompleteSeries, PowerSeries.coeff_mk]
    congr 1
    omega
  · simp only [TwoSeries.shiftedRow, ite_eq_right hs]
    symm
    apply complete_of_neg
    omega

theorem shifted_oddCompleteSeries {M : ℕ} (s : ℕ) (j : Fin M) :
    TwoSeries.shiftedRow oddCompleteSeries s j =
      complete (2 * ((j.val : ℤ) - s) + 1) := by
  by_cases hs : s ≤ j.val
  · simp only [TwoSeries.shiftedRow, ite_eq_left hs, oddCompleteSeries, PowerSeries.coeff_mk]
    congr 1
    omega
  · simp only [TwoSeries.shiftedRow, ite_eq_right hs]
    symm
    apply complete_of_neg
    omega

/-- The two-series specialization is an equality of actual complete-generator matrices. -/
theorem completeWordMatrix_two_series (x : Fin N → Bool) :
    completeWordMatrix (Fin.cases 1 (Fin.cases 2 (binaryLength x))) =
      TwoSeries.wordMatrix evenCompleteSeries oddCompleteSeries x := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
    simp only [completeWordMatrix, TwoSeries.wordMatrix, Matrix.of_apply, Fin.cases_zero,
      Fin.val_zero, shifted_oddCompleteSeries]
    apply congrArg complete
    ring
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      simp only [completeWordMatrix, TwoSeries.wordMatrix, Matrix.of_apply, Fin.cases_succ,
        Fin.cases_zero, Fin.val_zero, Fin.val_succ, shifted_evenCompleteSeries]
      apply congrArg complete
      ring
    | succ i =>
      cases hx : x i <;>
        simp only [completeWordMatrix, TwoSeries.wordMatrix, Matrix.of_apply, Fin.cases_succ,
          Fin.val_succ, binaryLength, hx, Bool.false_eq_true, ite_false, ite_true,
          shifted_evenCompleteSeries, shifted_oddCompleteSeries] <;>
        apply congrArg complete <;> push_cast <;> ring

/-- The ratio remainder at `(2,1)` is the determinant of the specialized two-series word matrix. -/
theorem staircase_ratio_remainder_matrix (x : Fin N → Bool) (hN : 0 < N)
    (hfirst : binaryLength x ⟨0, hN⟩ = 2) :
    complete 1 * (staircaseDiagram (binaryLength x) (binaryLength_binary x)).capPolynomial 2 -
      (staircaseDiagram (binaryLength x) (binaryLength_binary x)).capPolynomial 3 =
        (TwoSeries.wordMatrix evenCompleteSeries oddCompleteSeries x).det := by
  let X := staircaseDiagram (binaryLength x) (binaryLength_binary x)
  let Z := (X.extendNortheast 2 (by omega)).extendNortheast 1 (by omega)
  have hz : Z.schurFunction = complete 1 * X.capPolynomial 2 - X.capPolynomial 3 := by
    dsimp [Z]
    rw [Diagram.schurFunction_iterated_extendNortheast]
    simp only [Diagram.schurFunction_extendNortheast]
    norm_num
  rw [← completeWordMatrix_two_series]
  change complete 1 * X.capPolynomial 2 - X.capPolynomial 3 = _
  rw [← hz, Diagram.schurFunction_eq_det_ordinaryMatrix]
  apply congrArg Matrix.det
  have hc : ∀ j : Fin (N + 2), Z.capShift j.succ = 2 * (j.val : ℤ) + 1 := by
    intro j
    dsimp [Z]
    rw [Diagram.extendNortheast_capShift_succ]
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      rw [Diagram.extendNortheast_capShift_succ]
      simp only [X, staircase_capShift _ _ hN hfirst, Fin.val_succ]
      push_cast
      ring
  apply Matrix.ext
  intro i j
  simp only [Diagram.ordinaryMatrix, staircaseMatrix, Matrix.of_apply, hc, completeWordMatrix]
  cases i using Fin.cases with
  | zero =>
    simp only [Z, Diagram.extendNortheast_rowParam_zero, Fin.cases_zero,
      Fin.val_zero, sub_zero]
    apply congrArg complete
    ring
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      simp only [Z, Diagram.extendNortheast_rowParam_succ,
        Diagram.extendNortheast_rowParam_zero, Fin.cases_succ, Fin.cases_zero,
        Fin.val_succ, Fin.val_zero]
      apply congrArg complete
      ring
    | succ i =>
      simp only [Z, Diagram.extendNortheast_rowParam_succ, X,
        staircase_rowParam _ _ hN hfirst, Fin.cases_succ, Fin.val_succ]
      apply congrArg complete
      push_cast
      ring

theorem staircase_capMatrix_entry (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) (i : Fin N) (j : Fin (N + 1)) :
    (staircaseDiagram w hw).capMatrix i j =
      complete ((w i : ℤ) + 2 * ((j.val : ℤ) - i.val - 1)) := by
  simp only [Diagram.capMatrix, Matrix.of_apply, staircase_capShift w hw hN hfirst,
    staircase_rowParam w hw hN hfirst]
  congr 1
  ring

/-- The capped staircase is upper triangular, including its cap column. -/
theorem staircase_capMatrix_zero_below (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2)
    (i : Fin N) (j : Fin (N + 1)) (hji : j.val < i.val) :
    (staircaseDiagram w hw).capMatrix i j = 0 := by
  rw [staircase_capMatrix_entry w hw hN hfirst]
  apply complete_of_neg
  rcases hw i with h | h <;> omega

/-- Deleting the last column leaves a triangular determinant with its exact signed product. -/
theorem staircase_cofactor_last (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) :
    (staircaseDiagram w hw).cofactor (Fin.last N) =
      (-1 : CompleteRing) ^ N * ∏ i, complete ((w i : ℤ) - 2) := by
  unfold Diagram.cofactor signedMaximalCofactor
  simp only [Fin.val_last, Fin.succAbove_last]
  have ht : ((staircaseDiagram w hw).capMatrix.submatrix id Fin.castSucc).IsUpperTriangular := by
    intro i j hij
    exact staircase_capMatrix_zero_below w hw hN hfirst i j.castSucc hij
  rw [Matrix.det_of_isUpperTriangular ht]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.submatrix_apply, id_eq, staircase_capMatrix_entry w hw hN hfirst,
    Fin.val_castSucc]
  congr 1
  ring

/-- Reversal preserves the terminal triangular product. -/
theorem staircase_terminal_product_reversal (w : Fin N → ℕ) :
    (∏ i, complete ((reversedWord w i : ℤ) - 2)) =
      ∏ i, complete ((w i : ℤ) - 2) := by
  exact Equiv.prod_comp Fin.revPerm (fun i => complete ((w i : ℤ) - 2))

theorem binaryLength_wordReverse (x : Fin N → Bool) :
    binaryLength (TwoSeries.wordReverse x) = reversedWord (binaryLength x) := rfl

/-- Full actual ratio identity for endpoint-two Boolean staircase words. -/
theorem binary_staircase_ratioIdentity (x : Fin N → Bool) (hN : 0 < N)
    (hfirst : x ⟨0, hN⟩ = false) (hlast : x ⟨N - 1, by omega⟩ = false) :
    RatioIdentity
      (gridDefect (staircaseDiagram (binaryLength x) (binaryLength_binary x))
        (staircaseDiagram (binaryLength (TwoSeries.wordReverse x))
          (binaryLength_binary (TwoSeries.wordReverse x)))) 2 1 := by
  have hw0 : binaryLength x ⟨0, hN⟩ = 2 := by simp [binaryLength, hfirst]
  have hy0 : binaryLength (TwoSeries.wordReverse x) ⟨0, hN⟩ = 2 := by
    change (if x ⟨N - (0 + 1), by omega⟩ then 3 else 2) = 2
    simp [hlast]
  have hleft := staircase_ratio_remainder_matrix x hN hw0
  have hright := staircase_ratio_remainder_matrix (TwoSeries.wordReverse x) hN hy0
  have hdet := TwoSeries.wordMatrix_det_reversal evenCompleteSeries oddCompleteSeries
    evenCompleteSeries_constant x
  rw [← hleft, ← hright] at hdet
  unfold RatioIdentity
  rw [gridDefect_response, gridDefect_response]
  change
    (staircaseDiagram (binaryLength x) (binaryLength_binary x)).capPolynomial 3 -
      (staircaseDiagram (binaryLength (TwoSeries.wordReverse x))
        (binaryLength_binary (TwoSeries.wordReverse x))).capPolynomial 3 =
    complete 1 * ((staircaseDiagram (binaryLength x) (binaryLength_binary x)).capPolynomial 2 -
      (staircaseDiagram (binaryLength (TwoSeries.wordReverse x))
        (binaryLength_binary (TwoSeries.wordReverse x))).capPolynomial 2)
  linear_combination -hdet

/-- The ratio assertion of `prop:staircase-reversal` for actual natural row-length words. -/
theorem staircase_ratioIdentity (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) (hlast : w ⟨N - 1, by omega⟩ = 2) :
    RatioIdentity (gridDefect (staircaseDiagram w hw)
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw))) 2 1 := by
  let x : Fin N → Bool := fun i => decide (w i = 3)
  have hx : binaryLength x = w := by
    funext i
    rcases hw i with h | h <;> simp [binaryLength, x, h]
  have hx0 : x ⟨0, hN⟩ = false := by simp [x, hfirst]
  have hxl : x ⟨N - 1, by omega⟩ = false := by simp [x, hlast]
  have h := binary_staircase_ratioIdentity x hN hx0 hxl
  simpa only [binaryLength_wordReverse, hx] using h

/-- Nonpalindromic endpoint-two staircase words are genuinely skew-Schur inequivalent. -/
theorem staircase_schurFunction_ne_reverse (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N)
    (hfirst : w ⟨0, hN⟩ = 2) (hlast : w ⟨N - 1, by omega⟩ = 2)
    (hne : w ≠ reversedWord w) :
    (staircaseDiagram w hw).schurFunction ≠
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).schurFunction := by
  intro he
  have hex := Diagram.equal_pair_ratio_exclusion
    (staircaseDiagram w hw)
    (staircaseDiagram (reversedWord w) (reversedWord_binary w hw))
    (staircase_connected w hw hN)
    (staircase_connected _ (reversedWord_binary w hw) hN)
    (staircase_common_inner _ _ hw (reversedWord_binary w hw))
    (staircase_ne_of_word_ne _ _ hw (reversedWord_binary w hw) hne)
    he 2 1 (by norm_num) (by norm_num)
  exact hex (staircase_ratioIdentity w hw hN hfirst hlast)

/-- Exact prefix-times-tail factorization of every nonzero-column staircase cofactor. -/
theorem staircase_cofactor_split {p q : ℕ} (w : Fin (p + q) → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hp : 0 < p)
    (hfirst : w ⟨0, by omega⟩ = 2) :
    (staircaseDiagram w hw).cofactor ⟨p, by omega⟩ =
      (-1 : CompleteRing) ^ p *
        (∏ i : Fin p, complete ((w (i.castAdd q) : ℤ) - 2)) *
          (completeWordMatrix (fun i : Fin q => w (i.natAdd p))).det := by
  classical
  let X := staircaseDiagram w hw
  let j : Fin (p + q + 1) := ⟨p, by omega⟩
  let M := X.capMatrix.submatrix id j.succAbove
  let A := M.submatrix (Fin.castAdd q) (Fin.castAdd q)
  let B := M.submatrix (Fin.castAdd q) (Fin.natAdd p)
  let D := M.submatrix (Fin.natAdd p) (Fin.natAdd p)
  have hleft : ∀ i : Fin p, j.succAbove (i.castAdd q) = (i.castAdd q).castSucc := by
    intro i
    apply Fin.succAbove_of_castSucc_lt
    change i.val < p
    exact i.isLt
  have hright : ∀ i : Fin q, j.succAbove (i.natAdd p) = (i.natAdd p).succ := by
    intro i
    apply Fin.succAbove_of_le_castSucc
    change p ≤ p + i.val
    omega
  have hzero : ∀ (i : Fin q) (l : Fin p), M (i.natAdd p) (l.castAdd q) = 0 := by
    intro i l
    change X.capMatrix (i.natAdd p) (j.succAbove (l.castAdd q)) = 0
    rw [hleft]
    apply staircase_capMatrix_zero_below w hw (by omega) hfirst
    have hl := l.isLt
    change l.val < p + i.val
    omega
  have hblocks : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks A B 0 D := by
    apply Matrix.ext
    intro i l
    cases i with
    | inl i => cases l <;> rfl
    | inr i =>
      cases l with
      | inl l => exact hzero i l
      | inr l => rfl
  have hdet : M.det = A.det * D.det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hblocks,
      Matrix.det_fromBlocks_zero₂₁]
  have hA : A.IsUpperTriangular := by
    intro i l hli
    change X.capMatrix (i.castAdd q) (j.succAbove (l.castAdd q)) = 0
    rw [hleft]
    exact staircase_capMatrix_zero_below w hw (by omega) hfirst _ _ hli
  have hAdiag : A.det = ∏ i : Fin p, complete ((w (i.castAdd q) : ℤ) - 2) := by
    rw [Matrix.det_of_isUpperTriangular hA]
    apply Finset.prod_congr rfl
    intro i _
    change X.capMatrix (i.castAdd q) (j.succAbove (i.castAdd q)) = _
    rw [hleft, staircase_capMatrix_entry w hw (by omega) hfirst]
    congr 1
    simp only [Fin.val_castSucc, Fin.val_castAdd]
    ring
  have hD : D = completeWordMatrix (fun i : Fin q => w (i.natAdd p)) := by
    apply Matrix.ext
    intro i l
    change X.capMatrix (i.natAdd p) (j.succAbove (l.natAdd p)) = _
    rw [hright, staircase_capMatrix_entry w hw (by omega) hfirst]
    simp only [completeWordMatrix, Matrix.of_apply, Fin.val_succ, Fin.val_natAdd]
    apply congrArg complete
    push_cast
    ring
  change (-1 : CompleteRing) ^ p * M.det = _
  rw [hdet, hAdiag, hD]
  ring

theorem staircase_cofactor_penultimate {n : ℕ} (w : Fin (n + 1) → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hn : 0 < n)
    (hfirst : w 0 = 2) (hlast : w (Fin.last n) = 2) :
    (staircaseDiagram w hw).cofactor (Fin.last n).castSucc =
      (-1 : CompleteRing) ^ n * complete 2 *
        ∏ i : Fin (n + 1), complete ((w i : ℤ) - 2) := by
  have hs := staircase_cofactor_split (p := n) (q := 1) w hw hn hfirst
  have htail : (completeWordMatrix (fun i : Fin 1 => w (i.natAdd n))).det = complete 2 := by
    rw [Matrix.det_unique]
    have he : (0 : Fin 1).natAdd n = Fin.last n := Fin.ext rfl
    simp [completeWordMatrix, Fin.default_eq_zero, he, hlast]
  have hp : (∏ i : Fin (n + 1), complete ((w i : ℤ) - 2)) =
      ∏ i : Fin n, complete ((w i.castSucc : ℤ) - 2) := by
    rw [Fin.prod_univ_castSucc]
    simp [hlast]
  rw [htail] at hs
  rw [hp]
  change (staircaseDiagram w hw).cofactor ⟨n, by omega⟩ = _
  change (staircaseDiagram w hw).cofactor ⟨n, by omega⟩ =
    (-1 : CompleteRing) ^ n *
      (∏ i : Fin n, complete ((w i.castSucc : ℤ) - 2)) * complete 2 at hs
  rw [hs]
  ring

theorem staircase_terminal_cofactors_reverse {n : ℕ} (w : Fin (n + 1) → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hn : 0 < n)
    (hfirst : w 0 = 2) (hlast : w (Fin.last n) = 2) :
    (staircaseDiagram w hw).cofactor (Fin.last (n + 1)) =
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).cofactor (Fin.last (n + 1)) ∧
    (staircaseDiagram w hw).cofactor (Fin.last n).castSucc =
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).cofactor
        (Fin.last n).castSucc := by
  have hr0 : reversedWord w 0 = 2 := by simpa [reversedWord] using hlast
  have hrl : reversedWord w (Fin.last n) = 2 := by simpa [reversedWord] using hfirst
  constructor
  · rw [staircase_cofactor_last w hw (by omega) hfirst,
      staircase_cofactor_last _ (reversedWord_binary w hw) (by omega) hr0,
      staircase_terminal_product_reversal]
  · rw [staircase_cofactor_penultimate w hw hn hfirst hlast,
      staircase_cofactor_penultimate _ (reversedWord_binary w hw) hn hr0 hrl,
      staircase_terminal_product_reversal]

theorem staircase_terminal_product_count (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) :
    (∏ i, complete ((w i : ℤ) - 2)) =
      complete 1 ^ ((Finset.univ : Finset (Fin N)).filter (fun i => w i = 3)).card := by
  classical
  have ht : ∀ i, complete ((w i : ℤ) - 2) = if w i = 3 then complete 1 else 1 := by
    intro i
    rcases hw i with h | h <;> norm_num [h]
  simp_rw [ht]
  rw [Finset.prod_ite]
  simp

/-- Actual adjacent square-weight cofactor costs on the even staircase grid. -/
theorem staircase_cofactor_square_increment (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 2) (i : Fin N) :
    leastWeight squareWeight.generatorWeight ((staircaseDiagram w hw).cofactor i.succ) -
      leastWeight squareWeight.generatorWeight ((staircaseDiagram w hw).cofactor i.castSucc) =
        4 - 4 * (w i : ℝ) := by
  let X := staircaseDiagram w hw
  have hX := staircase_connected w hw hN
  rw [Diagram.cofactor_leastWeight squareWeight _ hX,
    Diagram.cofactor_leastWeight squareWeight _ hX, Diagram.matching_weight_exchange]
  have hz : X.exchangeZero i = (w i : ℤ) - 2 := by
    unfold Diagram.exchangeZero
    simp only [X, staircase_capShift w hw hN hfirst, staircase_rowParam w hw hN hfirst,
      Fin.val_castSucc]
    ring
  have hr : X.exchangeRow i = (w i : ℤ) := by
    rw [Diagram.exchangeRow_eq_rowLength]
    exact congrArg Int.ofNat (staircase_rowLength w hw i)
  rw [hz, hr]
  have hn : 2 ≤ w i := by rcases hw i with h | h <;> omega
  have hc : (((w i : ℤ) - 2).toNat : ℝ) = (w i : ℝ) - 2 := by
    have hi : (((w i : ℤ) - 2).toNat : ℤ) = (w i : ℤ) - 2 := by omega
    exact_mod_cast hi
  change (((w i : ℤ) - 2).toNat : ℝ) ^ 2 - ((w i : ℤ).toNat : ℝ) ^ 2 = _
  rw [hc]
  simp only [Int.toNat_natCast]
  ring

theorem staircase_square_initial_reversal (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N)
    (_hfirst : w ⟨0, hN⟩ = 2) (hlast : w ⟨N - 1, by omega⟩ = 2) :
    leastWeight squareWeight.generatorWeight ((staircaseDiagram w hw).cofactor 0) =
      leastWeight squareWeight.generatorWeight
        ((staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).cofactor 0) := by
  have hr0 : reversedWord w ⟨0, hN⟩ = 2 := by
    change w ⟨N - (0 + 1), by omega⟩ = 2
    exact hlast
  have hx := Diagram.parentAction_zero squareWeight _ (staircase_connected w hw hN)
  have hy := Diagram.parentAction_zero squareWeight _
    (staircase_connected _ (reversedWord_binary w hw) hN)
  unfold Diagram.parentAction at hx hy
  simp only [Diagram.capShift_zero, Int.toNat_zero, squareWeight.zero, add_zero,
    staircase_rowLength] at hx hy
  rw [hx, hy]
  exact (Equiv.sum_comp Fin.revPerm (fun i => squareWeight.weight (w i))).symm

end SkewSchurReconstruction
