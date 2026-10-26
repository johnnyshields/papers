/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Coherent

/-!
# The finite enumerations of the unshifted exclusion

Formalizes the finite enumerations asserted without derivation in
`shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion» (`sec:unshifted`,
`ph:unshifted-exclusion`).

* `span_three_classification`: the connected normalized diagrams of span three are the five lists
  `(3 | 0)`, `(3 2 | 1 0)`, `(3 2 | 2 0)`, `(3 1 | 1 0)`, `(3 2 1 | 2 1 0)` of row and column betas.
* `coframe_coeff_two_span_three`: the coefficient `g₂` of `z²` in the complete coframe of such a
  diagram is `0`, `-H₂/ϑ` or `(H₁² - ϑ H₂)/ϑ²`.
* `small_span_numerator_ne_zero`: `H₁² g₂ - 2 H₂² ≠ 0` for each of the three values.
* `balanced_flag_symmetric`: the closing step for `M = 7, 8`, where every balanced complete flag
  list with the stated endpoint positions is its own rotation.

Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe Polynomial

/-- The `i`-th row beta lies at least `i` below the top one. -/
theorem row_add_le_row_zero {n : ℕ} (D : BetaDiagram (n + 1)) (i : Fin (n + 1)) :
    D.row i + i.val ≤ D.row 0 := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => simp
  | succ k ih =>
    have := D.row_strictAnti
      (show (⟨k, by omega⟩ : Fin (n + 1)) < ⟨k + 1, hi⟩ from Fin.mk_lt_mk.mpr (by omega))
    have := ih (by omega)
    simp only at *
    omega

/-- The connected normalized diagrams of span three are exactly five, listed by their row and
column betas. -/
theorem span_three_classification {n : ℕ} (D : BetaDiagram (n + 1)) (hc : D.Connected)
    (hn : D.col (Fin.last n) = 0) (hs : span D = 3) :
    (List.ofFn D.row = [3] ∧ List.ofFn D.col = [0]) ∨
    (List.ofFn D.row = [3, 2] ∧ List.ofFn D.col = [1, 0]) ∨
    (List.ofFn D.row = [3, 2] ∧ List.ofFn D.col = [2, 0]) ∨
    (List.ofFn D.row = [3, 1] ∧ List.ofFn D.col = [1, 0]) ∨
    (List.ofFn D.row = [3, 2, 1] ∧ List.ofFn D.col = [2, 1, 0]) := by
  have h0 : D.row 0 = 3 := by
    have := D.largestLabel_pos
    unfold span BetaDiagram.largestLabel at hs this
    omega
  have hpos : ∀ i, 1 ≤ D.row i := by
    intro i
    have := col_last_le D i
    have := D.row_nonempty i
    omega
  have hle : ∀ i : Fin (n + 1), D.row i + i.val ≤ 3 := by
    intro i
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero => simp [h0]
    | succ k ih =>
      have := D.row_strictAnti
        (show (⟨k, by omega⟩ : Fin (n + 1)) < ⟨k + 1, hi⟩ from Fin.mk_lt_mk.mpr (by omega))
      have := ih (by omega)
      simp only at *
      omega
  have hn2 : n ≤ 2 := by
    have := hle (Fin.last n)
    have := hpos (Fin.last n)
    simp at *
    omega
  have hcc := hc.2
  interval_cases n
  · have a := hpos 0
    have b := hle 0
    have c : D.row 0 = 3 := h0
    have d : D.col 0 = 0 := hn
    left
    simp [List.ofFn_succ, c, d]
  · have c1 := hcc 0 (by simp)
    have a1 := hpos 1
    have b1 := hle 1
    have n0 := D.row_nonempty 0
    have n1 := D.row_nonempty 1
    have s0 := D.col_strictAnti (show (0 : Fin 2) < 1 by decide)
    have d : D.col 1 = 0 := hn
    simp at c1 b1
    simp [List.ofFn_succ]
    omega
  · have c1 := hcc 0 (by simp)
    have c2 := hcc 1 (by simp)
    have a1 := hpos 1
    have a2 := hpos 2
    have b1 := hle 1
    have b2 := hle 2
    have n0 := D.row_nonempty 0
    have n1 := D.row_nonempty 1
    have n2 := D.row_nonempty 2
    have s0 := D.col_strictAnti (show (0 : Fin 3) < 1 by decide)
    have s1 := D.col_strictAnti (show (1 : Fin 3) < 2 by decide)
    have d : D.col 2 = 0 := hn
    simp at c1 c2 b1 b2
    simp [List.ofFn_succ]
    omega

/-- The letters of the coherent field are nonzero. -/
theorem cohLetters_ne_zero (k : ℕ) : cohLetters k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 (MvPolynomial.X_ne_zero k)

/-- The `z²` coefficient of a coframe is the sum of the native coefficients at position two. -/
theorem coeff_two_coframeOf {L : Type*} [Field L] {n : ℕ} (h : ℕ → L) (D : BetaDiagram (n + 1)) :
    (coframeOf h D).coeff 2 = ∑ j : Fin n, if colPos D j = 2 then coframeVecOf h D j else 0 := by
  unfold coframeOf
  have h1 : (1 : L[X]).coeff 2 = 0 := by rw [Polynomial.coeff_one]; norm_num
  rw [Polynomial.coeff_add, finsetSum_coeff, h1, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hj : colPos D j = 2
  · simp [hj]
  · simp [hj, Ne.symm hj]

/-- The native coefficient of a two-row coframe. -/
theorem coframeVecOf_two_rows {L : Type*} [Field L] (h : ℕ → L) (D : BetaDiagram 2) :
    coframeVecOf h D 0 = -(letterOf h (D.row 1 - D.col 1) / letterOf h (D.row 1 - D.col 0)) := by
  have : properMatrixOf h D = Matrix.of fun _ _ => letterOf h (D.row 1 - D.col 0) := by
    ext i j; fin_cases i; fin_cases j; rfl
  simp [coframeVecOf, this, topVecOf, div_eq_inv_mul]

/-- The native coefficients of the three-row coframe with rows `3, 2, 1` and columns `2, 1, 0`. -/
theorem coframeVecOf_three_rows {L : Type*} [Field L] (h : ℕ → L) (D : BetaDiagram 3)
    (hr1 : D.row 1 = 2) (hr2 : D.row 2 = 1) (hc0 : D.col 0 = 2) (hc1 : D.col 1 = 1)
    (hc2 : D.col 2 = 0) (h0 : h 0 ≠ 0) :
    coframeVecOf h D 0 = (h 1 ^ 2 - h 0 * h 2) / h 0 ^ 2 ∧
      coframeVecOf h D 1 = -(h 1 / h 0) := by
  have hT : properMatrixOf h D = !![h 0, h 1; 0, h 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [properMatrixOf, hr1, hr2, hc0, hc1, letterOf]
  have hv : topVecOf h D = ![h 2, h 1] := by
    funext i; fin_cases i <;> simp [topVecOf, hr1, hr2, hc2, letterOf]
  simp only [coframeVecOf, hT, hv]
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  constructor <;> (simp [Matrix.det_fin_two, h0]; try field_simp; try ring)

/-- The `z²` coefficient `g₂` of the coframe of a connected normalized diagram of span three takes
exactly the three values `0`, `-H₂/ϑ` and `(H₁² - ϑ H₂)/ϑ²`. -/
theorem coframe_coeff_two_span_three {n : ℕ} (D : BetaDiagram (n + 1)) (hc : D.Connected)
    (hn : D.col (Fin.last n) = 0) (hs : span D = 3) :
    (coframe D).coeff 2 = 0 ∨
    (coframe D).coeff 2 = -(cohLetters 2 / cohLetters 0) ∨
    (coframe D).coeff 2 = (cohLetters 1 ^ 2 - cohLetters 0 * cohLetters 2) / cohLetters 0 ^ 2 := by
  have h0 := cohLetters_ne_zero 0
  have key : ∀ (m : ℕ) (E : BetaDiagram (m + 1)), E.col (Fin.last m) = 0 →
      ∀ j : Fin m, colPos E j = (E.col j.castSucc).toNat := by
    intro m E hE j
    simp [colPos, hE]
  rcases span_three_classification D hc hn hs with ⟨hr, hcl⟩ | ⟨hr, hcl⟩ | ⟨hr, hcl⟩ |
      ⟨hr, hcl⟩ | ⟨hr, hcl⟩
  · have hl := congrArg List.length hcl
    simp only [List.length_ofFn, List.length_cons, List.length_nil] at hl
    obtain rfl : n = 0 := by omega
    left
    simp [coframe, coeff_two_coframeOf]
  · have hl := congrArg List.length hcl
    simp only [List.length_ofFn, List.length_cons, List.length_nil] at hl
    obtain rfl : n = 1 := by omega
    simp only [List.ofFn_succ, List.ofFn_zero] at hr hcl
    simp at hr hcl
    left
    simp [coframe, coeff_two_coframeOf, colPos, hcl.2, hcl.1]
  · have hl := congrArg List.length hcl
    simp only [List.length_ofFn, List.length_cons, List.length_nil] at hl
    obtain rfl : n = 1 := by omega
    simp only [List.ofFn_succ, List.ofFn_zero] at hr hcl
    simp at hr hcl
    right; left
    have e : colPos D 0 = 2 := by simp [colPos, hcl.1, hcl.2]
    rw [coframe, coeff_two_coframeOf, Fin.sum_univ_one, coframeVecOf_two_rows]
    simp [e, letterOf, hr.2, hcl.1, hcl.2]
  · have hl := congrArg List.length hcl
    simp only [List.length_ofFn, List.length_cons, List.length_nil] at hl
    obtain rfl : n = 1 := by omega
    simp only [List.ofFn_succ, List.ofFn_zero] at hr hcl
    simp at hr hcl
    left
    simp [coframe, coeff_two_coframeOf, colPos, hcl.2, hcl.1]
  · have hl := congrArg List.length hcl
    simp only [List.length_ofFn, List.length_cons, List.length_nil] at hl
    obtain rfl : n = 2 := by omega
    simp only [List.ofFn_succ, List.ofFn_zero] at hr hcl
    simp at hr hcl
    right; right
    have hv := coframeVecOf_three_rows cohLetters D hr.2.1 hr.2.2 hcl.1 hcl.2.1 hcl.2.2 h0
    simp [coframe, coeff_two_coframeOf, colPos, hcl.2.2, hcl.1, hcl.2.1, Fin.sum_univ_succ]
    exact hv.1

/-- A coherent polynomial with a nonzero value at the all-ones point stays nonzero in the raw
field. -/
theorem algebraMap_ne_zero_of_eval {p : CohRing} (hp : MvPolynomial.eval (fun _ => (1 : ℚ)) p ≠ 0) :
    algebraMap CohRing CohField p ≠ 0 := by
  intro h
  have : p = 0 := IsFractionRing.injective CohRing CohField (by rw [h, map_zero])
  exact hp (by rw [this, map_zero])

/-- The numerator `H₁² g₂ - 2 H₂²` of the degree-`M` coefficient in the unequal-end case is
nonzero for each of the three values of `g₂`. -/
theorem small_span_numerator_ne_zero {g : CohField}
    (hg : g = 0 ∨ g = -(cohLetters 2 / cohLetters 0) ∨
      g = (cohLetters 1 ^ 2 - cohLetters 0 * cohLetters 2) / cohLetters 0 ^ 2) :
    cohLetters 1 ^ 2 * g - 2 * cohLetters 2 ^ 2 ≠ 0 := by
  have h0 := cohLetters_ne_zero 0
  have h2 := cohLetters_ne_zero 2
  rcases hg with rfl | rfl | rfl
  · simpa using h2
  · intro h
    have key : algebraMap CohRing CohField
        (-(MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2) - 2 * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2) =
        cohLetters 0 * (cohLetters 1 ^ 2 * -(cohLetters 2 / cohLetters 0) -
          2 * cohLetters 2 ^ 2) := by
      simp only [map_sub, map_neg, map_mul, map_pow, map_ofNat]
      simp only [cohLetters]
      field_simp
    refine algebraMap_ne_zero_of_eval (p := -(MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2) -
      2 * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2) (by norm_num) ?_
    rw [key, h, mul_zero]
  · intro h
    have key : algebraMap CohRing CohField
        (MvPolynomial.X 1 ^ 2 * (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 2) -
          2 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2) =
        cohLetters 0 ^ 2 * (cohLetters 1 ^ 2 * ((cohLetters 1 ^ 2 - cohLetters 0 * cohLetters 2) /
          cohLetters 0 ^ 2) - 2 * cohLetters 2 ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      simp only [cohLetters]
      field_simp
    refine algebraMap_ne_zero_of_eval (p := MvPolynomial.X 1 ^ 2 *
      (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 2) -
      2 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2) (by norm_num) ?_
    rw [key, h, mul_zero]

/-- Two strictly decreasing integer lists with the same set of values are equal. -/
theorem eq_of_strictAnti_of_range {k : ℕ} {f g : Fin k → ℤ} (hf : StrictAnti f) (hg : StrictAnti g)
    (h : ∀ x, (∃ i, f i = x) ↔ ∃ i, g i = x) : f = g := by
  classical
  let s : Finset ℤ := Finset.univ.image f
  have hcard : s.card = k := by
    rw [Finset.card_image_of_injective _ hf.injective]; simp
  have hfs : ∀ x, f x ∈ s := fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)
  have hgs : ∀ x, g x ∈ s := by
    intro x
    obtain ⟨i, hi⟩ := (h (g x)).2 ⟨x, rfl⟩
    rw [← hi]; exact hfs i
  have hf' : StrictMono fun i => f (Fin.rev i) := fun i j hij => hf (Fin.rev_lt_rev.mpr hij)
  have hg' : StrictMono fun i => g (Fin.rev i) := fun i j hij => hg (Fin.rev_lt_rev.mpr hij)
  have e1 := Finset.orderEmbOfFin_unique hcard (fun x => hfs (Fin.rev x)) hf'
  have e2 := Finset.orderEmbOfFin_unique hcard (fun x => hgs (Fin.rev x)) hg'
  funext x
  have := (congrFun (e1.trans e2.symm) (Fin.rev x))
  simpa using this

/-- The two balanced closing configurations: for span `M = 7` or `M = 8`, a normalized board whose
row positions are `M - 1`, `3` and positions in `[4, M - 4]`, and whose column positions are
`M - 3`, `1` and positions in `[4, M - 4]`, is its own rotation. -/
theorem balanced_flag_symmetric {n : ℕ} (M : ℤ) (hM : M = 7 ∨ M = 8) (V : BetaDiagram (n + 1))
    (hn : V.col (Fin.last n) = 0) (h0 : V.row 0 = M)
    (hr : ∀ i : Fin (n + 1), i ≠ 0 → V.row i = M - 1 ∨ V.row i = 3 ∨
      (4 ≤ V.row i ∧ V.row i ≤ M - 4))
    (hc : ∀ j : Fin (n + 1), j ≠ Fin.last n → V.col j = M - 3 ∨ V.col j = 1 ∨
      (4 ≤ V.col j ∧ V.col j ≤ M - 4))
    (hr1 : ∃ i, V.row i = M - 1) (hr3 : ∃ i, V.row i = 3)
    (hc1 : ∃ j, V.col j = M - 3) (hc2 : ∃ j, V.col j = 1) : V.Symmetric := by
  classical
  -- membership in the value sets
  have mR : ∀ x, (∃ i, V.row i = x) →
      x = M ∨ x = M - 1 ∨ x = 3 ∨ (4 ≤ x ∧ x ≤ M - 4) := by
    rintro x ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst hi; left; exact h0
    · rcases hr i hi with h | h | h <;> simp [h]
  have mC : ∀ x, (∃ i, V.col i = x) →
      x = 0 ∨ x = M - 3 ∨ x = 1 ∨ (4 ≤ x ∧ x ≤ M - 4) := by
    rintro x ⟨i, rfl⟩
    by_cases hi : i = Fin.last n
    · subst hi; left; exact hn
    · rcases hc i hi with h | h | h <;> simp [h]
  have pR : ∃ i, V.row i = M := ⟨0, h0⟩
  have pC : ∃ i, V.col i = 0 := ⟨Fin.last n, hn⟩
  -- the cardinality of the two value sets agrees, which balances the optional position four
  have four : M = 8 → ((∃ i, V.row i = 4) ↔ ∃ i, V.col i = 4) := by
    intro hM8
    subst hM8
    have cR : (Finset.univ.image V.row).card = n + 1 := by
      rw [Finset.card_image_of_injective _ V.row_strictAnti.injective]; simp
    have cC : (Finset.univ.image V.col).card = n + 1 := by
      rw [Finset.card_image_of_injective _ V.col_strictAnti.injective]; simp
    have eR : ∀ x, x ∈ Finset.univ.image V.row ↔ ∃ i, V.row i = x := by simp
    have eC : ∀ x, x ∈ Finset.univ.image V.col ↔ ∃ i, V.col i = x := by simp
    by_cases a : ∃ i, V.row i = 4 <;> by_cases b : ∃ i, V.col i = 4
    · exact ⟨fun _ => b, fun _ => a⟩
    · exfalso
      have e1 : Finset.univ.image V.row = {8, 7, 4, 3} := by
        ext x
        rw [eR]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx; have := mR x hx; omega
        · rintro (rfl | rfl | rfl | rfl)
          · exact pR
          · exact hr1
          · exact a
          · exact hr3
      have e2 : Finset.univ.image V.col = {5, 1, 0} := by
        ext x
        rw [eC]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have := mC x hx
          have hb : x ≠ 4 := fun h => b (h ▸ hx)
          omega
        · rintro (rfl | rfl | rfl)
          · exact hc1
          · exact hc2
          · exact pC
      rw [e1] at cR
      rw [e2] at cC
      have : (4 : ℕ) = 3 := cR.trans cC.symm
      omega
    · exfalso
      have e1 : Finset.univ.image V.row = {8, 7, 3} := by
        ext x
        rw [eR]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have := mR x hx
          have ha : x ≠ 4 := fun h => a (h ▸ hx)
          omega
        · rintro (rfl | rfl | rfl)
          · exact pR
          · exact hr1
          · exact hr3
      have e2 : Finset.univ.image V.col = {5, 4, 1, 0} := by
        ext x
        rw [eC]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx; have := mC x hx; omega
        · rintro (rfl | rfl | rfl | rfl)
          · exact hc1
          · exact b
          · exact hc2
          · exact pC
      rw [e1] at cR
      rw [e2] at cC
      have : (3 : ℕ) = 4 := cR.trans cC.symm
      omega
    · exact ⟨fun h => absurd h a, fun h => absurd h b⟩
  have hRC : ∀ x, (∃ i, V.row i = x) ↔ ∃ j, M - V.col j = x := by
    intro x
    constructor
    · intro hx
      rcases mR x hx with h | h | h | h
      · exact ⟨Fin.last n, by rw [hn]; omega⟩
      · obtain ⟨j, hj⟩ := hc2
        exact ⟨j, by omega⟩
      · obtain ⟨j, hj⟩ := hc1
        exact ⟨j, by omega⟩
      · have hM8 : M = 8 := by omega
        have hx4 : M = 8 ∧ x = 4 := ⟨hM8, by omega⟩
        obtain ⟨j, hj⟩ := (four hx4.1).1 (hx4.2 ▸ hx)
        exact ⟨j, by omega⟩
    · rintro ⟨j, rfl⟩
      rcases mC (V.col j) ⟨j, rfl⟩ with h | h | h | h
      · exact ⟨0, by omega⟩
      · obtain ⟨i, hi⟩ := hr3
        exact ⟨i, by omega⟩
      · obtain ⟨i, hi⟩ := hr1
        exact ⟨i, by omega⟩
      · have hM8 : M = 8 := by omega
        have hx4 : M = 8 ∧ V.col j = 4 := ⟨hM8, by omega⟩
        obtain ⟨i, hi⟩ := (four hx4.1).2 (hx4.2 ▸ ⟨j, rfl⟩)
        exact ⟨i, by omega⟩
  have hCR : ∀ x, (∃ j, V.col j = x) ↔ ∃ i, M - V.row i = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (hRC (M - x)).2 (by
        obtain ⟨j, rfl⟩ := hx; exact ⟨j, rfl⟩)
      exact ⟨i, by omega⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := (hRC (V.row i)).1 ⟨i, rfl⟩
      exact ⟨j, by omega⟩
  refine ⟨M, ?_, ?_⟩
  · have := eq_of_strictAnti_of_range (f := V.row) (g := fun i => M - V.col i.rev) V.row_strictAnti
      (fun i j hij => by simp only; have := V.col_strictAnti (Fin.rev_lt_rev.mpr hij); omega) ?_
    · intro i; exact congrFun this i
    · intro x
      rw [hRC x]
      constructor
      · rintro ⟨j, hj⟩; exact ⟨j.rev, by simpa using hj⟩
      · rintro ⟨i, hi⟩; exact ⟨i.rev, by simpa using hi⟩
  · have := eq_of_strictAnti_of_range (f := V.col) (g := fun i => M - V.row i.rev) V.col_strictAnti
      (fun i j hij => by simp only; have := V.row_strictAnti (Fin.rev_lt_rev.mpr hij); omega) ?_
    · intro i; exact congrFun this i
    · intro x
      rw [hCR x]
      constructor
      · rintro ⟨j, hj⟩; exact ⟨j.rev, by simpa using hj⟩
      · rintro ⟨i, hi⟩; exact ⟨i.rev, by simpa using hi⟩

/-- The numerator `H₁² g₂ - 2 H₂²` is nonzero for every connected normalized diagram of span
three. -/
theorem small_span_numerator_ne_zero_of_diagram {n : ℕ} (D : BetaDiagram (n + 1))
    (hc : D.Connected) (hn : D.col (Fin.last n) = 0) (hs : span D = 3) :
    cohLetters 1 ^ 2 * (coframe D).coeff 2 - 2 * cohLetters 2 ^ 2 ≠ 0 :=
  small_span_numerator_ne_zero (coframe_coeff_two_span_three D hc hn hs)

end SkewCoframeRigidity.Unshifted
