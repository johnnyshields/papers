import SkewJacobiNegative.FiveExceptionalFamilies
import SkewJacobiNegative.PositiveBorders
import SkewJacobiNegative.FiveOpeningComparisons
import SkewJacobiNegative.EndpointDifferences
import SkewJacobiNegative.ConnectedBorderRigidity
import SkewJacobiNegative.SingletonContexts
import SkewJacobiNegative.NegativeBudgetInventory
import SkewJacobiNegative.LowNegativeRigidity
import SkewJacobiNegative.LowNegativePatterns

/-!
# Five-negative endpoint, border, and higher-row rigidity

The endpoint criterion `lem:five-endpoint` and the cross-orbit exclusion
`lem:five-exceptional-borders` use actual beta diagrams.  The six-row
coefficient separators in `eq:five-border-separators` retain the common-unit
boundary.  Component budgets and singleton reconstruction supply the
higher-row induction in `thm:classification`.
-/

namespace SkewJacobiNegative
namespace FiveExceptional

/-- An ordered five-term beta list is an arithmetic progression. -/
def Arithmetic (v : Fin 5 → ℤ) : Prop :=
  ∃ d : ℤ, ∀ i : Fin 4, v i.castSucc - v i.succ = d

theorem rows_arithmetic (P : Parameters) : Arithmetic (rows P) := by
  refine ⟨P.g, ?_⟩
  intro i
  fin_cases i <;> simp [rows] <;> ring

theorem fCols_not_arithmetic (P : Parameters) (s : Bool) :
    ¬ Arithmetic (fCols P s) := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  have h3 := hd 3
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases s <;> norm_num [fCols] at h0 h3 <;> omega

theorem hCols_not_arithmetic (P : Parameters) (s : Bool) :
    ¬ Arithmetic (hCols P s) := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  cases s <;> norm_num [hCols] at h0 h1 h2 <;> omega

theorem F_extendTop_rows_not_arithmetic (P : Parameters) (s : Bool)
    (t : ℤ) (ht : 0 < t) :
    ¬ Arithmetic ((F P s).extendTop t ht).row := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  have h1 := hd 1
  norm_num [BetaDiagram.extendTop, F, rows] at h0 h1
  omega

theorem H_extendTop_rows_not_arithmetic (P : Parameters) (s : Bool)
    (t : ℤ) (ht : 0 < t) :
    ¬ Arithmetic ((H P s).extendTop t ht).row := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  have h1 := hd 1
  norm_num [BetaDiagram.extendTop, H, rows] at h0 h1
  omega

theorem F_extendTop_cols_not_arithmetic (P : Parameters) (s : Bool)
    (t : ℤ) (ht : 0 < t) :
    ¬ Arithmetic ((F P s).extendTop t ht).col :=
  fCols_not_arithmetic P s

theorem H_extendTop_cols_not_arithmetic (P : Parameters) (s : Bool)
    (t : ℤ) (ht : 0 < t) :
    ¬ Arithmetic ((H P s).extendTop t ht).col :=
  hCols_not_arithmetic P s

/-- Translation cannot change whether a beta list is arithmetic. -/
theorem arithmetic_translation {v w : Fin 5 → ℤ} (c : ℤ)
    (h : ∀ i, v i = w i + c) : Arithmetic v ↔ Arithmetic w := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro i
  · have hi := hd i
    rw [h i.castSucc, h i.succ] at hi
    linarith
  · rw [h i.castSucc, h i.succ]
    have hi := hd i
    linarith

/-- Every displayed exceptional representative has arithmetic row betas. -/
theorem extendTop_not_translation_displayed (P Q : Parameters) (s r : Bool)
    (t : ℤ) (ht : 0 < t) :
    ¬ ((F P s).extendTop t ht).TranslationEquivalent (F Q r) ∧
    ¬ ((F P s).extendTop t ht).TranslationEquivalent (H Q r) ∧
    ¬ ((H P s).extendTop t ht).TranslationEquivalent (F Q r) ∧
    ¬ ((H P s).extendTop t ht).TranslationEquivalent (H Q r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rintro ⟨c, hr, hc⟩
  · exact F_extendTop_rows_not_arithmetic P s t ht
      ((arithmetic_translation c hr).mpr (rows_arithmetic Q))
  · exact F_extendTop_rows_not_arithmetic P s t ht
      ((arithmetic_translation c hr).mpr (rows_arithmetic Q))
  · exact H_extendTop_rows_not_arithmetic P s t ht
      ((arithmetic_translation c hr).mpr (rows_arithmetic Q))
  · exact H_extendTop_rows_not_arithmetic P s t ht
      ((arithmetic_translation c hr).mpr (rows_arithmetic Q))

/-- Bottom endpoint extensions leave the displayed exceptional lists, even at units. -/
theorem extendBottom_not_translation_displayed (P Q : Parameters) (s r : Bool)
    (t : ℤ) (ht : 0 < t) :
    ¬ ((F P s).extendBottom t ht).TranslationEquivalent (F Q r) ∧
    ¬ ((F P s).extendBottom t ht).TranslationEquivalent (H Q r) ∧
    ¬ ((H P s).extendBottom t ht).TranslationEquivalent (F Q r) ∧
    ¬ ((H P s).extendBottom t ht).TranslationEquivalent (H Q r) := by
  have hPq := P.q_pos
  have hQq := Q.q_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rintro ⟨c, hr, hc⟩
    have hr3 := hr 3
    have hr4 := hr 4
    have hc1 := hc 1
    have hc2 := hc 2
    have hc3 := hc 3
    have hc4 := hc 4
    cases s <;> cases r <;>
      norm_num [BetaDiagram.extendBottom, F, H, rows, fCols, hCols] at hr3 hr4 hc1 hc2 hc3 hc4 <;>
      omega

/-- The tied row-reading contact in the first family has only the source margin. -/
theorem familyOne_margin (P : Parameters) (t : ℤ)
    (he : ({P.g+t,3*P.g-P.q} : Multiset ℤ) =
      {2*P.g-P.q+t,2*P.g}) : t=P.g := by
  have hm : P.g+t∈({2*P.g-P.q+t,2*P.g} : Multiset ℤ) := by rw [← he]; simp
  simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hm
  have := P.q_le_b
  have := P.b_lt_g
  rcases hm with hm | hm <;> omega

theorem familyTwo_margin (P : Parameters) (t : ℤ)
    (he : ({P.g-P.q+t,3*P.g-P.q} : Multiset ℤ) =
      {2*P.g-P.q+t,2*P.g-P.q}) : t=P.g := by
  have hm : P.g-P.q+t∈({2*P.g-P.q+t,2*P.g-P.q} : Multiset ℤ) := by rw [← he]; simp
  simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hm
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  rcases hm with hm | hm <;> omega

/-- Column words of the actual six-row tied positive borders. -/
def borderColumn (second endType : Bool) : Fin 6 → Bool × ℤ :=
  if endType then
    ![(true,-2),(false,-2),(second,-1),(true,0),(false,0),(false,1)]
  else
    ![(second,-3),(true,-1),(false,-1),(true,0),(false,0),(false,1)]

noncomputable def borderSymbol (v : Bool) (k : ℤ) : MvPolynomial (Fin 14) ℚ :=
  if h : 0 ≤ k ∧ k<7 then
    MvPolynomial.X ⟨k.toNat+(if v then 7 else 0),by
      have := h.1
      have := h.2
      cases v <;> simp <;> omega⟩
  else 0

noncomputable def universalBorderMatrix (second endType : Bool) :
    Matrix (Fin 6) (Fin 6) (MvPolynomial (Fin 14) ℚ) :=
  fun i j => borderSymbol (borderColumn second endType j).1
    (5-(i.val : ℤ)+(borderColumn second endType j).2)

noncomputable def separatorExponent (second : Bool) : Fin 14 →₀ ℕ :=
  if second then
    Finsupp.single 0 2 + Finsupp.single 5 1 + Finsupp.single 8 2 + Finsupp.single 11 1
  else
    Finsupp.single 0 3 + Finsupp.single 5 1 + Finsupp.single 9 1 + Finsupp.single 11 1

private def separatorEmbedding (second : Bool) : Fin 4 → Fin 14 :=
  if second then ![0,5,8,11] else ![0,5,9,11]

private theorem separatorEmbedding_injective (second : Bool) :
    Function.Injective (separatorEmbedding second) := by
  cases second <;> decide

private noncomputable def sparseProjection (second : Bool) :
    MvPolynomial (Fin 14) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ :=
  MvPolynomial.killCompl (separatorEmbedding_injective second)

private theorem sparseProjection_X (second : Bool) (j : Fin 14) :
    sparseProjection second (MvPolynomial.X j) =
      if j=0 then MvPolynomial.X 0 else if j=5 then MvPolynomial.X 1 else
      if j=(if second then 8 else 9) then MvPolynomial.X 2 else
      if j=11 then MvPolynomial.X 3 else 0 := by
  classical
  by_cases h : j ∈ Set.range (separatorEmbedding second)
  · obtain ⟨i,rfl⟩ := h
    change MvPolynomial.killCompl (separatorEmbedding_injective second)
      (MvPolynomial.X (separatorEmbedding second i)) = _
    rw [← MvPolynomial.rename_X (separatorEmbedding second) i,
      MvPolynomial.killCompl_rename_app]
    cases second <;> fin_cases i <;> norm_num [separatorEmbedding]
  · have hz : sparseProjection second (MvPolynomial.X j) = 0 := by
      unfold sparseProjection MvPolynomial.killCompl
      rw [MvPolynomial.aeval_X,dif_neg h]
    have hn (i : Fin 4) : j ≠ separatorEmbedding second i := by
      intro he
      exact h ⟨i,he.symm⟩
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    have h3 := hn 3
    cases second <;>
      norm_num [separatorEmbedding] at h0 h1 h2 h3 ⊢ <;>
      simp [hz,h0,h1,h2,h3]

private noncomputable def sparseSeparatorExponent (second : Bool) : Fin 4 →₀ ℕ :=
  if second then
    Finsupp.single 0 2 + Finsupp.single 1 1 +
      Finsupp.single 2 2 + Finsupp.single 3 1
  else
    Finsupp.single 0 3 + Finsupp.single 1 1 +
      Finsupp.single 2 1 + Finsupp.single 3 1

private theorem sparseSeparatorExponent_map (second : Bool) :
    (sparseSeparatorExponent second).mapDomain (separatorEmbedding second) =
      separatorExponent second := by
  cases second <;>
    simp only [sparseSeparatorExponent,separatorExponent,Bool.false_eq_true,↓reduceIte]
  all_goals
    repeat' rw [Finsupp.mapDomain_add]
    simp only [Finsupp.mapDomain_single]
    norm_num [separatorEmbedding]

open MvPolynomial (X)

private noncomputable def sparseBorderMatrix (second endType : Bool) :
    Matrix (Fin 6) (Fin 6) (MvPolynomial (Fin 4) ℚ) :=
  if second then
    if endType then
      ![![0,0,X 3,0,X 1,0],
        ![0,0,0,X 3,0,X 1],
        ![X 2,0,0,0,0,0],
        ![0,X 0,X 2,0,0,0],
        ![0,0,0,X 2,0,0],
        ![0,0,0,0,X 0,0]]
    else
      ![![0,X 3,0,0,X 1,0],
        ![X 2,0,0,X 3,0,X 1],
        ![0,0,0,0,0,0],
        ![0,X 2,0,0,0,0],
        ![0,0,X 0,X 2,0,0],
        ![0,0,0,0,X 0,0]]
  else
    if endType then
      ![![0,0,0,0,X 1,0],
        ![X 2,0,0,X 3,0,X 1],
        ![0,0,0,0,0,0],
        ![0,X 0,0,X 2,0,0],
        ![0,0,X 0,0,0,0],
        ![0,0,0,0,X 0,0]]
    else
      ![![0,X 3,0,0,X 1,0],
        ![0,0,0,X 3,0,X 1],
        ![X 0,X 2,0,0,0,0],
        ![0,0,0,X 2,0,0],
        ![0,0,X 0,0,0,0],
        ![0,0,0,0,X 0,0]]

private theorem sparseBorderMatrix_eq (second endType : Bool) :
    sparseBorderMatrix second endType =
      (sparseProjection second).mapMatrix (universalBorderMatrix second endType) := by
  apply Matrix.ext
  intro i j
  cases second <;> cases endType <;> fin_cases i <;> fin_cases j <;>
    norm_num [sparseBorderMatrix,AlgHom.mapMatrix_apply,
      universalBorderMatrix,borderColumn,borderSymbol,sparseProjection_X]

private noncomputable def sparseFive (second : Bool) :
    Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 4) ℚ) :=
  if second then
    ![![0,X 3,0,X 1,0],
      ![0,0,X 3,0,X 1],
      ![X 0,X 2,0,0,0],
      ![0,0,X 2,0,0],
      ![0,0,0,X 0,0]]
  else
    ![![0,X 3,0,X 1,0],
      ![0,0,0,0,X 1],
      ![X 0,X 2,0,0,0],
      ![0,0,X 0,0,0],
      ![0,0,0,X 0,0]]

private noncomputable def sparseFour (second : Bool) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) ℚ) :=
  if second then
    ![![0,X 3,X 1,0],
      ![0,0,0,X 1],
      ![X 0,X 2,0,0],
      ![0,0,X 0,0]]
  else
    ![![0,X 3,0,X 1],
      ![X 0,X 2,0,0],
      ![0,0,X 0,0],
      ![0,0,0,X 0]]

private noncomputable def sparseThree :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) ℚ) :=
  ![![0,X 3,X 1],![X 0,X 2,0],![0,0,X 0]]

private theorem sparse_minor_five (second : Bool) :
    (sparseBorderMatrix second second).submatrix
      (if second then (2 : Fin 6) else 3).succAbove
      (if second then (0 : Fin 6) else 3).succAbove = sparseFive second := by
  apply Matrix.ext
  intro i j
  change sparseBorderMatrix second second
    ((if second then (2 : Fin 6) else 3).succAbove i)
    ((if second then (0 : Fin 6) else 3).succAbove j) = sparseFive second i j
  cases second <;> fin_cases i <;> fin_cases j <;>
    norm_num [sparseBorderMatrix,sparseFive,Matrix.submatrix_apply,Fin.succAbove]

private theorem sparse_minor_four (second : Bool) :
    (sparseFive second).submatrix
      (if second then (3 : Fin 5) else 1).succAbove
      (if second then (2 : Fin 5) else 4).succAbove = sparseFour second := by
  apply Matrix.ext
  intro i j
  change sparseFive second
    ((if second then (3 : Fin 5) else 1).succAbove i)
    ((if second then (2 : Fin 5) else 4).succAbove j) = sparseFour second i j
  cases second <;> fin_cases i <;> fin_cases j <;>
    norm_num [sparseFive,sparseFour,Matrix.submatrix_apply,Fin.succAbove]

private theorem sparse_minor_three (second : Bool) :
    (sparseFour second).submatrix
      (if second then (1 : Fin 4) else 2).succAbove
      (if second then (3 : Fin 4) else 2).succAbove = sparseThree := by
  apply Matrix.ext
  intro i j
  change sparseFour second
    ((if second then (1 : Fin 4) else 2).succAbove i)
    ((if second then (3 : Fin 4) else 2).succAbove j) = sparseThree i j
  cases second <;> fin_cases i <;> fin_cases j <;>
    norm_num [sparseFour,sparseThree,Matrix.submatrix_apply,Fin.succAbove]

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

private theorem sparse_six_det (second : Bool) :
    (sparseBorderMatrix second second).det = X 2*(sparseFive second).det := by
  have hz : ∀ c : Fin 6, c ≠ (if second then 0 else 3) →
      sparseBorderMatrix second second (if second then 2 else 3) c=0 := by
    intro c hc
    cases second <;> fin_cases c <;>
      first | exact False.elim (hc rfl) | norm_num [sparseBorderMatrix]
  have hv : sparseBorderMatrix second second
      (if second then 2 else 3) (if second then 0 else 3) = X 2 := by
    cases second <;> norm_num [sparseBorderMatrix]
  rw [det_single_row _ (if second then 2 else 3) (if second then 0 else 3) hz,
    hv,sparse_minor_five]
  cases second <;> norm_num

private theorem sparse_five_det (second : Bool) :
    (sparseFive second).det =
      -(if second then X 2 else X 1)*(sparseFour second).det := by
  have hz : ∀ c : Fin 5, c ≠ (if second then 2 else 4) →
      sparseFive second (if second then 3 else 1) c=0 := by
    intro c hc
    cases second <;> fin_cases c <;>
      first | exact False.elim (hc rfl) | norm_num [sparseFive]
  have hv : sparseFive second (if second then 3 else 1)
      (if second then 2 else 4) = (if second then X 2 else X 1) := by
    cases second <;> norm_num [sparseFive]
  rw [det_single_row _ (if second then 3 else 1) (if second then 2 else 4) hz,
    hv,sparse_minor_four]
  cases second <;> norm_num

private theorem sparse_four_det (second : Bool) :
    (sparseFour second).det =
      (if second then X 1 else X 0)*sparseThree.det := by
  have hz : ∀ c : Fin 4, c ≠ (if second then 3 else 2) →
      sparseFour second (if second then 1 else 2) c=0 := by
    intro c hc
    cases second <;> fin_cases c <;>
      first | exact False.elim (hc rfl) | norm_num [sparseFour]
  have hv : sparseFour second (if second then 1 else 2)
      (if second then 3 else 2) = (if second then X 1 else X 0) := by
    cases second <;> norm_num [sparseFour]
  rw [det_single_row _ (if second then 1 else 2) (if second then 3 else 2) hz,
    hv,sparse_minor_three]
  cases second <;> norm_num

private theorem sparse_three_det : sparseThree.det = -((X 0)^2*X 3) := by
  rw [Matrix.det_fin_three]
  norm_num [sparseThree] <;> ring

private theorem sparseGood_det (second : Bool) :
    (sparseBorderMatrix second second).det =
      if second then (X 0)^2*X 1*(X 2)^2*X 3 else (X 0)^3*X 1*X 2*X 3 := by
  rw [sparse_six_det,sparse_five_det,sparse_four_det,sparse_three_det]
  cases second <;> norm_num <;> ring

private theorem sparseBad_det (second : Bool) :
    (sparseBorderMatrix second (!second)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (2 : Fin 6)
  intro j
  cases second <;> fin_cases j <;> norm_num [sparseBorderMatrix]

private theorem sparseBorder_separator (second : Bool) :
    ((sparseBorderMatrix second false).det -
      (sparseBorderMatrix second true).det).coeff (sparseSeparatorExponent second) =
        if second then -1 else 1 := by
  classical
  cases second
  · rw [show (sparseBorderMatrix false true).det=0 from sparseBad_det false,
      sparseGood_det false]
    norm_num [sparseSeparatorExponent,MvPolynomial.X,MvPolynomial.monomial_pow,
      MvPolynomial.monomial_mul_monomial,MvPolynomial.coeff_add,
      MvPolynomial.coeff_sub,MvPolynomial.coeff_neg,MvPolynomial.coeff_monomial,
      Finsupp.ext_iff,Fin.forall_fin_succ,Finsupp.add_apply,Finsupp.single_apply]
  · rw [show (sparseBorderMatrix true false).det=0 from sparseBad_det true,
      sparseGood_det true]
    norm_num [sparseSeparatorExponent,MvPolynomial.X,MvPolynomial.monomial_pow,
      MvPolynomial.monomial_mul_monomial,MvPolynomial.coeff_add,
      MvPolynomial.coeff_sub,MvPolynomial.coeff_neg,MvPolynomial.coeff_monomial,
      Finsupp.ext_iff,Fin.forall_fin_succ,Finsupp.add_apply,Finsupp.single_apply]

/-- The exact two coefficient separators in `eq:five-border-separators`. -/
theorem universal_border_separator (second : Bool) :
    (((universalBorderMatrix second false).det -
      (universalBorderMatrix second true).det).coeff (separatorExponent second)) =
        if second then -1 else 1 := by
  classical
  rw [← sparseSeparatorExponent_map]
  rw [← MvPolynomial.coeff_killCompl (separatorEmbedding_injective second)]
  change (sparseProjection second
    ((universalBorderMatrix second false).det -
      (universalBorderMatrix second true).det)).coeff
        (sparseSeparatorExponent second) = if second then -1 else 1
  rw [map_sub,(sparseProjection second).map_det,(sparseProjection second).map_det,
    ← sparseBorderMatrix_eq,← sparseBorderMatrix_eq]
  exact sparseBorder_separator second

theorem g_pos (P : Parameters) : 0<P.g := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  omega

def borderLabel (P : Parameters) (j : Fin 14) : ℤ :=
  P.b+((j.val%7 : ℕ) : ℤ)*P.g-(if j.val<7 then 0 else P.q)

def borderAlphabet (P : Parameters) (j : Fin 14) : ℕ := (borderLabel P j).toNat

theorem borderLabel_nonneg (P : Parameters) (j : Fin 14) : 0≤borderLabel P j := by
  have hb := P.q_le_b
  have hq := P.q_pos
  have hg := g_pos P
  have hm : 0≤((j.val%7 : ℕ) : ℤ)*P.g := mul_nonneg (by omega) hg.le
  unfold borderLabel
  split_ifs <;> omega

set_option maxHeartbeats 0 in
theorem borderAlphabet_injective (P : Parameters) : Function.Injective (borderAlphabet P) := by
  intro i j he
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hbg := P.b_lt_g
  have he' := congrArg (fun k : ℕ => (k : ℤ)) he
  change ((borderLabel P i).toNat : ℤ)=((borderLabel P j).toNat : ℤ) at he'
  rw [Int.toNat_of_nonneg (borderLabel_nonneg P i),
    Int.toNat_of_nonneg (borderLabel_nonneg P j)] at he'
  fin_cases i <;> fin_cases j <;> norm_num [borderLabel] at he' ⊢ <;> omega

/-- The actual positive border; its matrix retains the independent homogeneous zero label. -/
def tiedBorder (P : Parameters) (second endType : Bool) : BetaDiagram 6 :=
  (if endType then H P second else F P second).positiveBorder P.g P.g (g_pos P) (g_pos P)

private theorem borderSymbol_rename (P : Parameters) (v : Bool) (r : ℤ) (hr : r<7) :
    MvPolynomial.rename (borderAlphabet P) (borderSymbol v r) =
      Gluing.hTilde (P.b+r*P.g-(if v then P.q else 0)) := by
  have hq:=P.q_pos
  have hbg:=P.b_lt_g
  have hg:=g_pos P
  by_cases hr0 : 0≤r
  · let j : Fin 14 := ⟨r.toNat+(if v then 7 else 0),by
      cases v <;> simp <;> omega⟩
    have hrNat : r.toNat<7 := by omega
    have hlabel : borderLabel P j=P.b+r*P.g-(if v then P.q else 0) := by
      cases v <;>
        simp [borderLabel,j,Nat.add_mod,Nat.mod_eq_of_lt hrNat,
          Int.toNat_of_nonneg hr0,hrNat] <;> ring
    have hk : 0≤P.b+r*P.g-(if v then P.q else 0) := by
      rw [← hlabel]
      exact borderLabel_nonneg P j
    have he : borderAlphabet P j=(P.b+r*P.g-(if v then P.q else 0)).toNat := by
      unfold borderAlphabet
      rw [hlabel]
    rw [borderSymbol,dif_pos ⟨hr0,hr⟩,MvPolynomial.rename_X,
      Gluing.hTilde,if_neg (not_lt_of_ge hk)]
    exact congrArg MvPolynomial.X he
  · have hmul:=mul_le_mul_of_nonneg_right (show r≤ -1 by omega) hg.le
    have hk : P.b+r*P.g-(if v then P.q else 0)<0 := by
      cases v <;> simp <;> nlinarith
    rw [borderSymbol,dif_neg (by omega),map_zero,Gluing.hTilde,if_pos hk]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The free alphabet is identified entrywise with the actual full-board homogeneous matrix. -/
theorem tiedBorder_homMatrix (P : Parameters) (second endType : Bool) :
    (tiedBorder P second endType).homMatrix =
      (universalBorderMatrix second endType).map (MvPolynomial.rename (borderAlphabet P)) := by
  apply Matrix.ext
  intro i j
  have hr : 5-(i.val : ℤ)+(borderColumn second endType j).2<7 := by
    have hi:=i.isLt
    cases second <;> cases endType <;> fin_cases j <;>
      norm_num [borderColumn] <;> omega
  change Gluing.hTilde ((tiedBorder P second endType).row i-
      (tiedBorder P second endType).col j) =
    MvPolynomial.rename (borderAlphabet P)
      (borderSymbol (borderColumn second endType j).1
        (5-(i.val : ℤ)+(borderColumn second endType j).2))
  rw [borderSymbol_rename P _ _ hr]
  apply congrArg Gluing.hTilde
  cases second <;> cases endType <;> fin_cases i <;> fin_cases j <;>
    norm_num [tiedBorder,BetaDiagram.positiveBorder,F,H,rows,fCols,hCols,borderColumn] <;> ring

theorem tiedBorder_homSchur (P : Parameters) (second endType : Bool) :
    (tiedBorder P second endType).homSchur =
      MvPolynomial.rename (borderAlphabet P) (universalBorderMatrix second endType).det := by
  rw [BetaDiagram.homSchur,tiedBorder_homMatrix]
  exact (AlgHom.map_det _ _).symm

/-- The two actual six-row tied borders are unequal, including `q = b`. -/
theorem tiedBorder_schur_ne (P : Parameters) (second : Bool) :
    (tiedBorder P second false).schur ≠ (tiedBorder P second true).schur := by
  intro he
  have hh := ((tiedBorder P second false).homSchur_eq_iff (tiedBorder P second true)).mpr he
  rw [tiedBorder_homSchur,tiedBorder_homSchur] at hh
  have hfree := MvPolynomial.rename_injective (borderAlphabet P) (borderAlphabet_injective P) hh
  have hcoef := universal_border_separator second
  rw [hfree,sub_self,MvPolynomial.coeff_zero] at hcoef
  cases second <;> norm_num at hcoef

theorem extendTop_opening (D : BetaDiagram 5) (k : Fin 3)
    (ho : FiveOpening.HasOpening D k) (t : ℤ) (ht : 0<t) :
    FiveOpening.HasOpening (D.extendTop t ht) k := by
  intro i j
  have hnegative : (D.extendTop t ht).row i < (D.extendTop t ht).col j ↔ D.row i<D.col j := by
    by_cases hi : i=0
    · subst i
      have hc:=D.col_strictAnti.antitone (Fin.zero_le j)
      have hr:=D.row_nonempty 0
      change D.row 0+t<D.col j ↔ D.row 0<D.col j
      omega
    · simp [BetaDiagram.extendTop,hi]
  rw [hnegative]
  exact ho i j

theorem extendBottom_opening (D : BetaDiagram 5) (k : Fin 3)
    (ho : FiveOpening.HasOpening D k) (t : ℤ) (ht : 0<t) :
    FiveOpening.HasOpening (D.extendBottom t ht) k := by
  intro i j
  have hnegative : (D.extendBottom t ht).row i < (D.extendBottom t ht).col j ↔ D.row i<D.col j := by
    by_cases hj : j=Fin.last 4
    · subst j
      have hr:=D.row_strictAnti.antitone (Fin.le_last i)
      have hc:=D.row_nonempty (Fin.last 4)
      change D.row i<D.col (Fin.last 4)-t ↔ D.row i<D.col (Fin.last 4)
      omega
    · have hj' := hj
      change j≠(4 : Fin 5) at hj'
      simp [BetaDiagram.extendBottom,hj']
  rw [hnegative]
  exact ho i j

/-- `lem:five-endpoint`, with common betas and no exceptional-list hypothesis. -/
theorem five_endpoint_iff (D : BetaDiagram 5) (hD : D.Connected)
    (hν : negativeCount D=5) (t : ℤ) (ht : 0<t) :
    (D.extendTop t ht).schur=(D.extendBottom t ht).schur ↔ D.Symmetric := by
  constructor
  · intro he
    obtain ⟨k,ho⟩ := FiveOpening.opening_inventory D hD hν
    have hclass := FiveNegative.same_opening_rigidity
      (D.extendTop t ht) (D.extendBottom t ht)
      (D.extendTop_connected hD t ht) (D.extendBottom_connected hD t ht) k
      (extendTop_opening D k ho t ht) (extendBottom_opening D k ho t ht) he
    rcases hclass with h | h
    · exact (D.extendTop_not_translation_extendBottom t ht h).elim
    · exact D.symmetric_of_extendTop_rotation_extendBottom t ht h
  · intro hsym
    exact FiveNegative.actual_orbit_schur
      (Or.inr (D.extendTop_rotation_extendBottom_of_symmetric hsym t ht))

theorem arithmetic_reflection {v w : Fin 5 → ℤ} (c : ℤ)
    (h : ∀ i,v i=c-w i.rev) (hw : Arithmetic w) : Arithmetic v := by
  obtain ⟨d,hd⟩ := hw
  refine ⟨d,?_⟩
  intro i
  have hh:=hd i.rev
  rw [h i.castSucc,h i.succ]
  fin_cases i <;> norm_num [Fin.rev] at hh ⊢ <;> linarith

theorem orbit_requires_arithmetic (D W : BetaDiagram 5) (hW : Arithmetic W.row)
    (hO : FiveNegative.ActualOrbit D W) : Arithmetic D.row ∨ Arithmetic D.col := by
  rcases hO with ⟨c,hr,hc⟩ | ⟨c,hr,hc⟩
  · exact Or.inl ((arithmetic_translation c hr).mpr hW)
  · exact Or.inr (arithmetic_reflection c hc hW)

theorem no_exceptional_of_nonarithmetic (D : BetaDiagram 5)
    (hr : ¬Arithmetic D.row) (hc : ¬Arithmetic D.col) :
    ¬∃ Q second, FiveNegative.ExceptionalMember Q second D := by
  rintro ⟨Q,second,hO⟩
  rcases hO with hO | hO
  · rcases orbit_requires_arithmetic D (F Q second) (rows_arithmetic Q) hO with h | h
    · exact hr h
    · exact hc h
  · rcases orbit_requires_arithmetic D (H Q second) (rows_arithmetic Q) hO with h | h
    · exact hr h
    · exact hc h

theorem F_extendBottom_cols_not_arithmetic (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ¬Arithmetic ((F P s).extendBottom t ht).col := by
  rintro ⟨d,hd⟩
  have h0:=hd 0
  have h1:=hd 1
  have hq:=P.q_pos
  have hqb:=P.q_le_b
  have hbg:=P.b_lt_g
  cases s <;> norm_num [BetaDiagram.extendBottom,F,fCols] at h0 h1 <;> omega

theorem H_extendBottom_cols_not_arithmetic (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ¬Arithmetic ((H P s).extendBottom t ht).col := by
  rintro ⟨d,hd⟩
  have h0:=hd 0
  have h1:=hd 1
  have h2:=hd 2
  have hq:=P.q_pos
  have hqb:=P.q_le_b
  have hbg:=P.b_lt_g
  cases s <;> norm_num [BetaDiagram.extendBottom,H,hCols] at h0 h1 h2 <;> omega

theorem F_extendTop_not_exceptional (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ¬∃ Q second, FiveNegative.ExceptionalMember Q second ((F P s).extendTop t ht) :=
  no_exceptional_of_nonarithmetic _ (F_extendTop_rows_not_arithmetic P s t ht)
    (F_extendTop_cols_not_arithmetic P s t ht)

theorem H_extendTop_not_exceptional (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ¬∃ Q second, FiveNegative.ExceptionalMember Q second ((H P s).extendTop t ht) :=
  no_exceptional_of_nonarithmetic _ (H_extendTop_rows_not_arithmetic P s t ht)
    (H_extendTop_cols_not_arithmetic P s t ht)

theorem F_extendBottom_not_exceptional (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ¬∃ Q second, FiveNegative.ExceptionalMember Q second ((F P s).extendBottom t ht) := by
  rintro ⟨Q,j,hO⟩
  have htr:=extendBottom_not_translation_displayed P Q s j t ht
  rcases hO with (h | h) | (h | h)
  · exact htr.1 h
  · obtain ⟨c,hr,hc⟩ := h
    exact F_extendBottom_cols_not_arithmetic P s t ht
      (arithmetic_reflection c hc (rows_arithmetic Q))
  · exact htr.2.1 h
  · obtain ⟨c,hr,hc⟩ := h
    exact F_extendBottom_cols_not_arithmetic P s t ht
      (arithmetic_reflection c hc (rows_arithmetic Q))

theorem H_extendBottom_not_exceptional (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ¬∃ Q second, FiveNegative.ExceptionalMember Q second ((H P s).extendBottom t ht) := by
  rintro ⟨Q,j,hO⟩
  have htr:=extendBottom_not_translation_displayed P Q s j t ht
  rcases hO with (h | h) | (h | h)
  · exact htr.2.2.1 h
  · obtain ⟨c,hr,hc⟩ := h
    exact H_extendBottom_cols_not_arithmetic P s t ht
      (arithmetic_reflection c hc (rows_arithmetic Q))
  · exact htr.2.2.2 h
  · obtain ⟨c,hr,hc⟩ := h
    exact H_extendBottom_cols_not_arithmetic P s t ht
      (arithmetic_reflection c hc (rows_arithmetic Q))

theorem F_extendTop_rigid (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ((F P s).extendTop t ht).RotationRigid :=
  FiveNegative.five_base_rotation_rigid _ ((F P s).extendTop_connected (F_connected P s) t ht)
    (FiveNegative.opening_negativeCount _ 1 (extendTop_opening _ 1 (F_opening P s) t ht))
    (F_extendTop_not_exceptional P s t ht)

theorem H_extendTop_rigid (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ((H P s).extendTop t ht).RotationRigid :=
  FiveNegative.five_base_rotation_rigid _ ((H P s).extendTop_connected (H_connected P s) t ht)
    (FiveNegative.opening_negativeCount _ 0 (extendTop_opening _ 0 (H_opening P s) t ht))
    (H_extendTop_not_exceptional P s t ht)

theorem F_extendBottom_rigid (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ((F P s).extendBottom t ht).RotationRigid :=
  FiveNegative.five_base_rotation_rigid _ ((F P s).extendBottom_connected (F_connected P s) t ht)
    (FiveNegative.opening_negativeCount _ 1 (extendBottom_opening _ 1 (F_opening P s) t ht))
    (F_extendBottom_not_exceptional P s t ht)

theorem H_extendBottom_rigid (P : Parameters) (s : Bool) (t : ℤ) (ht : 0<t) :
    ((H P s).extendBottom t ht).RotationRigid :=
  FiveNegative.five_base_rotation_rigid _ ((H P s).extendBottom_connected (H_connected P s) t ht)
    (FiveNegative.opening_negativeCount _ 0 (extendBottom_opening _ 0 (H_opening P s) t ht))
    (H_extendBottom_not_exceptional P s t ht)

def endpoint (D : BetaDiagram 5) (bottom : Bool) (t : ℤ) (ht : 0<t) : BetaDiagram 5 :=
  if bottom then D.extendBottom t ht else D.extendTop t ht

theorem endpoint_connected (D : BetaDiagram 5) (hD : D.Connected)
    (bottom : Bool) (t : ℤ) (ht : 0<t) : (endpoint D bottom t ht).Connected := by
  cases bottom
  · exact D.extendTop_connected hD t ht
  · exact D.extendBottom_connected hD t ht

theorem exceptional_endpoint_rigid (P : Parameters) (second endType bottom : Bool)
    (t : ℤ) (ht : 0<t) :
    (endpoint (if endType then H P second else F P second) bottom t ht).RotationRigid := by
  cases endType <;> cases bottom
  · exact F_extendTop_rigid P second t ht
  · exact F_extendBottom_rigid P second t ht
  · exact H_extendTop_rigid P second t ht
  · exact H_extendBottom_rigid P second t ht

theorem endpoint_cross_orbit_ne (P : Parameters) (second bottomF bottomH : Bool)
    (t u : ℤ) (ht : 0<t) (hu : 0<u) :
    ¬ FiveNegative.ActualOrbit (endpoint (F P second) bottomF t ht)
      (endpoint (H P second) bottomH u hu) := by
  have hq:=P.q_pos
  have hqb:=P.q_le_b
  have hbg:=P.b_lt_g
  rintro (⟨c,hr,hc⟩ | ⟨c,hr,hc⟩)
  · cases bottomF <;> cases bottomH
    · have hc1:=hc 1
      have hc4:=hc 4
      norm_num [endpoint,BetaDiagram.extendTop,F,H,fCols,hCols] at hc1 hc4
      omega
    · apply F_extendTop_rows_not_arithmetic P second t ht
      exact (arithmetic_translation c hr).mpr (rows_arithmetic P)
    · apply H_extendTop_rows_not_arithmetic P second u hu
      exact (arithmetic_translation c hr).mp (rows_arithmetic P)
    · have hr4:=hr 4
      have hc1:=hc 1
      norm_num [endpoint,BetaDiagram.extendBottom,F,H,rows,fCols,hCols] at hr4 hc1
      omega
  · have hr3:=hr 3
    have hr4:=hr 4
    cases bottomF <;> cases bottomH <;>
      norm_num [endpoint,BetaDiagram.extendTop,BetaDiagram.extendBottom,
        F,H,rows,fCols,hCols,Fin.rev] at hr3 hr4 <;> omega

theorem endpoint_cross_schur_ne (P : Parameters) (second bottomF bottomH : Bool)
    (t u : ℤ) (ht : 0<t) (hu : 0<u) :
    (endpoint (F P second) bottomF t ht).schur ≠
      (endpoint (H P second) bottomH u hu).schur := by
  intro he
  have hrigid := exceptional_endpoint_rigid P second false bottomF t ht
  have hH := endpoint_connected (H P second) (H_connected P second) bottomH u hu
  have hO := ((endpoint (F P second) bottomF t ht).rotationRigid_iff_same_order).mp
    hrigid _ hH he.symm
  exact endpoint_cross_orbit_ne P second bottomF bottomH t u ht hu hO

def rowWord {n : ℕ} (D : BetaDiagram n) : Multiset ℤ :=
  Finset.univ.val.map D.rowLength

theorem rowWord_eq_of_schur_eq {n : ℕ} (D W : BetaDiagram (n+1))
    (hD : D.Connected) (hW : W.Connected) (he : D.schur=W.schur) : rowWord D=rowWord W := by
  have hp : (D.toProfile hD).schur=(W.toProfile hW).schur := by
    simpa only [BetaDiagram.toProfile_schur] using he
  have hrows := (Gluing.Profile.rows_eq_of_schur_eq hp).2
  have hcast := congrArg (Multiset.map (fun z : ℕ => (z : ℤ))) hrows
  have hDr (i) : ((D.toProfile hD).r i : ℤ)=D.rowLength i := by
    rw [← (D.toProfile hD).xi_sub_zeta i,D.toProfile_xi hD,D.toProfile_zeta hD]
    dsimp only [BetaDiagram.rowLength]
    ring
  have hWr (i) : ((W.toProfile hW).r i : ℤ)=W.rowLength i := by
    rw [← (W.toProfile hW).xi_sub_zeta i,W.toProfile_xi hW,W.toProfile_zeta hW]
    dsimp only [BetaDiagram.rowLength]
    ring
  simpa only [rowWord,Gluing.Profile.rowMultiset,Multiset.map_map,Function.comp_apply,hDr,hWr] using hcast

theorem F_tied_border_rows (P : Parameters) (second : Bool) (t : ℤ) (ht : 0<t) :
    ((F P second).positiveBorder t t ht ht).rowLength =
      ![P.b+(if second then P.g-P.q+t else P.g+t),
        P.b+3*P.g-P.q,P.b+2*P.g,P.b+2*P.g-P.q,P.b+P.g,P.b+t] := by
  funext i
  cases second <;> fin_cases i <;>
    norm_num [BetaDiagram.rowLength,BetaDiagram.positiveBorder,F,rows,fCols] <;> ring

theorem H_tied_border_rows (P : Parameters) (second : Bool) (t : ℤ) (ht : 0<t) :
    ((H P second).positiveBorder t t ht ht).rowLength =
      ![P.b+2*P.g-P.q+t,P.b+2*P.g,
        P.b+(if second then 2*P.g-P.q else 2*P.g),
        P.b+2*P.g-P.q,P.b+P.g,P.b+t] := by
  funext i
  cases second <;> fin_cases i <;>
    norm_num [BetaDiagram.rowLength,BetaDiagram.positiveBorder,H,rows,hCols] <;> ring

theorem tied_border_margin (P : Parameters) (second : Bool) (t : ℤ) (ht : 0<t)
    (he : ((F P second).positiveBorder t t ht ht).schur =
      ((H P second).positiveBorder t t ht ht).schur) : t=P.g := by
  have hrows:=rowWord_eq_of_schur_eq
    ((F P second).positiveBorder t t ht ht) ((H P second).positiveBorder t t ht ht)
    ((F P second).positiveBorder_connected t t ht ht)
    ((H P second).positiveBorder_connected t t ht ht) he
  have huniv : (Finset.univ : Finset (Fin 6)).val={0,1,2,3,4,5} := by decide
  unfold rowWord at hrows
  rw [F_tied_border_rows,H_tied_border_rows,huniv] at hrows
  simp only [Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] at hrows
  change (({P.b+(if second then P.g-P.q+t else P.g+t)}+
    ({P.b+3*P.g-P.q}+({P.b+2*P.g}+({P.b+2*P.g-P.q}+({P.b+P.g}+{P.b+t}))))) : Multiset ℤ) =
    {P.b+2*P.g-P.q+t}+({P.b+2*P.g}+
      ({P.b+(if second then 2*P.g-P.q else 2*P.g)}+
        ({P.b+2*P.g-P.q}+({P.b+P.g}+{P.b+t})))) at hrows
  let C : Multiset ℤ := {P.b+2*P.g}+({P.b+2*P.g-P.q}+({P.b+P.g}+{P.b+t}))
  have hpair : ({P.b+(if second then P.g-P.q+t else P.g+t),P.b+3*P.g-P.q} : Multiset ℤ) =
      {P.b+2*P.g-P.q+t,P.b+(if second then 2*P.g-P.q else 2*P.g)} := by
    have hfull :
        (({P.b+(if second then P.g-P.q+t else P.g+t)}+{P.b+3*P.g-P.q})+C : Multiset ℤ) =
        ({P.b+2*P.g-P.q+t}+{P.b+(if second then 2*P.g-P.q else 2*P.g)})+C := by
      convert hrows using 1 <;> dsimp only [C] <;> ac_rfl
    exact add_right_cancel hfull
  have hmem : P.b+(if second then P.g-P.q+t else P.g+t) ∈
      ({P.b+2*P.g-P.q+t,P.b+(if second then 2*P.g-P.q else 2*P.g)} : Multiset ℤ) := by
    rw [← hpair]
    simp
  have hq:=P.q_pos
  have hqb:=P.q_le_b
  have hbg:=P.b_lt_g
  cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hmem <;>
    rcases hmem with hmem | hmem <;> omega

theorem tied_equal_border_ne (P : Parameters) (second : Bool) (t : ℤ) (ht : 0<t) :
    ((F P second).positiveBorder t t ht ht).schur ≠
      ((H P second).positiveBorder t t ht ht).schur := by
  intro he
  have htG:=tied_border_margin P second t ht he
  subst t
  exact tiedBorder_schur_ne P second he

theorem unequal_border_endpoint_coefficient (D : BetaDiagram 5) (u v : ℤ)
    (hu : 0<u) (hv : 0<v) (hne : u≠v) :
    MvPolynomial.pderiv (D.positiveBorder u v hu hv).borderSecondGenerator
      (eraseGenerator (D.positiveBorder u v hu hv).borderLargestGenerator
        (D.positiveBorder u v hu hv).schur) =
      (endpoint D (decide (v<u)) (min u v) (lt_min hu hv)).schur := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hc:=D.positiveBorder_top_coefficient u v hu hv h
    dsimp only at hc
    norm_num at hc
    simpa [endpoint,min_eq_left h.le,show ¬v<u from by omega] using hc
  · have hc:=D.positiveBorder_bottom_coefficient u v hu hv h
    dsimp only at hc
    norm_num at hc
    simpa [endpoint,min_eq_right h.le,h] using hc

theorem exceptional_border_marker_readings (P : Parameters) (second : Bool)
    (u v U V : ℤ) (hu : 0<u) (hv : 0<v) (hU : 0<U) (hV : 0<V)
    (he : ((F P second).positiveBorder u v hu hv).schur =
      ((H P second).positiveBorder U V hU hV).schur) :
    ((u=U ∧ v=V) ∨ (u=V ∧ v=U)) ∧
    ((F P second).positiveBorder u v hu hv).borderLargestGenerator =
      ((H P second).positiveBorder U V hU hV).borderLargestGenerator := by
  let A:=(F P second).positiveBorder u v hu hv
  let B:=(H P second).positiveBorder U V hU hV
  have hAc:= (F P second).positiveBorder_connected u v hu hv
  have hBc:= (H P second).positiveBorder_connected U V hU hV
  have hmax:=A.largestLabel_eq_of_schur_eq B hAc hBc he
  have hmin:=A.border_minMargin_eq_of_schur_eq B hAc hBc
    ((F P second).positiveBorder_positiveCorner u v hu hv)
    ((H P second).positiveBorder_positiveCorner U V hU hV)
    (by simpa only [A,BetaDiagram.positiveBorder_cornerDiagram] using F_connected P second)
    (by simpa only [B,BetaDiagram.positiveBorder_cornerDiagram] using H_connected P second) he
  have hspan : (F P second).largestLabel=(H P second).largestLabel := by
    simp [BetaDiagram.largestLabel,F,H,rows,fCols,hCols]
  have hsum : u+v=U+V := by
    have hm' : (F P second).largestLabel+u+v=(H P second).largestLabel+U+V := by
      simpa only [A,B,BetaDiagram.positiveBorder_largestLabel] using hmax
    rw [hspan] at hm'
    omega
  have hmin' : min u v=min U V := by
    simpa only [A,B,BetaDiagram.positiveBorder_topMargin,BetaDiagram.positiveBorder_bottomMargin] using hmin
  refine ⟨by omega,?_⟩
  apply Subtype.ext
  change A.largestLabel.toNat=B.largestLabel.toNat
  exact congrArg Int.toNat hmax

theorem exceptional_border_second_marker_eq (P : Parameters) (second : Bool)
    (u v U V : ℤ) (hu : 0<u) (hv : 0<v) (hU : 0<U) (hV : 0<V)
    (hpair : (u=U ∧ v=V) ∨ (u=V ∧ v=U)) :
    ((F P second).positiveBorder u v hu hv).borderSecondGenerator =
      ((H P second).positiveBorder U V hU hV).borderSecondGenerator := by
  apply Subtype.ext
  change (((F P second).positiveBorder u v hu hv).secondLabel).toNat =
    (((H P second).positiveBorder U V hU hV).secondLabel).toNat
  congr 1
  rw [BetaDiagram.positiveBorder_secondLabel,BetaDiagram.positiveBorder_secondLabel]
  have hspan : (F P second).largestLabel=(H P second).largestLabel := by
    simp [BetaDiagram.largestLabel,F,H,rows,fCols,hCols]
  rw [hspan]
  rcases hpair with h | h <;> omega

/-- No positive border over the displayed middle representative equals one over the end representative. -/
theorem exceptional_positive_borders_ne (P : Parameters) (second : Bool)
    (u v U V : ℤ) (hu : 0<u) (hv : 0<v) (hU : 0<U) (hV : 0<V) :
    ((F P second).positiveBorder u v hu hv).schur ≠
      ((H P second).positiveBorder U V hU hV).schur := by
  intro he
  obtain ⟨hpair,hM⟩:=exceptional_border_marker_readings P second u v U V hu hv hU hV he
  have hN:=exceptional_border_second_marker_eq P second u v U V hu hv hU hV hpair
  by_cases huv : u=v
  · have hUu : U=u := by rcases hpair with h | h <;> omega
    have hVu : V=u := by rcases hpair with h | h <;> omega
    subst v
    subst U
    subst V
    exact tied_equal_border_ne P second u hu he
  · have hUV : U≠V := by rcases hpair with h | h <;> omega
    have hc :
        MvPolynomial.pderiv ((F P second).positiveBorder u v hu hv).borderSecondGenerator
          (eraseGenerator ((F P second).positiveBorder u v hu hv).borderLargestGenerator
            ((F P second).positiveBorder u v hu hv).schur) =
        MvPolynomial.pderiv ((H P second).positiveBorder U V hU hV).borderSecondGenerator
          (eraseGenerator ((H P second).positiveBorder U V hU hV).borderLargestGenerator
            ((H P second).positiveBorder U V hU hV).schur) := by
      rw [he,hM,hN]
    rw [unequal_border_endpoint_coefficient _ _ _ hu hv huv,
      unequal_border_endpoint_coefficient _ _ _ hU hV hUV] at hc
    exact endpoint_cross_schur_ne P second (decide (v<u)) (decide (V<U))
      (min u v) (min U V) (lt_min hu hv) (lt_min hU hV) hc

theorem positiveBorder_translation (D W : BetaDiagram 5) (h : D.TranslationEquivalent W)
    (u v : ℤ) (hu : 0<u) (hv : 0<v) :
    (D.positiveBorder u v hu hv).TranslationEquivalent (W.positiveBorder u v hu hv) := by
  obtain ⟨c,hr,hc⟩ := h
  refine ⟨c,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
        simp only [BetaDiagram.positiveBorder_row_zero]
        have hh:=hr 0
        omega
    | succ i =>
        simp only [BetaDiagram.positiveBorder_row_succ]
        exact hr i
  · intro j
    cases j using Fin.lastCases with
    | last =>
        simp only [BetaDiagram.positiveBorder_col_last]
        have hh:=hc (Fin.last 4)
        omega
    | cast j =>
        simp only [BetaDiagram.positiveBorder_col_castSucc]
        exact hc j

theorem positive_border_orbit_transport (D W : BetaDiagram 5)
    (h : FiveNegative.ActualOrbit D W) (u v : ℤ) (hu : 0<u) (hv : 0<v) :
    ∃ (U V : ℤ) (hU : 0<U) (hV : 0<V),
      (D.positiveBorder u v hu hv).schur=(W.positiveBorder U V hU hV).schur := by
  rcases h with h | ⟨c,hr,hc⟩
  · exact ⟨u,v,hu,hv,(positiveBorder_translation D W h u v hu hv).schur_eq⟩
  · have htr : D.TranslationEquivalent W.rotate := by
      refine ⟨c,?_,?_⟩
      · intro i
        change D.row i = -W.col i.rev+c
        have hh:=hr i
        omega
      · intro i
        change D.col i = -W.row i.rev+c
        have hh:=hc i
        omega
    refine ⟨v,u,hv,hu,?_⟩
    exact (positiveBorder_translation D W.rotate htr u v hu hv).schur_eq.trans
      (W.positiveBorder_rotate_schur u v hu hv)

/-- `lem:five-exceptional-borders` for both complete rotation orbits and all positive margins. -/
theorem exceptional_borders (P : Parameters) (second : Bool) (C D : BetaDiagram 5)
    (hC : FiveNegative.ActualOrbit C (F P second))
    (hD : FiveNegative.ActualOrbit D (H P second))
    (u v U V : ℤ) (hu : 0<u) (hv : 0<v) (hU : 0<U) (hV : 0<V) :
    (C.positiveBorder u v hu hv).schur ≠ (D.positiveBorder U V hU hV).schur := by
  intro he
  obtain ⟨u',v',hu',hv',hCF⟩:=positive_border_orbit_transport C (F P second) hC u v hu hv
  obtain ⟨U',V',hU',hV',hDH⟩:=positive_border_orbit_transport D (H P second) hD U V hU hV
  exact exceptional_positive_borders_ne P second u' v' U' V' hu' hv' hU' hV'
    (hCF.symm.trans (he.trans hDH))

/-- The source five-negative budget leaves only the two singleton split sizes. -/
theorem five_component_inventory {n : ℕ} {D : BetaDiagram n}
    (C : BetaDiagram.ComponentDecomposition D) (hn : 5≤n) (hD : ¬D.Connected)
    (hν : negativeCount D=5) :
    (n=5 ∧ ((C.components.map Sigma.fst)=[1,4] ∨ (C.components.map Sigma.fst)=[4,1]) ∧
      (C.components.map (fun X => negativeCount X.2)).sum=1) ∨
    (n=6 ∧ ((C.components.map Sigma.fst)=[1,5] ∨ (C.components.map Sigma.fst)=[5,1]) ∧
      (C.components.map (fun X => negativeCount X.2)).sum=0) := by
  let xs:=C.components.map Sigma.fst
  have hpos : ∀a∈xs,0<a := C.orders_positive
  have hsum : xs.sum=n := C.component_rows_sum
  have hbudget:=C.negative_budget
  rw [hν] at hbudget
  change 5=pairwiseRowProducts xs+
    (C.components.map (fun X => negativeCount X.2)).sum at hbudget
  have hcross : pairwiseRowProducts xs≤5 := by omega
  have hlen : xs.length=2 := by
    have hlo : 2≤xs.length := by simpa [xs] using C.disconnected_length_ge_two (by omega) hD
    by_contra hh
    have hthree:=ComponentOrderInventory.three_component_bound xs hpos (by omega)
    omega
  obtain ⟨a,b,hxs⟩:=List.length_eq_two.mp hlen
  have ha : 0<a := hpos a (by rw [hxs]; simp)
  have hb : 0<b := hpos b (by rw [hxs]; simp)
  rw [hxs] at hsum hcross hbudget
  simp only [List.sum_cons,List.sum_nil,pairwiseRowProducts,
    Nat.add_zero,Nat.mul_zero] at hsum hcross hbudget
  have hab : a=1 ∨ b=1 := by
    by_contra hh
    have ha2 : 2≤a := by omega
    have hb2 : 2≤b := by omega
    have ha' : a-2+2=a := by omega
    have hb' : b-2+2=b := by omega
    have hprod : 0≤(a-2)*(b-2) := Nat.zero_le _
    nlinarith
  change (n=5 ∧ (xs=[1,4] ∨ xs=[4,1]) ∧ _) ∨
    (n=6 ∧ (xs=[1,5] ∨ xs=[5,1]) ∧ _)
  rw [hxs]
  rcases hab with rfl | rfl
  · have hbc : b=4 ∨ b=5 := by omega
    rcases hbc with rfl | rfl
    · exact Or.inl ⟨by omega,Or.inl rfl,by omega⟩
    · exact Or.inr ⟨by omega,Or.inl rfl,by omega⟩
  · have hac : a=4 ∨ a=5 := by omega
    rcases hac with rfl | rfl
    · exact Or.inl ⟨by omega,Or.inr rfl,by omega⟩
    · exact Or.inr ⟨by omega,Or.inr rfl,by omega⟩

/-- From eight parent rows onward a five-negative maximal cofactor cannot disconnect. -/
theorem five_large_cofactor_connected {n : ℕ} (D : BetaDiagram (n+1))
    (hP : D.PositiveCorner) (hn : 8≤n+1) (hν : negativeCount D=5) :
    (D.cornerDiagram hP).Connected := by
  by_contra hC
  let C:=(D.cornerDiagram hP).componentDecomposition
  have hcount : negativeCount (D.cornerDiagram hP)=5 := by
    rw [D.corner_negativeCount hP]
    exact hν
  have hbound:=C.negative_budget_row_bound (by omega) hC 5 (by omega)
  omega

theorem parent_border_translation (D : BetaDiagram 6) (hP : D.PositiveCorner) :
    D.TranslationEquivalent
      ((D.cornerDiagram hP).positiveBorder D.topMargin D.bottomMargin
        D.topMargin_pos D.bottomMargin_pos) := by
  refine ⟨0,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
        change D.row 0=(D.row 1+(D.row 0-D.row 1))+0
        ring
    | succ i =>
        change D.row i.succ=D.row i.succ+0
        ring
  · intro j
    cases j using Fin.lastCases with
    | last =>
        change D.col (Fin.last 5) =
          (D.col ((Fin.last 4).castSucc) -
            (D.col ((Fin.last 4).castSucc)-D.col (Fin.last 5)))+0
        ring
    | cast j =>
        rw [BetaDiagram.positiveBorder_col_castSucc]
        simp [BetaDiagram.cornerDiagram]

theorem five_parent_connected_core_orbit (D W : BetaDiagram 6)
    (hD : D.Connected) (hW : W.Connected) (hPD : D.PositiveCorner) (hPW : W.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected) (hCW : (W.cornerDiagram hPW).Connected)
    (hν : negativeCount D=5) (he : D.schur=W.schur) :
    FiveNegative.ActualOrbit (D.cornerDiagram hPD) (W.cornerDiagram hPW) := by
  have hc : (D.cornerDiagram hPD).schur=(W.cornerDiagram hPW).schur := by
    rw [BetaDiagram.cornerDiagram_schur,BetaDiagram.cornerDiagram_schur]
    exact D.cornerPolynomial_eq_of_schur_eq W hD hW he
  have hνC : negativeCount (D.cornerDiagram hPD)=5 := by
    rw [D.corner_negativeCount hPD]
    exact hν
  have hborders :
      ((D.cornerDiagram hPD).positiveBorder D.topMargin D.bottomMargin
        D.topMargin_pos D.bottomMargin_pos).schur =
      ((W.cornerDiagram hPW).positiveBorder W.topMargin W.bottomMargin
        W.topMargin_pos W.bottomMargin_pos).schur :=
    (parent_border_translation D hPD).schur_eq.symm.trans
      (he.trans (parent_border_translation W hPW).schur_eq)
  rcases (FiveNegative.five_base_pair _ _ hCD hCW hνC).mp hc with h | ⟨P,second,hD',hW'⟩
  · exact h
  · rcases hD' with hD' | hD' <;> rcases hW' with hW' | hW'
    · exact FiveNegative.actual_orbit_trans hD' (FiveNegative.actual_orbit_symm hW')
    · exact (exceptional_borders P second _ _ hD' hW'
        D.topMargin D.bottomMargin W.topMargin W.bottomMargin
        D.topMargin_pos D.bottomMargin_pos W.topMargin_pos W.bottomMargin_pos hborders).elim
    · exact (exceptional_borders P second _ _ hW' hD'
        W.topMargin W.bottomMargin D.topMargin D.bottomMargin
        W.topMargin_pos W.bottomMargin_pos D.topMargin_pos D.bottomMargin_pos hborders.symm).elim
    · exact FiveNegative.actual_orbit_trans hD' (FiveNegative.actual_orbit_symm hW')

/-- The connected-cofactor six-row clause, with exceptional cross-orbit borders discharged. -/
theorem five_six_connected_cofactor_rigid (D : BetaDiagram 6) (hD : D.Connected)
    (hPD : D.PositiveCorner) (hCD : (D.cornerDiagram hPD).Connected)
    (hν : negativeCount D=5) : D.RotationRigid := by
  apply (D.rotationRigid_iff_same_order).mpr
  intro W hW he
  let hPW:=D.positiveCorner_of_cornerPolynomial_eq W hD hW hPD
    (D.cornerPolynomial_eq_of_schur_eq W hD hW he.symm)
  have hCW : (W.cornerDiagram hPW).Connected :=
    D.connected_corner_of_corner_eq W hD hW hPD hCD he.symm
  have hνC : negativeCount (D.cornerDiagram hPD)=5 := by
    rw [D.corner_negativeCount hPD]
    exact hν
  have hEnds : ∀ (t : ℤ) (ht : 0<t),
      ((D.cornerDiagram hPD).extendTop t ht).schur =
        ((D.cornerDiagram hPD).extendBottom t ht).schur →
      (D.cornerDiagram hPD).Symmetric := by
    intro t ht hext
    exact (five_endpoint_iff _ hCD hνC t ht).mp hext
  rcases five_parent_connected_core_orbit D W hD hW hPD hPW hCD hCW hν he.symm with htr | hrot
  · exact D.connected_border_aligned_rigidity W hD hW hPD hPW hCD hCW htr hEnds he.symm
  · have hWr:=W.rotate_connected hW
    have heR : D.schur=W.rotate.schur := he.symm.trans W.rotate_schur.symm
    have hCR : (W.rotate.cornerDiagram (W.rotate_positiveCorner hPW)).Connected := by
      apply BetaDiagram.connected_of_schur_irreducible _ (by omega)
      rw [← (D.corner_translation_of_rotation W hPD hPW hrot).schur_eq]
      exact (D.cornerDiagram hPD).schur_irreducible hCD
    rcases D.connected_border_aligned_rigidity W.rotate hD hWr hPD
      (W.rotate_positiveCorner hPW) hCD hCR
      (D.corner_translation_of_rotation W hPD hPW hrot) hEnds heR with h | h
    · exact Or.inr ((D.translation_rotate_iff_rotation W).mp h)
    · exact Or.inl ((D.rotation_rotate_iff_translation W).mp h)

theorem singleton_cut_negative_count {m : ℕ} (C : BetaDiagram (m+2))
    (hcut : C.row 1<C.col 0) :
    negativeCount C=(m+1)+negativeCount C.tail := by
  have hrow0 (j : Fin (m+2)) : ¬ C.row 0<C.col j := by
    have hc:=C.col_strictAnti.antitone (Fin.zero_le j)
    have hr:=C.row_nonempty 0
    omega
  have hcol0 (i : Fin (m+1)) : C.row i.succ<C.col 0 := by
    have hidx : (1 : Fin (m+2)) ≤ i.succ := by
      change 1 % (m+2) ≤ i.val+1
      rw [Nat.mod_eq_of_lt (by omega : 1 < m + 2)]
      omega
    have hr:=C.row_strictAnti.antitone hidx
    omega
  calc
    negativeCount C =
        (∑ j : Fin (m+2),if C.row 0<C.col j then (1 : ℕ) else 0) +
        ∑ i : Fin (m+1),∑ j : Fin (m+2),if C.row i.succ<C.col j then 1 else 0 := by
      rw [C.negativeCount_eq_cell_sum,Fin.sum_univ_succ]
    _ = ∑ i : Fin (m+1),(1+∑ j : Fin (m+1),if C.row i.succ<C.col j.succ then 1 else 0) := by
      simp only [hrow0,ite_false,Finset.sum_const_zero,zero_add]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.sum_univ_succ]
      simp only [hcol0,ite_true]
    _ = (m+1)+negativeCount C.tail := by
      rw [Finset.sum_add_distrib,C.tail.negativeCount_eq_cell_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
      rfl

theorem five_six_first_cut_rigid (D : BetaDiagram 6) (hD : D.Connected) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hν : negativeCount D=5) (hcut : D.row 2<D.col 0) : D.RotationRigid := by
  let Q:=(D.cornerDiagram hP).tail
  have hcount : negativeCount Q=1 := by
    have hh:=singleton_cut_negative_count (m:=3) (D.cornerDiagram hP) hcut
    rw [D.corner_negativeCount hP,hν] at hh
    dsimp only [Q]
    omega
  have hQ : Q.Connected := BetaDiagram.connected_of_negativeCount_small Q (by omega) (by omega)
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  have hRQ:=Q.one_negative_rigidity hQ (by omega)
  have hLead : ¬Q.Symmetric → Q.EndpointLeader := by
    intro hS
    exact Q.endpointLeader_one_negative_four hQ hQZ hcount hS
  obtain ⟨s,u,v,g,hs,hu,hv,hg,hT⟩:=D.singleton_parent_of_first_cut hP hcut
  apply D.rotationRigid_of_translation _ hT
  exact Q.singletonContext_rotationRigid hQ hQZ hRQ hLead s u v g hs hu hv hg

theorem five_seven_first_cut_rigid (D : BetaDiagram 7) (hD : D.Connected) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hν : negativeCount D=5) (hcut : D.row 2<D.col 0) : D.RotationRigid := by
  let Q:=(D.cornerDiagram hP).tail
  have hcount : negativeCount Q=0 := by
    have hh:=singleton_cut_negative_count (m:=4) (D.cornerDiagram hP) hcut
    rw [D.corner_negativeCount hP,hν] at hh
    dsimp only [Q]
    omega
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  have hDense : Q.Dense := by
    intro i j
    have hzero : negativeSites Q=∅ := Finset.card_eq_zero.mp hcount
    have hne:=hQZ i j
    by_contra hh
    have hneg : Q.row i<Q.col j := by omega
    have hm : (i,j)∈negativeSites Q := by simp [negativeSites,hneg]
    simpa [hzero] using hm
  obtain ⟨s,u,v,g,hs,hu,hv,hg,hT⟩:=D.singleton_parent_of_first_cut hP hcut
  apply D.rotationRigid_of_translation _ hT
  exact Q.singletonContext_rotationRigid_of_dense hDense s u v g hs hu hv hg

/-- The actual disconnected cofactor has a singleton at one of its two ends. -/
theorem five_disconnected_singleton_side {n : ℕ} (D : BetaDiagram (n+3))
    (hn : 6≤n+3) (hP : D.PositiveCorner) (hν : negativeCount D=5)
    (hdis : ¬(D.cornerDiagram hP).Connected) :
    D.row 2<D.col 0 ∨ D.rotate.row 2<D.rotate.col 0 := by
  let K:=D.cornerDiagram hP
  let C:=K.componentDecomposition
  have hcount : negativeCount K=5 := by rw [D.corner_negativeCount hP]; exact hν
  have hinv:=five_component_inventory C (by omega) hdis hcount
  have hlen : C.components.length=2 := by
    rcases hinv with ⟨_,h,_⟩ | ⟨_,h,_⟩ <;> rcases h with h | h
    all_goals
      have hh:=congrArg List.length h
      simpa only [List.length_map,List.length_cons,List.length_nil] using hh
  obtain ⟨a,b,ha,hb,horder,hcut,hLC,hRC,hlist⟩:=K.component_list_two_cut C hlen
  have horders : C.components.map Sigma.fst=[a,b] := by rw [hlist]; rfl
  have hab : a=1 ∨ b=1 := by
    rcases hinv with ⟨_,h,_⟩ | ⟨_,h,_⟩ <;> rcases h with h | h <;>
      rw [horders] at h <;> simp only [List.cons.injEq] at h <;> omega
  rcases hab with rfl | rfl
  · have hr : Fin.cast horder (⟨1,by omega⟩ : Fin (1+b))=(1 : Fin (n+2)) := by
      apply Fin.ext
      rfl
    have hc : Fin.cast horder (⟨0,by omega⟩ : Fin (1+b))=(0 : Fin (n+2)) := by
      apply Fin.ext
      rfl
    change K.row (Fin.cast horder ⟨1,by omega⟩)<K.col (Fin.cast horder ⟨0,by omega⟩) at hcut
    rw [hr,hc] at hcut
    exact Or.inl hcut
  · have ha' : a=n+1 := by omega
    subst a
    have heOrder : horder=rfl := Subsingleton.elim _ _
    rw [heOrder] at hcut
    change K.row (Fin.last (n+1))<K.col (⟨n,by omega⟩ : Fin (n+2)) at hcut
    change D.row (Fin.last (n+1)).succ<D.col (⟨n,by omega⟩ : Fin (n+2)).castSucc at hcut
    have htwo : (2 : Fin (n+3)).val=2 := by
      change 2 % (n+3)=2
      exact Nat.mod_eq_of_lt (by omega)
    have hrev : ((2 : Fin (n+3)).rev)=(⟨n,by omega⟩ : Fin (n+2)).castSucc := by
      apply Fin.ext
      simp only [Fin.val_rev,Fin.val_castSucc,htwo]
      omega
    apply Or.inr
    change -D.col (2 : Fin (n+3)).rev< -D.row (0 : Fin (n+3)).rev
    rw [hrev,Fin.rev_zero]
    rw [Fin.succ_last] at hcut
    change D.row (Fin.last (n+2)) <
      D.col (⟨n,by omega⟩ : Fin (n+2)).castSucc at hcut
    omega

theorem five_disconnected_cofactor_rigid {n : ℕ} (D : BetaDiagram (n+3))
    (hn : 6≤n+3) (hD : D.Connected) (hZ : D.ZeroFree) (hP : D.PositiveCorner)
    (hν : negativeCount D=5) (hdis : ¬(D.cornerDiagram hP).Connected) : D.RotationRigid := by
  let C:=(D.cornerDiagram hP).componentDecomposition
  have hcount : negativeCount (D.cornerDiagram hP)=5 := by
    rw [D.corner_negativeCount hP]
    exact hν
  have hinv:=five_component_inventory C (by omega) hdis hcount
  have hn34 : n=3 ∨ n=4 := by
    rcases hinv with ⟨h,_,_⟩ | ⟨h,_,_⟩ <;> omega
  have hDr:=D.rotate_connected hD
  have hZr : D.rotate.ZeroFree := by
    intro i j hh
    apply hZ j.rev i.rev
    change -D.col i.rev = -D.row j.rev at hh
    omega
  have hνr : negativeCount D.rotate=5 := by
    rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
    exact hν
  have hPr:=D.rotate.positiveCorner_of_connected_zeroFree hDr hZr
  have hside:=five_disconnected_singleton_side D hn hP hν hdis
  rcases hn34 with rfl | rfl
  · rcases hside with h | h
    · exact five_six_first_cut_rigid D hD hZ hP hν h
    · apply D.rotationRigid_of_rotate
      exact five_six_first_cut_rigid D.rotate hDr hZr hPr hνr h
  · rcases hside with h | h
    · exact five_seven_first_cut_rigid D hD hZ hP hν h
    · apply D.rotationRigid_of_rotate
      exact five_seven_first_cut_rigid D.rotate hDr hZr hPr hνr h

/-- The full unbounded higher-row induction, before faithful Gamma descent. -/
theorem five_higher_zeroFree_rigidity {n : ℕ} (D : BetaDiagram n) (hn : 6≤n)
    (hD : D.Connected) (hZ : D.ZeroFree) (hν : negativeCount D=5) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      let hP:=D.positiveCorner_of_connected_zeroFree hD hZ
      let C:=D.cornerDiagram hP
      have hcount : negativeCount C=5 := by
        rw [D.corner_negativeCount hP]
        exact hν
      by_cases hC : C.Connected
      · by_cases h6 : k+3=6
        · have hk : k=3 := by omega
          subst k
          exact five_six_connected_cofactor_rigid D hD hP hC hν
        · have hsmall : k+2<k+3 := by omega
          have hnC : 6≤k+2 := by omega
          have hCZ : C.ZeroFree:=D.corner_zeroFree hZ hP
          apply D.connected_border_rigidity hD hP hC
          · exact ih (k+2) hsmall C hnC hC hCZ hcount
          · intro t ht
            apply ih (k+2) hsmall (C.extendTop t ht) hnC
              (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
            rw [BetaDiagram.extendTop_negativeCount]
            exact hcount
      · exact five_disconnected_cofactor_rigid D hn hD hZ hP hν hC

/-- `thm:classification`'s five-negative higher-row clause, including every common-beta source. -/
theorem five_higher_rigidity {n : ℕ} (D : BetaDiagram n) (hn : 6≤n)
    (hD : D.Connected) (hν : negativeCount D=5) : D.RotationRigid := by
  cases n with
  | zero => omega
  | succ n =>
      have hΓ : D.gamma.RotationRigid :=
        five_higher_zeroFree_rigidity D.gamma hn
          ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
          (by simpa only [BetaDiagram.gamma_negativeCount] using hν)
      apply D.gamma_zeroFree_rigidity_descends hD
      intro W hW _ he
      exact (D.gamma.rotationRigid_iff_same_order).mp hΓ W hW he

theorem five_higher_full_class {n m : ℕ} (D : BetaDiagram n) (hn : 6≤n)
    (hD : D.Connected) (hν : negativeCount D=5) (W : BetaDiagram m)
    (he : W.schur=D.schur) : D.MotionEquivalent W :=
  (five_higher_rigidity D hn hD hν).full_mate hD W he

end FiveExceptional
end SkewJacobiNegative
