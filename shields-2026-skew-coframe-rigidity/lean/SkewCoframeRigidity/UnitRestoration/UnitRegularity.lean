/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.UnitCore
import SkewCoframeRigidity.Coframe.Algebra
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Regularity of the complete coframe at `ε = 0`

Formalizes the regularity clause of `sc:unit-expansion` in
`shields-2026-skew-coframe-rigidity.tex`: with every positive raw letter scaled by `ε` and the
coherent unit retained, the complete coframe of a connected diagram with units is regular at
`ε = 0`, with leading term the coframe of its zero-free core.

Regularity is stated through the field `Frac(K[ε])`.  The proper system `T g = -v` is
rescaled on the core rows by `ε`: the rescaled matrix `T̃` and right side `ṽ` are polynomials in
`ε` whose values at `ε = 0` are the unit identity on the unit rows and the core proper matrix
on the core rows.  Cramer's rule then gives `g = N / B` with polynomials `N`, `B` and
`B(0) ≠ 0`, and `N(0) / B(0)` is the core coframe on the core columns and zero on the unit
columns.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity.Coframe Polynomial

/-- A beta diagram `C` presented as the zero-free core of `D`: its rows and columns are the
non-common rows and columns of `D`, in order. -/
structure CoreData {n m : ℕ} (D : BetaDiagram (n + 1)) (C : BetaDiagram (m + 1)) where
  re : Fin (m + 1) → Fin (n + 1)
  ce : Fin (m + 1) → Fin (n + 1)
  re_mono : StrictMono re
  ce_mono : StrictMono ce
  row_eq : ∀ k, C.row k = D.row (re k)
  col_eq : ∀ k, C.col k = D.col (ce k)
  re_range : ∀ i, i ∉ unitRows D.row D.col ↔ ∃ k, re k = i
  ce_range : ∀ j, j ∉ unitCols D.row D.col ↔ ∃ k, ce k = j

namespace CoreData

variable {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)} (P : CoreData D C)

theorem top_not_unit {n : ℕ} (D : BetaDiagram (n + 1)) : (0 : Fin (n + 1)) ∉ unitRows D.row D.col := by
  rintro ⟨j, hj⟩
  have := lt_of_row_eq_col D hj
  exact absurd this (by simp)

theorem last_not_unit {n : ℕ} (D : BetaDiagram (n + 1)) :
    Fin.last n ∉ unitCols D.row D.col := by
  rintro ⟨i, hi⟩
  have := lt_of_row_eq_col D hi
  exact absurd this (not_lt.mpr (Fin.le_last i))

theorem re_zero : P.re 0 = 0 := by
  obtain ⟨k, hk⟩ := (P.re_range 0).mp (top_not_unit D)
  exact le_antisymm (hk ▸ P.re_mono.monotone (Fin.zero_le k)) (Fin.zero_le _)

theorem ce_last : P.ce (Fin.last m) = Fin.last n := by
  obtain ⟨k, hk⟩ := (P.ce_range _).mp (last_not_unit D)
  exact le_antisymm (Fin.le_last _) (hk ▸ P.ce_mono.monotone (Fin.le_last k))

theorem re_ne_zero {k : Fin (m + 1)} (hk : k ≠ 0) : P.re k ≠ 0 := by
  rw [← P.re_zero]
  exact (P.re_mono.injective.ne hk)

theorem ce_ne_last {k : Fin (m + 1)} (hk : k ≠ Fin.last m) : P.ce k ≠ Fin.last n := by
  rw [← P.ce_last]
  exact P.ce_mono.injective.ne hk

/-- The `k`-th core column among the interior columns, as an index of `Fin n`. -/
def ι (k : Fin m) : Fin n :=
  (P.ce k.castSucc).castPred (P.ce_ne_last (Fin.castSucc_lt_last k).ne)

theorem castSucc_ι (k : Fin m) : (P.ι k).castSucc = P.ce k.castSucc := by
  simp [ι]

theorem ι_injective : Function.Injective P.ι := by
  intro k l h
  have := congrArg Fin.castSucc h
  rw [castSucc_ι, castSucc_ι] at this
  exact Fin.castSucc_injective _ (P.ce_mono.injective this)

/-- The `k`-th core row among the rows below the top one, as an index of `Fin n`. -/
def ρ (k : Fin m) : Fin n :=
  (P.re k.succ).pred (P.re_ne_zero (Fin.succ_ne_zero k))

theorem succ_ρ (k : Fin m) : (P.ρ k).succ = P.re k.succ := by
  simp [ρ]

/-- An interior row below the top one is a core row iff it is some `ρ k`. -/
theorem exists_ρ {i : Fin n} (hi : i.succ ∉ unitRows D.row D.col) : ∃ k, P.ρ k = i := by
  obtain ⟨k, hk⟩ := (P.re_range _).mp hi
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [P.re_zero] at hk
    exact (Fin.succ_ne_zero i) hk.symm
  obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr hk0
  exact ⟨k', Fin.succ_injective _ (by rw [succ_ρ, hk])⟩

/-- An interior column is not a common beta iff it is some `ι k`. -/
theorem exists_ι {j : Fin n} (hj : j.castSucc ∉ unitCols D.row D.col) : ∃ k, P.ι k = j := by
  obtain ⟨k, hk⟩ := (P.ce_range _).mp hj
  have hk0 : k ≠ Fin.last m := by
    rintro rfl
    rw [P.ce_last] at hk
    exact (Fin.castSucc_lt_last j).ne hk.symm
  obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk0
  exact ⟨k', Fin.castSucc_injective _ (by rw [castSucc_ι, hk])⟩

theorem ι_not_unit (k : Fin m) : (P.ι k).castSucc ∉ unitCols D.row D.col := by
  rw [castSucc_ι]
  exact (P.ce_range _).mpr ⟨_, rfl⟩

theorem ρ_not_unit (k : Fin m) : (P.ρ k).succ ∉ unitRows D.row D.col := by
  rw [succ_ρ]
  exact (P.re_range _).mpr ⟨_, rfl⟩

/-- The proper matrix of the core is the sub-block of the proper matrix of `D`. -/
theorem properMatrix_core {K : Type*} [Zero K] (h : ℕ → K) (k l : Fin m) :
    properMatrixOf h C k l = letterOf h (D.row (P.ρ k).succ - D.col (P.ι l).castSucc) := by
  simp only [properMatrixOf, Matrix.of_apply, P.row_eq, P.col_eq, succ_ρ, castSucc_ι]

theorem topVec_core {K : Type*} [Zero K] (h : ℕ → K) (k : Fin m) :
    topVecOf h C k = letterOf h (D.row (P.ρ k).succ - D.col (Fin.last n)) := by
  simp only [topVecOf, P.row_eq, P.col_eq, succ_ρ, ← P.ce_last]

end CoreData

/-! ### The rescaled system -/

section Rescaled

open scoped Classical Matrix

variable {K : Type*} [Field K] {n m : ℕ} (D : BetaDiagram (n + 1))

/-- The rescaling of row `i + 1`: `ε` on a core row, one on a unit row. -/
noncomputable def rowScale (i : Fin n) : K[X] :=
  if i.succ ∈ unitRows D.row D.col then 1 else X

/-- The proper matrix with the core rows divided by `ε`. -/
noncomputable def tTilde (h : ℕ → K) : Matrix (Fin n) (Fin n) K[X] :=
  Matrix.of fun i j =>
    if i.succ ∈ unitRows D.row D.col then scaledLetter h (D.row i.succ - D.col j.castSucc)
    else Polynomial.C (letterOf h (D.row i.succ - D.col j.castSucc))

/-- The top column with the core rows divided by `ε`. -/
noncomputable def vTilde (h : ℕ → K) : Fin n → K[X] := fun i =>
  if i.succ ∈ unitRows D.row D.col then scaledLetter h (D.row i.succ - D.col (Fin.last n))
  else Polynomial.C (letterOf h (D.row i.succ - D.col (Fin.last n)))

theorem rowScale_ne_zero (i : Fin n) : rowScale D i ≠ (0 : K[X]) := by
  unfold rowScale
  split_ifs
  · exact one_ne_zero
  · exact Polynomial.X_ne_zero

theorem scaledLetter_core_row (h : ℕ → K) {i : Fin n} (hi : i.succ ∉ unitRows D.row D.col)
    (j : Fin (n + 1)) : scaledLetter h (D.row i.succ - D.col j) =
      Polynomial.X * Polynomial.C (letterOf h (D.row i.succ - D.col j)) := by
  apply scaledLetter_of_ne
  intro h0
  exact hi ⟨j, by omega⟩

theorem scaledLetter_eq_rowScale_mul_tTilde (h : ℕ → K) (i j : Fin n) :
    scaledLetter h (D.row i.succ - D.col j.castSucc) = rowScale D i * tTilde D h i j := by
  unfold rowScale tTilde
  by_cases hi : i.succ ∈ unitRows D.row D.col
  · simp [hi]
  · simp only [hi, if_false, Matrix.of_apply]
    exact scaledLetter_core_row D h hi _

theorem scaledLetter_eq_rowScale_mul_vTilde (h : ℕ → K) (i : Fin n) :
    scaledLetter h (D.row i.succ - D.col (Fin.last n)) = rowScale D i * vTilde D h i := by
  unfold rowScale vTilde
  by_cases hi : i.succ ∈ unitRows D.row D.col
  · simp [hi]
  · simp only [hi, if_false]
    exact scaledLetter_core_row D h hi _

/-- The matrix `T̃` at `ε = 0`. -/
noncomputable def tZero (h : ℕ → K) : Matrix (Fin n) (Fin n) K :=
  (tTilde D h).map Polynomial.constantCoeff

/-- The column `ṽ` at `ε = 0`. -/
noncomputable def vZero (h : ℕ → K) : Fin n → K := fun i => Polynomial.constantCoeff (vTilde D h i)

theorem tZero_unit_row (h : ℕ → K) {i : Fin n} (hi : i.succ ∈ unitRows D.row D.col) (j : Fin n) :
    tZero D h i j = if D.row i.succ = D.col j.castSucc then 1 else 0 := by
  simp only [tZero, tTilde, hi, if_true, Matrix.map_apply, Matrix.of_apply,
    constantCoeff_scaledLetter]
  congr 1
  simp only [eq_iff_iff]
  omega

theorem tZero_core_row (h : ℕ → K) {i : Fin n} (hi : i.succ ∉ unitRows D.row D.col) (j : Fin n) :
    tZero D h i j = letterOf h (D.row i.succ - D.col j.castSucc) := by
  simp [tZero, tTilde, hi]

theorem vZero_unit_row (h : ℕ → K) {i : Fin n} (hi : i.succ ∈ unitRows D.row D.col) :
    vZero D h i = 0 := by
  have hne : D.row i.succ - D.col (Fin.last n) ≠ 0 := by
    intro h0
    exact CoreData.last_not_unit D ⟨i.succ, by omega⟩
  unfold vZero vTilde
  rw [if_pos hi, constantCoeff_scaledLetter, if_neg hne]

theorem vZero_core_row (h : ℕ → K) {i : Fin n} (hi : i.succ ∉ unitRows D.row D.col) :
    vZero D h i = letterOf h (D.row i.succ - D.col (Fin.last n)) := by
  simp [vZero, vTilde, hi]

end Rescaled

/-! ### The system at `ε = 0` -/

section AtZero

open scoped Classical Matrix

variable {K : Type*} [Field K] {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
  (P : CoreData D C) (h : ℕ → K)

/-- A column vector vanishing on the columns that are not interior core columns. -/
theorem sum_core_columns (f : Fin n → K) (hf : ∀ l, l ∉ Set.range P.ι → f l = 0) :
    ∑ l, f l = ∑ k, f (P.ι k) :=
  (Fintype.sum_of_injective P.ι P.ι_injective (fun k => f (P.ι k)) f
    (fun l hl => hf l hl) (fun _ => rfl)).symm

theorem not_range_ι_of_unit {l : Fin n} (hl : l.castSucc ∈ unitCols D.row D.col) :
    l ∉ Set.range P.ι := by
  rintro ⟨k, rfl⟩
  exact P.ι_not_unit k hl

include P in
/-- `T̃(0)` is injective, given the core proper matrix is. -/
theorem tZero_injective (hK : (properMatrixOf h C).det ≠ 0) (x : Fin n → K)
    (hx : tZero D h *ᵥ x = 0) : x = 0 := by
  have hunit : ∀ j : Fin n, j.castSucc ∈ unitCols D.row D.col → x j = 0 := by
    intro j hj
    obtain ⟨i', hi'⟩ := hj
    have hi0 : i' ≠ 0 := by
      rintro rfl
      exact CoreData.top_not_unit D ⟨j.castSucc, hi'⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hi0
    have hrow := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
    rw [Finset.sum_eq_single j] at hrow
    · rwa [tZero_unit_row D h ⟨j.castSucc, hi'⟩, if_pos hi', one_mul] at hrow
    · intro l _ hl
      rw [tZero_unit_row D h ⟨j.castSucc, hi'⟩, if_neg, zero_mul]
      intro hh
      apply hl
      exact Fin.castSucc_injective _ (D.col_strictAnti.injective (hi'.symm.trans hh).symm ▸ rfl)
    · simp
  have hcore : (fun k : Fin m => x (P.ι k)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hK
    ext k
    have hrow := congrFun hx (P.ρ k)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow ⊢
    rw [sum_core_columns P (fun l => tZero D h (P.ρ k) l * x l) (fun l hl => ?_)] at hrow
    · rw [← hrow]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [tZero_core_row D h (P.ρ_not_unit k), CoreData.properMatrix_core P]
    · by_cases hu : l.castSucc ∈ unitCols D.row D.col
      · rw [hunit l hu, mul_zero]
      · exact absurd (P.exists_ι hu) (fun ⟨k, hk⟩ => hl ⟨k, hk⟩)
  funext l
  by_cases hu : l.castSucc ∈ unitCols D.row D.col
  · exact hunit l hu
  · obtain ⟨k, rfl⟩ := P.exists_ι hu
    exact congrFun hcore k

end AtZero

/-! ### The leading solution -/

section Leading

open scoped Classical Matrix

variable {K : Type*} [Field K] {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
  (P : CoreData D C) (h : ℕ → K)

/-- The candidate leading coframe vector: the core coframe on the interior core columns, zero on
the unit columns. -/
noncomputable def leadingVec : Fin n → K :=
  Function.extend P.ι (coframeVecOf h C) 0

theorem leadingVec_ι (k : Fin m) : leadingVec P h (P.ι k) = coframeVecOf h C k :=
  P.ι_injective.extend_apply _ _ _

theorem leadingVec_of_not_range {l : Fin n} (hl : l ∉ Set.range P.ι) : leadingVec P h l = 0 := by
  unfold leadingVec
  rw [Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => hl ⟨k, hk⟩)]
  rfl

include P in
theorem tZero_mulVec_leadingVec (hK : (properMatrixOf h C).det ≠ 0) :
    tZero D h *ᵥ leadingVec P h = -vZero D h := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply]
  by_cases hi : i.succ ∈ unitRows D.row D.col
  · rw [vZero_unit_row D h hi, neg_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : D.row i.succ = D.col l.castSucc
    · rw [leadingVec_of_not_range P h (not_range_ι_of_unit P ⟨i.succ, hl⟩), mul_zero]
    · rw [tZero_unit_row D h hi, if_neg hl, zero_mul]
  · obtain ⟨k, rfl⟩ := P.exists_ρ hi
    rw [sum_core_columns P (fun l => tZero D h (P.ρ k) l * leadingVec P h l)
      (fun l hl => by rw [leadingVec_of_not_range P h hl, mul_zero])]
    rw [vZero_core_row D h hi, ← CoreData.topVec_core P h k]
    have hsys := congrFun (properMatrix_mulVec_coframeVecOf h C hK) k
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at hsys
    rw [← hsys]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [tZero_core_row D h hi, CoreData.properMatrix_core P, leadingVec_ι]

end Leading

/-! ### Cramer's rule over `Frac(K[ε])` -/

section Cramer

open scoped Classical Matrix

variable {K : Type*} [Field K] {n : ℕ} (D : BetaDiagram (n + 1)) (h : ℕ → K)

/-- The raw field of the scaled letters. -/
abbrev EpsField (K : Type*) [Field K] : Type _ := FractionRing K[X]

/-- The scaled letter sequence in `Frac(K[ε])`: positive letters carry `ε`, the unit is one. -/
noncomputable def scaledSeq (h : ℕ → K) : ℕ → EpsField K :=
  fun m => algebraMap K[X] (EpsField K) (scaledLetter h m)

theorem letterOf_scaledSeq (k : ℤ) :
    letterOf (scaledSeq h) k = algebraMap K[X] (EpsField K) (scaledLetter h k) := by
  unfold letterOf scaledSeq
  by_cases hk : k < 0
  · simp [hk, scaledLetter]
  · rw [if_neg hk]
    have := Int.toNat_of_nonneg (not_lt.mp hk)
    show algebraMap K[X] (EpsField K) (scaledLetter h (k.toNat : ℤ)) = _
    rw [this]

theorem properMatrix_scaledSeq :
    properMatrixOf (scaledSeq h) D =
      Matrix.diagonal (fun i => algebraMap K[X] (EpsField K) (rowScale D i)) *
        (tTilde D h).map (algebraMap K[X] (EpsField K)) := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [properMatrixOf, Matrix.of_apply, Matrix.map_apply, letterOf_scaledSeq,
    scaledLetter_eq_rowScale_mul_tTilde, map_mul]

theorem topVec_scaledSeq (i : Fin n) :
    topVecOf (scaledSeq h) D i = algebraMap K[X] (EpsField K) (rowScale D i) *
      algebraMap K[X] (EpsField K) (vTilde D h i) := by
  simp only [topVecOf, letterOf_scaledSeq, scaledLetter_eq_rowScale_mul_vTilde, map_mul]

/-- The numerator polynomials: `N = -adj(T̃) ṽ`. -/
noncomputable def numPoly : Fin n → K[X] := -((tTilde D h).adjugate *ᵥ vTilde D h)

/-- The common denominator `B = det T̃`. -/
noncomputable def denomPoly : K[X] := (tTilde D h).det

theorem coeff_zero_denomPoly : (denomPoly D h).coeff 0 = (tZero D h).det := by
  rw [← Polynomial.constantCoeff_apply]
  unfold denomPoly tZero
  rw [RingHom.map_det]
  rfl

theorem coeff_zero_numPoly (j : Fin n) :
    (numPoly D h j).coeff 0 =
      -(((tZero D h).adjugate *ᵥ vZero D h) j) := by
  rw [← Polynomial.constantCoeff_apply]
  unfold numPoly tZero vZero
  simp only [Pi.neg_apply, map_neg]
  congr 1
  have := RingHom.map_mulVec Polynomial.constantCoeff ((tTilde D h).adjugate) (vTilde D h) j
  rw [this]
  have e : (tTilde D h).adjugate.map Polynomial.constantCoeff =
      ((tTilde D h).map Polynomial.constantCoeff).adjugate :=
    RingHom.map_adjugate (Polynomial.constantCoeff (R := K)) (tTilde D h)
  rw [e]
  rfl

/-- **Cramer's rule for the scaled coframe**: `B · g_j = N_j` in `Frac(K[ε])`, as soon as `B`
does not vanish at `ε = 0`. -/
theorem denom_mul_coframeVec (hdet : (tZero D h).det ≠ 0) (j : Fin n) :
    algebraMap K[X] (EpsField K) (denomPoly D h) * coframeVecOf (scaledSeq h) D j =
      algebraMap K[X] (EpsField K) (numPoly D h j) := by
  set φ := algebraMap K[X] (EpsField K) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] (EpsField K)
  have hB : denomPoly D h ≠ 0 := by
    intro h0
    have := coeff_zero_denomPoly D h
    rw [h0, Polynomial.coeff_zero] at this
    exact hdet this.symm
  have hφB : φ (denomPoly D h) ≠ 0 := (map_ne_zero_iff φ hinj).mpr hB
  have hdetmap : ((tTilde D h).map φ).det = φ (denomPoly D h) := by
    unfold denomPoly
    rw [RingHom.map_det]
    rfl
  have hTdet : (properMatrixOf (scaledSeq h) D).det ≠ 0 := by
    rw [properMatrix_scaledSeq, Matrix.det_mul, Matrix.det_diagonal, hdetmap]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hφB
    exact (map_ne_zero_iff φ hinj).mpr (rowScale_ne_zero D i)
  have hg := properMatrix_mulVec_coframeVecOf (scaledSeq h) D hTdet
  rw [properMatrix_scaledSeq, ← Matrix.mulVec_mulVec] at hg
  have hg' : ((tTilde D h).map φ) *ᵥ coframeVecOf (scaledSeq h) D =
      -(fun i => φ (vTilde D h i)) := by
    ext i
    have hi := congrFun hg i
    simp only [Matrix.mulVec_diagonal, Pi.neg_apply, topVec_scaledSeq] at hi ⊢
    have hne : φ (rowScale D i) ≠ 0 := (map_ne_zero_iff φ hinj).mpr (rowScale_ne_zero D i)
    apply mul_left_cancel₀ hne
    rw [hi]; ring
  have hadj := congrArg (fun v => ((tTilde D h).map φ).adjugate *ᵥ v) hg'
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdetmap, Matrix.mulVec_neg] at hadj
  have hj := congrFun hadj j
  have hmap := RingHom.map_mulVec φ ((tTilde D h).adjugate) (vTilde D h) j
  have e : (tTilde D h).adjugate.map φ = ((tTilde D h).map φ).adjugate :=
    RingHom.map_adjugate φ (tTilde D h)
  rw [e] at hmap
  simp only [numPoly, Pi.neg_apply, map_neg]
  rw [hmap]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hj
  simpa [Function.comp_def] using hj

end Cramer

/-! ### The regularity theorem -/

section Regular

open scoped Classical Matrix

variable {K : Type*} [Field K] {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
  (P : CoreData D C) (h : ℕ → K)

include P in
theorem tZero_det_ne_zero (hK : (properMatrixOf h C).det ≠ 0) : (tZero D h).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  exact hx (tZero_injective P h hK x hx0)

include P in
theorem coeff_zero_numPoly_eq (hK : (properMatrixOf h C).det ≠ 0) (j : Fin n) :
    (numPoly D h j).coeff 0 = (denomPoly D h).coeff 0 * leadingVec P h j := by
  rw [coeff_zero_numPoly, coeff_zero_denomPoly]
  have hw := tZero_mulVec_leadingVec P h hK
  have := congrArg (fun v => (tZero D h).adjugate *ᵥ v) hw
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_neg] at this
  have hj := congrFun this j
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hj
  simpa using hj.symm

theorem colPos_core (k : Fin m) : colPos C k = colPos D (P.ι k) := by
  unfold colPos
  rw [P.col_eq, P.col_eq, CoreData.castSucc_ι, CoreData.ce_last]

include P in
/-- **Regularity at `ε = 0`** (`sc:unit-expansion`): the coefficients of the complete coframe of
the `ε`-scaled letters (positive letters times `ε`, the coherent unit kept) are quotients
`N_s / B` of polynomials in `ε` with a common denominator `B` that does not vanish at `ε = 0`,
and `N_s(0) / B(0)` is the corresponding coefficient of the coframe of the zero-free core.
Positions are measured from the last column beta, which is a core column. -/
theorem coframe_regular_at_zero (hK : (properMatrixOf h C).det ≠ 0) :
    ∃ (B : K[X]) (N : ℕ → K[X]), B.coeff 0 ≠ 0 ∧ ∀ s,
      (coframeOf (scaledSeq h) D).coeff s * algebraMap K[X] (EpsField K) B =
          algebraMap K[X] (EpsField K) (N s) ∧
        (N s).coeff 0 = B.coeff 0 * (coframeOf h C).coeff s := by
  have hdet := tZero_det_ne_zero P h hK
  refine ⟨denomPoly D h, fun s => (if s = 0 then denomPoly D h else 0) +
    ∑ j, if colPos D j = s then numPoly D h j else 0, ?_, fun s => ⟨?_, ?_⟩⟩
  · rw [coeff_zero_denomPoly]; exact hdet
  · rw [coframeOf_eq_uniPoly, uniPoly_coeff]
    simp only [map_add, map_sum, add_mul, Finset.sum_mul]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [mul_comm, denom_mul_coframeVec D h hdet]
      · simp
  · rw [Polynomial.coeff_add, finset_sum_coeff]
    have hs : ∀ j, ((if colPos D j = s then numPoly D h j else 0).coeff 0 : K) =
        if colPos D j = s then (denomPoly D h).coeff 0 * leadingVec P h j else 0 := by
      intro j
      split_ifs
      · exact coeff_zero_numPoly_eq P h hK j
      · simp
    simp only [hs]
    rw [sum_core_columns P _ (fun l hl => by simp [leadingVec_of_not_range P h hl])]
    rw [coframeOf_eq_uniPoly, uniPoly_coeff, mul_add, Finset.mul_sum]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← colPos_core P k, leadingVec_ι]
      split_ifs <;> simp

end Regular

/-! ### The core of a diagram as a presented core -/

section Present

open scoped Classical

variable {n m : ℕ} (D : BetaDiagram (n + 1)) (hm : coreCount D = m + 1)

/-- The zero-free core of `D`, indexed by `Fin (m + 1)` once its size is known to be `m + 1`. -/
noncomputable def coreOfEq : BetaDiagram (m + 1) where
  row k := D.row (coreRowEmb D (Fin.cast hm.symm k))
  col k := D.col (coreColEmb D (Fin.cast hm.symm k))
  row_strictAnti :=
    (coreDiagram D).row_strictAnti.comp_strictMono (Fin.castOrderIso hm.symm).strictMono
  col_strictAnti :=
    (coreDiagram D).col_strictAnti.comp_strictMono (Fin.castOrderIso hm.symm).strictMono
  row_nonempty k := (coreDiagram D).row_nonempty (Fin.cast hm.symm k)

/-- The core presented by its embeddings into `D`. -/
noncomputable def coreDataOfEq : CoreData D (coreOfEq D hm) where
  re k := coreRowEmb D (Fin.cast hm.symm k)
  ce k := coreColEmb D (Fin.cast hm.symm k)
  re_mono := (coreRowEmb D).strictMono.comp (Fin.castOrderIso hm.symm).strictMono
  ce_mono := (coreColEmb D).strictMono.comp (Fin.castOrderIso hm.symm).strictMono
  row_eq _ := rfl
  col_eq _ := rfl
  re_range i := by
    constructor
    · intro hi
      obtain ⟨k, hk⟩ := exists_coreRowEmb D hi
      exact ⟨Fin.cast hm k, by simpa using hk⟩
    · rintro ⟨k, rfl⟩
      exact coreRowEmb_mem D _
  ce_range j := by
    constructor
    · intro hj
      obtain ⟨k, hk⟩ := exists_coreColEmb D hj
      exact ⟨Fin.cast hm k, by simpa using hk⟩
    · rintro ⟨k, rfl⟩
      exact coreColEmb_mem D _

/-- The reindexed core has the same skew Schur function as the core. -/
theorem schur_coreOfEq : (coreOfEq D hm).schur = (coreDiagram D).schur := by
  unfold BetaDiagram.schur
  rw [← Matrix.det_submatrix_equiv_self (Fin.castOrderIso hm.symm).toEquiv
    (coreDiagram D).matrix]
  congr 1

end Present

end SkewCoframeRigidity.UnitRestoration
