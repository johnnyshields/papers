/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.BCell
import SkewCoframeRigidity.Unshifted.Components

/-!
# Component rigidity from the same-cell splice

Formalizes `shields-2026-skew-coframe-rigidity.tex`, the last two paragraphs of the proof of
`sc:top-matching`.  Two children of the same span `L ≥ 2` with equal top quotient `k` have equal
physical functions: the products `s_E κ_F = s_F κ_E` with `s_E` prime and prime to its corner force
`s_E = u s_F` for a rational unit `u`, and `u = 1` because the signed corner has a monomial of
coefficient one.  The relation `[Hδ]_{L+1} = δ_1 k` then makes the difference of the same-cell
splice functions the multiple `-s_E δ_1` of `s_E`, with `κ δ_1` a polynomial by Cramer's rule, so
`BCell.children_eq_of_cell_relation` identifies the normalized children.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

/-! ### Translation does not change the coframe data -/

section Translation

variable {n : ℕ} {L : Type*}

theorem translate_properMatrix [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1)) (c : ℤ) :
    properMatrixOf h (D.translate c) = properMatrixOf h D := by
  ext i j
  change letterOf h (D.row i.succ + c - (D.col j.castSucc + c)) = _
  rw [add_sub_add_right_eq_sub]
  rfl

theorem translate_topVec [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1)) (c : ℤ) :
    topVecOf h (D.translate c) = topVecOf h D := by
  ext i
  change letterOf h (D.row i.succ + c - (D.col (Fin.last n) + c)) = _
  rw [add_sub_add_right_eq_sub]
  rfl

theorem translate_colPos (D : BetaDiagram (n + 1)) (c : ℤ) :
    colPos (D.translate c) = colPos D := by
  ext j
  change (D.col j.castSucc + c - (D.col (Fin.last n) + c)).toNat = _
  rw [add_sub_add_right_eq_sub]
  rfl

theorem translate_span (D : BetaDiagram (n + 1)) (c : ℤ) :
    span (D.translate c) = span D := by
  unfold span BetaDiagram.largestLabel
  change (D.row 0 + c - (D.col (Fin.last n) + c)).toNat = _
  rw [add_sub_add_right_eq_sub]

theorem translate_coframe (D : BetaDiagram (n + 1)) (c : ℤ) :
    coframe (D.translate c) = coframe D := by
  unfold coframe coframeOf coframeVecOf
  rw [translate_properMatrix, translate_topVec, translate_colPos]

theorem translate_cohCorner (D : BetaDiagram (n + 1)) (c : ℤ) :
    cohCorner (D.translate c) = cohCorner D := by
  unfold cohCorner cornerOf
  rw [translate_properMatrix]

theorem translate_topQuotient (D : BetaDiagram (n + 1)) (c : ℤ) :
    topQuotient (D.translate c) = topQuotient D := by
  unfold topQuotient topQuotientOf
  rw [translate_span]
  change PowerSeries.coeff _ (letterSeries * ((coframe (D.translate c) : CohField[X]) :
    PowerSeries CohField)) = PowerSeries.coeff _ (letterSeries * ((coframe D : CohField[X]) :
    PowerSeries CohField))
  rw [translate_coframe]

end Translation

/-! ### The physical retraction of the coherent ring -/

section Retraction

open MvPolynomial

/-- Setting `ϑ = 1` and reading the remaining letters as complete symmetric generators. -/
noncomputable def physRet : CohRing →ₐ[ℚ] CompleteRing :=
  aeval fun k => if h : k = 0 then 1 else X ⟨k, Nat.pos_of_ne_zero h⟩

theorem physRet_physInclude (p : CompleteRing) : physRet (physInclude p) = p := by
  have h : physRet.comp physInclude = AlgHom.id ℚ CompleteRing := by
    apply MvPolynomial.algHom_ext
    intro j
    have hj : (j : ℕ) ≠ 0 := j.ne_zero
    simp [physRet, physInclude, hj]
    rfl
  exact congrArg (fun f => f p) h

theorem physRet_physSpec (p : CohRing) : physRet (physSpec p) = physRet p := by
  have h : physRet.comp physSpec = physRet := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [physRet, physSpec]
    · simp [physRet, physSpec, hk]
  exact congrArg (fun f => f p) h

theorem physRet_cohSchur {n : ℕ} (D : BetaDiagram n) : physRet (cohSchur D) = D.schur := by
  rw [← physRet_physSpec, cohSchur, physSpec_schurOf, physRet_physInclude]

theorem physRet_cohCorner {n : ℕ} (D : BetaDiagram (n + 1)) :
    physRet (cohCorner D) = D.cornerCoefficient := by
  unfold cohCorner cornerOf BetaDiagram.cornerCoefficient
  rw [map_mul, map_pow, map_neg, map_one, ← physRet_physSpec, physSpec_properDet,
    physRet_physInclude]

end Retraction

/-! ### The corner clears the denominators of the coframe -/

section Cramer

variable {n : ℕ}

theorem corner_mul_coframeVec_mem (D : BetaDiagram (n + 1)) (hD : D.Connected) (j : Fin n) :
    algebraMap CohRing CohField (cohCorner D) * coframeVec D j ∈
      (algebraMap CohRing CohField).range := by
  set A := algebraMap CohRing CohField
  set T := properMatrixOf cohLetters D with hTdef
  have hT : T.det ≠ 0 := properDet_cohLetters_ne_zero hD
  have hκ : A (cohCorner D) = (-1) ^ n * T.det := by
    rw [algebraMap_cohCorner]; rfl
  have hcr : T.det • (T⁻¹ *ᵥ topVecOf cohLetters D) = T.adjugate *ᵥ topVecOf cohLetters D := by
    rw [Matrix.det_smul_inv_mulVec_eq_cramer T _ (isUnit_iff_ne_zero.mpr hT),
      Matrix.cramer_eq_adjugate_mulVec]
  have hentry : (T.adjugate *ᵥ topVecOf cohLetters D) j ∈ A.range := by
    have hadj : T.adjugate =
        A.mapMatrix (properMatrixOf (MvPolynomial.X : ℕ → CohRing) D).adjugate := by
      rw [RingHom.map_adjugate, hTdef, properMatrix_cohLetters]
    simp only [Matrix.mulVec, dotProduct]
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
    · rw [hadj]
      exact ⟨_, rfl⟩
    · refine ⟨letterOf (MvPolynomial.X : ℕ → CohRing) (D.row i.succ - D.col (Fin.last n)), ?_⟩
      exact (letterOf_map A (map_zero _) (MvPolynomial.X : ℕ → CohRing) _).symm
  have hv : coframeVec D j = -((T⁻¹ *ᵥ topVecOf cohLetters D) j) := rfl
  have key : A (cohCorner D) * coframeVec D j =
      -((-1) ^ n * (T.adjugate *ᵥ topVecOf cohLetters D) j) := by
    rw [hκ, hv, ← hcr]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]
  exact Subring.neg_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _
    (Subring.one_mem _)) _) hentry)

theorem corner_mul_coframe_coeff_mem (D : BetaDiagram (n + 1)) (hD : D.Connected) (s : ℕ) :
    algebraMap CohRing CohField (cohCorner D) * (coframe D).coeff s ∈
      (algebraMap CohRing CohField).range := by
  set A := algebraMap CohRing CohField
  have hcoef : (coframe D).coeff s = (if s = 0 then 1 else 0) +
      ∑ j : Fin n, if s = colPos D j then coframeVec D j else 0 := by
    unfold coframe coframeOf
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.finset_sum_coeff]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp [coframeVec]
  rw [hcoef, mul_add, Finset.mul_sum]
  refine Subring.add_mem _ ?_ (Subring.sum_mem _ fun j _ => ?_)
  · split_ifs
    · exact ⟨cohCorner D, by simp⟩
    · simp
  · split_ifs
    · exact corner_mul_coframeVec_mem D hD j
    · simp

end Cramer

/-! ### Equal top quotients give equal functions -/

section Functions


theorem prod_complete_eq_monomial {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∃ m, ∏ i ∈ s, complete (a i) = (MvPolynomial.monomial m 1 : CompleteRing) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨m, hm⟩ := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hai := ha i (Finset.mem_insert_self i s)
    obtain ⟨m', hm'⟩ : ∃ m', complete (a i) = (MvPolynomial.monomial m' 1 : CompleteRing) := by
      rcases hai.eq_or_lt with h | h
      · exact ⟨0, by rw [← h, complete_zero]; simp⟩
      · exact ⟨_, complete_of_pos h⟩
    exact ⟨m' + m, by rw [Finset.prod_insert hi, hm, hm', MvPolynomial.monomial_mul, one_mul]⟩

/-- Two connected diagrams whose functions cross-multiply with each other's corners have
proportional functions and corners. -/
theorem schur_proportional {n m : ℕ} (E : BetaDiagram (n + 1)) (F : BetaDiagram (m + 1))
    (hE : E.Connected) (hF : F.Connected)
    (hx : E.schur * F.cornerCoefficient = F.schur * E.cornerCoefficient) :
    n = m ∧ ∃ c : ℚ, c ≠ 0 ∧ F.schur = MvPolynomial.C c * E.schur ∧
      F.cornerCoefficient = MvPolynomial.C c * E.cornerCoefficient := by
  have hEp : Prime E.schur := (BetaDiagram.connected_irreducible E hE).prime
  have hFp : Prime F.schur := (BetaDiagram.connected_irreducible F hF).prime
  obtain ⟨a, ha⟩ := (hEp.dvd_or_dvd (show E.schur ∣ F.schur * E.cornerCoefficient from
    ⟨_, hx.symm⟩)).resolve_right (BCell.not_schur_dvd_corner E hE)
  obtain ⟨b, hb⟩ := (hFp.dvd_or_dvd (show F.schur ∣ E.schur * F.cornerCoefficient from
    ⟨_, hx⟩)).resolve_right (BCell.not_schur_dvd_corner F hF)
  have hE0 : E.schur ≠ 0 := hEp.ne_zero
  have hF0 : F.schur ≠ 0 := hFp.ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; rw [mul_zero] at ha; exact hF0 ha
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hb; exact hE0 hb
  have h1 := congrArg MvPolynomial.totalDegree ha
  have h2 := congrArg MvPolynomial.totalDegree hb
  rw [MvPolynomial.totalDegree_mul_of_isDomain hE0 ha0, BetaDiagram.rowDegree,
    BetaDiagram.rowDegree] at h1
  rw [MvPolynomial.totalDegree_mul_of_isDomain hF0 hb0, BetaDiagram.rowDegree,
    BetaDiagram.rowDegree] at h2
  have hnm : n = m := by omega
  have hda : a.totalDegree = 0 := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℚ, a = MvPolynomial.C c :=
    ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hda⟩
  subst hc
  refine ⟨hnm, c, ?_, by rw [ha, mul_comm], ?_⟩
  · intro h0
    rw [h0] at ha0
    simp at ha0
  · have : E.schur * F.cornerCoefficient =
        E.schur * (MvPolynomial.C c * E.cornerCoefficient) := by
      rw [hx, ha]
      ring
    exact mul_left_cancel₀ hE0 this
    
theorem schur_eq_of_proportional {n : ℕ} (E F : BetaDiagram (n + 1)) (hE : E.Connected)
    (hF : F.Connected) (c : ℚ) (hc : c ≠ 0)
    (hcor : F.cornerCoefficient = MvPolynomial.C c * E.cornerCoefficient)
    (hs : F.schur = MvPolynomial.C c * E.schur) : E.schur = F.schur := by
  have hP : F.cornerPolynomial = MvPolynomial.C c * E.cornerPolynomial := by
    unfold BetaDiagram.cornerCoefficient at hcor
    have h0 : ((-1 : CompleteRing) ^ n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    apply mul_left_cancel₀ h0
    rw [hcor]
    ring
  have hC0 : (MvPolynomial.C c : CompleteRing) ≠ 0 := by simpa using hc
  have h2 := F.corner_square_initialForm hF
  rw [hP, Base.initialForm_mul hC0 (E.cornerPolynomial_ne_zero hE),
    Base.initialForm_eq_of_homogeneous hC0 (MvPolynomial.isWeightedHomogeneous_C _ c),
    E.corner_square_initialForm hE] at h2
  obtain ⟨mE, hmE⟩ := prod_complete_eq_monomial (Finset.univ : Finset (Fin n))
    (fun i => E.row i.succ - E.col i.castSucc) fun i _ => by
      have := E.corner_diagonal_nonnegative hE i
      omega
  obtain ⟨mF, hmF⟩ := prod_complete_eq_monomial (Finset.univ : Finset (Fin n))
    (fun i => F.row i.succ - F.col i.castSucc) fun i _ => by
      have := F.corner_diagonal_nonnegative hF i
      omega
  rw [hmE, hmF, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_eq_monomial_iff] at h2
  rcases h2 with ⟨-, h2⟩ | ⟨h2, -⟩
  · have hc1 : c = 1 := by simpa using h2
    rw [hs, hc1]
    simp
  · exact absurd (by simpa using h2) hc

end Functions

/-! ### The same-cell splice and the conclusion -/

section Core

open FixedCap

theorem cellCap_leftCoframe : FixedCap.leftCoframe cellCap = 1 := by
  unfold FixedCap.leftCoframe FixedCap.leftCoframeOf capPoly
  simp

theorem cellCap_span : span cellCap = 1 := by
  simp [span, BetaDiagram.largestLabel, cellCap]

theorem cellCap_corner : cornerOf cohLetters cellCap = 1 := by
  simp [cornerOf]

/-- The function of the same-cell splice of a connected normalized diagram. -/
theorem splice_cell_schur {b : ℕ} (D : BetaDiagram (b + 1)) (hDn : IsNorm D)
    (hDc : D.Connected) :
    algebraMap CohRing CohField (cohSchur (splice cellCap D cellCap_isNorm hDn)) =
      algebraMap CohRing CohField (cohCorner D) *
        PowerSeries.coeff (span D + 1) (letterSeries * ((coframe D : CohField[X]) :
          PowerSeries CohField)) := by
  rw [algebraMap_cohSchur, splice_schur_cohLetters cellCap cellCap_isNorm cellCap_connected D
    hDn hDc, cellCap_corner, cellCap_leftCoframe, cellCap_span, one_mul, one_mul,
    cornerOf_cohLetters]

/-- Component rigidity for normalized children, given the descent for the one-cell cap. -/
theorem component_rigidity_norm {b : ℕ} (hcap : CapVanishing cellCap)
    (E F : BetaDiagram (b + 1)) (hEn : IsNorm E) (hFn : IsNorm F) (hE : E.Connected)
    (hF : F.Connected) (hs : E.schur = F.schur)
    (hV : PowerSeries.coeff (span E + 1)
        (letterSeries * ((coframe F - coframe E : CohField[X]) : PowerSeries CohField)) =
      (coframe F - coframe E).coeff 1 * topQuotient E) :
    E = F := by
  obtain ⟨-, hCor, hspan, -, -, -⟩ := coequal_data hE hs
  obtain ⟨rE, hrE⟩ := corner_mul_coframe_coeff_mem E hE 1
  obtain ⟨rF, hrF⟩ := corner_mul_coframe_coeff_mem F hF 1
  rw [← hCor] at hrF
  have hcoh : cohCorner E * (cohSchur (splice cellCap E cellCap_isNorm hEn) -
      cohSchur (splice cellCap F cellCap_isNorm hFn)) = cohSchur E * (rE - rF) := by
    apply IsFractionRing.injective CohRing CohField
    simp only [map_mul, map_sub]
    rw [splice_cell_schur E hEn hE, splice_cell_schur F hFn hF, hrE, hrF,
      schur_eq_corner_mul_topQuotient hE, ← hCor, ← hspan]
    rw [Polynomial.coe_sub, mul_sub, map_sub, Polynomial.coeff_sub] at hV
    linear_combination (algebraMap CohRing CohField (cohCorner E)) ^ 2 * (-hV)
  have hrel : ∃ r : CompleteRing, E.cornerCoefficient *
      ((splice cellCap E cellCap_isNorm hEn).schur - (splice cellCap F cellCap_isNorm hFn).schur) =
        E.schur * r := by
    refine ⟨physRet (rE - rF), ?_⟩
    have := congrArg physRet hcoh
    simpa only [map_mul, map_sub, physRet_cohCorner, physRet_cohSchur] using this
  exact BCell.children_eq_of_cell_relation hcap E F hEn hFn hE hF hs hrel

end Core

/-- **Component rigidity** (`sc:top-matching`), given the descent for the one-cell cap.  The
children of two highest strict components of the same span `L ≥ 2`, with equal top quotient and
`[Hδ]_{L+1} = δ_1 k`, have equal complete coframes. -/
theorem component_rigidity_of_cap (hcap : FixedCap.CapVanishing cellCap) {n' m' : ℕ}
    (E : BetaDiagram (n' + 1)) (F : BetaDiagram (m' + 1))
    (hE : E.Connected) (hF : F.Connected) (hs : span E = span F) (_hL : 2 ≤ span E)
    (hq : topQuotient E = topQuotient F)
    (hV : PowerSeries.coeff (span E + 1)
        (letterSeries * ((coframe F - coframe E : CohField[X]) : PowerSeries CohField)) =
      (coframe F - coframe E).coeff 1 * topQuotient E) :
    coframe E = coframe F := by
  have hx : E.schur * F.cornerCoefficient = F.schur * E.cornerCoefficient := by
    have a := schur_eq_corner_mul_topQuotient hE
    have b := schur_eq_corner_mul_topQuotient hF
    have h : cohSchur E * cohCorner F = cohSchur F * cohCorner E := by
      apply IsFractionRing.injective CohRing CohField
      simp only [map_mul]
      rw [a, b, hq]
      ring
    have := congrArg physRet h
    simpa only [map_mul, physRet_cohCorner, physRet_cohSchur] using this
  obtain ⟨rfl, c, hc, hsc, hcc⟩ := schur_proportional E F hE hF hx
  have hsEF : E.schur = F.schur := schur_eq_of_proportional E F hE hF c hc hcc hsc
  let E' := BetaDiagram.normalize E
  let F' := BetaDiagram.normalize F
  have hE' : E'.Connected := hE.translate _
  have hF' : F'.Connected := hF.translate _
  have hs' : E'.schur = F'.schur := by
    have e1 : E'.schur = E.schur := (BetaDiagram.translate_translationEquivalent E _).schur_eq
    have e2 : F'.schur = F.schur := (BetaDiagram.translate_translationEquivalent F _).schur_eq
    rw [e1, e2, hsEF]
  have hV' : PowerSeries.coeff (span E' + 1)
      (letterSeries * ((coframe F' - coframe E' : CohField[X]) : PowerSeries CohField)) =
        (coframe F' - coframe E').coeff 1 * topQuotient E' := by
    simp only [E', F', BetaDiagram.normalize, translate_span, translate_coframe,
      translate_topQuotient]
    exact hV
  have := component_rigidity_norm hcap E' F' (BetaDiagram.normalize_col_last E)
    (BetaDiagram.normalize_col_last F) hE' hF' hs' hV'
  have h2 := congrArg coframe this
  simpa only [E', F', BetaDiagram.normalize, translate_coframe] using h2

end SkewCoframeRigidity.Coframe
