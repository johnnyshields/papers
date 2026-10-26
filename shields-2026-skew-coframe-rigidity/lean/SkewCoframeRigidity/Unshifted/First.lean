/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.CoequalData
import SkewCoframeRigidity.Unshifted.YExpansion
import SkewCoframeRigidity.Unshifted.UpstreamInputs
import SkewCoframeRigidity.Unshifted.Components
import SkewCoframeRigidity.Stationary.BCell

/-!
# The first coefficient of the defect

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`), the display `ph:first-D`.  At the generic top letter the defect of a
board and its rotation has coefficient
`[z^{M+1}] D = -(J₂ - (G₁ - C₁) s_V) / κ` at degree `M + 1`, where `J₂` is the difference of the two
cell splices; it does not involve `H_M`, so it equals `-J₂|_{e=0}/κ`.  If it vanished, then
`κ J₂` would be a multiple of the connected function `s_V`, and the degree and weight argument
of `BCell` gives equal cell splices, hence `V = V*` by fixed-cap rigidity for the cell.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial
open scoped Matrix

section Clipped

variable {R : Type*} [CommRing R]

/-- The coefficient of the clipped operator one past its cutoff, for two polynomials with
constant term one whose products with `H` agree at the cutoff. -/
theorem clippedOp_coeff_succ (M : ℕ) (G C : R[X]) (H : PowerSeries R) (hG : G.coeff 0 = 1)
    (hC : C.coeff 0 = 1)
    (htop : PowerSeries.coeff M (H * (G : PowerSeries R)) =
      PowerSeries.coeff M (H * (C : PowerSeries R))) :
    (clippedOp M G C H).coeff (M + 1) =
      (PowerSeries.coeff (M + 1) (H * (G : PowerSeries R)) -
        PowerSeries.coeff (M + 1) (H * (C : PowerSeries R))) +
      (C.coeff 1 - G.coeff 1) * PowerSeries.coeff M (H * (G : PowerSeries R)) := by
  set a1 : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + M) (H * G) with ha1
  set b1 : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + M) (H * C) with hb1
  have ha := PowerSeries.eq_shift_mul_X_pow_add_trunc M (H * (G : PowerSeries R))
  have hb := PowerSeries.eq_shift_mul_X_pow_add_trunc M (H * (C : PowerSeries R))
  have key : ((clippedOp M G C H : R[X]) : PowerSeries R) =
      PowerSeries.X ^ M * ((C : PowerSeries R) * a1 - (G : PowerSeries R) * b1) := by
    unfold clippedOp
    rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul]
    have e1 : ((PowerSeries.trunc M (H * (C : PowerSeries R)) : R[X]) : PowerSeries R) =
        H * (C : PowerSeries R) - b1 * PowerSeries.X ^ M := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]; exact hb.symm
    have e2 : ((PowerSeries.trunc M (H * (G : PowerSeries R)) : R[X]) : PowerSeries R) =
        H * (G : PowerSeries R) - a1 * PowerSeries.X ^ M := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]; exact ha.symm
    rw [e1, e2]
    ring
  have h1 : ∀ A B : PowerSeries R, PowerSeries.coeff 1 (A * B) =
      PowerSeries.constantCoeff A * PowerSeries.coeff 1 B +
        PowerSeries.coeff 1 A * PowerSeries.constantCoeff B := by
    intro A B
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  rw [← Polynomial.coeff_coe, key, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
    show M + 1 - M = 1 by omega, map_sub, h1, h1]
  simp only [Polynomial.constantCoeff_coe, Polynomial.coeff_coe, hG, hC, one_mul, ha1, hb1,
    PowerSeries.coeff_mk]
  have h0 : ∀ f : ℕ → R, PowerSeries.constantCoeff (PowerSeries.mk f) = f 0 := fun f => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  rw [h0, h0, zero_add, ← htop, add_comm 1 M]
  ring

end Clipped

section Polynomial

variable {n : ℕ}

/-- The signed corner times a native coefficient of the complete coframe is the image of a
polynomial: `κ G_j = ∓ (adj T · (H_i))_j`. -/
theorem corner_mul_coframeVec_mem (D : BetaDiagram (n + 1)) (hD : D.Connected) (j : Fin n) :
    ∃ r : CohRing, algebraMap CohRing CohField r =
      cornerOf cohLetters D * coframeVecOf cohLetters D j := by
  set T : Matrix (Fin n) (Fin n) CohRing := properMatrixOf (MvPolynomial.X : ℕ → CohRing) D
  set t : Fin n → CohRing := topVecOf (MvPolynomial.X : ℕ → CohRing) D
  set f : CohRing →+* CohField := algebraMap CohRing CohField
  have hT : properMatrixOf cohLetters D = f.mapMatrix T := properMatrix_cohLetters D
  have ht : topVecOf cohLetters D = f ∘ t := by
    ext i
    exact letterOf_map f (map_zero f) (MvPolynomial.X : ℕ → CohRing) _
  have hdet : f T.det ≠ 0 := by
    have := properDet_cohLetters_ne_zero hD
    rwa [hT, ← RingHom.map_det] at this
  refine ⟨-((-1) ^ n * (T.adjugate *ᵥ t) j), ?_⟩
  have hk : cornerOf cohLetters D = (-1) ^ n * f T.det := by
    rw [← algebraMap_cohCorner]
    simp [cohCorner, cornerOf, T, f]
  unfold coframeVecOf
  rw [hT, ht, hk, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, ← RingHom.map_det,
    ← RingHom.map_adjugate]
  have e := RingHom.map_mulVec f T.adjugate t j
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_mul, map_pow, map_one]
  rw [RingHom.mapMatrix_apply, ← e]
  field_simp

/-- For `s > 0`, `κ [z^s] G` is the image of a polynomial. -/
theorem corner_mul_coframe_coeff_mem (D : BetaDiagram (n + 1)) (hD : D.Connected) {s : ℕ}
    (hs : 0 < s) : ∃ r : CohRing, algebraMap CohRing CohField r =
      cornerOf cohLetters D * (coframe D).coeff s := by
  choose r hr using corner_mul_coframeVec_mem D hD
  refine ⟨∑ j, if colPos D j = s then r j else 0, ?_⟩
  change _ = cornerOf cohLetters D * (uniPoly (coframeVecOf cohLetters D) (colPos D)).coeff s
  rw [uniPoly_coeff, ite_eq_right hs.ne', zero_add, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact hr j
  · simp

end Polynomial

section Physical

open MvPolynomial

/-- The physical normalization as a map back into the physical ring: `ϑ ↦ 1`. -/
noncomputable def physBack : CohRing →ₐ[ℚ] SkewCofactorIndependence.CompleteRing :=
  aeval fun k => if h : k = 0 then 1 else X ⟨k, Nat.pos_of_ne_zero h⟩

theorem physInclude_physBack (r : CohRing) : physInclude (physBack r) = physSpec r := by
  have : (physInclude : SkewCofactorIndependence.CompleteRing →ₐ[ℚ] CohRing).comp physBack =
      physSpec := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hk : k = 0
    · simp [physBack, physSpec, hk]
    · simp only [AlgHom.comp_apply, physBack, physSpec, MvPolynomial.aeval_X, hk, dite_false,
        ite_false]
      exact rename_X _ _
  exact congrArg (fun F => F r) this

theorem physSpec_cohSchur {m : ℕ} (D : BetaDiagram m) :
    physSpec (cohSchur D) = physInclude D.schur := physSpec_schurOf D

theorem physSpec_cohCorner {n : ℕ} (D : BetaDiagram (n + 1)) :
    physSpec (cohCorner D) = physInclude D.cornerCoefficient := by
  unfold cohCorner cornerOf BetaDiagram.cornerCoefficient
  rw [map_mul, physSpec_properDet D, map_mul]
  simp

end Physical

section Rotation

variable {n : ℕ}

/-- A normalized rotation equivalent of a normalized diagram is its half-turn. -/
theorem eq_rotation_of_rotationEquivalent {V W : BetaDiagram (n + 1)}
    (hVn : V.col (Fin.last n) = 0) (hWn : W.col (Fin.last n) = 0) (hrot : V.RotationEquivalent W) :
    W = V.rotation := by
  obtain ⟨c, hr, hc⟩ := hrot
  have h0 := hr 0
  simp only [Fin.rev_zero, hWn, sub_zero] at h0
  have hl : V.largestLabel = c := by simp [BetaDiagram.largestLabel, hVn, h0]
  have ext : ∀ A B : BetaDiagram (n + 1), A.row = B.row → A.col = B.col → A = B := by
    intro A B h1 h2
    cases A
    cases B
    simp_all
  refine ext _ _ (funext fun i => ?_) (funext fun i => ?_)
  · have := hc i.rev
    simp only [Fin.rev_rev] at this
    simp only [BetaDiagram.rotation_row, hl]
    omega
  · have := hr i.rev
    simp only [Fin.rev_rev] at this
    simp only [BetaDiagram.rotation_col, hl]
    omega

end Rotation

section Main

variable {n : ℕ}

theorem span_cellCap : span cellCap = 1 := by
  simp [span, BetaDiagram.largestLabel, cellCap]

theorem cornerOf_cellCap : cornerOf cohLetters cellCap = 1 := by
  simp [cornerOf, properMatrixOf]

theorem leftCoframe_cellCap : FixedCap.leftCoframe cellCap = 1 := by
  simp [FixedCap.leftCoframe, leftCoframeOf, capPoly]

/-- The cell splice of a connected normalized diagram: `s_{cell ◁ V} = κ [z^{M+1}] H G`. -/
theorem schurOf_cellSplice (V : BetaDiagram (n + 1)) (hVn : IsNorm V) (hV : V.Connected) :
    schurOf cohLetters (splice cellCap V cellCap_isNorm hVn) = cornerOf cohLetters V *
      PowerSeries.coeff (span V + 1) (letterSeries * (coframe V : PowerSeries CohField)) := by
  rw [splice_schur_cohLetters cellCap cellCap_isNorm cellCap_connected V hVn hV, cornerOf_cellCap,
    span_cellCap, leftCoframe_cellCap]
  simp only [one_mul]

/-- **`ph:first-D`.**  For an actual connected nonself board, the defect of the board and its
rotation has nonzero coefficient at `M + 1`.  The bound `3 ≤ M` is not used. -/
theorem first_defect_coeff_ne_zero' {V W : BetaDiagram (n + 1)} (hV : V.Connected)
    (hVn : V.col (Fin.last n) = 0) (hWn : W.col (Fin.last n) = 0) (hrot : V.RotationEquivalent W)
    (hne : V ≠ W) (_hM : 3 ≤ span V) : (defect V W).coeff (span V + 1) ≠ 0 := by
  have hWV := eq_rotation_of_rotationEquivalent hVn hWn hrot
  have hschur : V.schur = W.schur := by rw [hWV, BetaDiagram.schur_rotation]
  have hWc : W.Connected := V.connected_of_schur_eq W hV hschur
  obtain ⟨-, hcorner, hs, htop, -, -⟩ := coequal_data hV hschur
  intro hd
  set M := span V with hMdef
  set G := coframe V with hG
  set C := coframe W with hC
  set q := PowerSeries.coeff M (letterSeries * (G : PowerSeries CohField)) with hq
  have hqC : q = PowerSeries.coeff M (letterSeries * (C : PowerSeries CohField)) := by
    have h1 : topQuotient V = q := rfl
    have h2 : topQuotient W = PowerSeries.coeff M (letterSeries * (C : PowerSeries CohField)) := by
      unfold topQuotient topQuotientOf
      rw [← hs]
      rfl
    rw [← h1, ← h2, htop]
  have h1 := clippedOp_coeff_succ M G C letterSeries (coframe_coeff_zero V)
    (coframe_coeff_zero W) hqC
  have hd' : (clippedOp M G C letterSeries).coeff (M + 1) = 0 := hd
  rw [hd'] at h1
  -- the two cell splices
  have hS1 := schurOf_cellSplice V hVn hV
  have hS2 := schurOf_cellSplice W hWn hWc
  rw [← hs] at hS2
  rw [← hMdef] at hS1
  have hκ : cornerOf cohLetters W = cornerOf cohLetters V := by
    rw [← algebraMap_cohCorner, ← algebraMap_cohCorner, hcorner]
  rw [hκ] at hS2
  -- polynomial multiples of the first coframe coefficients
  obtain ⟨r1, hr1⟩ := corner_mul_coframe_coeff_mem V hV one_pos
  obtain ⟨r2, hr2⟩ := corner_mul_coframe_coeff_mem W hWc one_pos
  rw [hκ] at hr2
  have hsq := schur_eq_corner_mul_topQuotient hV
  rw [algebraMap_cohSchur, algebraMap_cohCorner] at hsq
  have hqV : topQuotient V = q := rfl
  rw [hqV] at hsq
  have key : algebraMap CohRing CohField (cohCorner V) *
      (algebraMap CohRing CohField (cohSchur (splice cellCap V cellCap_isNorm hVn)) -
        algebraMap CohRing CohField (cohSchur (splice cellCap W cellCap_isNorm hWn))) =
      algebraMap CohRing CohField (r1 - r2) * algebraMap CohRing CohField (cohSchur V) := by
    rw [algebraMap_cohSchur, algebraMap_cohSchur, algebraMap_cohSchur, algebraMap_cohCorner,
      map_sub, hr1, hr2, hS1, hS2, hsq]
    have e : PowerSeries.coeff (M + 1) (letterSeries * (G : PowerSeries CohField)) -
        PowerSeries.coeff (M + 1) (letterSeries * (C : PowerSeries CohField)) =
        (G.coeff 1 - C.coeff 1) * q := by linear_combination (-1 : CohField) * h1
    linear_combination (cornerOf cohLetters V) * (cornerOf cohLetters V) * e
  have key' := IsFractionRing.injective CohRing CohField
    (by simpa only [← map_mul, ← map_sub] using key)
  generalize r1 - r2 = r at key'
  -- specialize to the physical letters
  have hphys := congrArg physSpec key'
  simp only [map_mul, map_sub, physSpec_cohSchur, physSpec_cohCorner] at hphys
  rw [← physInclude_physBack r] at hphys
  have hrel : V.cornerCoefficient *
      ((splice cellCap V cellCap_isNorm hVn).schur - (splice cellCap W cellCap_isNorm hWn).schur) =
        V.schur * physBack r := by
    apply physInclude_injective
    rw [map_mul, map_mul, map_sub, mul_comm (physInclude V.schur)]
    exact hphys
  exact hne (BCell.children_eq_of_cell_relation cellCap_vanishing V W hVn hWn hV hWc hschur
    ⟨_, hrel⟩)

end Main

end SkewCoframeRigidity.Unshifted
