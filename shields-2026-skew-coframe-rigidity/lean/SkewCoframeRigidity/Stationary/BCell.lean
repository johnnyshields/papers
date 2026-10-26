/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.CellExample
import SkewCoframeRigidity.FixedCap.Reduction
import SkewCofactorIndependence.WeightedReadings

/-!
# The same-cell splice step of top matching

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Finite stationary separation»
(`sec:stationary`), the last paragraph of the proof of `sc:top-matching`: two actual children with
equal whole function whose same-cell splice functions differ by `B_cell = -s_E δ₁`, where
`κ δ₁` is a polynomial and `κ` is the common signed corner.  The connected function `s_E` is
irreducible and has row degree `b + 1`, which exceeds that of `κ`, so `s_E ∣ B_cell`; the two
splices add one cell without adding a row, so `B_cell` has row degree at most that of `s_E`, while
its weighted degree is one higher, and a nonzero quotient is impossible.  Hence the same-cell
splice functions agree, and `sc:fixed-cap` identifies the children.  Sorry-free.
-/

namespace SkewCoframeRigidity

open SkewCofactorIndependence MvPolynomial

namespace BCell

variable {b : ℕ}

theorem area_cellSplice (E : BetaDiagram (b + 1)) (hE : IsNorm E) :
    (splice cellCap E cellCap_isNorm hE).area = E.area + 1 := by
  unfold BetaDiagram.area
  obtain ⟨e, hv⟩ : ∃ e : Fin (0 + b + 1) ≃ Fin (b + 1), ∀ i, (e i).val = i.val :=
    ⟨finCongr (by omega), fun _ => rfl⟩
  have hr : ∑ i, (splice cellCap E cellCap_isNorm hE).row i =
      ∑ j : Fin (b + 1), (E.row j + if j = 0 then 1 else 0) := by
    refine Fintype.sum_equiv e _ _ fun i => ?_
    change spliceRow cellCap E i = _
    by_cases h : i.val < 1
    · have h0 : e i = 0 := by ext; rw [hv, Fin.val_zero]; omega
      rw [spliceRow_top cellCap E i (by omega), h0]
      have : i = 0 := by ext; rw [Fin.val_zero]; omega
      subst this
      simp [cellCap]
    · have h0 : e i ≠ 0 := by
        intro hh
        have := congrArg Fin.val hh
        rw [hv, Fin.val_zero] at this
        omega
      rw [spliceRow_bot cellCap E i (by omega)]
      simp only [h0, ↓reduceIte, add_zero]
      congr 1
      ext
      rw [hv]
      simp
  have hc : ∑ i, (splice cellCap E cellCap_isNorm hE).col i = ∑ j, E.col j := by
    refine Fintype.sum_equiv e _ _ fun i => ?_
    change spliceCol cellCap E i = _
    rw [spliceCol_bot cellCap E i (by omega)]
    congr 1
    ext
    rw [hv]
    simp
  rw [hr, hc, Finset.sum_add_distrib]
  simp
  ring

/-- A board determinant has ordinary degree at most its size. -/
theorem betaBoard_det_totalDegree_le {n : ℕ} (u v : Fin n → ℤ) :
    (betaBoard u v).det.totalDegree ≤ n := by
  classical
  unfold betaBoard
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  refine (MvPolynomial.totalDegree_smul_le (Equiv.Perm.sign σ : ℤ) _).trans ?_
  refine (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans ?_
  calc
    (∑ i, (complete (u i - v (σ i))).totalDegree) ≤ ∑ _ : Fin n, 1 :=
      Finset.sum_le_sum (fun i _ => complete_totalDegree_le_one _)
    _ = n := by simp

/-- The signed corner has ordinary degree at most the number of non-top rows. -/
theorem corner_totalDegree_le (D : BetaDiagram (b + 1)) :
    D.cornerCoefficient.totalDegree ≤ b := by
  have hs : (-1 : CompleteRing) ^ b = MvPolynomial.C ((-1 : ℚ) ^ b) := by simp
  unfold BetaDiagram.cornerCoefficient BetaDiagram.cornerPolynomial BetaDiagram.cornerBoard
  rw [hs]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact betaBoard_det_totalDegree_le _ _

/-- The function of a connected child does not divide its signed corner. -/
theorem not_schur_dvd_corner (E : BetaDiagram (b + 1)) (hEc : E.Connected) :
    ¬ E.schur ∣ E.cornerCoefficient := by
  rintro ⟨t, ht⟩
  have hk : E.cornerCoefficient ≠ 0 := (BetaDiagram.largestGenerator E hEc).2.2.2
  have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hk ht
  have hs0 : E.schur ≠ 0 := by
    intro h
    have := E.schur_totalDegree
    rw [h] at this
    simp at this
  have h1 := corner_totalDegree_le E
  rw [ht, totalDegree_mul_of_isDomain hs0 ht0, E.schur_totalDegree] at h1
  omega

/-- **The `B_cell` step.**  Two connected normalized children with equal whole function whose
same-cell splice functions satisfy `κ (s_{cell ◁ E} - s_{cell ◁ F}) = s_E r` for a polynomial `r`
(that is, `B_cell = -s_E δ₁` with `κ δ₁ = -r` polynomial) have equal same-cell splice functions. -/
theorem cellSplice_schur_eq (E F : BetaDiagram (b + 1)) (hE : IsNorm E) (hF : IsNorm F)
    (hEc : E.Connected) (hs : E.schur = F.schur)
    (hrel : ∃ r : CompleteRing, E.cornerCoefficient *
      ((splice cellCap E cellCap_isNorm hE).schur - (splice cellCap F cellCap_isNorm hF).schur) =
        E.schur * r) :
    (splice cellCap E cellCap_isNorm hE).schur = (splice cellCap F cellCap_isNorm hF).schur := by
  obtain ⟨r, hr⟩ := hrel
  by_contra hne
  set Bc := (splice cellCap E cellCap_isNorm hE).schur -
    (splice cellCap F cellCap_isNorm hF).schur with hBc
  have hB0 : Bc ≠ 0 := sub_ne_zero.mpr hne
  have hprime : Prime E.schur := (BetaDiagram.connected_irreducible E hEc).prime
  have hdvd : E.schur ∣ E.cornerCoefficient * Bc := ⟨r, hr⟩
  obtain ⟨q, hq⟩ := (hprime.dvd_or_dvd hdvd).resolve_left (not_schur_dvd_corner E hEc)
  have hs0 : E.schur ≠ 0 := hprime.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hB0 hq
  have hdeg : Bc.totalDegree ≤ b + 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · have := BetaDiagram.rowDegree (splice cellCap E cellCap_isNorm hE)
      omega
    · have := BetaDiagram.rowDegree (splice cellCap F cellCap_isNorm hF)
      omega
  have hqd : q.totalDegree = 0 := by
    have h1 := congrArg MvPolynomial.totalDegree hq
    rw [totalDegree_mul_of_isDomain hs0 hq0, E.schur_totalDegree] at h1
    omega
  have hc := (totalDegree_eq_zero_iff_eq_C).mp hqd
  have hAE := E.schur_reverse_homogeneous
  have hAF : IsWeightedHomogeneous reverseIndexWeight E.schur (-(F.area : ℝ)) :=
    hs ▸ F.schur_reverse_homogeneous
  have hArea : (E.area : ℝ) = F.area := by
    have := hAE.inj_right hs0 hAF
    linarith
  have h1 := (splice cellCap E cellCap_isNorm hE).schur_reverse_homogeneous
  have h2 := (splice cellCap F cellCap_isNorm hF).schur_reverse_homogeneous
  rw [area_cellSplice E hE] at h1
  rw [area_cellSplice F hF] at h2
  have h2' : IsWeightedHomogeneous reverseIndexWeight
      (splice cellCap F cellCap_isNorm hF).schur (-((E.area + 1 : ℤ) : ℝ)) := by
    have : (-((F.area + 1 : ℤ) : ℝ)) = -((E.area + 1 : ℤ) : ℝ) := by push_cast; linarith
    rwa [this] at h2
  have hh : IsWeightedHomogeneous reverseIndexWeight Bc (-((E.area + 1 : ℤ) : ℝ)) := h1.sub h2'
  have hh' : IsWeightedHomogeneous reverseIndexWeight Bc (-(E.area : ℝ)) := by
    rw [hq, hc]
    simpa using hAE.mul (isWeightedHomogeneous_C reverseIndexWeight (q.coeff 0))
  have := hh.inj_right hB0 hh'
  push_cast at this
  linarith

/-- The `B_cell` step with its use of `sc:fixed-cap`: the actual children are the same diagram,
given the descent for the one-cell cap. -/
theorem children_eq_of_cell_relation (hcap : FixedCap.CapVanishing cellCap)
    (E F : BetaDiagram (b + 1)) (hE : IsNorm E) (hF : IsNorm F) (hEc : E.Connected)
    (hFc : F.Connected) (hs : E.schur = F.schur)
    (hrel : ∃ r : CompleteRing, E.cornerCoefficient *
      ((splice cellCap E cellCap_isNorm hE).schur - (splice cellCap F cellCap_isNorm hF).schur) =
        E.schur * r) :
    E = F :=
  eq_of_heq (FixedCap.fixed_cap_rigidity cellCap cellCap_isNorm cellCap_connected hcap E F hE hF
    hEc hFc hs (cellSplice_schur_eq E F hE hF hEc hs hrel)).2

end BCell

end SkewCoframeRigidity
