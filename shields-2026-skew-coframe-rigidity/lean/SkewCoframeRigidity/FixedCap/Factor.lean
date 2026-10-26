/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.RowDegree
import SkewCoframeRigidity.Coframe.Coherent
import SkewCoframeRigidity.Coframe.Atlas

/-!
# Unique factorization of connected skew Schur polynomials

Formalizes the unique-factorization step of the descent in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`: if `s_N s_{E'} = s_{N'} s_E` for connected diagrams with
`span E < span N` and `span E' < span N'`, then `s_E = s_{E'}` and `s_N = s_{N'}`.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity MvPolynomial
open scoped Polynomial Matrix

/-- Proportional skew Schur polynomials are equal: the initial form for the square weight is a
product of generators, so its value at the all-ones point is `1`. -/
theorem schur_const_mul_eq_one {m m' : ℕ} (D : BetaDiagram m) (D' : BetaDiagram m') {μ : ℚ}
    (hμ : μ ≠ 0) (h : D'.schur = C μ * D.schur) : μ = 1 := by
  have hC : (C μ : CompleteRing) ≠ 0 := by simpa using hμ
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) h
  rw [Base.initialForm_mul hC D.schur_ne_zero,
    Base.initialForm_eq_of_homogeneous hC (isWeightedHomogeneous_C _ _),
    BetaDiagram.square_initialForm, BetaDiagram.square_initialForm] at hi
  have hev := congrArg (MvPolynomial.eval fun _ => (1 : ℚ)) hi
  have key : ∀ {k : ℕ} (E : BetaDiagram k),
      MvPolynomial.eval (fun _ => (1 : ℚ)) (∏ i, complete (E.row i - E.col i)) = 1 := by
    intro k E
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have := E.row_nonempty i
    rw [complete_of_pos (by omega)]
    exact MvPolynomial.eval_X _
  rw [map_mul, key, key] at hev
  simpa using hev.symm

/-- A connected skew Schur polynomial does not divide a connected one of strictly smaller span. -/
theorem not_dvd_of_span_lt {m m' : ℕ} (N : BetaDiagram (m + 1)) (E : BetaDiagram (m' + 1))
    (hN : N.Connected) (hE : E.Connected) (hlt : E.largestLabel < N.largestLabel) :
    ¬ N.schur ∣ E.schur := by
  intro hd
  have hass := (N.schur_irreducible hN).associated_of_dvd (E.schur_irreducible hE) hd
  obtain ⟨u, hu⟩ := hass
  obtain ⟨μ, hμu, hμ⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  have hmem := N.largest_mem_vars hN
  have hE' : N.schur * C μ = E.schur := by rw [← hu, hμ]
  have hμ0 : μ ≠ 0 := hμu.ne_zero
  have hN2 : N.schur = E.schur * C μ⁻¹ := by
    rw [← hE', mul_assoc, ← C_mul, mul_inv_cancel₀ hμ0, C_1, mul_one]
  have : (⟨N.largestLabel.toNat, by have := N.largestLabel_pos; omega⟩ : ℕ+) ∈ E.schur.vars := by
    rw [hN2] at hmem
    rcases Finset.mem_union.1 (MvPolynomial.vars_mul E.schur (C μ⁻¹) hmem) with h | h
    · exact h
    · rw [MvPolynomial.vars_C] at h
      exact absurd h (Finset.notMem_empty _)
  have h2 := E.vars_le_largestLabel _ this
  change ((N.largestLabel.toNat : ℕ) : ℤ) ≤ E.largestLabel at h2
  have := N.largestLabel_pos
  omega

/-- **Unique factorization.**  If `s_N s_{E'} = s_{N'} s_E` for connected diagrams with
`span E < span N` and `span E' < span N'`, then `s_E = s_{E'}` and `s_N = s_{N'}`. -/
theorem factor_eq {m1 m2 m3 m4 : ℕ} (N : BetaDiagram (m1 + 1)) (N' : BetaDiagram (m3 + 1))
    (E : BetaDiagram (m2 + 1)) (E' : BetaDiagram (m4 + 1)) (hN : N.Connected)
    (hN' : N'.Connected) (hE : E.Connected) (hE' : E'.Connected)
    (h1 : E.largestLabel < N.largestLabel) (h2 : E'.largestLabel < N'.largestLabel)
    (h : N.schur * E'.schur = N'.schur * E.schur) :
    E.schur = E'.schur ∧ N.schur = N'.schur := by
  have hpN := (N.schur_irreducible hN).prime
  have hpN' := (N'.schur_irreducible hN').prime
  have hd1 : N.schur ∣ N'.schur := by
    have : N.schur ∣ N'.schur * E.schur := Dvd.intro _ h
    exact (hpN.dvd_or_dvd this).resolve_right (not_dvd_of_span_lt N E hN hE h1)
  have hd2 : N'.schur ∣ N.schur := by
    have : N'.schur ∣ N.schur * E'.schur := Dvd.intro _ h.symm
    exact (hpN'.dvd_or_dvd this).resolve_right (not_dvd_of_span_lt N' E' hN' hE' h2)
  obtain ⟨u, hu⟩ := (dvd_dvd_iff_associated.1 ⟨hd1, hd2⟩ : Associated N.schur N'.schur)
  obtain ⟨μ, hμu, hμ⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  have hμ0 : μ ≠ 0 := hμu.ne_zero
  have hN'eq : N'.schur = C μ * N.schur := by rw [← hu, hμ, mul_comm]
  have hE'eq : E'.schur = C μ * E.schur := by
    have : N.schur * E'.schur = N.schur * (C μ * E.schur) := by
      rw [h, hN'eq]; ring
    exact mul_left_cancel₀ N.schur_ne_zero this
  have hμ1 := schur_const_mul_eq_one E E' hμ0 hE'eq
  subst hμ1
  simp only [map_one, one_mul] at hE'eq hN'eq
  exact ⟨hE'eq.symm, hN'eq.symm⟩

/-- A product of two nonconstant skew Schur polynomials is not the Schur polynomial of a
connected diagram. -/
theorem not_connected_of_mul {m1 m2 m3 : ℕ} (N : BetaDiagram (m1 + 1)) (A : BetaDiagram (m2 + 1))
    (B : BetaDiagram (m3 + 1)) (hN : N.Connected) (h : A.schur * B.schur = N.schur) : False := by
  have hirr := N.schur_irreducible hN
  rw [← h] at hirr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · exact A.schur_not_isUnit (Nat.succ_pos _) hu
  · exact B.schur_not_isUnit (Nat.succ_pos _) hu

end SkewCoframeRigidity.FixedCap
