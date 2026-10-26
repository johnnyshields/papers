/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoEscape
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Coefficient-one normalization and exact component matching

Formalizes the connected factor-matching input in `subsec:readings`
of `shields-2026-skew-class-inflation.tex`.  Actual Schur polynomials
are normalized by their proved coefficient-one square-weight leaders.
Sorry-free.
-/

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {n m : ℕ}

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/SingletonContexts.lean
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

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/SingletonLift.lean
/-- Products of actual connected diagrams recover their exact polynomial
inventory, with all multiplicities and no size restriction. -/
theorem connected_product_functions_eq
    (xs ys : List (Σ k : ℕ, BetaDiagram k))
    (hx : ∀ X ∈ xs, X.2.Connected) (hy : ∀ Y ∈ ys, Y.2.Connected)
    (he : (xs.map (fun X => X.2.schur)).prod =
      (ys.map (fun Y => Y.2.schur)).prod) :
    ((xs.map (fun X => X.2.schur)) : Multiset CompleteRing) =
      ((ys.map (fun Y => Y.2.schur)) : Multiset CompleteRing) := by
  let f : Multiset CompleteRing := xs.map (fun X => X.2.schur)
  let g : Multiset CompleteRing := ys.map (fun Y => Y.2.schur)
  have hf : ∀ a ∈ f, Irreducible a := by
    intro a ha
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp (show a ∈ xs.map (fun X => X.2.schur) by
      simpa only [f, Multiset.mem_coe] using ha)
    exact X.2.schur_irreducible (hx X hX)
  have hg : ∀ a ∈ g, Irreducible a := by
    intro a ha
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp (show a ∈ ys.map (fun X => X.2.schur) by
      simpa only [g, Multiset.mem_coe] using ha)
    exact X.2.schur_irreducible (hy X hX)
  have hprod : f.prod = g.prod := by simpa only [f, g, Multiset.prod_coe] using he
  have hrel := UniqueFactorizationMonoid.factors_unique hf hg
    (show Associated f.prod g.prod by
      rw [hprod])
  apply Multiset.rel_eq.mp
  apply hrel.mono
  intro a ha b hb hab
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp (show a ∈ xs.map (fun X => X.2.schur) by
    simpa only [f, Multiset.mem_coe] using ha)
  obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp (show b ∈ ys.map (fun Y => Y.2.schur) by
    simpa only [g, Multiset.mem_coe] using hb)
  exact X.2.schur_eq_of_associated Y.2 hab

/-- Factor matches carry their actual row counts, read from polynomial total degree. -/
theorem product_component_matching
    (xs ys : List (Σ k : ℕ, BetaDiagram k))
    (hx : ∀ X ∈ xs, X.2.Connected) (hy : ∀ Y ∈ ys, Y.2.Connected)
    (he : (xs.map (fun X => X.2.schur)).prod =
      (ys.map (fun Y => Y.2.schur)).prod) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k =>
      X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (xs : Multiset _) (ys : Multiset _) := by
  have hfunc : Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k => X.2.schur = Y.2.schur)
      (xs : Multiset _) (ys : Multiset _) := by
    apply Multiset.rel_map.mp
    apply Multiset.rel_eq.mpr
    exact connected_product_functions_eq xs ys hx hy he
  apply hfunc.mono
  intro X _ Y _ hXY
  refine ⟨hXY, ?_⟩
  have hdeg := congrArg MvPolynomial.totalDegree hXY
  simpa only [schur_totalDegree] using hdeg

end SkewJacobiNegative.BetaDiagram
