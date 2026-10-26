/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic

/-!
# Finite triangular sign chambers

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Successive coordinate choices give both common signs for every finite family whose corrections
use strictly lower coordinates. Continuous corrections make the resulting chambers open.
The same-anchor root constraints are separate obligations.

Sorry-free.
-/

namespace SkewCornerDescent

/-- The common sign condition for a real scalar response. -/
def responseSign (positive : Bool) (z : ℝ) : Prop :=
  if positive then 0 < z else z < 0

/-- A finite triangular family can be assigned either common sign while fixing lower coordinates. -/
theorem exists_signed_triangular_assignment {ι : Type*} [Finite ι]
    (top : ι → ℕ) (correction : ι → (ℕ → ℝ) → ℝ) (N : ℕ)
    (hN : ∀ i, N ≤ top i)
    (hlocal : ∀ i x y, (∀ j, j < top i → x j = y j) → correction i x = correction i y)
    (base : ℕ → ℝ) (positive : Bool) :
    ∃ x : ℕ → ℝ, (∀ j, j < N → x j = base j) ∧
      ∀ i, responseSign positive (x (top i) + correction i x) := by
  classical
  let _ := Fintype.ofFinite ι
  have stage (m : ℕ) : ∃ x : ℕ → ℝ, (∀ j, j < N → x j = base j) ∧
      ∀ i, top i < m → responseSign positive (x (top i) + correction i x) := by
    induction m with
    | zero => exact ⟨base, fun _ _ => rfl, fun i hi => (Nat.not_lt_zero _ hi).elim⟩
    | succ m ih =>
      obtain ⟨x, hx, hs⟩ := ih
      by_cases hm : m < N
      · exact ⟨x, hx, fun i hi => hs i (by have := hN i; omega)⟩
      · let A : ℝ := (∑ i, |correction i x|) + 1
        let v : ℝ := if positive then A else -A
        let y := Function.update x m v
        have hcorr (i : ι) (hi : top i ≤ m) : correction i y = correction i x := by
          apply hlocal
          intro j hj
          exact Function.update_of_ne (by omega : j ≠ m) _ _
        refine ⟨y, ?_, ?_⟩
        · intro j hj
          dsimp only [y]
          rw [Function.update_of_ne (by omega : j ≠ m)]
          exact hx j hj
        · intro i hi
          have hit : top i ≤ m := by omega
          rw [hcorr i hit]
          by_cases he : top i = m
          · dsimp only [y]
            rw [he, Function.update_self]
            have hb : |correction i x| ≤ ∑ j, |correction j x| :=
              Finset.single_le_sum (fun j _ => abs_nonneg (correction j x)) (Finset.mem_univ i)
            have hab := le_abs_self (correction i x)
            have hba := neg_abs_le (correction i x)
            cases positive <;> simp [v, responseSign] <;> dsimp [A] <;> linarith
          · dsimp only [y]
            rw [Function.update_of_ne he]
            exact hs i (by omega)
  obtain ⟨x, hx, hs⟩ := stage ((Finset.univ.sup top) + 1)
  refine ⟨x, hx, fun i => hs i ?_⟩
  have := Finset.le_sup (f := top) (Finset.mem_univ i)
  omega

/-- Polynomial corrections supported below their top satisfy the required coordinate locality. -/
theorem triangular_polynomial_locality {ι : Type*} (top : ι → ℕ)
    (p : ι → MvPolynomial ℕ ℝ) (hp : ∀ i j, j ∈ (p i).vars → j < top i)
    (i : ι) (x y : ℕ → ℝ) (hxy : ∀ j, j < top i → x j = y j) :
    MvPolynomial.eval x (p i) = MvPolynomial.eval y (p i) := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro j hj _
  exact hxy j (hp i j hj)

/-- Both signs are inhabited for the actual finite polynomial form `X_top + lower`. -/
theorem exists_signed_triangular_polynomials {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p : ι → MvPolynomial ℕ ℝ) (N : ℕ)
    (hN : ∀ i, N ≤ top i) (hp : ∀ i j, j ∈ (p i).vars → j < top i)
    (base : ℕ → ℝ) (positive : Bool) :
    ∃ x : ℕ → ℝ, (∀ j, j < N → x j = base j) ∧
      ∀ i, responseSign positive (MvPolynomial.eval x (MvPolynomial.X (top i) + p i)) := by
  obtain ⟨x, hx, hs⟩ := exists_signed_triangular_assignment top
    (fun i x => MvPolynomial.eval x (p i)) N hN
    (triangular_polynomial_locality top p hp) base positive
  refine ⟨x, hx, ?_⟩
  simpa only [map_add, MvPolynomial.eval_X] using hs

/-- The simultaneous strict sign constraints form an open chamber. -/
theorem triangular_polynomial_chamber_open {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p : ι → MvPolynomial ℕ ℝ) (positive : Bool) :
    IsOpen {x : ℕ → ℝ | ∀ i,
      responseSign positive (MvPolynomial.eval x (MvPolynomial.X (top i) + p i))} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  have hc := (MvPolynomial.X (top i) + p i).continuous_eval
  cases positive
  · exact isOpen_lt hc continuous_const
  · exact isOpen_lt continuous_const hc

/-- Either complete sign chamber is nonempty, not merely a formal list of inequalities. -/
theorem triangular_polynomial_chamber_nonempty {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p : ι → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < top i) (positive : Bool) :
    ({x : ℕ → ℝ | ∀ i,
      responseSign positive (MvPolynomial.eval x (MvPolynomial.X (top i) + p i))} :
      Set (ℕ → ℝ)).Nonempty := by
  obtain ⟨x, _, hs⟩ := exists_signed_triangular_polynomials top p 0 (fun _ => Nat.zero_le _)
    hp (fun _ => 0) positive
  exact ⟨x, hs⟩

end SkewCornerDescent
