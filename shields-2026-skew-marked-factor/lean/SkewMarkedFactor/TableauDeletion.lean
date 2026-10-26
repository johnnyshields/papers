/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.StandardTableaux

/-!
# Terminal singleton deletion

The successive-largest-entry argument in «Recovering the factors»
(`sec:extraction`, `eq:penultimate`, `eq:last`) of
`shields-2026-skew-marked-factor.tex`.
The penultimate identity is stated after a linear map with a proved constant
value on translated singletons.  Literal singleton cells are not identified
inside the free shape space.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan
open scoped BigOperators

@[simp]
theorem removableCells_empty : removableCells ∅ = ∅ := by simp [removableCells]

@[simp]
theorem removableCells_singleton (x : Cell) : removableCells {x} = {x} := by
  ext y
  simp [removableCells, eq_comm]
  tauto

@[simp]
theorem standardTableauCount_singleton (x : Cell) : standardTableauCount {x} = 1 := by
  simp [standardTableauCount, standardTableaux, deletionTableaux]

/-- Complete tableaux are partitioned by their largest entry. -/
theorem standardTableaux_eq_biUnion {D : Diagram} (hD : D ≠ ∅) :
    standardTableaux D = (removableCells D).biUnion fun x =>
      (standardTableaux (D.erase x)).image (List.cons x) := by
  classical
  ext l
  cases l with
  | nil => simp [mem_standardTableaux, IsTableauDeletion, hD]
  | cons x xs =>
    simp only [mem_standardTableaux, IsTableauDeletion, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨hx, hxs⟩
      exact ⟨x, hx, xs, hxs, rfl⟩
    · rintro ⟨y, hy, ys, hys, he⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      exact ⟨hy, hys⟩

/-- Distinct largest entries index disjoint tableau sets. -/
theorem tableau_cons_disjoint (D : Diagram) (x y : Cell) (hxy : x ≠ y) :
    Disjoint ((standardTableaux (D.erase x)).image (List.cons x))
      ((standardTableaux (D.erase y)).image (List.cons y)) := by
  rw [Finset.disjoint_left]
  intro l hx hy
  obtain ⟨xs, _, hx⟩ := Finset.mem_image.mp hx
  obtain ⟨ys, _, hy⟩ := Finset.mem_image.mp hy
  exact hxy (List.cons.inj (hx.trans hy.symm)).1

/-- The genuine standard-tableau recurrence. -/
theorem standardTableauCount_rec {D : Diagram} (hD : D ≠ ∅) :
    standardTableauCount D = ∑ x ∈ removableCells D, standardTableauCount (D.erase x) := by
  classical
  unfold standardTableauCount
  rw [standardTableaux_eq_biUnion hD, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    exact Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
  · intro x hx y hy hxy
    exact tableau_cons_disjoint D x y hxy

/-- Evaluation after successive unsigned singleton removals. -/
noncomputable def deletionSum : ℕ → (Diagram → Lambda) → Diagram → Lambda
  | 0, F, D => F D
  | n + 1, F, D => ∑ x ∈ removableCells D, deletionSum n F (D.erase x)

/-- No singleton deletion word longer than the cell count survives. -/
theorem deletionSum_eq_zero_of_card_lt (n : ℕ) (F : Diagram → Lambda) (D : Diagram)
    (hn : D.card < n) : deletionSum n F D = 0 := by
  induction n generalizing D with
  | zero => omega
  | succ n ih =>
    rw [deletionSum]
    apply Finset.sum_eq_zero
    intro x hx
    have hxD := (mem_removableCells.mp hx).1
    have hp : 0 < D.card := Finset.card_pos.mpr ⟨x, hxD⟩
    apply ih
    rw [Finset.card_erase_of_mem hxD]
    omega

/-- At the full order every standard tableau leaves the empty diagram. -/
theorem deletionSum_top (D : Diagram) (F : Diagram → Lambda) :
    deletionSum D.card F D = (standardTableauCount D : ℚ) • F ∅ := by
  classical
  induction hcard : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
    rcases n with _ | n
    · have he : D = ∅ := Finset.card_eq_zero.mp hcard
      subst D
      simp [deletionSum]
    · have hne : D ≠ ∅ := by intro he; subst D; simp at hcard
      rw [deletionSum]
      calc
        (∑ x ∈ removableCells D, deletionSum n F (D.erase x)) =
            ∑ x ∈ removableCells D, (standardTableauCount (D.erase x) : ℚ) • F ∅ := by
          apply Finset.sum_congr rfl
          intro x hx
          have he : (D.erase x).card = n := by
            rw [Finset.card_erase_of_mem (mem_removableCells.mp hx).1, hcard]
            omega
          simpa only [he] using ih n (by omega) (D.erase x) he
        _ = (standardTableauCount D : ℚ) • F ∅ := by
          rw [standardTableauCount_rec hne, Nat.cast_sum, Finset.sum_smul]

/-- At the penultimate order every remaining singleton has the same supplied value. -/
theorem deletionSum_penultimate (D : Diagram) (hD : D.Nonempty)
    (F : Diagram → Lambda) (S : Lambda) (hF : ∀ x, F {x} = S) :
    deletionSum (D.card - 1) F D = (standardTableauCount D : ℚ) • S := by
  classical
  induction hcard : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
    rcases n with _ | n
    · have hp := Finset.card_pos.mpr hD
      omega
    · rcases n with _ | n
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
        subst D
        simp [deletionSum, hF]
      · have hne : D ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hD
        have hi : n + 1 + 1 - 1 = n + 1 := by omega
        rw [hi, deletionSum]
        calc
          (∑ x ∈ removableCells D, deletionSum n F (D.erase x)) =
              ∑ x ∈ removableCells D, (standardTableauCount (D.erase x) : ℚ) • S := by
            apply Finset.sum_congr rfl
            intro x hx
            have he : (D.erase x).card = n + 1 := by
              rw [Finset.card_erase_of_mem (mem_removableCells.mp hx).1, hcard]
              omega
            have hp : (D.erase x).Nonempty := Finset.card_pos.mp (by omega)
            have hh := ih (n + 1) (by omega) (D.erase x) hp he
            simpa only [he, Nat.add_sub_cancel] using hh
          _ = (standardTableauCount D : ℚ) • S := by
            rw [standardTableauCount_rec hne, Nat.cast_sum, Finset.sum_smul]

/-- The actual repeated singleton-removal endomorphism on the free shape space. -/
noncomputable def oneCellWord (n : ℕ) : Module.End ℚ ShapeSpace := (rightOp 1) ^ n

/-- The endomorphism is the copied signed ribbon word; singleton signs are one. -/
theorem oneCellWord_eq_rightWord (n : ℕ) : oneCellWord n = rightWord (List.replicate n 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [oneCellWord, pow_succ', List.replicate_succ, rightWord]
    change (rightOp 1).comp (oneCellWord n) = (rightOp 1).comp (rightWord (List.replicate n 1))
    rw [ih]

/-- A linear evaluation of singleton words is exactly the tableau deletion sum. -/
theorem oneCellWord_evaluation (φ : ShapeSpace →ₗ[ℚ] Lambda) (n : ℕ) (D : Diagram) :
    φ (oneCellWord n (shape D)) = deletionSum n (fun X => φ (shape X)) D := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih =>
    rw [oneCellWord, pow_succ]
    change φ (((rightOp 1) ^ n) (rightOp 1 (shape D))) = _
    rw [rightOp_one_shape, deletionSum]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact ih (D.erase x)

/-- The terminal free-shape evaluation uses the actual standard-tableau count. -/
theorem oneCellWord_top (φ : ShapeSpace →ₗ[ℚ] Lambda) (D : Diagram) :
    φ (oneCellWord D.card (shape D)) =
      (standardTableauCount D : ℚ) • φ (shape ∅) := by
  rw [oneCellWord_evaluation, deletionSum_top]

/-- The penultimate statement is valid after, not before, translation-invariant evaluation. -/
theorem oneCellWord_penultimate (φ : ShapeSpace →ₗ[ℚ] Lambda) (D : Diagram)
    (hD : D.Nonempty) (S : Lambda) (hS : ∀ x : Cell, φ (shape {x}) = S) :
    φ (oneCellWord (D.card - 1) (shape D)) = (standardTableauCount D : ℚ) • S := by
  rw [oneCellWord_evaluation]
  exact deletionSum_penultimate D hD _ S hS

/-- Every evaluation of a word one order past the cell count vanishes. -/
theorem oneCellWord_next (φ : ShapeSpace →ₗ[ℚ] Lambda) (D : Diagram) :
    φ (oneCellWord (D.card + 1) (shape D)) = 0 := by
  rw [oneCellWord_evaluation]
  exact deletionSum_eq_zero_of_card_lt _ _ _ (by omega)

/-- The standard-tableau count is the genuine terminal derivative of the skew Schur function. -/
theorem standardTableauCount_derivative {D : Diagram} (hD : IsSkew D) :
    pDerivWord (List.replicate D.card 1) (cellSchur D) =
      MvPolynomial.C (standardTableauCount D : ℚ) := by
  have h := oneCellWord_top shapeSchur D
  rw [oneCellWord_eq_rightWord,
    KernelAux.shapeSchur_rightWord (by simp) (KernelAux.shape_mem_skewSupportedSpace hD),
    KernelAux.shapeSchur_shape, KernelAux.shapeSchur_shape, cellSchur_empty] at h
  simpa only [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq] using h

end SkewMarkedFactor
