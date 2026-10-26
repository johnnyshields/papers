/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.OrdinaryAction
import SkewMarkedFactor.TableauDeletion

/-!
# Evaluation of complete ribbon words

«Recovering the factors» (`sec:extraction`, `eq:character`,
`eq:outer-recovery`) of `shields-2026-skew-marked-factor.tex`.
When the removed sizes sum to the cell count, every surviving branch ends at
the empty diagram.  Two evaluations agreeing there therefore have identical
values on the complete word.  This proves the normalization cancellation at
all character indices, not just at singleton indices.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan
open scoped BigOperators

/-- Literal signed southeast ribbon removal, with the first part removed first. -/
noncomputable def ribbonEvaluation : List ℕ → (Diagram → Lambda) → Diagram → Lambda
  | [], F, D => F D
  | m :: ν, F, D => ∑ R ∈ rightRibbons D m,
      (ribbonSign R : ℚ) • ribbonEvaluation ν F (D \ R)

/-- A linear evaluation of the free shape word is exactly the signed ribbon recursion. -/
theorem removalWord_evaluation (ν : List ℕ) (φ : ShapeSpace →ₗ[ℚ] Lambda) (D : Diagram) :
    φ (removalWord ν (shape D)) = ribbonEvaluation ν (fun X => φ (shape X)) D := by
  induction ν generalizing D with
  | nil => rfl
  | cons m ν ih =>
    rw [removalWord, LinearMap.comp_apply, KernelAux.rightOp_shape]
    simp only [map_sum, map_smul]
    rw [ribbonEvaluation]
    apply Finset.sum_congr rfl
    intro R hR
    rw [ih]

/-- Complete words are insensitive to any evaluation away from the empty diagram. -/
theorem ribbonEvaluation_total_congr (ν : List ℕ) (D : Diagram)
    (hsum : ν.sum = D.card) (F G : Diagram → Lambda) (hFG : F ∅ = G ∅) :
    ribbonEvaluation ν F D = ribbonEvaluation ν G D := by
  induction ν generalizing D with
  | nil =>
    have he : D = ∅ := Finset.card_eq_zero.mp hsum.symm
    subst D
    exact hFG
  | cons m ν ih =>
    rw [ribbonEvaluation, ribbonEvaluation]
    apply Finset.sum_congr rfl
    intro R hR
    have hr := mem_rightRibbons.mp hR
    have hle := Finset.card_le_card hr.1
    have he : ν.sum = (D \ R).card := by
      rw [Finset.card_sdiff_of_subset hr.1, hr.2.1]
      simp only [List.sum_cons] at hsum
      omega
    rw [ih (D \ R) he]

/-- Murnaghan–Nakayama identifies the recursion with the actual power-sum adjoints. -/
theorem cellSchur_ribbonEvaluation {D : Diagram} (hD : IsSkew D)
    (ν : List ℕ) (hν : ∀ m ∈ ν, 0 < m) :
    pDerivWord ν (cellSchur D) = ribbonEvaluation ν cellSchur D := by
  induction ν generalizing D with
  | nil => rfl
  | cons m ν ih =>
    have hm : 0 < m := hν m (by simp)
    have hrest : ∀ k ∈ ν, 0 < k := fun k hk => hν k (List.mem_cons_of_mem _ hk)
    rw [pDerivWord, LinearMap.comp_apply, Derivation.coeFn_coe,
      pDeriv_cellSchur_right hD hm]
    unfold ribbonSumRight
    simp only [← KernelAux.smul_int_eq, map_sum, map_smul]
    rw [ribbonEvaluation]
    apply Finset.sum_congr rfl
    intro R hR
    have hr := mem_rightRibbons.mp hR
    have hsk : IsSkew (D \ R) := KernelAux.isSkew_sdiff_of_isUpsetIn hD hr.2.2.2
    have h := ih hsk hrest
    exact congrArg (fun f : Lambda => (ribbonSign R : ℚ) • f) h

/-- The genuine modified evaluation and the Schur evaluation agree on every complete word. -/
theorem modified_map_total_word (η : MarkedInner) {D : Diagram} (hD : IsSkew D)
    (ν : List ℕ) (hν : ∀ m ∈ ν, 0 < m) (hsum : ν.sum = D.card) :
    modifiedMap η (removalWord ν (shape D)) = pDerivWord ν (cellSchur D) := by
  rw [removalWord_evaluation]
  have he := ribbonEvaluation_total_congr ν D hsum
    (fun X => modifiedMap η (shape X)) cellSchur (by rw [modified_map_empty, cellSchur_empty])
  rw [he, ← cellSchur_ribbonEvaluation hD ν hν]

/-- Repeated singleton removal is the actual tableau endomorphism already counted. -/
theorem removalWord_replicate_one (n : ℕ) :
    removalWord (List.replicate n 1) = oneCellWord n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, removalWord, ih]
    change ((rightOp 1) ^ n).comp (rightOp 1) = (rightOp 1) ^ (n + 1)
    exact (pow_succ (rightOp 1) n).symm

/-- The normalized terminal word is precisely the actual tableau count. -/
theorem modified_terminal_word (η : MarkedInner) (D : Diagram) :
    modifiedMap η (removalWord (List.replicate D.card 1) (shape D)) =
      MvPolynomial.C (standardTableauCount D : ℚ) := by
  rw [removalWord_replicate_one, oneCellWord_top, modified_map_empty]
  simp only [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]

/-- The normalized penultimate word evaluates every literal singleton to the actual inner. -/
theorem modified_penultimate_word {η : MarkedInner} (ho : η.IsOrdinary)
    (D : Diagram) (hD : D.Nonempty) :
    modifiedMap η (removalWord (List.replicate (D.card - 1) 1) (shape D)) =
      (standardTableauCount D : ℚ) • cellSchur η.E := by
  rw [removalWord_replicate_one]
  exact oneCellWord_penultimate (modifiedMap η) D hD _ (modified_map_singleton ho)

/-- One order beyond the outer area vanishes before any scalar cancellation. -/
theorem modified_next_word (η : MarkedInner) (D : Diagram) :
    modifiedMap η (removalWord (List.replicate (D.card + 1) 1) (shape D)) = 0 := by
  rw [removalWord_replicate_one]
  exact oneCellWord_next (modifiedMap η) D

end SkewMarkedFactor
