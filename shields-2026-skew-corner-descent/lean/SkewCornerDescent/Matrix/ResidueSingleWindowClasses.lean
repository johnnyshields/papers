/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueNonplaneClasses
import SkewCornerDescent.SingleWindowClasses

/-!
# Rational response classes in a single actual residue window

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). With one complete window, every
retained response has the closure top and a full rational plane correction.
The original field equation produces class balance before coprimality excludes
all balanced classes from the two inventories.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residueSingleWindowRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Every response in a single full residue window is a genuine rational plane response. -/
theorem actualResidue_single_window_classes (N : ℕ+) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (L : κ → ResidueHigherIndex N) (D : κ → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K J₀ L₀ : ResidueHigherIndex N} (hJ : J₀ < K) (hL : L₀ < K)
    (A B₀ D₀ c : ResidueHigherPolynomial N) (hA : ∀ j ∈ A.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) (p q : Polynomial ℚ) (hpq : IsCoprime p q) (v b d : ℕ)
    (hcop : b.Coprime v) (hs : s.card + 1 = b) (ht : t.card + 1 = v) (hd : d + v = b)
    (hdep : let F := (X J₀ + B₀) * (X L₀ + D₀)
      residueHigherEval N c *
          (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
          ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
            (residueHigherEval N F) ^ d) =
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) p /
          Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) q) :
    let F := (X J₀ + B₀) * (X L₀ + D₀)
    (∀ i ∈ s, J i = K ∧ ∃ α : ℚ,
      B i = A - C (algebraMap ℚ (residueLowerField N N) α) * F) ∧
    (∀ i ∈ t, L i = K ∧ ∃ α : ℚ,
      D i = A - C (algebraMap ℚ (residueLowerField N N) α) * F) := by
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  have hclass (H : ResidueHigherIndex N) (E : ResidueHigherPolynomial N)
      (hE : ∀ j ∈ E.vars, j < H)
      (hpos : 0 < triangularClassCount s J B (X H + E) ∨
        0 < triangularClassCount t L D (X H + E)) :
      H = K ∧ ∃ α : ℚ,
        E = A - C (algebraMap ℚ (residueLowerField N N) α) * F := by
    have hnotbalance
        (hb : v * triangularClassCount s J B (X H + E) =
          b * triangularClassCount t L D (X H + E)) : False := by
      obtain ⟨hzeroU, hzeroW⟩ := singleWindow_balanced_class_empty
        s t J B L D (X H + E) v b hcop hs hb
      rcases hpos with hu | hw
      · omega
      · omega
    have hHK : H = K := by
      by_contra hne
      apply hnotbalance
      exact actualResidue_off_top_class_balance N s t J B L D hB hD
        hne hJ hL A E B₀ D₀ c hA hE hB₀ hD₀ hc p q hpq 1 v b d
        (by simpa only [one_mul] using hs) (by simpa only [one_mul] using ht) hd hdep
    refine ⟨hHK, ?_⟩
    subst H
    by_contra hmiss
    push Not at hmiss
    apply hnotbalance
    exact actualResidue_nonplane_class_balance N s t J B L D hB hD
      hJ hL A E B₀ D₀ c hA hE hB₀ hD₀ hc p q hpq 1 v b d
      (by simpa only [one_mul] using hs) (by simpa only [one_mul] using ht) hd hmiss hdep
  constructor
  · intro i hi
    exact hclass (J i) (B i) (hB i hi) (Or.inl (triangularClassCount_pos_of_mem s J B hi))
  · intro i hi
    exact hclass (L i) (D i) (hD i hi) (Or.inr (triangularClassCount_pos_of_mem t L D hi))

end SkewCornerDescent.Matrix
