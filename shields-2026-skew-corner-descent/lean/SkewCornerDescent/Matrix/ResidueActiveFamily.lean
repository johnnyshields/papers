/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalResponseClassCounts

/-!
# Produced rational labels of all active original classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`).
The exact rational residue equation produces an entire label family and full source
identities. Active top and label identities are conclusions, not proof-gap inputs.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance activeFamilyRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- The original residue equation simultaneously classifies every unbalanced response.
The source counts use literal equality, including all repeated inventory occurrences. -/
theorem actualResidue_active_family (N : ℕ+) {ι κ α : Type*}
    (s : Finset ι) (t : Finset κ)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (L : κ → ResidueHigherIndex N) (D : κ → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    (H : α → ResidueHigherIndex N) (E : α → ResidueHigherPolynomial N)
    (hE : ∀ a, ∀ j ∈ (E a).vars, j < H a)
    {K J₀ L₀ : ResidueHigherIndex N} (hJ : J₀ < K) (hL : L₀ < K)
    (A B₀ D₀ c : ResidueHigherPolynomial N) (hA : ∀ j ∈ A.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) (p q : Polynomial ℚ) (hpq : IsCoprime p q) (r v b d : ℕ)
    (hs : s.card + 1 = r * b) (ht : t.card + 1 = r * v) (hd : d + v = b)
    (hdep : let F := (X J₀ + B₀) * (X L₀ + D₀)
      residueHigherEval N c *
          (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
          ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
            (residueHigherEval N F) ^ d) =
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) p /
          Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) q) :
    ∃ label : α → ℚ, ∀ a,
      v * (s.filter fun i => residueHigherEval N (X (H a) + E a) =
          residueHigherEval N (X (J i) + B i)).card ≠
        b * (t.filter fun i => residueHigherEval N (X (H a) + E a) =
          residueHigherEval N (X (L i) + D i)).card →
      H a = K ∧ residueHigherEval N (X (H a) + E a) =
        residueHigherEval N (X K + A) - (label a : OtherField N) *
          (residueHigherEval N (X J₀ + B₀) * residueHigherEval N (X L₀ + D₀)) := by
  classical
  let active := fun a => v * triangularClassCount s J B (X (H a) + E a) ≠
    b * triangularClassCount t L D (X (H a) + E a)
  have hclass (a : α) (ha : active a) : H a = K ∧ ∃ z : ℚ,
      E a = A - C (algebraMap ℚ (residueLowerField N N) z) *
        ((X J₀ + B₀) * (X L₀ + D₀)) :=
    actualResidue_active_class N s t J B L D hB hD hJ hL A (E a) B₀ D₀ c
      hA (hE a) hB₀ hD₀ hc p q hpq r v b d hs ht hd ha hdep
  let label := fun a => if ha : active a then Classical.choose (hclass a ha).2 else 0
  refine ⟨label, ?_⟩
  intro a ha
  have ha' : active a := by
    dsimp only [active]
    rw [triangularClassCount_eq_source_count N s J B hB (H a) (E a) (hE a),
      triangularClassCount_eq_source_count N t L D hD (H a) (E a) (hE a)]
    exact ha
  obtain ⟨hHK, _⟩ := hclass a ha'
  have he : E a = A - C (algebraMap ℚ (residueLowerField N N) (label a)) *
      ((X J₀ + B₀) * (X L₀ + D₀)) := by
    simpa only [label, dite_eq_left ha'] using Classical.choose_spec (hclass a ha').2
  refine ⟨hHK, ?_⟩
  rw [hHK]
  simpa only [map_mul] using actualResidue_active_identity N K A (E a)
    ((X J₀ + B₀) * (X L₀ + D₀)) (label a) he

end SkewCornerDescent.Matrix
