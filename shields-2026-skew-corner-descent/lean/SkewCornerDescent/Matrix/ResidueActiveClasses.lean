/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueNonplaneClasses

/-!
# Active classes in the unchanged original residue field

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`).
An unbalanced full response class first has its top identified with the literal closure
top. Its entire correction then has a rational label, not merely a specialized value or
an associated prime. Both assertions follow from the exact rational residue equation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residueActiveRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- An active full response is exactly a rational-label closure response. The closure-top
identification is produced before the correction identity, including possible cap aliases. -/
theorem actualResidue_active_class (N : ℕ+) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (L : κ → ResidueHigherIndex N) (D : κ → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K H J₀ L₀ : ResidueHigherIndex N} (hJ : J₀ < K) (hL : L₀ < K)
    (A E B₀ D₀ c : ResidueHigherPolynomial N) (hA : ∀ j ∈ A.vars, j < K)
    (hE : ∀ j ∈ E.vars, j < H)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) (p q : Polynomial ℚ) (hpq : IsCoprime p q) (r v b d : ℕ)
    (hs : s.card + 1 = r * b) (ht : t.card + 1 = r * v) (hd : d + v = b)
    (hactive : v * triangularClassCount s J B (X H + E) ≠
      b * triangularClassCount t L D (X H + E))
    (hdep : let F := (X J₀ + B₀) * (X L₀ + D₀)
      residueHigherEval N c *
          (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
          ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
            (residueHigherEval N F) ^ d) =
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) p /
          Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) q) :
    H = K ∧ ∃ α : ℚ,
      E = A - C (algebraMap ℚ (residueLowerField N N) α) *
        ((X J₀ + B₀) * (X L₀ + D₀)) := by
  classical
  have hHK : H = K := by
    by_contra hHK
    exact hactive (actualResidue_off_top_class_balance N s t J B L D hB hD hHK
      hJ hL A E B₀ D₀ c hA hE hB₀ hD₀ hc p q hpq r v b d hs ht hd hdep)
  refine ⟨hHK, ?_⟩
  subst H
  by_contra hmiss
  push Not at hmiss
  exact hactive (actualResidue_nonplane_class_balance N s t J B L D hB hD
    hJ hL A E B₀ D₀ c hA hE hB₀ hD₀ hc p q hpq r v b d hs ht hd hmiss hdep)

/-- A full polynomial correction identity yields the full source-field affine identity.
There is no real specialization in this bridge. -/
theorem actualResidue_active_identity (N : ℕ+) (K : ResidueHigherIndex N)
    (A E F : ResidueHigherPolynomial N) (α : ℚ)
    (he : E = A - C (algebraMap ℚ (residueLowerField N N) α) * F) :
    residueHigherEval N (X K + E) = residueHigherEval N (X K + A) -
      (α : OtherField N) * residueHigherEval N F := by
  rw [he, map_add, map_sub, map_mul, map_add]
  have hC : residueHigherEval N (C (algebraMap ℚ (residueLowerField N N) α)) =
      (α : OtherField N) := by
    simp only [residueHigherEval, aeval_C, Subfield.algebraMap_ofSubfield]
    change algebraMap (residueLowerField N N) (OtherField N)
      (algebraMap ℚ (residueLowerField N N) α) = (α : OtherField N)
    rw [← IsScalarTower.algebraMap_apply ℚ (residueLowerField N N) (OtherField N)]
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ (OtherField N)) α
  rw [hC]
  ring

end SkewCornerDescent.Matrix
