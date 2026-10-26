/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.SignedCornerTransport

/-!
# Positive all-ones specializations

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:transport`).  Actual skew functions and products are positive
on sufficiently large all-ones alphabets.  This fixes the global transport sign.

Sorry-free.
-/

namespace SkewGluing

/-- Evaluation on an all-ones alphabet of size `n`. -/
noncomputable def onesSpecialization (n : ℕ) : Lambda →ₐ[ℚ] ℝ :=
  MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom n k (fun _ => (1 : ℝ)))

/-- Strict positivity once the all-ones alphabet is sufficiently large. -/
def PositiveAtOnes (f : Lambda) : Prop :=
  ∀ᶠ n in Filter.atTop, 0 < onesSpecialization n f

namespace PositiveAtOnes

protected theorem one : PositiveAtOnes (1 : Lambda) := by
  simp [PositiveAtOnes]

protected theorem mul {f g : Lambda} (hf : PositiveAtOnes f) (hg : PositiveAtOnes g) :
    PositiveAtOnes (f * g) := by
  filter_upwards [hf, hg] with n hfn hgn
  simpa only [map_mul] using mul_pos hfn hgn

protected theorem pow {f : Lambda} (hf : PositiveAtOnes f) (k : ℕ) :
    PositiveAtOnes (f ^ k) := by
  filter_upwards [hf] with n hfn
  simpa only [map_pow] using pow_pos hfn k

protected theorem prod {ι : Type*} (s : Finset ι) (f : ι → Lambda)
    (hf : ∀ i ∈ s, PositiveAtOnes (f i)) : PositiveAtOnes (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PositiveAtOnes.one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Positive polynomials cannot be negatives of each other. -/
theorem ne_neg {f g : Lambda} (hf : PositiveAtOnes f) (hg : PositiveAtOnes g) : f ≠ -g := by
  intro he
  have hb := hf.and hg
  obtain ⟨n, hn, hgn⟩ := hb.exists
  have hh := congrArg (onesSpecialization n) he
  rw [map_neg] at hh
  linarith

end PositiveAtOnes

/-- Every actual skew function has a positive sufficiently large all-ones specialization. -/
theorem positiveAtOnes_cellSchur {D : Diagram} (hD : IsSkew D) :
    PositiveAtOnes (cellSchur D hD) := by
  obtain ⟨N, hN⟩ := GluingCore.Plan.MarkFacts.exists_aeval_cellSchur_pos
    (show GluingCore.IsSkew D from hD)
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  rw [cellSchur_eq_gluing]
  exact hN n hn

namespace MarkedInner
variable {ω : MarkedInner}

/-- All four normalization factors are positive eventually, including empty marks. -/
theorem IsLegal.positiveAtOnes_normalFactors (h : ω.IsLegal) :
    PositiveAtOnes (ω.normalA h) ∧ PositiveAtOnes (ω.normalB h) ∧
      PositiveAtOnes (ω.normalC h) ∧ PositiveAtOnes (ω.normalTheta h) := by
  by_cases hW : ω.W.Nonempty
  · simp only [normalA, normalB, normalC, normalTheta, dite_eq_left hW,
      markA, hatMarkB, middleCofactor, capTheta]
    exact ⟨positiveAtOnes_cellSchur _, positiveAtOnes_cellSchur _, positiveAtOnes_cellSchur _,
      (positiveAtOnes_cellSchur _).mul (positiveAtOnes_cellSchur _)⟩
  · simp only [normalA, normalB, normalC, normalTheta, dite_eq_right hW]
    exact ⟨PositiveAtOnes.one, PositiveAtOnes.one, positiveAtOnes_cellSchur _, PositiveAtOnes.one⟩

/-- The complete right side of corner transport is positive on large alphabets. -/
theorem IsLegal.positiveAtOnes_transport (h : ω.IsLegal) {D : Diagram} (hD : IsSkew D) :
    PositiveAtOnes (ω.transportScalar h D * ω.childProduct h D hD) := by
  obtain ⟨ha, hb, hc, ht⟩ := h.positiveAtOnes_normalFactors
  unfold transportScalar childProduct
  apply (((ht.mul (ha.pow _)).mul (hb.pow _)).mul (hc.pow _)).mul
  apply PositiveAtOnes.prod
  intro C _
  exact positiveAtOnes_cellSchur _

end MarkedInner
end SkewGluing
