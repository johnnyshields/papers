/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPlaneClassSupport
import SkewCornerDescent.Matrix.OriginalRationalClassTransfer
import SkewCornerDescent.Matrix.OriginalMaximalBinReciprocal
import SkewCornerDescent.CyclicDetectors

/-!
# The full supplied rational function and exact actual class sums

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `cor:many-active`).
The actual monic-plane class support is reindexed by the produced closure orientation.
Full rational-series transfer and every signed class sum use that same support and
those same actual virtual responses. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

noncomputable local instance rationalClassSumsRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact standing residue dependence supplies a full rational class packet and
identifies its signed virtual-response sums with the unchanged literal class sums. -/
theorem originalWindow_rational_class_sums {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a : ℕ) (hab : a < b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ ε δ : ℤ, ∃ support : Finset ℚ, ∃ e : ℚ → ℤ,
      (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      (∀ α, α ∈ support ↔ e α ≠ 0) ∧ (∑ α ∈ support, e α) = ((b - a : ℕ) : ℤ) ∧
      (c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (ε : OtherField c.top) * ∏ α ∈ support,
          (c.residueMap Q.schur / c.residueMap P.schur ^ 2 - (α : OtherField c.top)) ^ e α) ∧
      c.originalRationalFunctionSeries P Q p₀ p₁ = c.originalRationalPrefactor P Q support id e ε ∧
      PowerSeries.constantCoeff (c.originalRationalFunctionSeries P Q p₀ p₁) ≠ 0 ∧
      (∀ H : OtherField c.top → OtherField c.top,
        (∑ X : c.OriginalResponseClass P,
          (c.originalResponseClassExponent P W a b X : OtherField c.top) * H X.val) =
          ∑ α ∈ support, (e α : OtherField c.top) *
            H (c.originalVirtualCentralResponse P Q middle α)) ∧
      CyclicWindows.closureLabelSum (c.originalResponseClassExponent P W a b)
        (Subtype.val : c.OriginalResponseClass P → OtherField c.top) ≠ 0 := by
  classical
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq' hcutLq' hC
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  obtain ⟨ε, oldsupport, olde, hε, hsupport, hdegree, hweights, hfactor, hsums⟩ :=
    c.originalWindow_plane_class_support P W Q q v z w hwindow hW hQ hcutq' hcutLq' hC
      hmax hmaxW Λ b a (b - a) (by omega) hKU hKW p₀ p₁ hpq hdep
  have hcQ := originalHorizontalClosure_profile_selected_count (hD := hD) P Q w hQ
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by omega⟩
  obtain ⟨δ, hδ, hquot⟩ := c.originalHorizontalClosure_residue_quotient P Q w hQ hB hmax
  have hcoord : c.regularResidue (c.originalHessenbergResponse Q middle middle) /
      c.originalTrueCapProduct P =
        (δ : OtherField c.top) * (c.residueMap Q.schur / c.residueMap P.schur ^ 2) := by
    rcases hδ with h | h
    · rw [h] at hquot ⊢
      simpa only [Int.cast_one, one_mul] using hquot.symm
    · rw [h] at hquot ⊢
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_div] at hquot ⊢
      linear_combination hquot
  obtain ⟨ε', support, e, hε', he, hdegree', hexp, hs, hfactor'⟩ :=
    signedRationalFactors_change_coordinate _ _ _ ε δ oldsupport olde (b - a) hε hδ
      (fun α hα => (hsupport α).mp hα) hdegree hfactor hcoord
  have hnewSupport : ∀ α, α ∈ support ↔ e α ≠ 0 := by
    intro α
    rw [hs α, hexp α, hsupport]
  have htrans := c.originalHorizontalClosure_residue_transcendental P Q w hQ hB hmax
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  have hW0 := c.originalSchur_residue_ne_zero W hC hmaxW
  have hden : p₁ ≠ 0 := by
    intro hz
    apply (div_ne_zero (pow_ne_zero a hf0) (pow_ne_zero b hW0))
    rw [hdep, hz, map_zero, div_zero]
  let γ := c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2
  have hγ : PowerSeries.constantCoeff γ = c.residueMap Q.schur / c.residueMap P.schur ^ 2 := by
    simp only [γ, map_mul, map_pow, PowerSeries.constantCoeff_inv,
      c.normalPolynomialSeries_constant, div_eq_mul_inv, inv_pow]
  have hrepresentation := signedRational_series_transfer
    (c.residueMap Q.schur / c.residueMap P.schur ^ 2) htrans γ hγ
    p₀ p₁ hden ε' support e (hdep.symm.trans hfactor')
  have hρ : c.originalRationalFunctionSeries P Q p₀ p₁ =
      c.originalRationalPrefactor P Q support id e ε' := by
    simpa only [originalRationalFunctionSeries, originalRationalPrefactor, γ, id_eq] using
      hrepresentation
  have hρ0 : PowerSeries.constantCoeff (c.originalRationalFunctionSeries P Q p₀ p₁) ≠ 0 := by
    rw [hρ]
    exact c.originalRationalPrefactor_constant_ne_zero P Q w hQ hB hmax support id e ε' hε'
  have hshift := c.originalVirtualCentralResponse_eq_oriented_cap P Q w hQ hB hmax δ hcoord
  dsimp only at hfactor hfactor' hsums hshift ⊢
  have hclassSums (H : OtherField c.top → OtherField c.top) :
      (∑ X : c.OriginalResponseClass P,
        (c.originalResponseClassExponent P W a b X : OtherField c.top) * H X.val) =
        ∑ α ∈ support, (e α : OtherField c.top) *
          H (c.originalVirtualCentralResponse P Q middle α) := by
    rw [hsums H]
    have hc := signed_support_sum_coordinate δ hδ oldsupport support hs
      (fun α => (olde α : OtherField c.top) * H
        (c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (α : OtherField c.top) * c.originalTrueCapProduct P))
    rw [hc]
    apply Finset.sum_congr rfl
    intro α _
    rw [hexp α, hshift α, Rat.cast_mul, Rat.cast_intCast]
  refine ⟨ε', δ, support, e, hε', hδ, hnewSupport, hdegree', hfactor',
    hρ, hρ0, hclassSums, ?_⟩
  unfold CyclicWindows.closureLabelSum
  rw [hclassSums (fun x => x⁻¹)]
  simpa only [div_eq_mul_inv] using c.originalVirtual_signed_reciprocal_ne_zero
    P Q w hQ hB hmax support e (by rw [hdegree']; exact_mod_cast (Nat.sub_pos_of_lt hab).ne')

end SkewCornerDescent.Matrix.SelectedCoordinate
