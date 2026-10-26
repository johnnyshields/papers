/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.TransportPowers

/-!
# Corner transport before positivity fixes the sign

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:transport`).  The normalized coefficient comparison and every
component's geometric image compose and cancel, leaving exactly the stated product
up to its global sign.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω : MarkedInner}

/-- The normalization that remains after cancelling the composition prefactor. -/
noncomputable def transportScalar (ω : MarkedInner) (h : ω.IsLegal) (D : Diagram) : Lambda :=
  ω.normalTheta h *
    ω.normalA h ^ ((D.image Prod.fst).card - 1 - ((diagramInterior D).image Prod.fst).card) *
    ω.normalB h ^ ((D.image Prod.snd).card - 1 - ((diagramInterior D).image Prod.snd).card) *
    ω.normalC h ^ (span D - span (diagramInterior D))

/-- The actual geometric child product, including single-cell children. -/
noncomputable def childProduct (ω : MarkedInner) (h : ω.IsLegal)
    (D : Diagram) (hD : IsSkew D) : Lambda :=
  ∏ C ∈ (edgeComponents (diagramInterior D)).attach,
    cellSchur (ω.compose C.1)
      (h.connected_compose (isConnectedSkew_component hD.interior C.2)).1

/-- Every composition prefactor is nonzero. -/
theorem IsLegal.compositionPrefactor_ne_zero (h : ω.IsLegal) (D : Diagram) :
    ω.compositionPrefactor h D ≠ 0 := by
  obtain ⟨ha, hb, hc, _⟩ := h.normal_factors_ne_zero
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)) (pow_ne_zero _ hc)

/-- Squaring erases a global sign without using positivity or a characteristic assumption. -/
theorem sign_pow_sq (n : ℕ) : ((-1 : Lambda) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]

/-- The actual corner cofactor is the displayed transport product or its negative. -/
theorem IsLegal.corner_transport_signed (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) (M L : ℕ+)
    (hM : (M : ℕ) = span D) (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) :
    cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior =
        ω.transportScalar h D * ω.childProduct h D hD.1 ∨
      cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior =
        -(ω.transportScalar h D * ω.childProduct h D hD.1) := by
  obtain ⟨sign, hs⟩ := h.normalized_cofactor_transport hD M L hM hL
  obtain ⟨signI, hI⟩ := h.modifiedCompositionMap_component_product hD.1.interior
  rw [hI] at hs
  have he := congrArg (fun f : Lambda => f ^ 2) hs
  simp only [mul_pow, sign_pow_sq, one_mul] at he
  rw [hM] at he
  dsimp only [compositionPrefactor] at he
  let P := ω.compositionPrefactor h D
  let F := cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior
  let G := ω.childProduct h D hD.1
  let Q := ω.normalA h ^ (span D - 1) * ω.normalTheta h * ω.normalC h ^ span D *
    ω.normalB h ^ (span D - 1) * ω.compositionPrefactor h (diagramInterior D)
  have he' : (P * F) ^ 2 = (Q * G) ^ 2 := by
    dsimp [P, F, Q, G, compositionPrefactor, childProduct]
    convert he using 1 <;> ring
  have hQ : P * ω.transportScalar h D = Q := h.transport_power_identity hD hcard
  have hsq : F ^ 2 = (ω.transportScalar h D * G) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (h.compositionPrefactor_ne_zero D))
    change P ^ 2 * F ^ 2 = P ^ 2 * (ω.transportScalar h D * G) ^ 2
    rw [← mul_pow, ← mul_pow, he']
    exact congrArg (fun f : Lambda => f ^ 2) (by rw [← hQ, mul_assoc])
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

end SkewGluing.MarkedInner
