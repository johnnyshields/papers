/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.TransportFactors

/-!
# Discrete interiors and powers of the first generator

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `def:discrete-interior`, `eq:discrete-polynomial`).
The geometric singleton-component condition is equivalent to the stated cofactor power.

Sorry-free.
-/

namespace SkewGluing
open SkewCornerDescent.Matrix MvPolynomial

/-- All nonempty southeast-interior components are single cells. -/
def HasDiscreteInterior (D : Diagram) : Prop :=
  ∀ C ∈ edgeComponents (diagramInterior D), C.card = 1

/-- Singleton component functions give the first-generator power for a discrete interior. -/
theorem cellSchur_interior_of_discrete {D : Diagram} (hD : IsConnectedSkew D)
    (hd : HasDiscreteInterior D) :
    cellSchur (diagramInterior D) hD.1.interior = X (1 : ℕ+) ^ (D.card - span D) := by
  classical
  have hc : (diagramInterior D).card = (edgeComponents (diagramInterior D)).card := by
    rw [card_eq_sum_edgeComponents]
    calc
      (∑ C ∈ edgeComponents (diagramInterior D), C.card) =
          ∑ _C ∈ edgeComponents (diagramInterior D), 1 :=
        Finset.sum_congr rfl fun C hC => hd C hC
      _ = _ := by simp
  have hp : cellSchur (diagramInterior D) hD.1.interior =
      ∏ _C ∈ (edgeComponents (diagramInterior D)), (X (1 : ℕ+) : Lambda) := by
    rw [cellSchur_eq_gluing]
    unfold GluingCore.cellSchur
    apply Finset.prod_congr rfl
    intro C hC
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hd C hC)
    rw [hx, GluingCore.connectedSchur_singleton]
  rw [Finset.prod_const, ← hc] at hp
  have ha := card_eq_span_add_interior hD.1
  have he : D.card - span D = (diagramInterior D).card := by omega
  simpa only [he] using hp

/-- A first-generator cofactor cannot contain a component with span at least two. -/
theorem discrete_of_cellSchur_interior {D : Diagram} (hD : IsConnectedSkew D)
    (he : cellSchur (diagramInterior D) hD.1.interior = X (1 : ℕ+) ^ (D.card - span D)) :
    HasDiscreteInterior D := by
  classical
  intro C hC
  have hc := isConnectedSkew_component hD.1.interior hC
  have hdvd : cellSchur C hc.1 ∣ cellSchur (diagramInterior D) hD.1.interior := by
    rw [cellSchur_eq_gluing, cellSchur_eq_gluing]
    rw [GluingCore.cellSchur_of_isConnectedSkew hc,
      ← GluingCore.connectedSchur_of_isConnectedSkew hc]
    exact Finset.dvd_prod_of_mem GluingCore.connectedSchur hC
  have hne : cellSchur (diagramInterior D) hD.1.interior ≠ 0 := by
    rw [cellSchur_eq_gluing]
    exact GluingCore.Plan.MarkFacts.cellSchur_ne_zero hD.1.interior
  have hb := polynomialSpan_le_of_dvd hne hdvd
  rw [he] at hb
  have hs := polynomialSpan_pow_le (X (1 : ℕ+) : Lambda) (D.card - span D)
  have hx : polynomialSpan (X (1 : ℕ+) : Lambda) = 1 := by
    simp [polynomialSpan, MvPolynomial.vars_X]
  rw [hx] at hs
  rw [polynomialSpan_cellSchur hc] at hb
  have hpos := Finset.card_pos.mpr hc.2.1
  by_contra hn
  have ht := two_le_span_of_two_le_card hc (show 2 ≤ C.card by omega)
  omega

/-- The discrete-interior criterion is intrinsic to the connected Schur function. -/
theorem discreteInterior_iff {D : Diagram} (hD : IsConnectedSkew D) :
    HasDiscreteInterior D ↔
      cellSchur (diagramInterior D) hD.1.interior = X (1 : ℕ+) ^ (D.card - span D) :=
  ⟨cellSchur_interior_of_discrete hD, discrete_of_cellSchur_interior hD⟩

end SkewGluing
