/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.PrimeOrder

/-!
# Component prime orders and maximum generator span

Supports `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `lem:alpha-row-candidate`).
The span criterion uses the proved actual connected-component Schur product.

Sorry-free.
-/

namespace SkewGluing
open SkewCornerDescent.Matrix

/-- A finite product cannot introduce a generator above the bounds on its factors. -/
theorem polynomialSpan_prod_le {ι : Type*} (s : Finset ι) (a : ι → Lambda) (n : ℕ)
    (ha : ∀ i ∈ s, polynomialSpan (a i) ≤ n) : polynomialSpan (∏ i ∈ s, a i) ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialSpan]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (polynomialSpan_mul_le _ _).trans (max_le (ha i (Finset.mem_insert_self _ _))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj)))

/-- Every actual component function divides the full skew function. -/
theorem component_cellSchur_dvd {D C : Diagram} (hD : IsSkew D) (hC : C ∈ edgeComponents D) :
    cellSchur C (isSkew_component hD hC) ∣ cellSchur D hD := by
  rw [cellSchur_eq_connected (isConnectedSkew_component hD hC)]
  unfold cellSchur
  exact Finset.dvd_prod_of_mem (a := ⟨C, hC⟩) (s := (edgeComponents D).attach)
    (fun S : {C // C ∈ edgeComponents D} => connectedSchur S.1 (isConnectedSkew_component hD S.2))
    (Finset.mem_attach _ ⟨C, hC⟩)

/-- Excluding every high-span connected prime forces the entire skew function below the bound. -/
theorem polynomialSpan_cellSchur_lt_of_orders {D : Diagram} (hD : IsSkew D) {u : ℕ}
    (hu : 0 < u)
    (ho : ∀ f : Lambda, Prime f → u ≤ polynomialSpan f → primeOrder f (cellSchur D hD) = 0) :
    polynomialSpan (cellSchur D hD) < u := by
  classical
  have hb (C : {C // C ∈ edgeComponents D}) :
      polynomialSpan (connectedSchur C.1 (isConnectedSkew_component hD C.2)) ≤ u - 1 := by
    have hc := isConnectedSkew_component hD C.2
    have hf : Irreducible (cellSchur C.1 hc.1) := by
      simpa only [map_integralCellSchur] using irreducible_integralCellSchur (K := ℚ) hc
    have hlt : polynomialSpan (cellSchur C.1 hc.1) < u := by
      by_contra hn
      have hz := ho _ hf.prime (Nat.le_of_not_gt hn)
      exact ((primeOrder_eq_zero_iff hf.prime (cellSchur_ne_zero D hD)).mp hz)
        (component_cellSchur_dvd hD C.2)
    rw [← cellSchur_eq_connected hc]
    omega
  have hs : polynomialSpan (cellSchur D hD) ≤ u - 1 :=
    polynomialSpan_prod_le (edgeComponents D).attach _ _ fun C _ => hb C
  omega

end SkewGluing
