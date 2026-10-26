/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.DerivationConstantField

/-!
# Constants in a simple rational extension

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A constant rational fraction in one moving generator lies in the original
coefficient field. This identifies actual coefficients, not a renamed
derivative. Sorry-free.
-/

namespace SkewCornerDescent
open Polynomial

/-- In a simple rational extension, the constants of a moving-variable
partial derivative are exactly the original coefficient field. -/
theorem simple_extension_derivation_constants {E : Type*} [Field E] [Algebra ℚ E]
    {m : Module ℚ E} [CharZero E] (δ : @Derivation ℚ E E _ _ _ _ _ m) (B : Subfield E)
    (hB : ∀ s : B, δ (s : E) = 0) (x f : E) (hx : δ x ≠ 0)
    (hf : f ∈ IntermediateField.adjoin B {x}) (hδ : δ f = 0) : f ∈ B := by
  classical
  by_cases hf0 : f = 0
  · rw [hf0]
    exact B.zero_mem
  let S := derivationConstantField δ
  let ι : B →+* S :=
    { toFun := fun s => ⟨s, hB s⟩
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let ff : S := ⟨f, hδ⟩
  obtain ⟨p, q, hrep⟩ := (IntermediateField.mem_adjoin_simple_iff B f).mp hf
  have hq : q ≠ 0 := by
    intro he
    rw [he, map_zero, div_zero] at hrep
    exact hf0 hrep
  have heval (p : Polynomial B) :
      Polynomial.aeval x (p.map ι) = Polynomial.aeval x p := by
    change Polynomial.eval₂ S.subtype x (p.map ι) = Polynomial.eval₂ B.subtype x p
    rw [Polynomial.eval₂_map]
    rfl
  have hroot : Polynomial.aeval x (p.map ι - Polynomial.C ff * q.map ι) = 0 := by
    rw [map_sub, map_mul, Polynomial.aeval_C, heval, heval]
    change Polynomial.aeval x p - f * Polynomial.aeval x q = 0
    have hqeval : Polynomial.aeval x q ≠ 0 := by
      intro he
      rw [he, div_zero] at hrep
      exact hf0 hrep
    rw [hrep, div_mul_cancel₀ _ hqeval, sub_self]
  have hpoly : p.map ι - Polynomial.C ff * q.map ι = 0 :=
    (transcendental_iff_injective.mp
      (transcendental_over_derivation_constants δ x hx)) (hroot.trans (map_zero _).symm)
  have hc := congrArg (fun t : Polynomial S => ((t.coeff q.natDegree : S) : E)) hpoly
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map,
    Polynomial.coeff_zero, Subfield.coe_sub, Subfield.coe_mul, ZeroMemClass.coe_zero] at hc
  change ((p.coeff q.natDegree : B) : E) - f * ((q.coeff q.natDegree : B) : E) = 0 at hc
  have hqn : ((q.coeff q.natDegree : B) : E) ≠ 0 := by
    exact B.subtype.injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hfEq : f = ((p.coeff q.natDegree : B) : E) / ((q.coeff q.natDegree : B) : E) :=
    (eq_div_iff hqn).mpr (sub_eq_zero.mp hc).symm
  rw [hfEq]
  exact B.div_mem (p.coeff q.natDegree).property (q.coeff q.natDegree).property

end SkewCornerDescent
