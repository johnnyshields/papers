/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Intersection with a purely transcendental extension

Algebraic input of `cor:stationary-field-descent` in `shields-2026-skew-coframe-rigidity.tex`:
if `x` is algebraically independent over a field `F`, and `k₀ ⊆ F`, then an element of `F` that
is a quotient of polynomials in `x` over `k₀` already lies in `k₀`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open MvPolynomial

variable {F E ι : Type*} [Field F] [Field E] [Algebra F E]

/-- If `z q(x) = p(x)` with `p, q` polynomials in an `F`-independent family `x` having
coefficients in `k₀ ⊆ F`, `q(x) ≠ 0` and `z ∈ F`, then `z ∈ k₀`. -/
theorem mem_of_mul_aeval_eq {x : ι → E} (hx : AlgebraicIndependent F x) (k₀ : Subfield F)
    (p q : MvPolynomial ι F) (hp : ∀ m, p.coeff m ∈ k₀) (hq : ∀ m, q.coeff m ∈ k₀)
    (hq0 : aeval x q ≠ 0) (z : F)
    (hz : algebraMap F E z * aeval x q = aeval x p) : z ∈ k₀ := by
  have hinj : Function.Injective (aeval (R := F) x) := hx
  have h0 : C z * q = p := by
    apply hinj
    simp [hz]
  have hq' : q ≠ 0 := by
    rintro rfl
    simp at hq0
  obtain ⟨m, hm⟩ : ∃ m, q.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    exact hq' (MvPolynomial.ext _ _ fun m => by simpa using h m)
  have hc := congrArg (fun r => r.coeff m) h0
  simp only [coeff_C_mul] at hc
  have : z = p.coeff m / q.coeff m := by
    rw [eq_div_iff hm]; exact hc
  rw [this]
  exact k₀.div_mem (hp m) (hq m)

end SkewCoframeRigidity
