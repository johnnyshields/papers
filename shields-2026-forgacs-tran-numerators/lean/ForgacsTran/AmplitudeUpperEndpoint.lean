/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.DominanceSupplyClosure
import ForgacsTran.AmplitudeAlong

/-!
# `hWL` is false at `2 ≤ r` with the arc radius

`BranchSupply`'s amplitude group asks for the amplitude to vanish at **both**
endpoints.  At the lower one it does, for the reason BANK-71 records: the
principal pair collides there, the cofactor vanishes, and `ftAmp = -(B/0) = 0` by
the division convention.

At the upper one, with `2 ≤ r`, it does **not**, and this is not a convention
question.  The branch runs into the **origin** there, so `ftTauArc … (π/r) = 0`
and the branch point is `0`.  But the pencil does not vanish at `0` —
`Q(0) = c∏a_k ≠ 0` — so there is no collision, the cofactor is finite and nonzero,
and the amplitude is a finite nonzero number whenever `B(0) ≠ 0`.

The cofactor's value there is `(ftDen Q r z).coeff 1`, which at `2 ≤ r` is
`Q.coeff 1` — the spectral term `z t^r` reaches no lower than degree `r` — and
`Q.coeff 1 ≠ 0` for a pencil with positive zeros
(`DominanceSupplyClosure.ftRootPoly_coeff_one_ne_zero`).  So the obstruction is
uniform in `z`, and holds however the endpoint's spectral value is defined.

**Consequence.**  The general amplitude group is not a packaging exercise: at
`2 ≤ r` the supply's `hWL` cannot be discharged at this radius by any argument,
because it is false.  Either the binder is wrong for the `2 ≤ r` upper endpoint,
or the radius is — and the `r = 1` witnesses do not see it, because there the
upper endpoint is finite and carries a genuine collision (`cubicTau π = 1/2`,
where the denominator has a double root).

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `lem:amplitude-divisor`.

## Tags

amplitude, upper endpoint, division convention, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

/-- The cofactor at the origin is the pencil's degree-one coefficient. -/
theorem eval_zero_divByMonic_X (p : Polynomial ℂ) :
    (p /ₘ (X - C (0 : ℂ))).eval 0 = p.coeff 1 := by
  have hdecomp := modByMonic_add_div p (X - C (0 : ℂ))
  rw [modByMonic_X_sub_C_eq_C_eval p 0] at hdecomp
  have hc1 := congrArg (fun q => Polynomial.coeff q 1) hdecomp
  simp only [map_zero, sub_zero, coeff_add, coeff_C, coeff_X_mul] at hc1
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa using hc1

/-- **The amplitude does not vanish at the origin.**  Whatever spectral value is
used, at `2 ≤ r` the cofactor there is `Q.coeff 1`, which is nonzero for a pencil
with positive zeros — so the amplitude is `-(B(0)/Q.coeff 1)`. -/
theorem ftAmp_origin_ne_zero {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}
    (hn : 0 < n) (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r)
    (hB0 : B.eval 0 ≠ 0) (zv : ℂ) :
    ftAmp (ftRootPoly c a) B r zv 0 ≠ 0 := by
  have hcoeff : (ftDen (ftRootPoly c a) r zv).coeff 1 = (ftRootPoly c a).coeff 1 := by
    rw [ftDen, coeff_add, coeff_C_mul, coeff_X_pow]
    rw [if_neg (by omega : ¬ (1 = r))]
    ring
  have hne : (ftRootPoly c a).coeff 1 ≠ 0 := ftRootPoly_coeff_one_ne_zero hn hc ha
  rw [ftAmp, ftCofactor, eval_zero_divByMonic_X, hcoeff]
  simpa using div_ne_zero hB0 hne

/-- **`hWL` is unsatisfiable at `2 ≤ r` with the arc radius.**  The branch point at
the upper endpoint is the origin, and the amplitude there is nonzero. -/
theorem hWL_false_of_two_le_r {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    {B : Polynomial ℂ} (hn : 0 < n) (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r)
    (hB0 : B.eval 0 ≠ 0) :
    ftAmp (ftRootPoly c a) B r ((z (π / r) : ℝ) : ℂ)
      (ftPrincipal (ftTauArc a r (n - 1) x₁) (π / r)) ≠ 0 := by
  have hprin : ftPrincipal (ftTauArc a r (n - 1) x₁) (π / r) = 0 := by
    rw [ftPrincipal, ftTauArc_arc_end]
    simp
  rw [hprin]
  exact ftAmp_origin_ne_zero hn hc ha hr hB0 _

end ForgacsTran
