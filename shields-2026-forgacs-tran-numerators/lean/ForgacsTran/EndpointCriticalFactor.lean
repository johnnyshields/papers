/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointCollision

/-!
# The factorization of `E` at a branch endpoint

`ArcPhaseBound.exists_bound_im_logDeriv_ftAmp_endpoint` is the region bound at an
endpoint, and it takes the factorization of the critical polynomial as a binder:

  `ftCritical Q r = (X - C te) ^ m * H`,  `H(te) ≠ 0`.

This produces that binder at any nonzero real critical point, which is what a
branch endpoint is.  `Geometry.exists_ftCritical_factor` supplies the
factorization with `m = k - 1` for `k` the multiplicity of `te` in the pencil, and
`EndpointCollision.two_le_rootMultiplicity_ftDen_at_critical` supplies `k ≥ 2`
there — a collision is exactly what makes the multiplicity at least two, so the
one nontrivial input is free wherever the binder is wanted.

## `m` stays symbolic, and that is the point

The multiplicity is **not** computed.  At a repeated smallest zero it is `ρ - 1`
and at a simple one it is `1`, and the paper's `k = max{ρ, 2}` says the same
thing; none of that has to be decided, because the consumer takes `m` as a
parameter.  So one statement covers both multiplicities with no case split, and it
covers both ends of the arc as well: the hypothesis on the point is `t ≠ 0`, not
`0 < t`, so the negative critical point an `r = 1` upper endpoint sits at is
included.

## Main statements

* `exists_ftCritical_factor_at_critical` — the binder, at any nonzero real zero of
  `E`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `lem:amplitude-divisor`, `eq:W-endpoint-form`.

## Tags

critical polynomial, branch endpoint, multiplicity, factorization
-/

namespace ForgacsTran

open Polynomial

/-- **The endpoint factorization binder, at any nonzero real critical point.**
`m` is `k - 1` for `k` the multiplicity of `te` in the pencil at its own spectral
value, and it is left existential because nothing downstream reads the number. -/
theorem exists_ftCritical_factor_at_critical {n r : ℕ} {a : Fin n → ℝ} {c t : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r) (ht : t ≠ 0)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval t = 0) :
    ∃ (m : ℕ) (H : Polynomial ℂ),
      ftCritical (ftRootPoly c a) r = (X - C ((t : ℝ) : ℂ)) ^ m * H
        ∧ H.eval ((t : ℝ) : ℂ) ≠ 0 := by
  have hte : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hmult := two_le_rootMultiplicity_ftDen_at_critical ha hc hr ht hE
  have hP : ftDen (ftRootPoly c a) r
      ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at hmult
    simp [Polynomial.rootMultiplicity_zero] at hmult
  obtain ⟨H, hfac, hH0⟩ := exists_ftCritical_factor hr hte hP (by omega)
  exact ⟨_, H, hfac, hH0⟩

end ForgacsTran
