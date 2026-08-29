/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.TauArcAt
import ForgacsTran.FTBranchGap
import ForgacsTran.PencilIndex

/-!
# The lower endpoint of the viewing arc at a simple smallest zero

`BranchSupplyGeometry` supplies the collar's endpoint binders at a **repeated**
smallest zero: there the branch radius runs into `a_i` itself, and the one-sided
derivative of `γ = τe^{iθ}` at `0` is `-a_i cot(π/ρ) + a_i i`, proved under
`2 ≤ ρ`.  This module is about the other multiplicity, and the point of it is
that `ρ = 1` is not that statement with a different constant — it is a statement
about a **different point**.

At a simple smallest zero the radius does not reach `a_i` at all.
`FTBranchGap.exists_tendsto_ftTau_mem_first_gap` places its limit at a value `L`
with `a_i < L < a_j` for every other zero, and `L` is a zero of `E = XQ' - rQ`.
So:

* the arc extension carrying `x₁ = a_i` is **discontinuous** at `0` when `ρ = 1`
  — not merely unproved there, but false, since its value at `0` is `a_i` and its
  limit from the arc is `L ≠ a_i`;
* the extension carrying `x₁ = L` is continuous at `0`;
* the endpoint is **not a collision with a zero of the pencil**: `L` misses every
  `a_k`, so a chord `dγ/(γ - a_k)` has no singularity there at all.

## The `ρ ≥ 2` slope formula returns junk at `ρ = 1`, and the junk looks like a tangent

`cot(π/ρ)` has a pole at `ρ = 1`, and `x / 0 = 0` turns that pole into `0`, so
`-a_i cot(π/ρ) + a_i i` evaluates at `ρ = 1` to `a_i i`.  That is a nonzero
vector of exactly the shape an endpoint tangent takes, it is perpendicular to the
real axis as the true tangent is, and nothing about it signals that the formula
does not apply.  The true endpoint tangent at `ρ = 1` is `L i`, and `a_i < L`, so
the junk is the *wrong object* rather than a wrong number.
`endpointSlope_rho_one` records the evaluation so that no later pass reads the
`ρ ≥ 2` formula as covering `ρ = 1` by continuity.

## Main statements

* `tendsto_ftTauArcAt_nhdsGT_zero` — the extension inherits the branch's
  one-sided limit whatever endpoint values it carries.
* `continuousWithinAt_ftTauArcAt_Ici_zero`,
  `not_continuousWithinAt_ftTauArcAt_Ici_zero` — the endpoint value that works
  and the fact that no other one does.
* `exists_lower_endpoint_of_simple` — the endpoint value at `ρ = 1`, with the
  gap clause for *every* other index rather than for one.
* `lower_endpoint_ne_root_of_simple`, `ftPrincipal_lower_endpoint_ne_root` — the
  endpoint misses every zero of the pencil.
* `not_continuousWithinAt_ftTauArcAt_min_of_simple` — the `ρ ≥ 2` endpoint value
  is refuted at `ρ = 1`.
* `endpointSlope_rho_one` — the `ρ ≥ 2` slope formula at `ρ = 1`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `thm:FT-geometry`, `lem:principal-endpoint-regularity`.
* `Forgacs2017RationalDenominator`, Proposition 1 and Fig. 5.

## Tags

branch endpoint, simple zero, first gap, discontinuity, Forgacs-Tran
-/

namespace ForgacsTran

open Real Set Filter Topology

/-! ### The endpoint value, for an arbitrary limit -/

section Generic

variable {n : ℕ} (a : Fin n → ℝ) (r l : ℕ)

/-- **The extension inherits the branch's one-sided limit.**  On the arc's own
side of `0` it *is* the branch radius, so neither endpoint value it carries can
affect the limit — only whether that limit is the value it takes at `0`. -/
theorem tendsto_ftTauArcAt_nhdsGT_zero (x₁ aEnd : ℝ) {L : ℝ} (hr : 0 < π / r)
    (hL : Tendsto (ftTau a r l) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (ftTauArcAt a r l x₁ aEnd) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  refine hL.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with θ hθ
  exact (ftTauArcAt_agree a r l x₁ aEnd hθ.1 hθ.2).symm

/-- **With the endpoint value the branch actually has, the extension is
continuous at `0`.** -/
theorem continuousWithinAt_ftTauArcAt_Ici_zero (aEnd : ℝ) {L : ℝ} (hr : 0 < π / r)
    (hL : Tendsto (ftTau a r l) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ContinuousWithinAt (ftTauArcAt a r l L aEnd) (Ici 0) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt,
    ftTauArcAt_zero a r l L aEnd hr]
  exact tendsto_ftTauArcAt_nhdsGT_zero a r l L aEnd hr hL

/-- **And no other endpoint value is continuous there.**  This is what makes the
`ρ = 1` case a different statement rather than the same one with a different
constant: a binder asking for regularity at `0` of the extension carrying the
wrong `x₁` is unsatisfiable, so it cannot be discharged by any argument. -/
theorem not_continuousWithinAt_ftTauArcAt_Ici_zero {x₁ aEnd L : ℝ} (hr : 0 < π / r)
    (hL : Tendsto (ftTau a r l) (𝓝[>] (0 : ℝ)) (𝓝 L)) (hne : x₁ ≠ L) :
    ¬ ContinuousWithinAt (ftTauArcAt a r l x₁ aEnd) (Ici 0) 0 := by
  intro hc
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt,
    ftTauArcAt_zero a r l x₁ aEnd hr] at hc
  exact hne (tendsto_nhds_unique hc (tendsto_ftTauArcAt_nhdsGT_zero a r l x₁ aEnd hr hL))

end Generic

/-! ### At a simple smallest zero -/

/-- **The lower endpoint at a simple smallest zero.**
`FTBranchGap.exists_tendsto_ftTau_mem_first_gap` places the limit above `a_i` and
below one named `a_j`; the gap clause holds for *every* other index, since the
limit is the same object each time and `lt_of_tendsto_ftTau` takes it as an
input rather than producing it. -/
theorem exists_lower_endpoint_of_simple {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, a i < L ∧ (∀ j, j ≠ i → L < a j) ∧
      Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn2
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  obtain ⟨L, hLi, -, hLt, hLe⟩ :=
    exists_tendsto_ftTau_mem_first_gap hn2 ha hr (Ne.symm hj₀) hmin hsimple hc
  exact ⟨L, hLi, fun j hj => lt_of_tendsto_ftTau hn2 ha hr (Ne.symm hj) hLt hLi, hLt, hLe⟩

/-- **The endpoint misses every zero of the pencil.**  It is above the smallest
and below all the others, so there is no index it can equal.  At `ρ ≥ 2` the
endpoint *is* a zero of `Q`; at `ρ = 1` it is not, which is why the two ends of
the multiplicity split need different chord estimates and not the same one at a
different point. -/
theorem lower_endpoint_ne_root_of_simple {n : ℕ} {a : Fin n → ℝ} {i : Fin n} {L : ℝ}
    (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j) (k : Fin n) : L ≠ a k := by
  rcases eq_or_ne k i with rfl | hk
  · exact ne_of_gt hLi
  · exact ne_of_lt (hgap k hk)

/-- The same, at the branch point itself: `γ(0) = L` is not a zero of the pencil. -/
theorem ftPrincipal_lower_endpoint_ne_root {n : ℕ} {a : Fin n → ℝ} (r l : ℕ) {i : Fin n}
    {L aEnd : ℝ} (hr : 0 < π / r) (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j) (k : Fin n) :
    ftPrincipal (ftTauArcAt a r l L aEnd) 0 ≠ ((a k : ℝ) : ℂ) := by
  have hval : ftPrincipal (ftTauArcAt a r l L aEnd) 0 = ((L : ℝ) : ℂ) := by
    rw [ftPrincipal, ftTauArcAt_zero a r l L aEnd hr]
    simp
  rw [hval]
  exact fun h => lower_endpoint_ne_root_of_simple hLi hgap k (by exact_mod_cast h)

/-- **The `ρ ≥ 2` endpoint value is refuted at `ρ = 1`.**  The extension carrying
`x₁ = a_i` is discontinuous at `0` there, so the collar binders written against
it are not open questions at `ρ = 1` — they are unsatisfiable. -/
theorem not_continuousWithinAt_ftTauArcAt_min_of_simple {n r : ℕ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) {c : ℝ} (hc : 0 < c) (aEnd : ℝ) :
    ¬ ContinuousWithinAt (ftTauArcAt a r (n - 1) (a i) aEnd) (Ici 0) 0 := by
  have hrpos : (0 : ℝ) < π / r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    exact div_pos pi_pos hr0
  obtain ⟨L, hLi, -, hLt, -⟩ := exists_lower_endpoint_of_simple hn2 ha hr hmin hsimple hc
  exact not_continuousWithinAt_ftTauArcAt_Ici_zero a r (n - 1) hrpos hLt (ne_of_lt hLi)

/-- **The `ρ ≥ 2` slope formula at `ρ = 1`.**  `sin(π/1) = 0`, so `x / 0 = 0`
collapses the cotangent and the collision value `-x cot(π/ρ) + x i` returns
`x i`.  The return is a well-formed nonzero tangent vector, perpendicular to the
real axis exactly as a true endpoint tangent is, so no sanity check on the value
can detect that the formula has left its range of validity — the structural form
of the division trap rather than the numeric one. -/
theorem endpointSlope_rho_one (x : ℝ) :
    ((-(x * Real.cos (π / ((1 : ℕ) : ℝ)) / Real.sin (π / ((1 : ℕ) : ℝ))) : ℝ) : ℂ)
      + ((x : ℝ) : ℂ) * Complex.I = ((x : ℝ) : ℂ) * Complex.I := by
  rw [pi_div_natCast_one, Real.sin_pi]
  simp

end ForgacsTran
