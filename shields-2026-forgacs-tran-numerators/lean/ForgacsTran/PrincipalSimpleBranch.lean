/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PrincipalSimple
import ForgacsTran.FTGeometryAssembly

/-!
# `eq:principal-simple` in the shapes the dominance chain asks for

`PrincipalSimple.eval_derivative_ftDen_ftRootPoly_ne_zero` proves the pencil has
only simple zeros off the real axis.  The dominance chain asks for that fact at
the two named points `t_±(θ)` of `eq:principal-pair`, quantified over a parameter
interval, and calls the two halves `hsp` and `hsm`.  This module states it there.

Two grades of statement, and the difference is which data is assumed:

* the `_of_root` forms take arbitrary `τ, z : ℝ → ℝ` and the root property as a
  hypothesis, which is exactly what `DominanceFTSupply.interior_remainder_uniform` and
  `EndpointDominance.interior_remainder_bound` already carry beside `hsp`;
* `ft_principal_simple_at_branch` takes the branch's own `ftTau` and `ftBranchZ`,
  where `FTGeometryAssembly.ft_branch_root_and_pos` discharges both the root
  property and positivity, so nothing is assumed beyond the admissible class.

The parameter range is the whole viewing arc, at every `r ≥ 1`: the argument
sees only that the point is off the real axis, so neither endpoint behaviour nor
the minimum-modulus gap enters.

## Containment

`ft_principal_simple_at_branch` relates `derivative (ftDen (ftRootPoly c a) r
(ftBranchZ …))` and `ftPrincipal (ftTau …) θ`.  Its hypotheses are `0 < n`,
`∀ k, 0 < a k`, `c ≠ 0`, `1 ≤ r`, `2 ≤ n ∨ 2 ≤ r` and `θ ∈ Ioo 0 (π/r)`: not one
of them mentions the pencil's derivative, and none mentions `ftPrincipal` at all.
The `_of_root` forms add `hroot`, a vanishing statement about `ftDen` itself,
which is satisfiable at every angle of the arc — `ft_branch_root_and_pos` is the
witness, and instantiating the `_of_root` forms at it is how
`ft_principal_simple_at_branch` is proved.

## Main statements

* `ftPrincipal_simple_of_root`, `ftArcPoint_simple_of_root` — the point forms of
  `hsp` and `hsm`.
* `ftPrincipal_conj_simple_of_root` — `hsm` written at
  `(starRingEnd ℂ) (ftPrincipal τ θ)`, the spelling `FTGeometryAssembly` uses.
* `ftPrincipal_simple_uniform`, `ftArcPoint_simple_uniform` — the same quantified
  over `Icc lo hi`, which is the binder shape of `interior_remainder_uniform`.
* `ft_principal_simple_at_branch` — `eq:principal-simple` at the constructed
  branch, with no hypothesis beyond the admissible class.

## References

Formalizes `eq:principal-simple` of
`../shields-2026-forgacs-tran-numerators.tex`, «The principal amplitude and its
phase» (`subsec:principal-amplitude`).

## Tags

simple zero, principal pair, dominance
-/

namespace ForgacsTran

open Real Set Polynomial Complex

/-! ### The point forms

`PrincipalSimple.eval_derivative_ftDen_ftRootPoly_ne_zero` is the theorem; everything
in this section is that one fact re-bound.  The three below carry it to the two named
points of `eq:principal-pair` and to the `starRingEnd` spelling
`FTGeometryAssembly` writes `t_-` in. -/

/-- **`hsp` at one angle.**  `t_+(θ) = τ(θ)e^{iθ}` sits in the open upper half
plane whenever `τ(θ) > 0` and `0 < θ < π`, so a zero there is simple. -/
theorem ftPrincipal_simple_of_root {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z τ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ) (hθ : θ ∈ Ioo 0 π)
    (hroot : (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) :
    (derivative (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0 :=
  eval_derivative_ftDen_ne_zero_of_arg hn ha hc hr hτ hθ hroot

/-- **`hsm` at one angle.**  The conjugate point `t_-(θ) = τ(θ)e^{-iθ}` sits in
the open lower half plane under the same hypotheses. -/
theorem ftArcPoint_simple_of_root {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z τ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ) (hθ : θ ∈ Ioo 0 π)
    (hroot : (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) = 0) :
    (derivative (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ))).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0 :=
  eval_derivative_ftDen_conj_ne_zero_of_arg hn ha hc hr hτ hθ hroot

/-- **`hsm`, in the `starRingEnd` spelling.**  `FTGeometryAssembly` writes `t_-`
as the conjugate of `t_+`; this is `ftArcPoint_simple_of_root` there. -/
theorem ftPrincipal_conj_simple_of_root {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z τ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ) (hθ : θ ∈ Ioo 0 π)
    (hroot : (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval
      ((starRingEnd ℂ) (ftPrincipal τ θ)) = 0) :
    (derivative (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ))).eval
      ((starRingEnd ℂ) (ftPrincipal τ θ)) ≠ 0 := by
  rw [conj_ftPrincipal] at hroot ⊢
  exact ftArcPoint_simple_of_root hn ha hc hr hτ hθ hroot

/-! ### The same, quantified over a parameter interval

Pure re-binding: `interior_remainder_uniform` and `EndpointDominance.interior_remainder_bound`
carry `hsp` and `hsm` under `∀ θ, lo ≤ θ → θ ≤ hi`, so the point forms are wrapped rather
than reproved.  No hypothesis is added and none is dropped. -/

/-- **`hsp`, in `interior_remainder_uniform`'s binder shape.** -/
theorem ftPrincipal_simple_uniform {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z τ : ℝ → ℝ} {lo hi : ℝ}
    (hτ : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → 0 < τ θ)
    (harc : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → θ ∈ Ioo 0 π)
    (hroot : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) :
    ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (derivative (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0 :=
  fun θ h1 h2 => ftPrincipal_simple_of_root hn ha hc hr (hτ θ h1 h2) (harc θ h1 h2)
    (hroot θ h1 h2)

/-- **`hsm`, in `interior_remainder_uniform`'s binder shape.** -/
theorem ftArcPoint_simple_uniform {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {r : ℕ} (hr : 1 ≤ r) {z τ : ℝ → ℝ} {lo hi : ℝ}
    (hτ : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → 0 < τ θ)
    (harc : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → θ ∈ Ioo 0 π)
    (hroot : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval
        (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) = 0) :
    ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (derivative (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ))).eval
        (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0 :=
  fun θ h1 h2 => ftArcPoint_simple_of_root hn ha hc hr (hτ θ h1 h2) (harc θ h1 h2)
    (hroot θ h1 h2)

/-! ### At the constructed branch -/

/-- **`eq:principal-simple` at the constructed branch, unconditionally.**  Both
members of the principal pair are simple zeros of `Q + z(θ)t^r` at every angle of
the viewing arc, for every `r ≥ 1`, with no hypothesis beyond the admissible
class.  `FTGeometryAssembly.ft_branch_root_and_pos` supplies the root property
and `τ(θ) > 0`, and the arc sits inside `(0, π)` by `ftArc_subset`. -/
theorem ft_principal_simple_at_branch {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    (derivative (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))).eval
        (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0
      ∧ (derivative (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))).eval
        ((starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ)) ≠ 0 := by
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  have hτ : 0 < ftTau a r (n - 1) θ := hpos θ hθ
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hrp := hroot θ hθ
  refine ⟨ftPrincipal_simple_of_root hn ha hc hr hτ hθπ hrp,
    ftPrincipal_conj_simple_of_root hn ha hc hr hτ hθπ ?_⟩
  exact ftPrincipal_conj_eval_eq_zero (hasRealCoeffs_ftRootPoly c a) hrp

/-! ### Why the admissible class excludes `n = r = 1`

Not about simplicity of a zero: this is the solvability of the branch equation, and it
belongs with `FTBranchAngle.lt_ftAngle`, the single fact it consumes.  It sits here
because `ft_principal_simple_at_branch` above is where the `2 ≤ n ∨ 2 ≤ r` binder is
first met, and moving it is a rename across the tree rather than a local edit. -/

/-- **`2 ≤ n ∨ 2 ≤ r` is forced, and by the branch rather than by the cone.**  At
`n = r = 1` the branch equation reads `θ_1 = θ`, which contradicts clause (i) of
`Forgacs2017RationalDenominator` Lemma 2 — `FTBranchAngle.lt_ftAngle`, which holds
with no hypothesis on the pencil beyond `a > 0`.  So no `τ > 0` solves it at any
angle of the arc.

The exclusion is `thm:FT-geometry`'s own, not an artifact: at `n = r = 1` the
pencil `Q + zX^r` has degree at most one, so it cannot carry the conjugate pair
`eq:principal-pair` asserts, and `g(t) = -Q(t)/t` has `g'(t) = Q(0)/t^2 > 0` and
hence no positive critical point, so the `t_a` of `eq:ab-def` does not exist
either.  `eq:Q-hypotheses` admits the case; the theorem built on it does not. -/
theorem not_ftBranchAt_one_one {a : Fin 1 → ℝ} (ha : ∀ k, 0 < a k) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) : ¬ FTBranchAt a 1 0 θ := by
  rintro ⟨τ, hτ, hsum⟩
  rw [ftAngleSum] at hsum
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, one_mul,
    Nat.cast_zero, zero_mul, add_zero] at hsum
  exact absurd hsum (ne_of_gt (lt_ftAngle (ha _) hτ hθ))

end ForgacsTran
