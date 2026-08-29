/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchSupply

/-!
# The amplitude group, at a general pencil

`exists_uniform_ftBranchSupply` asks four things of the amplitude along the branch —
`hWd`, `hWc`, `hW0`, `hWL` — and they have been available only at the cubic.  They are
general, and three of the four cost nothing new: the supply already carries `hSd`, `hSc`
and `hS0` about the **cofactor** `ftCofactorAlong`, and

    ftAmp Q B r (z θ) (γ θ) = -(B(γ θ) / ftCofactorAlong Q r z τ θ)

by definition, so the amplitude's derivative is the quotient rule over data already in
hand.  **Nothing divides by the amplitude**, which is why this reaches the whole open arc
including the amplitude's own zeros.

`hW0` and `hWL` are the fourth thing, and they hold for one reason: at each endpoint the
principal pair **collides**, so `∂_tD` vanishes there and the formalized amplitude is
`-(B/0) = 0`.  That is a statement about the formalized object rather than about the
paper's `W`, which diverges at a collision — the hypothesis is stated as the vanishing of
`∂_tD` so a caller sees exactly what it is buying.

## Main statements

* `ftAmpAlong`, `ftAmpAlong_eq` — the amplitude along the branch, as `-B(γ)/S`.
* `ftAmpAlongDeriv`, `hasDerivAt_ftAmpAlong`, `continuousOn_ftAmpAlongDeriv` — `hWd` and
  `hWc` from the cofactor data the supply already carries.
* `ftAmpAlong_eq_zero_of_collision` — `hW0` and `hWL` from `∂_tD = 0` at the endpoint.
* `im_logDeriv_ftAmpAlong_eq`, `abs_im_logDeriv_ftAmpAlong_le`, `region_bounds_of_halves`
  — `Im(W'/W) = Im((B∘γ)'/(B∘γ)) - Im(S'/S)`, so `h₁ h₂ h₃` reduce to a numerator bound
  and a cofactor bound on each region.  The cofactor half is `BranchSupply`'s own cover,
  already built for `κ₀`; the numerator half is where the amplitude divisor sits.
* `ftCofactorAlongDeriv`, `hasDerivAt_ftCofactorAlong`,
  `continuousOn_ftCofactorAlongDeriv` — `hSd` and `hSc` at a general pencil, from `γ'`
  and `γ ≠ 0` alone.  These were being read off a witness rather than produced, which is
  the pattern a bundle field makes easy to miss: a hypothesis a single instance supplies
  looks discharged from every consumer's side.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`,
`lem:amplitude-divisor`, `eq:W-def`.

## Tags

residue amplitude, branch, collision, Forgács–Tran
-/

namespace ForgacsTran

open Set Polynomial

variable {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}

/-- The residue amplitude along the branch, as a function of the angle. -/
noncomputable def ftAmpAlong (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)

/-- `W = -B(γ)/S` with `S` the cofactor along the branch.  Definitional, and it is what
makes the quotient rule below available without dividing by `W`. -/
theorem ftAmpAlong_eq (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (θ : ℝ) :
    ftAmpAlong Q B r z τ θ
      = -(B.eval (ftPrincipal τ θ) / ftCofactorAlong Q r z τ θ) := rfl

/-- The amplitude's derivative, by the quotient rule on `-B(γ)/S`. -/
noncomputable def ftAmpAlongDeriv (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (dγ dS : ℝ → ℂ) (θ : ℝ) : ℂ :=
  -((dγ θ * (derivative B).eval (ftPrincipal τ θ) * ftCofactorAlong Q r z τ θ
      - B.eval (ftPrincipal τ θ) * dS θ) / ftCofactorAlong Q r z τ θ ^ 2)

/-- **`hWd` at a general pencil.**  Everything it consumes is already a hypothesis of
`exists_uniform_ftBranchSupply`: the branch's derivative, and the cofactor's derivative
and nonvanishing.  In particular it holds **at the amplitude's zeros too** — the quotient
rule differentiates `-B(γ)/S`, and `S` is what must not vanish, not `W`. -/
theorem hasDerivAt_ftAmpAlong {dγ dS : ℝ → ℂ} {θ : ℝ}
    (hγd : HasDerivAt (ftPrincipal τ) (dγ θ) θ)
    (hSd : HasDerivAt (ftCofactorAlong Q r z τ) (dS θ) θ)
    (hS0 : ftCofactorAlong Q r z τ θ ≠ 0) :
    HasDerivAt (ftAmpAlong Q B r z τ) (ftAmpAlongDeriv Q B r z τ dγ dS θ) θ := by
  have hB : HasDerivAt (fun s : ℝ => B.eval (ftPrincipal τ s))
      (dγ θ * (derivative B).eval (ftPrincipal τ θ)) θ :=
    hasDerivAt_eval_comp (γ := ftPrincipal τ) (dγ := fun _ => dγ θ) B hγd
  exact ((hB.div hSd hS0).neg).congr_deriv rfl

/-- **`hWc` at a general pencil.**  The same data, as continuity. -/
theorem continuousOn_ftAmpAlongDeriv {dγ dS : ℝ → ℂ} {U : Set ℝ}
    (hγc : ContinuousOn (ftPrincipal τ) U) (hdγ : ContinuousOn dγ U)
    (hSc : ContinuousOn (ftCofactorAlong Q r z τ) U) (hdS : ContinuousOn dS U)
    (hS0 : ∀ s ∈ U, ftCofactorAlong Q r z τ s ≠ 0) :
    ContinuousOn (ftAmpAlongDeriv Q B r z τ dγ dS) U := by
  have hp : ∀ P : Polynomial ℂ, ContinuousOn (fun s : ℝ => P.eval (ftPrincipal τ s)) U :=
    fun P => (Polynomial.continuous P).comp_continuousOn hγc
  refine ContinuousOn.neg (ContinuousOn.div ?_ (hSc.pow 2) ?_)
  · exact ((hdγ.mul (hp _)).mul hSc).sub ((hp B).mul hdS)
  · exact fun s hs => pow_ne_zero 2 (hS0 s hs)

/-- **`hW0` and `hWL` at a general pencil.**  At an endpoint the principal pair collides,
so `∂_tD` vanishes at the branch point and the formalized amplitude is `-(B/0) = 0`.

**This is a fact about the formalized object, not about the paper's `W`.**  At a collision
the paper's amplitude *diverges*; the value `0` here is Lean's division convention, and the
hypothesis is stated as the vanishing of `∂_tD` precisely so that a caller sees which of
the two it is buying.  On the open arc the two agree.

`hroot` is the branch condition at the endpoint and `hcrit` is the collision. -/
theorem ftAmpAlong_eq_zero_of_collision {θ : ℝ}
    (hroot : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hcrit : (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) = 0) :
    ftAmpAlong Q B r z τ θ = 0 := by
  have hcof : ftCofactorAlong Q r z τ θ = 0 := by
    rw [ftCofactorAlong, ← eval_derivative_ftDen hroot]
    exact hcrit
  rw [ftAmpAlong_eq, hcof, div_zero, neg_zero]

/-! ### The region bounds, reduced to numerator and cofactor -/

/-- **`Im(W'/W)` splits into numerator and cofactor.**  `W = -B(γ)/S`, so
`W'/W = (B∘γ)'/(B∘γ) - S'/S` and the constant `-1` drops out.  The split is where the
`κ` for `eq:phase-derivative-bound` comes from at a general pencil: the cofactor half is
`BranchSupply`'s own cover, and the numerator half is where the amplitude divisor lives.

**The guard is what makes it legitimate.**  `W ≠ 0` gives `B(γ) ≠ 0`, since `B(γ) = 0`
would make `W` vanish; without it the numerator's logarithmic derivative is a quotient by
zero and the identity would hold by convention rather than by algebra. -/
theorem im_logDeriv_ftAmpAlong_eq {dγ dS : ℝ → ℂ} {θ : ℝ}
    (hS0 : ftCofactorAlong Q r z τ θ ≠ 0) (hW0 : ftAmpAlong Q B r z τ θ ≠ 0) :
    (ftAmpAlongDeriv Q B r z τ dγ dS θ / ftAmpAlong Q B r z τ θ).im
      = ((dγ θ * (derivative B).eval (ftPrincipal τ θ))
          / B.eval (ftPrincipal τ θ)).im
        - (dS θ / ftCofactorAlong Q r z τ θ).im := by
  have hB0 : B.eval (ftPrincipal τ θ) ≠ 0 := by
    intro h
    exact hW0 (by rw [ftAmpAlong_eq, h, zero_div, neg_zero])
  have hkey : ftAmpAlongDeriv Q B r z τ dγ dS θ / ftAmpAlong Q B r z τ θ
      = (dγ θ * (derivative B).eval (ftPrincipal τ θ)) / B.eval (ftPrincipal τ θ)
        - dS θ / ftCofactorAlong Q r z τ θ := by
    rw [ftAmpAlong_eq, ftAmpAlongDeriv]
    field_simp
  rw [hkey, Complex.sub_im]

/-- **The region bound from the two halves.**  What a caller owes at a general pencil is a
bound on the numerator's logarithmic derivative and one on the cofactor's, over the same
region; this adds them.

The cofactor half is exactly what `BranchSupply.exists_bound_im_logDeriv_ftCofactorAlong_of_cover`
produces for `κ₀`, so at a general pencil the two constants come from the same cover and
only the numerator half is new work — and that is where the amplitude divisor sits. -/
theorem abs_im_logDeriv_ftAmpAlong_le {dγ dS : ℝ → ℂ} {θ cB cS : ℝ}
    (hS0 : ftCofactorAlong Q r z τ θ ≠ 0) (hW0 : ftAmpAlong Q B r z τ θ ≠ 0)
    (hB : |((dγ θ * (derivative B).eval (ftPrincipal τ θ))
        / B.eval (ftPrincipal τ θ)).im| ≤ cB)
    (hS : |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ cS) :
    |(ftAmpAlongDeriv Q B r z τ dγ dS θ / ftAmpAlong Q B r z τ θ).im| ≤ cB + cS := by
  rw [im_logDeriv_ftAmpAlong_eq hS0 hW0]
  exact le_trans (abs_sub _ _) (add_le_add hB hS)

/-- **`h₁`, `h₂`, `h₃` at a general pencil**, from the two halves on each region.  The
three regions are not required to share a constant — at the cubic they happen to, because
the phase derivative there is a rational function of `τ` with no `θ` in it, but that is a
feature of that pencil and not of the geometry. -/
theorem region_bounds_of_halves {dγ dS : ℝ → ℂ} {b₁ b₂ e : ℝ}
    {cB₁ cB₂ cB₃ cS₁ cS₂ cS₃ : ℝ}
    (hS0 : ∀ s ∈ Icc (0 : ℝ) e, ftAmpAlong Q B r z τ s ≠ 0 →
      ftCofactorAlong Q r z τ s ≠ 0)
    (hB₁ : ∀ s ∈ Icc (0 : ℝ) b₁, ftAmpAlong Q B r z τ s ≠ 0 →
      |((dγ s * (derivative B).eval (ftPrincipal τ s))
        / B.eval (ftPrincipal τ s)).im| ≤ cB₁)
    (hS₁ : ∀ s ∈ Icc (0 : ℝ) b₁, |(dS s / ftCofactorAlong Q r z τ s).im| ≤ cS₁)
    (hB₂ : ∀ s ∈ Icc b₁ b₂, ftAmpAlong Q B r z τ s ≠ 0 →
      |((dγ s * (derivative B).eval (ftPrincipal τ s))
        / B.eval (ftPrincipal τ s)).im| ≤ cB₂)
    (hS₂ : ∀ s ∈ Icc b₁ b₂, |(dS s / ftCofactorAlong Q r z τ s).im| ≤ cS₂)
    (hB₃ : ∀ s ∈ Icc b₂ e, ftAmpAlong Q B r z τ s ≠ 0 →
      |((dγ s * (derivative B).eval (ftPrincipal τ s))
        / B.eval (ftPrincipal τ s)).im| ≤ cB₃)
    (hS₃ : ∀ s ∈ Icc b₂ e, |(dS s / ftCofactorAlong Q r z τ s).im| ≤ cS₃)
    (h₁sub : Icc (0 : ℝ) b₁ ⊆ Icc (0 : ℝ) e) (h₂sub : Icc b₁ b₂ ⊆ Icc (0 : ℝ) e)
    (h₃sub : Icc b₂ e ⊆ Icc (0 : ℝ) e) :
    (∀ s ∈ Icc (0 : ℝ) b₁, ftAmpAlong Q B r z τ s ≠ 0 →
        |(ftAmpAlongDeriv Q B r z τ dγ dS s / ftAmpAlong Q B r z τ s).im| ≤ cB₁ + cS₁)
      ∧ (∀ s ∈ Icc b₁ b₂, ftAmpAlong Q B r z τ s ≠ 0 →
        |(ftAmpAlongDeriv Q B r z τ dγ dS s / ftAmpAlong Q B r z τ s).im| ≤ cB₂ + cS₂)
      ∧ (∀ s ∈ Icc b₂ e, ftAmpAlong Q B r z τ s ≠ 0 →
        |(ftAmpAlongDeriv Q B r z τ dγ dS s / ftAmpAlong Q B r z τ s).im| ≤ cB₃ + cS₃) :=
  ⟨fun s hs hne => abs_im_logDeriv_ftAmpAlong_le (hS0 s (h₁sub hs) hne) hne
      (hB₁ s hs hne) (hS₁ s hs),
   fun s hs hne => abs_im_logDeriv_ftAmpAlong_le (hS0 s (h₂sub hs) hne) hne
      (hB₂ s hs hne) (hS₂ s hs),
   fun s hs hne => abs_im_logDeriv_ftAmpAlong_le (hS0 s (h₃sub hs) hne) hne
      (hB₃ s hs hne) (hS₃ s hs)⟩

/-! ### The cofactor group -/

/-- **`S'` along the arc.**  `S = E(γ)/γ` there, so the derivative is
`γ'(E'(γ)γ - E(γ))/γ²`.

**It carries no `z`.**  `ftCofactorAlong` is defined through `ftCofactor Q r (z θ)`, and
`z` looks like data the derivative would have to differentiate; it is not.  On the arc the
branch point is a root of the pencil at its own spectral value, and there `∂_tD` collapses
to `E(γ)/γ` with `E = XQ' - rQ` independent of `z` — so the whole group needs `γ'` and
`γ ≠ 0` and nothing else.  Had `z'` been needed this would have been a different task, and
the tree carries no `z'`. -/
noncomputable def ftCofactorAlongDeriv (Q : Polynomial ℂ) (r : ℕ) (τ : ℝ → ℝ)
    (dγ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  dγ θ * ((derivative (ftCritical Q r)).eval (ftPrincipal τ θ) * ftPrincipal τ θ
      - (ftCritical Q r).eval (ftPrincipal τ θ)) / ftPrincipal τ θ ^ 2

/-- **`hSd` at a general pencil.**  The identity `S = E(γ)/γ` holds pointwise on the arc,
so it holds on a neighbourhood of each of its points and the derivative transfers. -/
theorem hasDerivAt_ftCofactorAlong {U : Set ℝ} {dγ : ℝ → ℂ} {θ : ℝ} (hr : 1 ≤ r)
    (hU : IsOpen U) (hθ : θ ∈ U) (hγd : HasDerivAt (ftPrincipal τ) (dγ θ) θ)
    (hγ0 : ∀ s ∈ U, ftPrincipal τ s ≠ 0)
    (hroot : ∀ s ∈ U, (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0) :
    HasDerivAt (ftCofactorAlong Q r z τ) (ftCofactorAlongDeriv Q r τ dγ θ) θ := by
  have hnum : HasDerivAt (fun s : ℝ => (ftCritical Q r).eval (ftPrincipal τ s))
      (dγ θ * (derivative (ftCritical Q r)).eval (ftPrincipal τ θ)) θ :=
    hasDerivAt_eval_comp (γ := ftPrincipal τ) (dγ := fun _ => dγ θ) _ hγd
  have hq := hnum.fun_div hγd (hγ0 θ hθ)
  refine (hq.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [ftCofactorAlongDeriv]
    ring
  · filter_upwards [hU.mem_nhds hθ] with s hs
    exact ftCofactorAlong_eq_ftCritical_div hr (hγ0 s hs) (hroot s hs)

/-- **`hSc` at a general pencil.**  The same data, as continuity: a polynomial evaluated
along a continuous branch, over a nonvanishing one. -/
theorem continuousOn_ftCofactorAlongDeriv {U : Set ℝ} {dγ : ℝ → ℂ}
    (hγc : ContinuousOn (ftPrincipal τ) U) (hdγ : ContinuousOn dγ U)
    (hγ0 : ∀ s ∈ U, ftPrincipal τ s ≠ 0) :
    ContinuousOn (ftCofactorAlongDeriv Q r τ dγ) U := by
  have hE : ContinuousOn (fun s : ℝ => (ftCritical Q r).eval (ftPrincipal τ s)) U :=
    (Polynomial.continuous_eval₂ (ftCritical Q r) (RingHom.id ℂ)).comp_continuousOn hγc
  have hE' : ContinuousOn
      (fun s : ℝ => (derivative (ftCritical Q r)).eval (ftPrincipal τ s)) U :=
    (Polynomial.continuous_eval₂ (derivative (ftCritical Q r))
      (RingHom.id ℂ)).comp_continuousOn hγc
  exact (hdγ.mul ((hE'.mul hγc).sub hE)).div (hγc.pow 2)
    fun s hs => pow_ne_zero 2 (hγ0 s hs)

end ForgacsTran
