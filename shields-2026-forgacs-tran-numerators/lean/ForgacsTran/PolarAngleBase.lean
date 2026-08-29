/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Topology.EMetricSpace.BoundedVariationAlgebra
import ForgacsTran.ViewingAngle

/-!
# Moving a branch's base point

`BranchSupply.RootBranchState` bases its branches at the endpoints of the arc, which is
what drags the **closed** arc — and with it two endpoint corners that no definition fix
removes — into every hypothesis above it.  The base points are a choice rather than
mathematics: every *evaluation* point is already interior, since a block on which the
amplitude does not vanish cannot reach an endpoint.  Moving them inside is only legitimate
if the branch is base-point free in the two things the supply actually caps, and that is
what is proved here.

**It is, and it needs far less than the branch lemmas around it.**  `polarAngle` is
`arg(γ(c) - β) + ∫_c^x Im(γ'/(γ-β))`, and `x` enters only through the upper limit.  Two
base points therefore differ by

    arg(γ(c₀) - β) - arg(γ(c₁) - β) + ∫_{c₀}^{c₁} Im(γ'/(γ-β)),

a number.  No differentiability is used, no open set containing the interval, and nothing
at the endpoints — the identity is about the *definition* of `polarAngle`, so `dγ` need
not even be `γ'`.

## The hypothesis, named

What is required is that the three points — both base points and the evaluation point —
lie in **one interval on which `γ ≠ β`**.  Connectedness is where the argument lives:
it is `∫_{c₀}^{c₁} + ∫_{c₁}^{x} = ∫_{c₀}^{x}`, and the integrand has to be integrable
along the way.

**So a base point cannot be moved across the parameter the arc meets `β` at.**  In
`RootBranchState`'s second state the integrand blows up at `m`, and a single interval
holding base points on both sides of it violates `γ ≠ β`.  That is not a limitation to be
worked around — it is the reason the two sides carry different base points in the first
place.  Within one side, the move is free.

## Main statements

* `eVariationOn_add_const`, `eVariationOn_congr_add_const` — a constant shift leaves
  `eVariationOn` alone; re-exported from
  `Shields.Topology.EMetricSpace.BoundedVariationAlgebra`, since Mathlib carries
  `eVariationOn.eq_of_eqOn` but not this.
* `polarAngle_base_shift` — the branch shifts by a constant.
* `eVariationOn_polarAngle_base`, `abs_sub_polarAngle_base` — hence the variation and the
  increments, which are the two things the supply caps, do not see the base point.
* `polarAngle_base_shift_of_meet`, `eVariationOn_polarAngle_base_of_meet` — the same with
  the nonvanishing discharged from `RootBranchState`'s own meet clause, so a caller names
  the side rather than producing a hypothesis.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`cor:linear-phase-variation`, `eq:linear-phase-variation`, `eq:viewing-angle-bound`.

## Tags

viewing angle, base point, bounded variation, Forgács–Tran
-/
namespace ForgacsTran

open Set MeasureTheory intervalIntegral

/-! ### A constant shift does not move the variation

`Shields.eVariationOn_add_const` and `Shields.eVariationOn_congr_add_const`, re-exported.
The second is the one used below: the two branches agree up to a constant on the arc, and
nowhere else. -/

export Shields (eVariationOn_add_const eVariationOn_congr_add_const)

/-! ### The base point shifts the branch by a constant -/

/-- **Moving the base point changes the branch by a constant.**  `polarAngle` is
`arg(γ(c) - β)` plus `∫_c^x Im(γ'/(γ - β))`, and `x` enters only through the upper limit,
so two base points differ by `arg(γ(c₀) - β) - arg(γ(c₁) - β) + ∫_{c₀}^{c₁}` — a number,
not a function of `x`.

**What this needs is much less than the branch lemmas around it.**  No differentiability,
no open set containing the interval, nothing at the endpoints: `polarAngle` is an
integral, and all that is asked is that the integrand be interval-integrable between the
three points involved.  Continuity of `γ` and `dγ` on the closed interval, and `γ ≠ β`
there, is enough — and the interval must be an interval, since the argument is
`∫_{c₀}^{c₁} + ∫_{c₁}^{x} = ∫_{c₀}^{x}` and that is where connectedness enters.

`hd` — that `dγ` *is* `γ'` — is not among them.  The identity is about the definition of
`polarAngle`, and holds for any pairing of a curve with a putative derivative. -/
theorem polarAngle_base_shift {γ dγ : ℝ → ℂ} {β : ℂ} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hdc : ContinuousOn dγ (Icc a b))
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    {c₀ c₁ : ℝ} (h₀ : c₀ ∈ Icc a b) (h₁ : c₁ ∈ Icc a b) :
    ∃ k : ℝ, ∀ x ∈ Icc a b,
      polarAngle γ dγ β c₀ x = polarAngle γ dγ β c₁ x + k := by
  have hcont : ContinuousOn (fun u => dγ u / (γ u - β)) (Icc a b) :=
    hdc.div (hγc.sub continuousOn_const) fun s hs => sub_ne_zero.2 (hne s hs)
  have hint : ∀ p ∈ Icc a b, ∀ q ∈ Icc a b,
      IntervalIntegrable (fun u => dγ u / (γ u - β)) volume p q := by
    intro p hp q hq
    exact (hcont.mono (uIcc_subset_Icc hp hq)).intervalIntegrable
  refine ⟨(Complex.log (γ c₀ - β)).im - (Complex.log (γ c₁ - β)).im
      + (∫ u in c₀..c₁, dγ u / (γ u - β)).im, fun x hx => ?_⟩
  have hadd : (∫ u in c₀..c₁, dγ u / (γ u - β)) + (∫ u in c₁..x, dγ u / (γ u - β))
      = ∫ u in c₀..x, dγ u / (γ u - β) :=
    integral_add_adjacent_intervals (hint c₀ h₀ c₁ h₁) (hint c₁ h₁ x hx)
  rw [polarAngle, polarAngle, logLift, logLift, Complex.add_im, Complex.add_im, ← hadd,
    Complex.add_im]
  ring

/-- **The variation is base-point free.**  What `BranchSupply`'s branch data caps is
`∑ eVariationOn (ψ i)`, and moving each block's base point leaves every term unchanged. -/
theorem eVariationOn_polarAngle_base {γ dγ : ℝ → ℂ} {β : ℂ} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hdc : ContinuousOn dγ (Icc a b))
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    {c₀ c₁ : ℝ} (h₀ : c₀ ∈ Icc a b) (h₁ : c₁ ∈ Icc a b)
    {s : Set ℝ} (hs : s ⊆ Icc a b) :
    eVariationOn (polarAngle γ dγ β c₀) s = eVariationOn (polarAngle γ dγ β c₁) s := by
  obtain ⟨k, hk⟩ := polarAngle_base_shift hγc hdc hne h₀ h₁
  exact eVariationOn_congr_add_const fun x hx => hk x (hs hx)

/-- **The increments are base-point free too**, which is the other clause the supply
carries: `|ψ(R) - ψ(L)|` is unchanged. -/
theorem abs_sub_polarAngle_base {γ dγ : ℝ → ℂ} {β : ℂ} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hdc : ContinuousOn dγ (Icc a b))
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    {c₀ c₁ : ℝ} (h₀ : c₀ ∈ Icc a b) (h₁ : c₁ ∈ Icc a b)
    {L R : ℝ} (hL : L ∈ Icc a b) (hR : R ∈ Icc a b) :
    |polarAngle γ dγ β c₀ R - polarAngle γ dγ β c₀ L|
      = |polarAngle γ dγ β c₁ R - polarAngle γ dγ β c₁ L| := by
  obtain ⟨k, hk⟩ := polarAngle_base_shift hγc hdc hne h₀ h₁
  rw [hk R hR, hk L hL]
  ring_nf

/-! ### The hypothesis in the shape the root state supplies -/

/-- **The move, discharged from `RootBranchState`'s own meet clause.**  Its second state
carries `∀ x ∈ Icc a b, x ≠ m → γ x ≠ β` — that, plus a sub-interval missing `m`, is
already `polarAngle_base_shift`'s `hne`.  A caller does not have to produce a
nonvanishing hypothesis of its own; it names the side.

`m ∉ Icc p q` is the whole of the restriction, and it is not a technicality: the integrand
blows up at `m`, so a sub-interval spanning it has no interval-additivity and the two base
points genuinely give different branches.  That is why the state carries one base point
per side rather than one for the arc. -/
theorem polarAngle_base_shift_of_meet {γ dγ : ℝ → ℂ} {β : ℂ} {a b m : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hdc : ContinuousOn dγ (Icc a b))
    (hmeet : ∀ x ∈ Icc a b, x ≠ m → γ x ≠ β)
    {p q : ℝ} (hpq : Icc p q ⊆ Icc a b) (hmiss : m ∉ Icc p q)
    {c₀ c₁ : ℝ} (h₀ : c₀ ∈ Icc p q) (h₁ : c₁ ∈ Icc p q) :
    ∃ k : ℝ, ∀ x ∈ Icc p q,
      polarAngle γ dγ β c₀ x = polarAngle γ dγ β c₁ x + k :=
  polarAngle_base_shift (hγc.mono hpq) (hdc.mono hpq)
    (fun s hs => hmeet s (hpq hs) (by rintro rfl; exact hmiss hs)) h₀ h₁

/-- The variation clause at the same hypotheses. -/
theorem eVariationOn_polarAngle_base_of_meet {γ dγ : ℝ → ℂ} {β : ℂ} {a b m : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hdc : ContinuousOn dγ (Icc a b))
    (hmeet : ∀ x ∈ Icc a b, x ≠ m → γ x ≠ β)
    {p q : ℝ} (hpq : Icc p q ⊆ Icc a b) (hmiss : m ∉ Icc p q)
    {c₀ c₁ : ℝ} (h₀ : c₀ ∈ Icc p q) (h₁ : c₁ ∈ Icc p q)
    {s : Set ℝ} (hs : s ⊆ Icc p q) :
    eVariationOn (polarAngle γ dγ β c₀) s = eVariationOn (polarAngle γ dγ β c₁) s := by
  obtain ⟨k, hk⟩ := polarAngle_base_shift_of_meet hγc hdc hmeet hpq hmiss h₀ h₁
  exact eVariationOn_congr_add_const fun x hx => hk x (hs hx)

end ForgacsTran
