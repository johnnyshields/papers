/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ConsequencesComposition.PhaseQuantization

/-!
# `prop:angular-discrepancy` as a supply, and the two laws that consume it

`prop:equidistribution` and `cor:angular-rigidity` are corollaries of
`prop:angular-discrepancy`, and in this tree they have stood with the discrepancy
as *numeric hypotheses* rather than as a theorem about a pencil.  This module
states the discrepancy once, as `FTAngularDiscrepancy`, and derives both laws
from it — so that when the general angular discrepancy lands, the two laws
follow by supplying one term rather than by re-deriving anything.

## Main statements

* `FTAngularDiscrepancy` — `eq:angular-discrepancy` as a statement about a
  pencil and its parameterization.
* `ft_equidistribution_of_discrepancy` — `eq:normalized-angular-discrepancy`.
* `ft_angular_clock_of_discrepancy` — `eq:angular-clock`.

## Implementation notes

**The binder order is the uniformity claim, and it is the whole content.**
`C₀` and `C₁` are bound *before* the weight `B` and the threshold `M₀` *after*
it: the constants do not see `B`, and only the threshold does.  That is exactly
what `prop:angular-discrepancy` asserts ("the threshold in `M` may depend on
`B`, but the discrepancy constants do not"), and it is what separates
`thm:main` clause 3 from clause 2.  A version with `C₀ C₁` inside `∀ B`
type-checks, reads almost the same, and is a strictly weaker theorem; both
consumers below preserve the order.

**The clock needs the half-open window, and the discrepancy does not give it
directly.**  `eq:angular-clock` brackets an index between the zeros of angle
*strictly* below `θ` and those of angle *at most* `θ`.  The first is
`ftWindow z 0 θ` and the discrepancy bounds it outright; the second is
`ftWindowIoc z 0 θ`, which no *open*-window bound reaches.  What does reach it
is that the open count at any `θ' > θ` dominates the half-open count at `θ`, so
the half-open count is under `(M+1)θ'/π + Δ` for **every** `θ' > θ` and hence
under `(M+1)θ/π + Δ`.  That is `le_of_forall_pos_le_add`, and it is why the
statement below asks for `θ < π/r` rather than `θ ≤ π/r`: at the right endpoint
there is no room to take `θ'` above `θ`, and the arc is open there anyway
because the principal pair collides on the negative real axis.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, «Global and local
zero laws» (`sec:consequences`, `prop:equidistribution`,
`eq:normalized-angular-discrepancy`, `cor:angular-rigidity`,
`eq:angular-clock`) off «Angular discrepancy and proof of the main theorem»
(`subsec:proof`, `prop:angular-discrepancy`, `eq:angular-discrepancy`).

## Tags

angular discrepancy, equidistribution, angular clock, uniformity
-/

namespace ForgacsTran

open Real Set

open scoped Classical in
/-- **`eq:angular-discrepancy` as a statement about a pencil.**  For the
denominator `Q + zt^r` and the parameterization `z` of `thm:FT-geometry`: two
constants, seeing neither the weight nor `M`, such that every admissible weight
has a threshold past which the zero count of `F_M` in every angular window sits
within `C₀ + C₁ deg B` of the uniform prediction.

The binder order is the claim.  `C₀` and `C₁` are bound before `B`; `M₀` after
it. -/
def FTAngularDiscrepancy (Q : Polynomial ℂ) (r : ℕ) (z : ℝ → ℝ) : Prop :=
  ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
    ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ α β : ℝ,
        0 ≤ α → α < β → β ≤ π / r →
          |(Multiset.card ((ftCoeffPoly Q B r M).roots.filter
                (· ∈ ftWindow z α β)) : ℝ)
              - ((M : ℝ) + 1) * (β - α) / π|
            ≤ C₀ + C₁ * (B.natDegree : ℝ)

open scoped Classical in
/-- **`prop:equidistribution` off the discrepancy.**  Normalized by
`deg F_M = ⌊M/r⌋`, the zero counting measure tracks the uniform angular density
`r(β-α)/π` to `O(1/d)`, uniformly over windows, with constants that see the
weight only through its degree.

`Consequences.equidistribution_of_angular_discrepancy` is what does the work;
what this adds is that the discrepancy it consumes is now a theorem about the
pencil rather than a numeric hypothesis, and that the uniformity survives the
composition — `D₀` and `D₁` are still bound before `B`. -/
theorem ft_equidistribution_of_discrepancy {Q : Polynomial ℂ} {r : ℕ} {z : ℝ → ℝ}
    (hr : 1 ≤ r) (hdisc : FTAngularDiscrepancy Q r z) :
    ∃ D₀ D₁ : ℝ, 0 ≤ D₀ ∧ 0 ≤ D₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M d s : ℕ, M₀ ≤ M → 1 ≤ d → M = r * d + s → s < r →
          ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ π / r →
            |(Multiset.card ((ftCoeffPoly Q B r M).roots.filter
                  (· ∈ ftWindow z α β)) : ℝ) / (d : ℝ)
                - (r : ℝ) * (β - α) / π|
              ≤ (D₀ + D₁ * (B.natDegree : ℝ) + 1) / (d : ℝ) := by
  classical
  obtain ⟨C₀, C₁, hC₀, hC₁, hmain⟩ := hdisc
  refine ⟨C₀, C₁, hC₀, hC₁, fun B hB hB0 => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hmain B hB hB0
  refine ⟨M₀, fun M d s hM hd hMrs hs α β hα hαβ hβ => ?_⟩
  have hπ : (0 : ℝ) < π := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  exact equidistribution_of_angular_discrepancy hr hd hMrs hs (by linarith)
    (by linarith) (hM₀ M hM α β hα hαβ hβ)

open scoped Classical in
/-- **`cor:angular-rigidity` off the discrepancy.**  Every index belonging to a
zero of angle `θ` sits within `π(E₀ + E₁deg B + 1)/(M+1)` of the uniform clock
`πj/(M+1)`.

The half-open count is reached by the limit described in the module note: it is
dominated by the open count at every `θ' > θ`, and `le_of_forall_pos_le_add`
closes the gap.

**No injectivity of `z` is needed**, which is worth saying because the open-window
version of this argument does need it.  Here the containment
`z(I_{0,θ}] ⊆ z(I_{0,θ'})` is a set-image inclusion off `Ioc 0 θ ⊆ Ioo 0 θ'`, so
nothing has to be known about `z` at all.  An earlier draft carried
`Set.InjOn z (Icc 0 (π/r))` and never used it — an inert binder makes a theorem
look like it needs more than it does. -/
theorem ft_angular_clock_of_discrepancy {Q : Polynomial ℂ} {r : ℕ} {z : ℝ → ℝ}
    (hr : 1 ≤ r) (hdisc : FTAngularDiscrepancy Q r z) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, 0 < θ → θ < π / r → ∀ j : ℕ,
            Multiset.card ((ftCoeffPoly Q B r M).roots.filter
              (· ∈ ftWindow z 0 θ)) < j →
            j ≤ Multiset.card ((ftCoeffPoly Q B r M).roots.filter
              (· ∈ ftWindowIoc z 0 θ)) →
            |θ - π * (j : ℝ) / ((M : ℝ) + 1)|
              ≤ π * (E₀ + E₁ * (B.natDegree : ℝ) + 1) / ((M : ℝ) + 1) := by
  classical
  obtain ⟨C₀, C₁, hC₀, hC₁, hmain⟩ := hdisc
  refine ⟨C₀, C₁, hC₀, hC₁, fun B hB hB0 => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hmain B hB hB0
  refine ⟨M₀, fun M hM θ hθ0 hθr j h1 h2 => ?_⟩
  have hπ : (0 : ℝ) < π := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  set Δ : ℝ := C₀ + C₁ * (B.natDegree : ℝ) with hΔ
  -- the open window, directly
  have hopen := hM₀ M hM 0 θ le_rfl hθ0 hθr.le
  rw [sub_zero] at hopen
  -- the half-open window: dominated by every open window strictly above `θ`
  have hIoc : |(Multiset.card ((ftCoeffPoly Q B r M).roots.filter
      (· ∈ ftWindowIoc z 0 θ)) : ℝ) - ((M : ℝ) + 1) * θ / π| ≤ Δ := by
    rw [abs_le]
    constructor
    · have hmono : (Multiset.card ((ftCoeffPoly Q B r M).roots.filter
          (· ∈ ftWindow z 0 θ)) : ℝ)
          ≤ (Multiset.card ((ftCoeffPoly Q B r M).roots.filter
            (· ∈ ftWindowIoc z 0 θ)) : ℝ) := by
        exact_mod_cast count_filter_mono (P := ftCoeffPoly Q B r M)
          ftWindow_subset_ftWindowIoc
      have := (abs_le.1 hopen).1
      linarith
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      set θ' : ℝ := min (θ + ε * π / ((M : ℝ) + 1)) (π / r) with hθ'
      have hθθ' : θ < θ' := by
        refine lt_min ?_ hθr
        have : (0 : ℝ) < ε * π / ((M : ℝ) + 1) := by positivity
        linarith
      have hθ'r : θ' ≤ π / r := min_le_right _ _
      have hsub : ftWindowIoc z 0 θ ⊆ ftWindow z 0 θ' := by
        refine Set.image_mono (Set.image_mono ?_)
        exact fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθθ'⟩
      have hmono : (Multiset.card ((ftCoeffPoly Q B r M).roots.filter
          (· ∈ ftWindowIoc z 0 θ)) : ℝ)
          ≤ (Multiset.card ((ftCoeffPoly Q B r M).roots.filter
            (· ∈ ftWindow z 0 θ')) : ℝ) := by
        exact_mod_cast count_filter_mono (P := ftCoeffPoly Q B r M) hsub
      have hup := hM₀ M hM 0 θ' le_rfl (lt_trans hθ0 hθθ') hθ'r
      rw [sub_zero] at hup
      have hθ'le : θ' ≤ θ + ε * π / ((M : ℝ) + 1) := min_le_left _ _
      have hstep : ((M : ℝ) + 1) * θ' / π ≤ ((M : ℝ) + 1) * θ / π + ε := by
        rw [div_le_iff₀ hπ]
        have : ((M : ℝ) + 1) * θ' ≤ ((M : ℝ) + 1) * (θ + ε * π / ((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hθ'le hMpos.le
        have hexp : ((M : ℝ) + 1) * (θ + ε * π / ((M : ℝ) + 1))
            = ((M : ℝ) + 1) * θ + ε * π := by field_simp
        rw [hexp] at this
        have hdiv : ((M : ℝ) + 1) * θ / π * π = ((M : ℝ) + 1) * θ := by
          field_simp
        nlinarith [this, hdiv]
      have := (abs_le.1 hup).2
      linarith
  exact angular_clock_of_bracketing hopen hIoc h1 h2

end ForgacsTran
