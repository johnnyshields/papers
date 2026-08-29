/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ConsequencesComposition.PhaseQuantization
import ForgacsTran.CubicPhaseDerivative

/-!
# The inner window count of `prop:equidistribution`

`ft_equidistribution` takes two counts as binders, `hin` on the window and
`hout` on its complement.  `hin` is produced here, at the cubic pencil and
unconditionally past a threshold in `M`.

The three pieces existed and were never joined.  `PhaseCount.card_le_count_filter`
turns *distinct* zeros into the multiplicity count, `count_lower_of_phase_turning`
turns a phase turning into the count `eq:angular-distinct-lower` claims, and
`CubicPhaseDerivative.cubic_exists_phaseZeros` supplies the zeros with no
analytic binder left.  What was also missing is the window itself: the producer
places its zeros in `Icc (z u) (z v)`, while `ftWindow` is the image of an open
angular interval, and the intermediate value theorem is what identifies them.

## Main statements

* `count_filter_lower_of_zeros` — the bridge, in general: distinct roots in a set
  `A`, with a phase-turning lower bound, give `eq:angular-distinct-lower` for the
  multiplicity count in `A`.
* `mem_ftWindow_of_subarc`, `count_filter_lower_of_subarc` — the same with the
  window supplied as `ftWindow`, the membership carried across by the
  intermediate value theorem.
* `count_filter_lower_of_two` — two disjoint component counts added and bridged
  to the multiplicity count in one step.
* `cubic_count_filter_lower` — `hin` at the cubic pencil, past one threshold in
  `M`, for every subarc of the retained range of `eq:retained-range` that misses
  the deleted window.  Phase-free: the variation is already paid inside
  `cubic_exists_phaseZeros`, at `eq:phase-derivative-bound`'s uniform `κ`.

## Implementation notes

**`card_le_count_filter` runs in the safe direction.**  It bounds a `Finset` of
*distinct* roots above by the multiplicity count, `Z.card ≤ card (roots.filter)`,
so it strengthens a lower bound rather than weakening one.  A bound the other way
would be false, and would type-check.

**The deficit is explicit and carries the shrink.**  The producer counts on a
compact subarc `[u,v]` strictly inside the open window `(α,β)`, so the deficit
against `ft_equidistribution`'s `hin` is
`(3(β-α)/2 + (M-1/2)((β-α)-(v-u)))/π + 2`.  The first term is `M`-free and is
the phase variation at `eq:phase-derivative-bound`'s uniform `κ = 3/2`; the
second is `O(1)` exactly when the subarc is shrunk by `O(1/M)`.  Taking
`u = α + (M+1)^{-2}` and `v = β - (M+1)^{-2}` costs under one unit at every
`M ≥ 10`, which `scripts/` measures.  Choosing the subarc is the caller's, so
the deficit is stated rather than fixed.

**`hout` is out of reach at this pencil, and for a measured reason.**  The
deleted set `CubicWitnessInterior.cubicTheta` is `{θ : |θ - π/2| < 1}`, the same
set for every `M`, of length `2` inside an interval of length `π`.  The two
complementary windows of `hout` cover everything outside `(α,β)`, so their union
contains that middle whatever the window is, and the phase turning lost across a
set of fixed measure `m` is `(M+1)m/π`.  So `hout` would hold only with
`C₂ ≥ 2(M+1)/π`, and `C₂/d → 2/π` rather than to `0`, which is not the `O(1/d)`
`eq:normalized-angular-discrepancy` claims.  A pencil whose deleted windows
shrink with `M` is what `hout` needs; this one's do not.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `prop:equidistribution`,
`eq:normalized-angular-discrepancy`, `prop:angular-discrepancy`,
`eq:angular-distinct-lower`, `eq:retained-range`, `eq:Phi-def`).

## Tags

zero counting, equidistribution, angular window, phase turning, cubic pencil
-/

namespace ForgacsTran

open Real Set

/-! ### The bridge

Nothing under this heading mentions the cubic pencil, `ftCoeffPoly` or the branch.
The three statements are about a polynomial, a `Finset` of its distinct roots and a
phase-turning lower bound, and they are what turns a count of *distinct* zeros into
the multiplicity count `eq:angular-distinct-lower` claims.  The pencil enters only
in § `hin` at the cubic pencil below. -/

/-- **`eq:angular-distinct-lower` as a multiplicity count.**  A `Finset` of
distinct roots inside `A`, carrying at least `L/π - 2` elements, bounds the
multiplicity count in `A` below by the phase turning.

The two halves are `PhaseCount.card_le_count_filter` and
`count_lower_of_phase_turning`; both existed, and nothing composed them. -/
theorem count_filter_lower_of_zeros {P : Polynomial ℂ} (hP : P ≠ 0) (A : Set ℂ)
    [DecidablePred (· ∈ A)] {Z : Finset ℂ} {L V α β : ℝ} {M : ℕ}
    (hZroot : ∀ w ∈ Z, P.IsRoot w) (hZmem : ∀ w ∈ Z, w ∈ A)
    (hn : L / π - 2 ≤ (Z.card : ℝ))
    (hturn : ((M : ℝ) + 1) * (β - α) - V ≤ L) :
    ((M : ℝ) + 1) * (β - α) / π - (V / π + 2)
      ≤ (Multiset.card (P.roots.filter (· ∈ A)) : ℝ) :=
  count_lower_of_phase_turning hn (card_le_count_filter hP A hZroot hZmem) hturn

/-- **The same, with the window as `eq:angular-subinterval`.**  The phase count
places its zeros in `Icc (z u) (z v)` for a compact subarc `[u,v]`; `ftWindow` is
the image of the *open* interval `(α,β)`.  For `[u,v] ⊆ (α,β)` and `z` continuous
there, the intermediate value theorem identifies the first inside the second, so
the count transfers. -/
theorem mem_ftWindow_of_subarc {z : ℝ → ℝ} {u v α β : ℝ} (huv : u ≤ v)
    (hzc : ContinuousOn z (Icc u v)) (hsub : Icc u v ⊆ Ioo α β)
    {w : ℂ} (hw : w ∈ Complex.ofReal '' Icc (z u) (z v)) : w ∈ ftWindow z α β := by
  obtain ⟨x, hx, rfl⟩ := hw
  exact ⟨x, Set.image_mono hsub (intermediate_value_Icc huv hzc hx), rfl⟩

theorem count_filter_lower_of_subarc {P : Polynomial ℂ} (hP : P ≠ 0) {z : ℝ → ℝ}
    {u v α β L V : ℝ} {M : ℕ} [DecidablePred (· ∈ ftWindow z α β)]
    (huv : u ≤ v) (hzc : ContinuousOn z (Icc u v)) (hsub : Icc u v ⊆ Ioo α β)
    {Z : Finset ℂ} (hZroot : ∀ w ∈ Z, P.IsRoot w)
    (hZmem : ∀ w ∈ Z, w ∈ Complex.ofReal '' Icc (z u) (z v))
    (hn : L / π - 2 ≤ (Z.card : ℝ))
    (hturn : ((M : ℝ) + 1) * (β - α) - V ≤ L) :
    ((M : ℝ) + 1) * (β - α) / π - (V / π + 2)
      ≤ (Multiset.card (P.roots.filter (· ∈ ftWindow z α β)) : ℝ) :=
  count_filter_lower_of_zeros hP _ hZroot
    (fun w hw => mem_ftWindow_of_subarc huv hzc hsub (hZmem w hw)) hn hturn

/-- **Two disjoint component counts add, and bridge to the multiplicity count.**
`card_le_count_filter` runs distinct-to-multiplicity, so it strengthens a lower
bound; applied to the union of two disjoint component sets it turns two phase
counts into one count in the window. -/
theorem count_filter_lower_of_two {P : Polynomial ℂ} (hP : P ≠ 0) (A : Set ℂ)
    [DecidablePred (· ∈ A)] {Z₁ Z₂ : Finset ℂ} (hdisj : Disjoint Z₁ Z₂)
    (hr₁ : ∀ w ∈ Z₁, P.IsRoot w) (hr₂ : ∀ w ∈ Z₂, P.IsRoot w)
    (hm₁ : ∀ w ∈ Z₁, w ∈ A) (hm₂ : ∀ w ∈ Z₂, w ∈ A)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ≤ (Z₁.card : ℝ)) (hc₂ : c₂ ≤ (Z₂.card : ℝ)) :
    c₁ + c₂ ≤ (Multiset.card (P.roots.filter (· ∈ A)) : ℝ) := by
  have hcard := card_le_count_filter hP A (Z := Z₁ ∪ Z₂)
    (fun w hw => (Finset.mem_union.1 hw).elim (hr₁ w) (hr₂ w))
    (fun w hw => (Finset.mem_union.1 hw).elim (hm₁ w) (hm₂ w))
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have : ((Z₁.card + Z₂.card : ℕ) : ℝ)
      ≤ (Multiset.card (P.roots.filter (· ∈ A)) : ℝ) := by exact_mod_cast hcard
  push_cast at this
  linarith

/-! ### `hin` at the cubic pencil -/

/-- **`ft_equidistribution`'s `hin`, at the cubic pencil, with nothing assumed
about the analysis.**  Past one threshold in `M`, on every compact subarc of the
retained range of `eq:retained-range` that misses the deleted window and sits
strictly inside an angular window `(α,β)`, the coefficient polynomial's zeros in
`z(I_{α,β})` — counted with multiplicity — are at least

`(M+1)(β-α)/π - ((3(β-α)/2 + (M-1/2)((β-α)-(v-u)))/π + 2)`.

The deficit is the second bracket and carries no phase: `cubic_exists_phaseZeros`
supplies the count in the `ψ`-free form `(M-1/2)(v-u)/π - 2`, in which the
variation of the phase has already been paid at `eq:phase-derivative-bound`'s
uniform `κ = 3/2` — that is the `3(β-α)/2`, which is `M`-free.  What is left is
the shrink `(β-α)-(v-u)`, and the deficit is `O(1)` exactly when that is
`O(1/M)`. -/
theorem cubic_count_filter_lower :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ u v α β : ℝ, u ≤ v → Icc u v ⊆ Ioo 0 π → Icc u v ⊆ Ioo α β →
        h / M ≤ u → v ≤ π - h / M →
        (∀ θ ∈ Icc u v, θ ∉ cubicTheta M) →
        ∀ P : Polynomial ℝ, P.map (algebraMap ℝ ℂ) = ftCoeffPoly cubicQ witB 1 M →
        P.map (algebraMap ℝ ℂ) ≠ 0 →
        ∀ [DecidablePred (· ∈ ftWindow (fun θ => cubicZ (cubicTau θ) θ) α β)],
          ((M : ℝ) + 1) * (β - α) / π
              - (((3 / 2 : ℝ) * (β - α)
                  + ((M : ℝ) - 1 / 2) * ((β - α) - (v - u))) / π + 2)
            ≤ (Multiset.card ((P.map (algebraMap ℝ ℂ)).roots.filter
                (· ∈ ftWindow (fun θ => cubicZ (cubicTau θ) θ) α β)) : ℝ) := by
  obtain ⟨h, hh, M₀, hzeros⟩ := cubic_exists_phaseZeros
  refine ⟨h, hh, M₀, fun M hM u v α β huv hsub0 hsubw hu hv hwin P hP hPne _ => ?_⟩
  obtain ⟨-, Z, -, -, hZroot, hZmem, hZcard⟩ :=
    hzeros M hM u v huv hsub0 hu hv hwin P hP
  exact count_filter_lower_of_subarc hPne huv continuous_cubicZ_branch.continuousOn
    hsubw hZroot hZmem hZcard (le_of_eq (by ring))

end ForgacsTran
