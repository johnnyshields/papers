/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EquidistributionCounts
import ForgacsTran.CubicMain

/-!
# `prop:angular-discrepancy` and `prop:equidistribution` at the cubic pencil

`cubic_window_zeros` is the engine: past one threshold in `M`, **every** angular
window `(α,β) ⊆ (0,π)` carries a `Finset` of distinct zeros of `F_M` inside
`z(I_{α,β})` of cardinality at least `(M+1)(β-α)/π - C`, at one `M`-free `C`.
Nothing is assumed about where the window sits.  `ft_angular_discrepancy`,
`ft_equidistribution` and `angular_clock_of_bracketing` take both of their
binders from it, so the three results below are unconditional instances of
`eq:angular-discrepancy`, `eq:normalized-angular-discrepancy` and
`eq:angular-clock`.

## Main statements

* `cubic_window_zeros` — `eq:angular-distinct-lower` at this pencil, for an
  arbitrary window, at one `M`-free constant.
* `cubic_window_counts` — the two counts `ft_equidistribution` binds: the
  multiplicity count inside `z(I_{α,β})` and the distinct counts on the two
  complementary windows.
* `cubic_angular_discrepancy` — the two-sided `eq:angular-discrepancy`.
* `cubic_equidistribution` — `eq:normalized-angular-discrepancy`.
* `cubic_angular_clock` — `eq:angular-clock`, off the half-open window
  `z(I_{0,θ}]` of `ftWindowIoc`.

## Implementation notes

**The shrinking window is what makes the outer count possible.**  Against the
fixed deleted set `cubicTheta M = {θ : \|θ - π/2\| < 1}` the outer count cannot
hold with an `M`-free constant: the two complementary windows cover everything
outside `(α,β)`, so their union contains that middle whatever the window is, and
the phase turning lost across a set of fixed measure `m` is `(M+1)m/π`.  That
forces `C₂ ≥ 2(M+1)/π`, whose ratio to `d` tends to `2/π` rather than to `0`.
`cubic_shrinkingWindow` deletes windows of half-width `h/M` instead, so the total
deleted measure is `4h/M` and the lost turning is bounded by `4h/π` — a
constant.  `scripts/` measures both.

**Two components, and neither is required to be nonempty.**  The deleted set
splits `(0,π)` at `π/2` and at the two endpoints, so an arbitrary window meets
the retained range in at most two components,
`[α+h/M, min(β-h/M, π/2-h/M)]` and `[max(α+h/M, π/2+h/M), β-h/M]`.  Either can
be empty — that is what a window lying wholly on one side of `π/2`, or a window
shorter than `2h/M`, looks like — so `hpiece` returns `∅` there and the length
enters as `max (v-u) 0`.  This is what removes the straddle and clearance
hypotheses: the *sum* of the two clipped lengths is at least `(β-α) - 4h/M`
whatever `α` and `β` are, which is the only fact the count needs.

**The window is shortened by `h/M` at each end** before the phase count is run,
so that the zeros land strictly inside it — that is what `mem_ftWindow_of_subarc`
needs — and that shrink is what puts `α+h/M` and `β-h/M` rather than `α` and `β`
at the ends of the two components above.

**The bridge runs distinct-to-multiplicity, and only there.**  `hin` wants the
multiplicity count and is a lower bound, so `card_le_count_filter` strengthens
it; `hout` wants `Finset.card` of *distinct* zeros and is what the producer gives
directly, so no bridge is applied to it.  Bridging `hout` the same way would be
the backwards application, and it would type-check.

**Containment.**  No hypothesis of `cubic_window_zeros` mentions the zero set:
the binders constrain `M` and the window alone, and the `Finset` in the
conclusion is produced by the phase count.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `prop:equidistribution`,
`eq:normalized-angular-discrepancy`, `cor:angular-rigidity`, `eq:angular-clock`,
`prop:angular-discrepancy`, `eq:angular-distinct-lower`, `eq:retained-range`,
`eq:amplitude-window-negligible`).

## Tags

equidistribution, angular window, angular clock, zero counting, cubic pencil,
shrinking window
-/

namespace ForgacsTran

open Real Set

/-- Paper `cor:panel-B-attractor`'s companion at the cubic pencil — the spectral
reparametrization `z(θ)` of `thm:FT-geometry` along the branch, as one function
rather than a lambda, so that `ftWindow` can be written against it. -/
noncomputable def cubicZbranch : ℝ → ℝ := fun θ => cubicZ (cubicTau θ) θ

theorem cubicZbranch_continuousOn (s : Set ℝ) : ContinuousOn cubicZbranch s :=
  continuous_cubicZ_branch.continuousOn

theorem cubicZbranch_strictMonoOn : StrictMonoOn cubicZbranch (Icc 0 π) :=
  cubicZ_strictMonoOn

/-- **The two clipped lengths cover the window, whatever the window is.**  Delete a
half-width `e` at each of `α`, `β` and the split point `m`; what is retained is at most
two intervals, and their lengths sum to at least `(β - α) - 4e`.

Either may be empty — a window lying wholly on one side of `m`, or one shorter than
`2e`, empties one of them — which is exactly what the `max … 0` carries, and it is why
no straddle hypothesis and no clearance hypothesis are needed.  That the *sum* is
bounded below whatever `α` and `β` do is the only fact the count consumes.

Four cases, on which side of `m` each endpoint falls.  Nothing about the branch enters,
so it is stated over bare reals with `m` free rather than at `π/2`. -/
private theorem clipped_lengths_cover {α β m e : ℝ} (he : 0 ≤ e) :
    (β - α) - 4 * e
      ≤ max (min (β - e) (m - e) - (α + e)) 0
        + max (β - e - max (α + e) (m + e)) 0 := by
  rcases le_or_gt β m with hb | hb
  · rw [min_eq_left (by linarith : β - e ≤ m - e)]
    have k1 := le_max_left (β - e - (α + e)) 0
    have k2 := le_max_right (β - e - max (α + e) (m + e)) 0
    linarith
  · rw [min_eq_right (by linarith : m - e ≤ β - e)]
    rcases le_or_gt m α with ha2 | ha2
    · rw [max_eq_left (by linarith : m + e ≤ α + e)]
      have k1 := le_max_right (m - e - (α + e)) 0
      have k2 := le_max_left (β - e - (α + e)) 0
      linarith
    · rw [max_eq_right (by linarith : α + e ≤ m + e)]
      have k1 := le_max_left (m - e - (α + e)) 0
      have k2 := le_max_left (β - e - (m + e)) 0
      linarith

/-- **`eq:angular-distinct-lower` at the cubic pencil, for an arbitrary window.**
Past one threshold in `M`, for every `0 ≤ α ≤ β ≤ π`, the coefficient polynomial
`F_M` has at least `(M+1)(β-α)/π - C` distinct zeros inside `z(I_{α,β})`, at a
constant `C` that does not move with `M`, with `α`, or with `β`.

Nothing is assumed about the window: it may straddle `π/2`, lie wholly on one
side of it, be anchored at either endpoint of `(0,π)`, or be degenerate. -/
theorem cubic_window_zeros :
    ∃ h > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ α β : ℝ,
      0 ≤ α → α ≤ β → β ≤ π →
        ∃ Z : Finset ℂ,
          (∀ w ∈ Z, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow cubicZbranch α β) ∧
          ((M : ℝ) + 1) * (β - α) / π - C ≤ (Z.card : ℝ) := by
  classical
  obtain ⟨h, hh, M₁, hdomAll⟩ := cubic_shrinkingWindow
  refine ⟨h, hh, 11 / 2 + 4 * h / π, by positivity, max M₁ 1, ?_⟩
  intro M hM α β hα hαβ hβ
  have hM₁ : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set e : ℝ := h / (M : ℝ) with he
  have he0 : 0 < e := div_pos hh hMpos
  have hMe : (M : ℝ) * e = h := by rw [he]; field_simp
  obtain ⟨P, hP⟩ :=
    exists_real_ftCoeffPoly_of_real hasRealCoeffs_cubicQ hasRealCoeffs_witB 1 M
  have hPne : (ftCoeffPoly cubicQ witB 1 M) ≠ 0 := ftCoeffPoly_cubic_ne_zero M
  -- every component sits inside the retained range and is dominated
  have hret : ∀ u v : ℝ, 0 < u → v < π → (∀ θ ∈ Icc u v, θ ≠ π / 2) →
      Icc u v ⊆ cubicRetained := by
    intro u v hu hv hne θ hθ
    exact ⟨⟨lt_of_lt_of_le hu hθ.1, lt_of_le_of_lt hθ.2 hv⟩, hne θ hθ⟩
  have hdomOf : ∀ u v : ℝ, e ≤ u → v ≤ π - e →
      (∀ θ ∈ Icc u v, e ≤ |θ - π / 2|) →
      ∀ θ ∈ Icc u v,
        ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
          ≤ ftPrincipalAmp cubicQ witB 1
              (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2 := by
    intro u v hu hv hmid θ hθ
    exact hdomAll M hM₁ θ (le_trans hu hθ.1) (le_trans hθ.2 hv) (hmid θ hθ)
  -- component data, one call each
  have hcomp : ∀ u v : ℝ, u ≤ v → e ≤ u → v ≤ π - e →
      (∀ θ ∈ Icc u v, e ≤ |θ - π / 2|) →
      ∃ Z : Finset ℂ, (∀ w ∈ Z, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ Complex.ofReal '' Icc (cubicZbranch u) (cubicZbranch v)) ∧
        (((M : ℝ) - 1 / 2) * (v - u) / π - 2 ≤ (Z.card : ℝ)) := by
    intro u v huv heu hev hmid
    have hu : 0 < u := lt_of_lt_of_le he0 heu
    have hv : v < π := lt_of_le_of_lt hev (by linarith)
    have hne : ∀ θ ∈ Icc u v, θ ≠ π / 2 := by
      intro θ hθ hc
      have := hmid θ hθ
      rw [hc] at this
      simp at this
      linarith
    obtain ⟨ψ, Z, -, -, hr, hm, hn⟩ :=
      cubic_phaseZeros_of_dominance huv (hret u v hu hv hne) hM1
        (hdomOf u v heu hev hmid) P hP
    refine ⟨Z, fun w hw => ?_, hm, hn⟩
    rw [← hP]; exact hr w hw
  -- one component, clipped into the window, allowed to be empty
  have hpiece : ∀ u v : ℝ, e ≤ u → v ≤ π - e →
      (∀ θ ∈ Icc u v, e ≤ |θ - π / 2|) → α < u → v < β →
      ∃ Z : Finset ℂ, (∀ w ∈ Z, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftWindow cubicZbranch α β) ∧
        (∀ w ∈ Z, w ∈ Complex.ofReal '' Icc (cubicZbranch u) (cubicZbranch v)) ∧
        (Z.Nonempty → u ≤ v) ∧
        ((M : ℝ) - 1 / 2) * max (v - u) 0 / π - 2 ≤ (Z.card : ℝ) := by
    intro u v heu hev hmid hαu hvβ
    rcases le_or_gt u v with huv | hvu
    · obtain ⟨Z, hr, hm, hn⟩ := hcomp u v huv heu hev hmid
      refine ⟨Z, hr, fun w hw => mem_ftWindow_of_subarc (z := cubicZbranch) huv
          (cubicZbranch_continuousOn _)
          (fun θ hθ => ⟨lt_of_lt_of_le hαu hθ.1, lt_of_le_of_lt hθ.2 hvβ⟩) (hm w hw),
        hm, fun _ => huv, ?_⟩
      rw [max_eq_left (by linarith)]
      exact hn
    · refine ⟨∅, by simp, by simp, by simp, by simp, ?_⟩
      rw [max_eq_right (by linarith)]
      simp
  -- the two components of the window
  obtain ⟨Z₁, hZ₁r, hZ₁w, hZ₁m, hZ₁n, hZ₁c⟩ :=
    hpiece (α + e) (min (β - e) (π / 2 - e)) (by linarith)
      (le_trans (min_le_right _ _) (by linarith))
      (fun θ hθ => by
        have hθ2 : θ ≤ π / 2 - e := le_trans hθ.2 (min_le_right _ _)
        rw [abs_of_nonpos (by linarith)]; linarith)
      (by linarith) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  obtain ⟨Z₂, hZ₂r, hZ₂w, hZ₂m, hZ₂n, hZ₂c⟩ :=
    hpiece (max (α + e) (π / 2 + e)) (β - e)
      (le_trans (by linarith) (le_max_right _ _)) (by linarith)
      (fun θ hθ => by
        have hθ1 : π / 2 + e ≤ θ := le_trans (le_max_right _ _) hθ.1
        rw [abs_of_nonneg (by linarith)]; linarith)
      (lt_of_lt_of_le (by linarith) (le_max_left _ _)) (by linarith)
  -- the two components are separated by the deleted middle, so they share no zero
  have hdisj : Disjoint Z₁ Z₂ := by
    refine Finset.disjoint_left.2 fun w hw1 hw2 => ?_
    -- both components are nonempty here, which is what puts them in order: a
    -- shrinking component can be empty, and then there is nothing to separate
    have h1 := hZ₁n ⟨w, hw1⟩
    have h2 := hZ₂n ⟨w, hw2⟩
    have hv1le : min (β - e) (π / 2 - e) ≤ π / 2 - e := min_le_right _ _
    have hu2ge : π / 2 + e ≤ max (α + e) (π / 2 + e) := le_max_right _ _
    obtain ⟨x, hx, rfl⟩ := hZ₁m w hw1
    obtain ⟨y, hy, hxy⟩ := hZ₂m _ hw2
    have hyx : y = x := by exact_mod_cast hxy
    subst hyx
    have hlt : cubicZbranch (min (β - e) (π / 2 - e))
        < cubicZbranch (max (α + e) (π / 2 + e)) :=
      cubicZbranch_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        (by linarith)
    linarith [hx.2, hy.1]
  -- the two clipped lengths cover the window up to `4h/M`, whatever the window is
  have hlen := clipped_lengths_cover (α := α) (β := β) (m := π / 2) he0.le
  refine ⟨Z₁ ∪ Z₂, fun w hw => (Finset.mem_union.1 hw).elim (hZ₁r w) (hZ₂r w),
    fun w hw => (Finset.mem_union.1 hw).elim (hZ₁w w) (hZ₂w w), ?_⟩
  rw [Finset.card_union_of_disjoint hdisj]
  push_cast
  have hMhalf : (0 : ℝ) ≤ (M : ℝ) - 1 / 2 := by linarith
  have hcov : ((M : ℝ) - 1 / 2) * ((β - α) - 4 * e) / π
      ≤ ((M : ℝ) - 1 / 2) * max (min (β - e) (π / 2 - e) - (α + e)) 0 / π
        + ((M : ℝ) - 1 / 2) * max (β - e - max (α + e) (π / 2 + e)) 0 / π := by
    have hsum : ((M : ℝ) - 1 / 2) * max (min (β - e) (π / 2 - e) - (α + e)) 0 / π
        + ((M : ℝ) - 1 / 2) * max (β - e - max (α + e) (π / 2 + e)) 0 / π
        = ((M : ℝ) - 1 / 2) * (max (min (β - e) (π / 2 - e) - (α + e)) 0
            + max (β - e - max (α + e) (π / 2 + e)) 0) / π := by ring
    rw [hsum, div_le_div_iff₀ hπ hπ]
    have := mul_le_mul_of_nonneg_left hlen hMhalf
    nlinarith [hπ]
  have hexp : ((M : ℝ) - 1 / 2) * ((β - α) - 4 * e) / π
      = ((M : ℝ) + 1) * (β - α) / π - (3 / 2) * (β - α) / π
        - ((M : ℝ) - 1 / 2) * (4 * e) / π := by
    field
  have h32 : (3 / 2 : ℝ) * (β - α) / π ≤ 3 / 2 := by
    rw [div_le_iff₀ hπ]; nlinarith
  have hbig : ((M : ℝ) - 1 / 2) * (4 * e) / π ≤ 4 * h / π := by
    rw [div_le_div_iff₀ hπ hπ]
    nlinarith [hMe, he0, hh]
  linarith [hZ₁c, hZ₂c, hcov, hexp ▸ hcov]

/-! ### The two counts `ft_equidistribution` and `ft_angular_discrepancy` bind -/

/-- **Both window counts of `prop:equidistribution`, at the cubic pencil.**  Past
one threshold in `M`, for **every** window `0 ≤ α ≤ β ≤ π`, the multiplicity
count inside `z(I_{α,β})` and the distinct counts on the two complementary
windows both hold at the single `M`-free constant `C`.

All three are `cubic_window_zeros` — at `(α,β)`, at `(0,α)` and at `(β,π)` — with
`card_le_count_filter` bridging the first from distinct zeros to the
multiplicity count, which is the direction that strengthens a lower bound. -/
theorem cubic_window_counts :
    ∃ h > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ α β : ℝ,
      0 ≤ α → α ≤ β → β ≤ π →
      ∀ [DecidablePred (· ∈ ftWindow cubicZbranch α β)],
        (((M : ℝ) + 1) * (β - α) / π - C
            ≤ (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
                (· ∈ ftWindow cubicZbranch α β)) : ℝ))
          ∧ ∃ Zlo Zhi : Finset ℂ,
              (∀ w ∈ Zlo, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
              (∀ w ∈ Zlo, w ∈ ftWindow cubicZbranch 0 α) ∧
              (∀ w ∈ Zhi, (ftCoeffPoly cubicQ witB 1 M).IsRoot w) ∧
              (∀ w ∈ Zhi, w ∈ ftWindow cubicZbranch β π) ∧
              ((M : ℝ) + 1) * (π - 0) / π - ((M : ℝ) + 1) * (β - α) / π - C
                ≤ (Zlo.card : ℝ) + (Zhi.card : ℝ) := by
  classical
  obtain ⟨h, hh, C, hC, M₀, hz⟩ := cubic_window_zeros
  refine ⟨h, hh, 2 * C, by linarith, M₀, ?_⟩
  intro M hM α β hα hαβ hβ _
  have hπ : (0 : ℝ) < π := Real.pi_pos
  constructor
  · obtain ⟨Z, hZr, hZw, hZc⟩ := hz M hM α β hα hαβ hβ
    have hbridge :=
      card_le_count_filter (ftCoeffPoly_cubic_ne_zero M) (ftWindow cubicZbranch α β) hZr hZw
    have hcast : (Z.card : ℝ)
        ≤ (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
            (· ∈ ftWindow cubicZbranch α β)) : ℝ) := by exact_mod_cast hbridge
    linarith
  · obtain ⟨Zlo, hlor, hlow, hloc⟩ := hz M hM 0 α le_rfl hα (by linarith)
    obtain ⟨Zhi, hhir, hhiw, hhic⟩ := hz M hM β π (by linarith) hβ le_rfl
    refine ⟨Zlo, Zhi, hlor, hlow, hhir, hhiw, ?_⟩
    have harith : ((M : ℝ) + 1) * (π - 0) / π - ((M : ℝ) + 1) * (β - α) / π
        = ((M : ℝ) + 1) * (α - 0) / π + ((M : ℝ) + 1) * (π - β) / π := by
      field
    linarith

/-! ### `eq:angular-discrepancy`, unconditional at this pencil -/

/-- **`eq:angular-discrepancy` at the cubic pencil, two-sided.**  The two counts
fed to `ft_angular_discrepancy`: for every window `0 ≤ α ≤ β ≤ π`, the count in
`z(I_{α,β})` sits within one `M`-free constant of the uniform prediction
`(M+1)(β-α)/π`.

The window is arbitrary — anchored at either endpoint, straddling `π/2` or lying
wholly to one side of it — which is what `cor:angular-rigidity` consumes, since
the windows it brackets an index between are anchored at `0`. -/
theorem cubic_angular_discrepancy :
    ∃ h > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ α β : ℝ,
      0 ≤ α → α ≤ β → β ≤ π →
      ∀ [DecidablePred (· ∈ ftWindow cubicZbranch α β)],
        |(Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
              (· ∈ ftWindow cubicZbranch α β)) : ℝ)
            - ((M : ℝ) + 1) * (β - α) / π| ≤ C := by
  classical
  obtain ⟨h, hh, C, hC, M₀, hcounts⟩ := cubic_window_counts
  refine ⟨h, hh, C, hC, max M₀ 1, ?_⟩
  intro M hM α β hα hαβ hβ _
  have hM₀ : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hin, Zlo, Zhi, hlor, hlom, hhir, hhim, hout⟩ := hcounts M hM₀ α β hα hαβ hβ
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hD : ((ftCoeffPoly cubicQ witB 1 M).natDegree : ℝ)
      ≤ ((M : ℝ) + 1) * (π - 0) / π + 0 := by
    rw [natDegree_ftCoeffPoly_cubic, add_zero, le_div_iff₀ hπ]
    nlinarith
  have hdisc := ft_angular_discrepancy (P := ftCoeffPoly cubicQ witB 1 M)
    (ftCoeffPoly_cubic_ne_zero M) (z := cubicZbranch) (a := 0) (b := π)
    (T := ((M : ℝ) + 1) * (π - 0) / π) (Tab := ((M : ℝ) + 1) * (β - α) / π)
    (C₃ := 0) (cubicZbranch_strictMonoOn.mono Ioo_subset_Icc_self).injOn hα hαβ hβ
    hlor hlom hhir hhim hin hout hD
  rw [add_zero, max_self] at hdisc
  exact hdisc

/-! ### `prop:equidistribution`, unconditional at this pencil -/

/-- **Paper `prop:equidistribution` at the cubic pencil, with nothing assumed.**
Normalized by `deg F_M = M`, the multiplicity count of the zeros of `F_M` in
`z(I_{α,β})` tracks the uniform density `(β-α)/π` with an error `O(1/M)`,
uniformly over every window `0 ≤ α ≤ β ≤ π`.

This is `ft_equidistribution` with both of its binders discharged:
`cubic_window_counts` supplies `hin` and `hout` at one `M`-free constant, the
degree is `natDegree_ftCoeffPoly_cubic`, and the reparametrization is injective
on `[0,π]` because it is strictly monotone there. -/
theorem cubic_equidistribution :
    ∃ h > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ α β : ℝ,
      0 ≤ α → α ≤ β → β ≤ π →
      ∀ [DecidablePred (· ∈ ftWindow cubicZbranch α β)],
        |(Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
              (· ∈ ftWindow cubicZbranch α β)) : ℝ) / (M : ℝ) - (β - α) / π|
          ≤ C / (M : ℝ) := by
  classical
  obtain ⟨h, hh, C, hC, M₀, hcounts⟩ := cubic_window_counts
  refine ⟨h, hh, C + 1, by linarith, max M₀ 1, ?_⟩
  intro M hM α β hα hαβ hβ _
  have hM₀ : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hin, Zlo, Zhi, hlor, hlom, hhir, hhim, hout⟩ := hcounts M hM₀ α β hα hαβ hβ
  have hmain := ft_equidistribution (P := ftCoeffPoly cubicQ witB 1 M)
    (ftCoeffPoly_cubic_ne_zero M) (z := cubicZbranch) (a := 0) (b := π) (α := α) (β := β)
    (C₁ := C) (C₂ := C) (M := M) (r := 1) (d := M) (s := 0)
    le_rfl hM1 (by omega) (by omega)
    (by rw [natDegree_ftCoeffPoly_cubic]; omega) (by norm_num)
    (cubicZbranch_strictMonoOn.mono Ioo_subset_Icc_self).injOn hα hαβ hβ
    hlor hlom hhir hhim hin hout
  rw [max_self] at hmain
  simpa using hmain

/-! ### `cor:angular-rigidity`, unconditional at this pencil -/

/-- **Paper `cor:angular-rigidity` at the cubic pencil, with nothing assumed.**
`eq:angular-clock`: an index `j` bracketed between the number of zeros of `F_M`
of angle strictly below `θ` and the number of angle at most `θ` puts its angle
within `π(C+1)/(M+1)` of the uniform clock `πj/(M+1)`, at an `M`-free `C`.

Both bracketing counts are anchored at `0`, which is the window shape
`cubic_window_zeros` was generalized to cover.  The lower one is
`cubic_window_zeros` at `(0,θ)`; the upper one is the same at `(θ,π)`, subtracted
from `deg F_M = M` by `count_add_card_le_natDegree` — the zeros of angle above
`θ` are not counted in `z(I_{0,θ}]` because `z` is injective on `[0,π]`.

The bracketing hypotheses are those of the paper's own proof: `j_- < j ≤ j_+`
for the two counts.  Neither of them, nor `θ`, is required to name a zero: where
no zero sits at angle `θ` the two counts agree and the statement is vacuous.

**Containment.**  The conclusion relates `θ` to `j`, and the two bracketing
binders name both — as they must, since `j` is *defined* by the bracket.  What
they do not carry is the conclusion: they place `j` between two counts and say
nothing about where those counts sit, and it is `cubic_window_zeros` that puts
each of them within `C` of `(M+1)θ/π`.  Delete either supply and the bound fails,
because nothing then stops both counts from being far from the uniform
prediction. -/
theorem cubic_angular_clock :
    ∃ C ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, 0 ≤ θ → θ ≤ π → ∀ j : ℕ,
      ∀ [DecidablePred (· ∈ ftWindow cubicZbranch 0 θ)]
        [DecidablePred (· ∈ ftWindowIoc cubicZbranch 0 θ)],
        Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
            (· ∈ ftWindow cubicZbranch 0 θ)) < j →
        j ≤ Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
            (· ∈ ftWindowIoc cubicZbranch 0 θ)) →
        |θ - π * (j : ℝ) / ((M : ℝ) + 1)| ≤ π * (C + 1) / ((M : ℝ) + 1) := by
  classical
  obtain ⟨h, hh, C, hC, M₀, hz⟩ := cubic_window_zeros
  refine ⟨C, hC, M₀, ?_⟩
  intro M hM θ hθ0 hθπ j _ _ h1 h2
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hPne : (ftCoeffPoly cubicQ witB 1 M) ≠ 0 := ftCoeffPoly_cubic_ne_zero M
  -- the two anchored supplies
  obtain ⟨Z, hZr, hZw, hZc⟩ := hz M hM 0 θ le_rfl hθ0 hθπ
  obtain ⟨Zhi, hhir, hhiw, hhic⟩ := hz M hM θ π hθ0 hθπ le_rfl
  -- `j_-`, the open window
  have hjmlo : ((M : ℝ) + 1) * θ / π - C
      ≤ (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
          (· ∈ ftWindow cubicZbranch 0 θ)) : ℝ) := by
    have hbridge := card_le_count_filter hPne (ftWindow cubicZbranch 0 θ) hZr hZw
    have hcast : (Z.card : ℝ)
        ≤ (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
            (· ∈ ftWindow cubicZbranch 0 θ)) : ℝ) := by exact_mod_cast hbridge
    have : ((M : ℝ) + 1) * (θ - 0) / π - C ≤ (Z.card : ℝ) := hZc
    simp only [sub_zero] at this
    linarith
  -- `j_+`, the half-open window: the zeros of angle above `θ` are disjoint from it
  have hnot : ∀ w ∈ Zhi, w ∉ ftWindowIoc cubicZbranch 0 θ := by
    intro w hw
    refine notMem_image_of_disjoint (z := cubicZbranch) (s := Icc 0 π)
      cubicZbranch_strictMonoOn.injOn
      (fun x hx => ⟨le_trans hθ0 hx.1.le, hx.2.le⟩)
      (fun x hx => ⟨hx.1.le, le_trans hx.2 hθπ⟩)
      (fun x hx hx' => absurd hx'.2 (not_le.2 hx.1)) (hhiw w hw)
  have hsplit := count_add_card_le_natDegree hPne (ftWindowIoc cubicZbranch 0 θ) hhir hnot
  have hsplitR : (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
        (· ∈ ftWindowIoc cubicZbranch 0 θ)) : ℝ) + (Zhi.card : ℝ) ≤ (M : ℝ) := by
    rw [natDegree_ftCoeffPoly_cubic] at hsplit
    exact_mod_cast hsplit
  have hjphi : (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
        (· ∈ ftWindowIoc cubicZbranch 0 θ)) : ℝ) ≤ ((M : ℝ) + 1) * θ / π + C := by
    have hid : ((M : ℝ) + 1) * (π - θ) / π = ((M : ℝ) + 1) - ((M : ℝ) + 1) * θ / π := by
      field_simp
    rw [hid] at hhic
    linarith
  have hmono : (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
        (· ∈ ftWindow cubicZbranch 0 θ)) : ℝ)
      ≤ (Multiset.card ((ftCoeffPoly cubicQ witB 1 M).roots.filter
        (· ∈ ftWindowIoc cubicZbranch 0 θ)) : ℝ) := by
    exact_mod_cast count_filter_mono
      (P := ftCoeffPoly cubicQ witB 1 M) ftWindow_subset_ftWindowIoc
  refine angular_clock_of_bracketing ?_ ?_ h1 h2
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

end ForgacsTran
