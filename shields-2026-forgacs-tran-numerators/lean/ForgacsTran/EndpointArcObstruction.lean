/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperPackage
import ForgacsTran.FTBranchZMono

/-!
# The closed arc is the wrong domain for the branch data

`thm:FT-geometry` builds `τ` and `z` on the **open** arc `(0, π/r)`, and
`eq:ab-def` puts the upper endpoint at `b = +∞` whenever `r > 1`.  The consumers
in `MainFT` ask instead for `0 < τ` and `StrictMonoOn z` on the **closed**
`Icc 0 (π/r)`.  Both fail at the branch the general supply produces, and this
module proves it.

The radius is the easy half: `ftTauArc` is `0` at `π/r` by construction, because
the branch runs into the origin there, so no positivity hypothesis on a set
containing `π/r` can hold.

The spectral parameter is the interesting half, and the mechanism is *not* the
division convention.  `ftTau` is a classical choice guarded by `FTBranchAt`, and
its fallback value is `1`, not `0`.  At `θ = π/r` the branch equation asks for
`∑_k θ_k = nπ` while every `θ_k` is strictly below `π`, so `FTBranchAt` is false
and the fallback fires: `ftTau … (π/r) = 1`.  The endpoint value of `ftBranchZ`
is therefore the finite positive number the pencil takes at unit radius, while
the branch itself diverges to `+∞` there
(`FTBranchEndpointUpper.tendsto_ftBranchZ_atTop_arc_end_of_pos`).  A strictly
increasing function on `Icc 0 (π/r)` would have to dominate its own blowup, so
`StrictMonoOn` on the closed arc is false.

What survives is the half-open statement `ftBranchZLower_strictMonoOn_Ico`, which
adjoins only the lower endpoint — where the value `0` really is the limit.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `thm:FT-geometry`, `lem:principal-endpoint-regularity`,
  `eq:principal-infinite-endpoint-regularity`.

## Tags

upper endpoint, viewing arc, branch radius, strict monotonicity, Forgács–Tran
-/

namespace ForgacsTran

open Real Set Filter Topology

/-! ### The radius: `0 < τ` fails on the closed arc -/

/-- **The positivity binder is false on the closed arc.**  The branch runs into
the origin at `π/r`, which is what `ftTauArc_arc_end` records, so no hypothesis
of the form `∀ θ ∈ Icc 0 (π/r), 0 < τ θ` is available at this radius.  Nothing
about the pencil enters: the failure is at the endpoint's definition. -/
theorem not_forall_ftTauArc_pos {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    ¬ ∀ θ ∈ Icc (0 : ℝ) (π / r), 0 < ftTauArc a r l x₁ θ := by
  intro h
  have hmem : (π / r) ∈ Icc (0 : ℝ) (π / r) :=
    ⟨div_nonneg pi_pos.le (Nat.cast_nonneg r), le_rfl⟩
  have := h _ hmem
  rw [ftTauArc_arc_end] at this
  exact lt_irrefl 0 this

/-! ### The radius at the upper endpoint is the fallback `1`, not `0` -/

/-- **The branch equation has no solution at the arc's upper end.**  At `θ = π/r`
clause (ii) reads `∑_k θ_k = nπ`, and every branch angle is strictly below `π`
(`ftAngle_lt_pi`), so the sum is strictly below `nπ` at every radius. -/
theorem not_ftBranchAt_arc_end {n r : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (hr : 1 ≤ r) :
    ¬ FTBranchAt a r (n - 1) (π / r) := by
  rintro ⟨τ, -, hsum⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlt : ftAngleSum a τ (π / r) < n * π := by
    rw [ftAngleSum]
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
    calc ∑ k, ftAngle (a k) τ (π / r)
        < ∑ _k : Fin n, π :=
          Finset.sum_lt_sum_of_nonempty hne fun k _ => ftAngle_lt_pi (a k) τ (π / r)
      _ = n * π := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [hsum, hcast] at hlt
  rw [mul_div_cancel₀ π hr0.ne'] at hlt
  nlinarith [hlt]

/-- **The radius at the arc's upper end is the classical fallback.**  `ftTau` is
`Classical.choose` guarded by `FTBranchAt`, whose `else` branch is `1`; the guard
is false at `π/r` by `not_ftBranchAt_arc_end`.  So the endpoint value is `1` —
in particular it is **not** `0`, and no division-by-zero convention is in play at
`ftBranchZ (π/r)`. -/
theorem ftTau_arc_end_eq_one {n r : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (hr : 1 ≤ r) :
    ftTau a r (n - 1) (π / r) = 1 := by
  rw [ftTau, dif_neg (not_ftBranchAt_arc_end a hn hr)]

/-- The endpoint value of the spectral parameter, in closed form: the chord
product of the pencil read at unit radius. -/
theorem ftBranchZ_arc_end_eq {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n) (hr : 1 ≤ r) :
    ftBranchZ a c r (n - 1) (π / r)
      = c * ∏ k, ftChord (a k) (π / r) (ftAngle (a k) 1 (π / r)) := by
  have hone := ftTau_arc_end_eq_one a hn hr
  have hprod : (∏ k, ftChord (a k) (π / r) (ftBranchAngle a r (n - 1) k (π / r)))
      = ∏ k, ftChord (a k) (π / r) (ftAngle (a k) 1 (π / r)) :=
    Finset.prod_congr rfl fun k _ => by rw [ftBranchAngle, hone]
  rw [ftBranchZ, hprod, hone, one_pow, div_one, (even_add_pred_add_one hn).neg_one_pow,
    one_mul]

/-- The endpoint value is a finite **positive** number.  This is what the
divergence at `π/r` has to be reconciled with, and cannot be. -/
theorem ftBranchZ_arc_end_pos {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    0 < ftBranchZ a c r (n - 1) (π / r) := by
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have harc : (π / r) ∈ Ioo (0 : ℝ) π := by
    refine ⟨div_pos pi_pos hr0, ?_⟩
    rw [div_lt_iff₀ hr0]
    nlinarith [pi_pos]
  rw [ftBranchZ_arc_end_eq hn hr1]
  refine mul_pos hc (Finset.prod_pos fun k _ => ?_)
  exact ftChord_pos (ha k) harc (ftAngle_mem_Ioo (ha k) one_pos harc)

/-! ### `StrictMonoOn` fails on the closed arc -/

/-- **The monotonicity binder is false on the closed arc, at `2 ≤ r`.**  The
spectral parameter diverges to `+∞` at the arc's upper end — `eq:ab-def`'s
`b = +∞` — while its value *at* `π/r` is the finite positive number
`ftBranchZ_arc_end_pos` names.  A strictly increasing function on
`Icc 0 (π/r)` would have to bound its own blowup by that value.

The refutation is uniform over the admissible pencils: every `n ≥ 1`, every
`c > 0`, every positive zero set and every `r ≥ 2`. -/
theorem not_ftBranchZLower_strictMonoOn_Icc {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    ¬ StrictMonoOn (ftBranchZLower a c r (n - 1)) (Icc 0 (π / r)) := by
  intro hmono
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have harc : (0 : ℝ) < π / r := div_pos pi_pos hr0
  set V : ℝ := ftBranchZLower a c r (n - 1) (π / r) with hV
  have hVmem : (π / r) ∈ Icc (0 : ℝ) (π / r) := ⟨harc.le, le_rfl⟩
  -- the whole open arc is below the endpoint value
  have hbelow : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ftBranchZ a c r (n - 1) θ < V := by
    intro θ hθ
    have hθmem : θ ∈ Icc (0 : ℝ) (π / r) := ⟨hθ.1.le, hθ.2.le⟩
    have := hmono hθmem hVmem hθ.2
    rwa [ftBranchZLower_agree a c r (n - 1) hθ.1] at this
  -- but the branch diverges upward there
  have hne : (𝓝[Ioo (0 : ℝ) (π / r)] (π / r)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsLT harc]
    infer_instance
  have hev := (tendsto_ftBranchZ_atTop_arc_end_of_pos hn ha hc hr).eventually_gt_atTop V
  obtain ⟨θ, hθz, hθarc⟩ := (hev.and self_mem_nhdsWithin).exists
  exact absurd (hbelow θ hθarc) (not_lt.2 hθz.le)

/-! ### What survives: the half-open arc -/

/-- **`z` is strictly increasing on `Ico 0 (π/r)`.**  Adjoining the *lower*
endpoint is legitimate — there the extension takes the value `0`, which is the
limit `a = g(x_1)` of `eq:ab-def` at a repeated smallest zero — and positivity of
`z` on the open arc supplies the one comparison the extension adds. -/
theorem ftBranchZLower_strictMonoOn_Ico {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hpar : Even (n + l + 1))
    (hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r l θ) :
    StrictMonoOn (ftBranchZLower a c r l) (Ico 0 (π / r)) := by
  intro x hx y hy hxy
  have hy0 : (0 : ℝ) < y := lt_of_le_of_lt hx.1 hxy
  have hyarc : y ∈ Ioo (0 : ℝ) (π / r) := ⟨hy0, hy.2⟩
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, ftBranchZLower_zero, ftBranchZLower_agree a c r l hy0]
    exact ftBranchZ_pos ha hc hpar (ftArc_subset hr hyarc) (hb y hyarc)
  · rw [ftBranchZLower_agree a c r l hx0, ftBranchZLower_agree a c r l hy0]
    exact ftBranchZ_strictMonoOn hn ha hc hr hpar hb ⟨hx0, hx.2⟩ hyarc hxy

/-- `ftBranchZLower_strictMonoOn_Ico` at the principal index, with the branch
equation discharged across the arc. -/
theorem ftBranchZLower_strictMonoOn_Ico_principal {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    StrictMonoOn (ftBranchZLower a c r (n - 1)) (Ico 0 (π / r)) :=
  ftBranchZLower_strictMonoOn_Ico hn ha hc hr (even_add_pred_add_one hn)
    fun _ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ

end ForgacsTran
