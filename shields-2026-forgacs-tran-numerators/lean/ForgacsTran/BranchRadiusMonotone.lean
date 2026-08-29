/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchRegularity
import ForgacsTran.PencilIndex

/-!
# The principal branch radius does not grow

`PhaseTangency.sum_eVariationOn_of_curvature` closes the phase-state binder against one
geometric hypothesis: the arc's signed curvature `τ² + 2τ'² - ττ''` does not vanish.  This
module proves the first half of what that hypothesis needs — **`τ' ≤ 0`**, the branch radius
is non-increasing across the viewing arc — for the pencils with `n ≤ 2r`.

**The mechanism is an inscribed polygon.**  `ftTauDeriv` is `-(∂_θΣ - r)/∂_τΣ` and `∂_τΣ < 0`
(`ftAngleSumDerivTau_neg`), so `τ' ≤ 0` is exactly `∂_θΣ ≤ r`.  Writing `φ_k = π - θ_k` for
the branch angles, the branch equation `∑_k θ_k = rθ + (n-1)π` becomes `∑_k φ_k = π - rθ`,
and `∂_θΣ ≤ r` becomes

    (n - 2r)·sin θ  ≤  ∑_k sin(θ + 2φ_k).

The `n` angles `θ + 2φ_k` together with `2r - n` copies of `θ` are nonnegative and sum to
exactly `2π`, so they are the arcs of a partition of the circle — and the sum of the sines of
such a partition is twice the area of the inscribed polygon, hence nonnegative.

**The polygon lemma proves itself by merging.**  `sin a + sin b - sin(a+b)` factors as
`4 sin(a/2) sin(b/2) sin((a+b)/2)`, nonnegative whenever `a`, `b` and `a+b` lie in `[0, 2π]`,
so merging two arcs can only lower the sine sum.  Merge down to two arcs and the sum is
`sin a + sin(2π - a) = 0`.

**What this does not do.**  `τ' ≤ 0` is one of two facts the curvature needs; it is not the
curvature.  And the argument above needs `n ≤ 2r`, because that is when the leftover `θ`'s
are on the correct side of the ledger; for `n > 2r` the inequality still holds numerically
(`../scripts/check_branch_convexity.py`) and is not proved here.

## Main statements

* `sin_add_sin_sub_sin_add` — the merge identity.
* `sin_add_le_sin_add_sin` — merging two arcs lowers the sine sum.
* `sum_sin_nonneg_of_sum_eq_two_pi` — the polygon lemma, for a list of arcs.
* `sum_sin_shift_ge` — the polygon lemma in the form the branch equation delivers.
* `ftAngleSumDerivAngle_le` — `∂_θΣ ≤ r` at the principal branch.
* `ftTauDeriv_nonpos` — `τ' ≤ 0`.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`,
  `lem:principal-endpoint-regularity`.
* `Forgacs2017RationalDenominator`, Lemma 2, whose branch equation is the constraint used.
* `../scripts/check_branch_convexity.py`.

## Tags

branch radius, monotonicity, inscribed polygon, angle sum, curvature
-/

namespace ForgacsTran

open Real Set

/-! ### The merge identity and the polygon lemma -/

/-- **`sin a + sin b - sin(a+b)` factors.**  Written at the half angles, which is where the
three sines that control its sign live. -/
theorem sin_add_sin_sub_sin_add (x y : ℝ) :
    Real.sin (2 * x) + Real.sin (2 * y) - Real.sin (2 * x + 2 * y)
      = 4 * Real.sin x * Real.sin y * Real.sin (x + y) := by
  have h : (2 : ℝ) * x + 2 * y = 2 * (x + y) := by ring
  rw [h, Real.sin_two_mul, Real.sin_two_mul, Real.sin_two_mul, Real.sin_add, Real.cos_add]
  linear_combination (-2 * Real.sin x * Real.cos x) * (Real.sin_sq_add_cos_sq y)
    + (-2 * Real.sin y * Real.cos y) * (Real.sin_sq_add_cos_sq x)

/-- **Merging two arcs lowers the sine sum.**  The one step the polygon lemma runs on. -/
theorem sin_add_le_sin_add_sin {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * π) :
    Real.sin (a + b) ≤ Real.sin a + Real.sin b := by
  have key := sin_add_sin_sub_sin_add (a / 2) (b / 2)
  rw [show (2 : ℝ) * (a / 2) + 2 * (b / 2) = a + b by ring,
    show (2 : ℝ) * (a / 2) = a by ring, show (2 : ℝ) * (b / 2) = b by ring] at key
  have hπ : (0 : ℝ) < π := pi_pos
  have hsa : 0 ≤ Real.sin (a / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsb : 0 ≤ Real.sin (b / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsab : 0 ≤ Real.sin (a / 2 + b / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  linarith [key, mul_nonneg (mul_nonneg hsa hsb) hsab]

private theorem sum_sin_nonneg_aux : ∀ (m : ℕ) (L : List ℝ), L.length ≤ m →
    (∀ x ∈ L, 0 ≤ x) → L.sum = 2 * π → 0 ≤ (L.map Real.sin).sum := by
  intro m
  induction m with
  | zero =>
      intro L hlen _ hsum
      rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)] at hsum
      simp only [List.sum_nil] at hsum
      exfalso
      have := pi_pos
      linarith
  | succ m ih =>
      intro L hlen hnn hsum
      match L with
      | [] =>
          simp only [List.sum_nil] at hsum
          exfalso
          have := pi_pos
          linarith
      | [x] =>
          have hx : x = 2 * π := by simpa using hsum
          simp [hx, Real.sin_two_pi]
      | x :: y :: t =>
          have hx : 0 ≤ x := hnn x (by simp)
          have hy : 0 ≤ y := hnn y (by simp)
          have ht : ∀ z ∈ t, 0 ≤ z := fun z hz => hnn z (by simp [hz])
          have hts : 0 ≤ t.sum := List.sum_nonneg ht
          have hsum' : x + y + t.sum = 2 * π := by simpa [add_assoc] using hsum
          have hxy : x + y ≤ 2 * π := by linarith
          have hIH := ih ((x + y) :: t) (by simpa using Nat.succ_le_succ_iff.1 hlen)
            (fun z hz => by
              rcases List.mem_cons.1 hz with rfl | hz'
              · linarith
              · exact ht z hz')
            (by simpa [add_assoc] using hsum')
          have hmerge := sin_add_le_sin_add_sin hx hy hxy
          simp only [List.map_cons, List.sum_cons] at hIH ⊢
          linarith

/-- **The polygon lemma.**  Arcs of a partition of the circle have nonnegative sine sum —
twice the area of the inscribed polygon they cut out.

Proved by merging: `sin(a+b) ≤ sin a + sin b` on arcs, so collapsing the list can only
lower the sum, and two arcs `a`, `2π - a` sum to `0`. -/
theorem sum_sin_nonneg_of_sum_eq_two_pi {L : List ℝ} (hnn : ∀ x ∈ L, 0 ≤ x)
    (hsum : L.sum = 2 * π) : 0 ≤ (L.map Real.sin).sum :=
  sum_sin_nonneg_aux L.length L le_rfl hnn hsum

/-- **The polygon lemma in the shape the branch equation delivers.**  `N` arcs `θ + 2φ_k`
and `M` copies of `θ`, with `Nθ + 2∑φ + Mθ = 2π`. -/
theorem sum_sin_shift_ge {N M : ℕ} {φ : Fin N → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hφ : ∀ k, 0 ≤ φ k)
    (hsum : (N : ℝ) * θ + 2 * ∑ k, φ k + (M : ℝ) * θ = 2 * π) :
    -((M : ℝ) * Real.sin θ) ≤ ∑ k, Real.sin (θ + 2 * φ k) := by
  classical
  set L : List ℝ := List.ofFn (fun k : Fin N => θ + 2 * φ k) ++ List.replicate M θ with hL
  have hnn : ∀ x ∈ L, 0 ≤ x := by
    intro x hx
    rw [hL, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      have := hφ k
      linarith
    · rw [List.eq_of_mem_replicate hx]; exact hθ
  have hsumL : L.sum = 2 * π := by
    rw [hL, List.sum_append, List.sum_ofFn, List.sum_replicate, nsmul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    linarith [hsum]
  have hpoly := sum_sin_nonneg_of_sum_eq_two_pi hnn hsumL
  rw [hL, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
    List.map_replicate, List.sum_replicate, nsmul_eq_mul] at hpoly
  simp only [Function.comp_apply] at hpoly
  linarith

/-! ### The branch equation, and `τ' ≤ 0`

`ftAngleSumDerivAngle` sums `sin θ_k · cos(θ_k - θ)/sin θ`, and `2 sin y cos(y - θ)` is
`sin(2y - θ) + sin θ`.  So the `θ`-partial is `(∑_k sin(2θ_k - θ) + n sin θ)/(2 sin θ)`, and
`∂_θΣ ≤ r` is `∑_k sin(2θ_k - θ) ≤ (2r - n) sin θ`.  Reflecting each angle through `π` turns
that into the polygon lemma. -/

/-- `sin(2y - θ) + sin θ = 2 sin y cos(y - θ)`, the product-to-sum step. -/
private theorem sin_two_sub_add_sin (y θ : ℝ) :
    Real.sin (2 * y - θ) + Real.sin θ = 2 * Real.sin y * Real.cos (y - θ) := by
  have h1 := Real.sin_add y (y - θ)
  rw [show y + (y - θ) = 2 * y - θ by ring] at h1
  have h2 := Real.sin_sub y (y - θ)
  rw [show y - (y - θ) = θ by ring] at h2
  linarith

/-- **`∂_θΣ ≤ r` at the principal branch.**  The branch angles reflect to arcs of a partition
of the circle, and the polygon lemma bounds their sine sum.

`n ≤ 2r` is what puts the leftover copies of `θ` on the correct side; the inequality holds
without it numerically and is not proved here. -/
theorem ftAngleSumDerivAngle_le {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : n ≤ 2 * r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hb : FTBranchAt a r (n - 1) θ) :
    ftAngleSumDerivAngle a (ftTau a r (n - 1) θ) θ ≤ r := by
  classical
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  set τ := ftTau a r (n - 1) θ with hτdef
  have hτ : 0 < τ := ftTau_pos hb
  set y : Fin n → ℝ := fun k => ftAngle (a k) τ θ with hydef
  have hymem : ∀ k, y k ∈ Ioo θ π := fun k => ftAngle_mem_Ioo (ha k) hτ hθπ
  -- the branch equation, as a statement about the reflected angles `φ k = π - y k`
  have hbranch : ∑ k, y k = r * θ + ((n : ℝ) - 1) * π := by
    have h := ftAngleSum_ftTau hb
    rw [ftAngleSum] at h
    rw [hydef]
    rw [h, cast_pred_eq_sub_one hn]
  set φ : Fin n → ℝ := fun k => π - y k with hφdef
  have hφnn : ∀ k, 0 ≤ φ k := fun k => by
    have := (hymem k).2
    simp only [hφdef]
    linarith
  have hφsum : ∑ k, φ k = π - r * θ := by
    simp only [hφdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hbranch]
    ring
  -- the polygon lemma on the `n` arcs `θ + 2 φ k` and the `2r - n` copies of `θ`
  have hcast : ((2 * r - n : ℕ) : ℝ) = 2 * r - n := by
    rw [Nat.cast_sub hnr]; push_cast; ring
  have hpoly := sum_sin_shift_ge (N := n) (M := 2 * r - n) (φ := φ) (θ := θ)
    hθπ.1.le hφnn (by rw [hcast, hφsum]; ring)
  rw [hcast] at hpoly
  -- each shifted arc is minus the angle the partial is written in
  have hrefl : ∀ k, Real.sin (θ + 2 * φ k) = -Real.sin (2 * y k - θ) := by
    intro k
    simp only [hφdef]
    rw [show θ + 2 * (π - y k) = -(2 * y k - θ) + 2 * π by ring, Real.sin_add_two_pi,
      Real.sin_neg]
  rw [Finset.sum_congr rfl (fun k _ => hrefl k), Finset.sum_neg_distrib] at hpoly
  -- assemble the partial
  have hy : ∀ k, y k = ftAngle (a k) τ θ := fun _ => rfl
  rw [ftAngleSumDerivAngle]
  simp only [← hy]
  have hsplit : ∑ k, Real.sin (y k) * Real.cos (y k - θ) / Real.sin θ
      = (∑ k, Real.sin (y k) * Real.cos (y k - θ)) / Real.sin θ := by
    rw [Finset.sum_div]
  rw [hsplit, div_le_iff₀ hsin]
  have hprod : ∑ k, Real.sin (y k) * Real.cos (y k - θ)
      = (∑ k, Real.sin (2 * y k - θ) + (n : ℝ) * Real.sin θ) / 2 := by
    have hpt : ∀ k : Fin n, Real.sin (y k) * Real.cos (y k - θ)
        = (Real.sin (2 * y k - θ) + Real.sin θ) / 2 := fun k => by
      linarith [sin_two_sub_add_sin (y k) θ]
    rw [Finset.sum_congr rfl (fun k _ => hpt k), ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hprod]
  have hn2 : (n : ℝ) ≤ 2 * r := by exact_mod_cast hnr
  linarith [hpoly]

/-- **`τ' ≤ 0`: the principal branch radius does not grow across the viewing arc.**
`ftTauDeriv` is `-(∂_θΣ - r)/∂_τΣ`, the numerator is nonnegative by
`ftAngleSumDerivAngle_le` and the denominator is negative by `ftAngleSumDerivTau_neg`.

**The bound is attained**, so it cannot be improved to a strict one: at `a = ![1,1]`, `r = 1`
the branch is the unit circle and `τ` is constant. -/
theorem ftTauDeriv_nonpos {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : n ≤ 2 * r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hb : FTBranchAt a r (n - 1) θ) :
    ftTauDeriv a r (n - 1) θ ≤ 0 := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hτ : 0 < ftTau a r (n - 1) θ := ftTau_pos hb
  have hneg : ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ < 0 :=
    ftAngleSumDerivTau_neg hn ha hτ hθπ
  have hle := ftAngleSumDerivAngle_le hn ha hr hnr hθ hb
  rw [ftTauDeriv]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le

/-- **The branch radius is antitone on the viewing arc**, the mean-value form of
`ftTauDeriv_nonpos`.  This is the statement a later pass consumes: it needs no derivative at
the point of use. -/
theorem antitoneOn_ftTau {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr2 : 2 ≤ n ∨ 2 ≤ r) (hnr : n ≤ 2 * r) :
    AntitoneOn (ftTau a r (n - 1)) (Ioo 0 (π / r)) := by
  have hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr2 hθ
  have hd : ∀ θ ∈ Ioo 0 (π / r),
      HasDerivAt (ftTau a r (n - 1)) (ftTauDeriv a r (n - 1) θ) θ :=
    fun θ hθ => hasDerivAt_ftTau hn ha hr hθ hb
  refine antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
    (fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ => by
      rw [interior_Ioo] at hθ
      exact (hd θ hθ).differentiableAt.differentiableWithinAt)
    (fun θ hθ => ?_)
  rw [interior_Ioo] at hθ
  rw [(hd θ hθ).deriv]
  exact ftTauDeriv_nonpos hn ha hr hnr hθ (hb θ hθ)

end ForgacsTran
