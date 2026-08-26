/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Shields.Analysis.Complex.NewtonInterpolation

/-!
# Deforming a circle outward past a cluster of poles

Cauchy's theorem in Mathlib moves a contour across a region with **no** hole
(`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`) or across a **concentric**
annulus (`circleIntegral_eq_of_differentiable_on_annulus_off_countable`).  What a residue
computation needs is the doubly-connected case: two concentric circles with a small disc
between them carrying the poles, the small disc not concentric with either.

For a function of the form `h/∏_{i<k}(z - a_i)` with `h` analytic on the annulus and every node
in the small disc, that case follows from the two Mathlib theorems with no new complex analysis.
`Shields.exists_newton_form_div` splits the function into proper rational terms plus an analytic
remainder; the remainder moves by the concentric annulus theorem and integrates to zero over the
small circle, and each rational term is evaluated outright:

* over a circle enclosing all of its nodes it is `2πi` when it has one factor and `0` when it has
  two or more;
* over a circle enclosing none of them it is `0`.

The vanishing for two or more factors is where the geometry enters, and it is elementary: the
integrand is `O(|z|^{-2})` at infinity and analytic outside the nodes, so the concentric annulus
theorem makes the integral independent of the radius while the length-times-supremum bound sends
it to zero.

**Repeated nodes are allowed throughout.**  Nothing here separates them, because nothing here
computes an individual residue: the Newton form is Hermite's when nodes collide, and the two
integral values above do not see multiplicity.

## Main results

* `Shields.circleIntegral_prod_inv_eq_zero_of_notMem`: no node enclosed.
* `Shields.circleIntegral_prod_inv_of_card_one`, `Shields.circleIntegral_prod_inv_eq_zero`:
  the two enclosed cases.
* `Shields.circleIntegral_cluster_deform`: **the deformation.**

## Tags

Cauchy theorem, contour deformation, residue, cluster, doubly connected, annulus
-/

open Set Metric Complex Filter

open scoped Real Topology

namespace Shields

/-! ### The integral of a product of inverse linear factors -/

/-- The integrand `(∏_{i ∈ S}(z - a_i))⁻¹` is continuous off the nodes. -/
theorem continuousOn_prod_inv {S : Finset ℕ} {a : ℕ → ℂ} {K : Set ℂ}
    (h : ∀ z ∈ K, ∀ i ∈ S, z ≠ a i) :
    ContinuousOn (fun z : ℂ => (∏ i ∈ S, (z - a i))⁻¹) K := by
  refine ContinuousOn.inv₀ (continuousOn_finsetProd _ fun i _ => ?_) fun z hz => ?_
  · exact continuousOn_id.sub continuousOn_const
  · exact Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (h z hz i hi)

/-- The integrand is differentiable off the nodes. -/
theorem differentiableAt_prod_inv {S : Finset ℕ} {a : ℕ → ℂ} {z : ℂ}
    (h : ∀ i ∈ S, z ≠ a i) :
    DifferentiableAt ℂ (fun w : ℂ => (∏ i ∈ S, (w - a i))⁻¹) z := by
  refine DifferentiableAt.inv ?_ (Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (h i hi))
  exact DifferentiableAt.fun_finsetProd fun i _ => differentiableAt_id.sub_const _

/-- **No node enclosed: the integral vanishes.**  The integrand is analytic on the closed disc,
so this is Cauchy's theorem. -/
theorem circleIntegral_prod_inv_eq_zero_of_notMem {S : Finset ℕ} {a : ℕ → ℂ} {c : ℂ} {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ i ∈ S, s < ‖a i - c‖) :
    (∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹) = 0 := by
  have hne : ∀ z ∈ closedBall c s, ∀ i ∈ S, z ≠ a i := by
    intro z hz i hi hzi
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [hzi] at hz
    exact absurd hz (not_le.mpr (h i hi))
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hs Set.countable_empty
    (continuousOn_prod_inv hne) fun z hz => ?_
  exact differentiableAt_prod_inv (hne z (ball_subset_closedBall hz.1))

/-- **One factor: the integral is `2πi`.** -/
theorem circleIntegral_prod_inv_of_card_one {S : Finset ℕ} {a : ℕ → ℂ} {c : ℂ} {s : ℝ}
    {i₀ : ℕ} (hS : S = {i₀}) (h : a i₀ ∈ ball c s) :
    (∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹) = 2 * π * I := by
  subst hS
  simpa using circleIntegral.integral_sub_inv_of_mem_ball h

/-- **Two or more factors, all enclosed: the integral vanishes.**  The concentric annulus
theorem makes the integral independent of the radius above the nodes, and the
length-times-supremum bound `2πS(S - M)^{-|S|}` sends it to zero as the radius grows.  This is
the only place the geometry of the nodes enters, and it needs no separation of them. -/
theorem circleIntegral_prod_inv_eq_zero {S : Finset ℕ} {a : ℕ → ℂ} {c : ℂ} {s M : ℝ}
    (hs : 0 < s) (hM : 0 ≤ M) (hMs : M < s) (hcard : 2 ≤ S.card)
    (h : ∀ i ∈ S, ‖a i - c‖ ≤ M) :
    (∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹) = 0 := by
  -- the integral does not change when the radius grows
  have hstep : ∀ T : ℝ, s ≤ T →
      (∮ z in C(c, T), (∏ i ∈ S, (z - a i))⁻¹) = ∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹ := by
    intro T hT
    have hne : ∀ z ∈ closedBall c T \ ball c s, ∀ i ∈ S, z ≠ a i := by
      intro z hz i hi hzi
      have hz2 := hz.2
      rw [mem_ball, dist_eq_norm, not_lt] at hz2
      rw [hzi] at hz2
      exact absurd (h i hi) (not_le.mpr (lt_of_lt_of_le hMs hz2))
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hs hT Set.countable_empty
      (continuousOn_prod_inv hne) fun z hz => ?_
    refine differentiableAt_prod_inv (hne z ⟨?_, ?_⟩)
    · exact ball_subset_closedBall hz.1.1
    · intro hmem
      exact hz.1.2 (ball_subset_closedBall hmem)
  -- and it is arbitrarily small
  have hbound : ∀ ε : ℝ, 0 < ε → ‖∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹‖ ≤ ε := by
    intro ε hε
    obtain ⟨T, hT1, hTs, hTε⟩ : ∃ T : ℝ, 1 ≤ T ∧ s ≤ M + T ∧ 2 * π * (M + 1) / T ≤ ε := by
      obtain ⟨T, hT⟩ := exists_nat_gt (max (max 1 s) (2 * π * (M + 1) / ε))
      refine ⟨(T : ℝ), ?_, ?_, ?_⟩
      · exact le_of_lt (lt_of_le_of_lt (le_trans (le_max_left 1 s) (le_max_left _ _)) hT)
      · have : s ≤ (T : ℝ) := le_of_lt (lt_of_le_of_lt
          (le_trans (le_max_right 1 s) (le_max_left _ _)) hT)
        linarith
      · have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num)
          (le_of_lt (lt_of_le_of_lt (le_trans (le_max_left 1 s) (le_max_left _ _)) hT))
        rw [div_le_iff₀ hTpos]
        have hlt : 2 * π * (M + 1) / ε < (T : ℝ) := lt_of_le_of_lt (le_max_right _ _) hT
        rw [div_lt_iff₀ hε] at hlt
        nlinarith
    set T' : ℝ := M + T with hT'
    have hT'pos : 0 < T' := by rw [hT']; linarith
    have hTpos : (0 : ℝ) < T := by linarith
    have hsup : ∀ z ∈ sphere c T', ‖(∏ i ∈ S, (z - a i))⁻¹‖ ≤ (T ^ 2)⁻¹ := by
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      have hfac : ∀ i ∈ S, T ≤ ‖z - a i‖ := by
        intro i hi
        have h1 : ‖z - c‖ - ‖a i - c‖ ≤ ‖z - a i‖ := by
          have hnn := norm_sub_norm_le (z - c) (a i - c)
          simpa [sub_sub_sub_cancel_right] using hnn
        have h2 := h i hi
        rw [hz, hT'] at h1
        linarith
      have hprod : T ^ S.card ≤ ‖∏ i ∈ S, (z - a i)‖ := by
        rw [norm_prod]
        calc T ^ S.card = ∏ _i ∈ S, T := by rw [Finset.prod_const]
          _ ≤ ∏ i ∈ S, ‖z - a i‖ :=
              Finset.prod_le_prod (fun i _ => by linarith) (fun i hi => hfac i hi)
      have hpow2 : T ^ (2 : ℕ) ≤ T ^ S.card := pow_le_pow_right₀ hT1 hcard
      have hppos : (0 : ℝ) < T ^ (2 : ℕ) := by positivity
      have hlow : T ^ (2 : ℕ) ≤ ‖∏ i ∈ S, (z - a i)‖ := le_trans hpow2 hprod
      rw [norm_inv, inv_le_inv₀ (lt_of_lt_of_le hppos hlow) hppos]
      exact hlow
    have hnorm := circleIntegral.norm_integral_le_of_norm_le_const (c := c) (R := T')
      hT'pos.le hsup
    rw [hstep T' hTs] at hnorm
    refine hnorm.trans ?_
    have hkey : 2 * π * T' * (T ^ 2)⁻¹ ≤ 2 * π * (M + 1) / T := by
      rw [hT', div_eq_mul_inv]
      have hexp : 2 * π * (M + 1) * T⁻¹ - 2 * π * (M + T) * (T ^ 2)⁻¹
          = 2 * π * (M * T - M) * (T ^ 2)⁻¹ := by
        field
      have hnn : 0 ≤ 2 * π * (M * T - M) * (T ^ 2)⁻¹ := by
        have h1 : (0 : ℝ) ≤ M * T - M := by nlinarith
        have h2 : (0 : ℝ) ≤ (T ^ 2)⁻¹ := by positivity
        have h3 : (0 : ℝ) ≤ 2 * π := by positivity
        exact mul_nonneg (mul_nonneg h3 h1) h2
      have hfin : 0 ≤ 2 * π * (M + 1) * T⁻¹ - 2 * π * (M + T) * (T ^ 2)⁻¹ := by
        rw [hexp]; exact hnn
      linarith
    exact hkey.trans hTε
  by_contra hI
  have hpos : 0 < ‖∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹‖ := norm_pos_iff.mpr hI
  have hhalf := hbound (‖∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹‖ / 2) (by linarith)
  linarith

/-- The enclosed-node form of the vanishing: two or more nodes, all in the open disc. -/
theorem circleIntegral_prod_inv_eq_zero_of_mem {S : Finset ℕ} {a : ℕ → ℂ} {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hcard : 2 ≤ S.card) (h : ∀ i ∈ S, a i ∈ ball c s) :
    (∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹) = 0 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set M : ℝ := S.sup' hne (fun i => ‖a i - c‖) with hMdef
  have hMs : M < s := by
    rw [hMdef, Finset.sup'_lt_iff]
    intro i hi
    have := h i hi
    rwa [mem_ball, dist_eq_norm] at this
  have hM : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hne
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun i => ‖a i - c‖) hi)
  exact circleIntegral_prod_inv_eq_zero hs hM hMs hcard
    (fun i hi => Finset.le_sup' (fun i => ‖a i - c‖) hi)

/-! ### The deformation -/

/-- The three-circle evaluation of one Newton term.  On a circle avoiding the nodes, the term
`d_j (∏_{i ∈ S}(z - a_i))⁻¹` integrates to `d_j · 2πi` when `S` is a singleton whose node the
circle encloses, and to `0` in the other two cases the deformation meets: `S` of two or more
enclosed nodes, and `S` of nodes all outside. -/
theorem circleIntegral_newton_term {S : Finset ℕ} {a : ℕ → ℂ} {c : ℂ} {s : ℝ} (hs : 0 < s)
    (hcard : 1 ≤ S.card) (h : ∀ i ∈ S, a i ∈ ball c s) :
    (∮ z in C(c, s), (∏ i ∈ S, (z - a i))⁻¹) = if S.card = 1 then 2 * π * I else 0 := by
  rcases eq_or_lt_of_le hcard with hone | htwo
  · rw [if_pos hone.symm]
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hone.symm
    exact circleIntegral_prod_inv_of_card_one hi₀
      (h i₀ (by rw [hi₀]; exact Finset.mem_singleton_self _))
  · rw [if_neg (by omega)]
    exact circleIntegral_prod_inv_eq_zero_of_mem hs (by omega) h

/-- The decomposition of the integral over one circle avoiding the nodes: the Newton terms with
their coefficients, plus the analytic remainder.  This is the common step of the two theorems
below, which differ only in how they evaluate the pieces. -/
private theorem circleIntegral_div_prod_eq {k : ℕ} {a : ℕ → ℂ} {h q : ℂ → ℂ}
    {d : ℕ → ℂ}
    (hrep : ∀ z, (∀ i ∈ Finset.range k, z ≠ a i) →
      h z / ∏ i ∈ Finset.range k, (z - a i)
        = (∑ j ∈ Finset.range k, d j / ∏ i ∈ Finset.Ico j k, (z - a i)) + q z)
    (cc : ℂ) (ss : ℝ) (hss : 0 ≤ ss)
    (hne : ∀ z ∈ sphere cc ss, ∀ i ∈ Finset.range k, z ≠ a i)
    (hqc : ContinuousOn q (sphere cc ss)) :
    (∮ z in C(cc, ss), h z / ∏ i ∈ Finset.range k, (z - a i))
      = (∑ j ∈ Finset.range k, d j * ∮ z in C(cc, ss), (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹)
        + ∮ z in C(cc, ss), q z := by
  have hterm : ∀ j ∈ Finset.range k,
      ContinuousOn (fun z : ℂ => d j * (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹) (sphere cc ss) := by
    intro j _
    refine continuousOn_const.mul (continuousOn_prod_inv ?_)
    intro z hz i hi
    exact hne z hz i (Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
  have hsum : CircleIntegrable
      (fun z : ℂ => ∑ j ∈ Finset.range k, d j * (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹) cc ss :=
    ContinuousOn.circleIntegrable hss (continuousOn_finsetSum _ hterm)
  have hqi : CircleIntegrable q cc ss := ContinuousOn.circleIntegrable hss hqc
  have hcongr : (∮ z in C(cc, ss), h z / ∏ i ∈ Finset.range k, (z - a i))
      = ∮ z in C(cc, ss),
          ((∑ j ∈ Finset.range k, d j * (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹) + q z) := by
    refine circleIntegral.integral_congr hss fun z hz => ?_
    rw [hrep z (hne z hz)]
    simp only [div_eq_mul_inv]
  rw [hcongr, circleIntegral.integral_add hsum hqi,
    circleIntegral.integral_fun_sum (fun j hj =>
      ContinuousOn.circleIntegrable hss (hterm j hj))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _

/-- **Deforming a circle outward past a cluster of poles.**  Let `h` be analytic on an open set
covering the closed annulus `ρ ≤ |z| ≤ R`, let every node lie in a disc `closedBall τ rr`
contained in the open annulus, and consider `g = h/∏_{i<k}(z - a_i)`.  Then

    ∮_{|z|=R} g = ∮_{|z|=ρ} g + ∮_{|z-τ|=rr} g .

The nodes may repeat in any pattern.  The proof splits `g` by `exists_newton_form_div`: the
analytic remainder moves between the two concentric circles by Cauchy's annulus theorem and
integrates to zero over the small one, and each rational term takes the same value on `|z| = R`
as on `|z - τ| = rr` and vanishes on `|z| = ρ`. -/
theorem circleIntegral_cluster_deform {ρ R rr : ℝ} {τ : ℂ} {A : Set ℂ} (hA : IsOpen A)
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h A) (k : ℕ) (a : ℕ → ℂ)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hrr : 0 < rr)
    (hnode : ∀ i, a i ∈ ball τ rr)
    (hAann : closedBall (0 : ℂ) R \ ball (0 : ℂ) ρ ⊆ A)
    (hsmall : closedBall τ rr ⊆ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ) :
    (∮ z in C((0 : ℂ), R), h z / ∏ i ∈ Finset.range k, (z - a i))
      = (∮ z in C((0 : ℂ), ρ), h z / ∏ i ∈ Finset.range k, (z - a i))
        + ∮ z in C(τ, rr), h z / ∏ i ∈ Finset.range k, (z - a i) := by
  have hballA : closedBall τ rr ⊆ A := by
    intro z hz
    refine hAann ⟨ball_subset_closedBall (hsmall hz).1, fun hmem => (hsmall hz).2 ?_⟩
    exact ball_subset_closedBall hmem
  have hAnode : ∀ i, a i ∈ A := fun i => hballA (ball_subset_closedBall (hnode i))
  obtain ⟨d, q, hq, hrep⟩ := exists_newton_form_div hA a hAnode k hh
  -- the nodes lie strictly inside the small disc, hence inside `|z| < R` and outside `|z| ≤ ρ`
  have hnodeR : ∀ i, a i ∈ ball (0 : ℂ) R := fun i =>
    (hsmall (ball_subset_closedBall (hnode i))).1
  have hnodeρ : ∀ i, ρ < ‖a i - 0‖ := by
    intro i
    have := (hsmall (ball_subset_closedBall (hnode i))).2
    rw [mem_closedBall, dist_zero_right, not_le] at this
    simpa using this
  have hdecomp := fun (cc : ℂ) (ss : ℝ) (hss : 0 ≤ ss) hne hqc =>
    circleIntegral_div_prod_eq (a := a) (h := h) (q := q) (d := d) hrep cc ss hss hne hqc
  -- continuity of `h` and `q` on the three circles
  have hsphR : sphere (0 : ℂ) R ⊆ A := fun z hz =>
    hAann ⟨sphere_subset_closedBall hz, by
      rw [mem_sphere, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right, not_lt, hz]
      exact hρR⟩
  have hsphρ : sphere (0 : ℂ) ρ ⊆ A := fun z hz =>
    hAann ⟨by
      rw [mem_sphere, dist_zero_right] at hz
      rw [mem_closedBall, dist_zero_right, hz]
      exact hρR, by
      rw [mem_sphere, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right, not_lt, hz]⟩
  have hsphτ : sphere τ rr ⊆ A := fun z hz => hballA (sphere_subset_closedBall hz)
  have hcont : ∀ {K : Set ℂ}, K ⊆ A → ContinuousOn h K ∧ ContinuousOn q K := fun hK =>
    ⟨hh.continuousOn.mono hK, hq.continuousOn.mono hK⟩
  have hneR : ∀ z ∈ sphere (0 : ℂ) R, ∀ i ∈ Finset.range k, z ≠ a i := by
    intro z hz i _ hzi
    rw [mem_sphere, dist_zero_right] at hz
    have := hnodeR i
    rw [mem_ball, dist_zero_right, ← hzi, hz] at this
    exact lt_irrefl R this
  have hneρ : ∀ z ∈ sphere (0 : ℂ) ρ, ∀ i ∈ Finset.range k, z ≠ a i := by
    intro z hz i _ hzi
    rw [mem_sphere, dist_zero_right] at hz
    have := hnodeρ i
    rw [← hzi, sub_zero, hz] at this
    exact lt_irrefl ρ this
  have hneτ : ∀ z ∈ sphere τ rr, ∀ i ∈ Finset.range k, z ≠ a i := by
    intro z hz i _ hzi
    rw [mem_sphere] at hz
    have := hnode i
    rw [mem_ball, ← hzi, hz] at this
    exact lt_irrefl rr this
  rw [hdecomp 0 R (le_trans hρ.le hρR) hneR (hcont hsphR).2,
    hdecomp 0 ρ hρ.le hneρ (hcont hsphρ).2,
    hdecomp τ rr hrr.le hneτ (hcont hsphτ).2]
  -- the analytic remainder
  have hqann : (∮ z in C((0 : ℂ), R), q z) = ∮ z in C((0 : ℂ), ρ), q z := by
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ hρR Set.countable_empty
      (hq.continuousOn.mono (fun z hz => hAann hz)) fun z hz => ?_
    refine (hq z (hAann ⟨ball_subset_closedBall hz.1.1, ?_⟩)).differentiableAt
    intro hmem
    exact hz.1.2 (ball_subset_closedBall hmem)
  have hqsmall : (∮ z in C(τ, rr), q z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hrr.le
      Set.countable_empty (hq.continuousOn.mono hballA) fun z hz => ?_
    exact (hq z (hballA (ball_subset_closedBall hz.1))).differentiableAt
  -- the rational terms
  have hVρ : ∀ j ∈ Finset.range k,
      (∮ z in C((0 : ℂ), ρ), (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹) = 0 := by
    intro j _
    exact circleIntegral_prod_inv_eq_zero_of_notMem hρ.le fun i _ => hnodeρ i
  have hVeq : ∀ j ∈ Finset.range k,
      (∮ z in C((0 : ℂ), R), (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹)
        = ∮ z in C(τ, rr), (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hcard : 1 ≤ (Finset.Ico j k).card := by
      rw [Nat.card_Ico]
      omega
    rw [circleIntegral_newton_term (lt_of_lt_of_le hρ hρR) hcard (fun i _ => hnodeR i),
      circleIntegral_newton_term hrr hcard (fun i _ => hnode i)]
  rw [hqann, hqsmall, add_zero]
  have hsplit : (∑ j ∈ Finset.range k, d j * ∮ z in C((0 : ℂ), R),
        (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹)
      = (∑ j ∈ Finset.range k, d j * ∮ z in C((0 : ℂ), ρ),
          (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹)
        + ∑ j ∈ Finset.range k, d j * ∮ z in C(τ, rr),
          (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hVρ j hj, hVeq j hj, mul_zero, zero_add]
  rw [hsplit]
  ring

/-- **Two circles enclosing the same cluster give the same integral.**  Neither the center nor
the radius matters: what matters is that every node is inside both and that `h` is analytic on
both closed discs.  The Newton terms take the same value on each circle and the analytic
remainder integrates to zero on both.

This is the companion of `circleIntegral_cluster_deform`: there the two circles have the
cluster *between* them, here they both have it inside. -/
theorem circleIntegral_prod_indep {c₁ c₂ : ℂ} {s₁ s₂ : ℝ} {A : Set ℂ} (hA : IsOpen A)
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h A) (k : ℕ) (a : ℕ → ℂ)
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hd₁ : closedBall c₁ s₁ ⊆ A) (hd₂ : closedBall c₂ s₂ ⊆ A)
    (hn₁ : ∀ i, a i ∈ ball c₁ s₁) (hn₂ : ∀ i, a i ∈ ball c₂ s₂) :
    (∮ z in C(c₁, s₁), h z / ∏ i ∈ Finset.range k, (z - a i))
      = ∮ z in C(c₂, s₂), h z / ∏ i ∈ Finset.range k, (z - a i) := by
  have hAnode : ∀ i, a i ∈ A := fun i => hd₁ (ball_subset_closedBall (hn₁ i))
  obtain ⟨d, q, hq, hrep⟩ := exists_newton_form_div hA a hAnode k hh
  have hne : ∀ (c : ℂ) (sr : ℝ), (∀ i, a i ∈ ball c sr) →
      ∀ z ∈ sphere c sr, ∀ i ∈ Finset.range k, z ≠ a i := by
    intro c sr hin z hz i _ hzi
    rw [mem_sphere] at hz
    have := hin i
    rw [mem_ball, ← hzi, hz] at this
    exact lt_irrefl sr this
  have hzero : ∀ (c : ℂ) (sr : ℝ), 0 < sr → closedBall c sr ⊆ A →
      (∮ z in C(c, sr), q z) = 0 := by
    intro c sr hsr hsub
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hsr.le
      Set.countable_empty (hq.continuousOn.mono hsub) fun z hz => ?_
    exact (hq z (hsub (ball_subset_closedBall hz.1))).differentiableAt
  have hval : ∀ (c : ℂ) (sr : ℝ), 0 < sr → closedBall c sr ⊆ A → (∀ i, a i ∈ ball c sr) →
      (∮ z in C(c, sr), h z / ∏ i ∈ Finset.range k, (z - a i))
        = ∑ j ∈ Finset.range k, d j * (if (Finset.Ico j k).card = 1 then 2 * π * I else 0) := by
    intro c sr hsr hsub hin
    rw [circleIntegral_div_prod_eq hrep c sr hsr.le (hne c sr hin)
        (hq.continuousOn.mono (fun z hz => hsub (sphere_subset_closedBall hz))),
      hzero c sr hsr hsub, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hcard : 1 ≤ (Finset.Ico j k).card := by rw [Nat.card_Ico]; omega
    rw [circleIntegral_newton_term hsr hcard (fun i _ => hin i)]
  rw [hval c₁ s₁ hs₁ hd₁ hn₁, hval c₂ s₂ hs₂ hd₂ hn₂]

/-- `circleIntegral_prod_indep` with the node condition asked only of the indices that appear.
The values `a i` for `i ≥ k` never enter the integrand, and clamping them into the range restores
the total hypothesis without constraining them. -/
theorem circleIntegral_prod_indep_of_lt {c₁ c₂ : ℂ} {s₁ s₂ : ℝ} {A : Set ℂ} (hA : IsOpen A)
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h A) (k : ℕ) (a : ℕ → ℂ)
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hd₁ : closedBall c₁ s₁ ⊆ A) (hd₂ : closedBall c₂ s₂ ⊆ A)
    (hn₁ : ∀ i < k, a i ∈ ball c₁ s₁) (hn₂ : ∀ i < k, a i ∈ ball c₂ s₂) :
    (∮ z in C(c₁, s₁), h z / ∏ i ∈ Finset.range k, (z - a i))
      = ∮ z in C(c₂, s₂), h z / ∏ i ∈ Finset.range k, (z - a i) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- No nodes: the integrand is `h`, analytic on each closed disc.
    have hzero : ∀ (c : ℂ) (sr : ℝ), 0 < sr → closedBall c sr ⊆ A →
        (∮ z in C(c, sr), h z / ∏ i ∈ Finset.range 0, (z - a i)) = 0 := by
      intro c sr hsr hsub
      simp only [Finset.range_zero, Finset.prod_empty, div_one]
      refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hsr.le
        Set.countable_empty (hh.continuousOn.mono hsub) fun z hz => ?_
      exact (hh z (hsub (ball_subset_closedBall hz.1))).differentiableAt
    rw [hzero c₁ s₁ hs₁ hd₁, hzero c₂ s₂ hs₂ hd₂]
  · -- Clamp the tail of the node family into the range, which changes no factor.
    set a' : ℕ → ℂ := fun i => a (min i (k - 1)) with ha'
    have hlt : ∀ i, min i (k - 1) < k := fun i => lt_of_le_of_lt (min_le_right _ _) (by omega)
    have heq : ∀ i ∈ Finset.range k, a' i = a i := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have : min i (k - 1) = i := min_eq_left (by omega)
      simp [ha', this]
    have hprod : ∀ z : ℂ, ∏ i ∈ Finset.range k, (z - a' i) = ∏ i ∈ Finset.range k, (z - a i) :=
      fun z => Finset.prod_congr rfl fun i hi => by rw [heq i hi]
    simp only [← hprod]
    exact circleIntegral_prod_indep hA hh k a' hs₁ hs₂ hd₁ hd₂
      (fun i => hn₁ _ (hlt i)) (fun i => hn₂ _ (hlt i))

/-- **The enclosed contribution is a single divided difference.**  Over a circle enclosing every
node, `h/∏_{i<k}(z - a_i)` integrates to `2πi` times the **last** Newton coefficient of `h` at
those nodes — the `(k-1)`-st divided difference.  Every earlier Newton term carries two or more
factors and integrates to zero, and the analytic remainder integrates to zero as well.

At simple nodes this is the sum of the residues; at a collision it is the Hermite coefficient,
and the statement does not change, which is the whole point of routing through `dslope`. -/
theorem exists_newton_local_value {A : Set ℂ} (hA : IsOpen A) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h A) (k : ℕ) (a : ℕ → ℂ) (hk : 1 ≤ k) (hAnode : ∀ i, a i ∈ A)
    {c : ℂ} {s : ℝ} (hs : 0 < s) (hsub : closedBall c s ⊆ A) (hn : ∀ i, a i ∈ ball c s) :
    ∃ d : ℕ → ℂ, ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q A ∧
      (∀ z, (∀ i ∈ Finset.range k, z ≠ a i) →
        h z / ∏ i ∈ Finset.range k, (z - a i)
          = (∑ j ∈ Finset.range k, d j / ∏ i ∈ Finset.Ico j k, (z - a i)) + q z) ∧
      (∮ z in C(c, s), h z / ∏ i ∈ Finset.range k, (z - a i)) = 2 * π * I * d (k - 1) := by
  obtain ⟨d, q, hq, hrep⟩ := exists_newton_form_div hA a hAnode k hh
  refine ⟨d, q, hq, hrep, ?_⟩
  have hne : ∀ z ∈ sphere c s, ∀ i ∈ Finset.range k, z ≠ a i := by
    intro z hz i _ hzi
    rw [mem_sphere] at hz
    have := hn i
    rw [mem_ball, ← hzi, hz] at this
    exact lt_irrefl s this
  have hqzero : (∮ z in C(c, s), q z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hs.le
      Set.countable_empty (hq.continuousOn.mono hsub) fun z hz => ?_
    exact (hq z (hsub (ball_subset_closedBall hz.1))).differentiableAt
  rw [circleIntegral_div_prod_eq hrep c s hs.le hne
      (hq.continuousOn.mono (fun z hz => hsub (sphere_subset_closedBall hz))),
    hqzero, add_zero]
  have hterm : ∀ j ∈ Finset.range k,
      d j * (∮ z in C(c, s), (∏ i ∈ Finset.Ico j k, (z - a i))⁻¹)
        = if j = k - 1 then 2 * π * I * d (k - 1) else 0 := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hcard : 1 ≤ (Finset.Ico j k).card := by rw [Nat.card_Ico]; omega
    rw [circleIntegral_newton_term hs hcard (fun i _ => hn i), Nat.card_Ico]
    by_cases hje : j = k - 1
    · subst hje
      rw [if_pos (by omega), if_pos rfl]
      ring
    · rw [if_neg (by omega), if_neg hje, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range k) (k - 1)]
  rw [if_pos (Finset.mem_range.mpr (by omega))]

end Shields
