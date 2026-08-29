/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ArcPhaseBound
import ForgacsTran.BranchSupplyGeometry

/-!
# The collision collar at the arc's RIGHT-hand endpoint

`BranchSupplyGeometry.exists_bound_im_logDeriv_ftCofactorAlong_at_collision` bounds
`Im(∂_tD'/∂_tD)` on a collar `(0, b)` whose endpoint `0` is a collision — a zero of
`E = XQ' - rQ` that the branch runs into.  It is anchored at the parameter `0` and
approaches it from the right, which is the arc's *lower* end.

At `r = 1` the arc's *upper* end is a collision too.  The branch radius tends to a
positive `L` and the principal pair meets at `-L`, where `E` vanishes
(`FTBranchEndpointUpper.exists_tendsto_ftTau_nhdsLT_pi`), so `E(γ(θ)) → 0` and
`BranchSupply.abs_im_logDeriv_ftCofactorAlong_le_of_bounds` — the estimate
`PhaseSupplyUpperRegion` uses at `2 ≤ r`, where `E(0) = -rQ(0) ≠ 0` — has nothing to
divide by.  What applies instead is this file: the same collar, approached from the left.

**Only the anchoring is mirrored; none of the mathematics is re-proved.**
`logDeriv_ftCriticalAlong_split` is already stated at an arbitrary `θ₀` and
`abs_im_logDeriv_ftCofactorAlong_le` at a single parameter, so both are position-free in
the sense `EndpointCollision`'s header sets out and both are used here verbatim.  The two
that are not are the reduced factor's ratio, which is stated on `Ioo θ₀ (θ₀ + b)` and is
restated below on `Ioo (θ₀ - b) θ₀`, and the chord, which is obtained from the existing
right-hand lemma by the substitution `s ↦ c - s` rather than by a second proof.

**The substitution negates the derivative and the conclusion cannot see it.**  Reflecting
carries `γ` to `s ↦ γ(c - s)` and `dγ` to `s ↦ -dγ(c - s)`; the chord's bound is on
`|Im(dγ/(γ - β))|`, and a sign inside an absolute value is invisible.  That is the same
observation `ArcPhaseBound.im_logDeriv_reflect` makes for the amplitude's logarithmic
derivative, at the one place where an arc endpoint has to be read in the other end's
chart.

Sorry-free.

## Main statements

* `exists_bound_ftCriticalReduced_ratio_left` — the reduced factor's ratio, bounded on a
  left collar.
* `exists_bound_im_chord_at_collision_left` — the chord, by reflection.
* `exists_bound_im_logDeriv_ftCofactorAlong_at_collision_left` — the collar itself.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`,
`eq:Dprime-identity`, `cor:linear-phase-variation`.

## Tags

collision, collar, upper endpoint, reflection, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

/-- **The reduced factor's logarithmic derivative on a LEFT collar.**  `Ẽ` does not vanish
at the collision, so `Ẽ'/Ẽ` is continuous there and the branch carries the bound back along
the arc.  `exists_bound_ftCriticalReduced_ratio` is the same statement on the other side,
and neither reads the collision's order. -/
theorem exists_bound_ftCriticalReduced_ratio_left {Q : Polynomial ℂ} {r : ℕ} {τ : ℝ → ℝ}
    {θ₀ : ℝ} (hE : ftCritical Q r ≠ 0)
    (hγc : ContinuousWithinAt (ftPrincipal τ) (Iio θ₀) θ₀) :
    ∃ b K : ℝ, 0 < b ∧ 0 ≤ K ∧ ∀ θ ∈ Ioo (θ₀ - b) θ₀,
      ‖(derivative (ftCriticalReduced Q r τ θ₀)).eval (ftPrincipal τ θ)‖
          / ‖(ftCriticalReduced Q r τ θ₀).eval (ftPrincipal τ θ)‖ ≤ K := by
  classical
  set H := ftCriticalReduced Q r τ θ₀ with hH
  have hH0 : H.eval (ftPrincipal τ θ₀) ≠ 0 := eval_ftCriticalReduced_ne_zero hE θ₀
  set Ψ : ℝ → ℝ := fun s =>
    ‖(derivative H).eval (ftPrincipal τ s)‖ / ‖H.eval (ftPrincipal τ s)‖ with hΨ
  have hp : ∀ P : Polynomial ℂ,
      ContinuousWithinAt (fun s : ℝ => P.eval (ftPrincipal τ s)) (Iio θ₀) θ₀ :=
    fun P => ((Polynomial.continuous P).continuousAt).comp_continuousWithinAt hγc
  have hΨc : ContinuousWithinAt Ψ (Iio θ₀) θ₀ :=
    (hp _).norm.div (hp H).norm (norm_ne_zero_iff.mpr hH0)
  have hK0 : 0 ≤ Ψ θ₀ + 1 := by
    have : 0 ≤ Ψ θ₀ := by rw [hΨ]; positivity
    linarith
  have hev : ∀ᶠ s in nhdsWithin θ₀ (Iio θ₀), Ψ s ≤ Ψ θ₀ + 1 := by
    filter_upwards [hΨc.eventually (eventually_lt_nhds (by linarith : Ψ θ₀ < Ψ θ₀ + 1))]
      with s hs using hs.le
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have huθ : u < θ₀ := hu
  refine ⟨θ₀ - u, Ψ θ₀ + 1, by linarith, hK0, fun θ hθ => ?_⟩
  exact hsub ⟨by linarith [hθ.1], hθ.2⟩

/-- **The chord's angular velocity at a collision approached from the LEFT.**
`ArcPhaseBound.exists_bound_im_chord_at_collision` under `s ↦ c - s`: the reflected curve
`γ(c - ·)` meets `β` at parameter `0` with derivative `-dγ c`, whose norm is the same, and
the sign the chain rule contributes dies under the absolute value. -/
theorem exists_bound_im_chord_at_collision_left {γ dγ : ℝ → ℂ} {b L c : ℝ} {β : ℂ}
    (hb : 0 < b) (hL : 0 ≤ L) (hγc : γ c = β)
    (hd0 : HasDerivWithinAt γ (dγ c) (Iic c) c)
    (hd : ∀ θ ∈ Ico (c - b) c, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (c - b) c, ‖dγ θ - dγ c‖ ≤ L * (c - θ))
    (h0 : dγ c ≠ 0) :
    ∃ b' : ℝ, 0 < b' ∧ b' ≤ b ∧ ∀ θ ∈ Icc (c - b') c, θ ≠ c →
      |(dγ θ / (γ θ - β)).im| ≤ 3 * L / ‖dγ c‖ := by
  have hd0' : HasDerivWithinAt (fun s : ℝ => γ (c - s)) (-dγ (c - 0)) (Ici (0 : ℝ)) 0 := by
    rw [sub_zero]
    have hmaps : MapsTo (fun t : ℝ => c - t) (Ici (0 : ℝ)) (Iic c) :=
      fun t ht => by simp only [mem_Iic]; linarith [mem_Ici.1 ht]
    have hg : HasDerivWithinAt γ (dγ c) (Iic c) ((fun t : ℝ => c - t) 0) := by
      simpa using hd0
    have hf : HasDerivWithinAt (fun t : ℝ => c - t) (-1 : ℝ) (Ici (0 : ℝ)) 0 := by
      simpa using (hasDerivWithinAt_id (0 : ℝ) (Ici (0 : ℝ))).const_sub c
    have h := hg.scomp (0 : ℝ) hf hmaps
    simpa [Function.comp_def] using h
  have hd' : ∀ s ∈ Ioc (0 : ℝ) b,
      HasDerivAt (fun t : ℝ => γ (c - t)) (-dγ (c - s)) s := by
    intro s hs
    have hmem : c - s ∈ Ico (c - b) c := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact HasDerivAt.comp_const_sub c s (hd (c - s) hmem)
  have hlip' : ∀ s ∈ Icc (0 : ℝ) b,
      ‖-dγ (c - s) - -dγ (c - 0)‖ ≤ L * s := by
    intro s hs
    have hmem : c - s ∈ Icc (c - b) c := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h := hlip (c - s) hmem
    rw [show c - (c - s) = s from by ring] at h
    have he : -dγ (c - s) - -dγ (c - 0) = -(dγ (c - s) - dγ c) := by
      rw [sub_zero]; ring
    rw [he, norm_neg]
    exact h
  have h0' : -dγ (c - 0) ≠ 0 := by rw [sub_zero]; simpa using h0
  obtain ⟨b', hb'0, hb'b, hbd⟩ :=
    exists_bound_im_chord_at_collision (γ := fun s : ℝ => γ (c - s))
      (dγ := fun s : ℝ => -dγ (c - s)) (β := β) (b := b) (L := L)
      hb hL (by simpa using hγc) hd0' hd' hlip' h0'
  refine ⟨b', hb'0, hb'b, fun θ hθ hθc => ?_⟩
  have hmem : c - θ ∈ Icc (0 : ℝ) b' := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hne : c - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθc)
  have h := hbd (c - θ) hmem hne
  simp only [sub_zero, sub_sub_cancel, norm_neg, neg_div, Complex.neg_im, abs_neg] at h
  exact h

/-- **`κ₀`'s collar at a collision the arc reaches from the LEFT.**  The mirror of
`BranchSupplyGeometry.exists_bound_im_logDeriv_ftCofactorAlong_at_collision`, and the
estimate the `r = 1` upper endpoint needs: there `E(γ(θ)) → 0`, so the ordinary bound
through `‖E'(γ)‖/‖E(γ)‖` has no denominator and this is what is left.

The two halves are the same two: the chord, which is where the branch's Lipschitz data
enters, and the reduced factor, which is continuity.  `abs_im_logDeriv_ftCofactorAlong_le`
then pays the `+1` for the `1/γ` of `∂_tD = E(γ)/γ`.

The collar is returned rather than taken, so the region assembly reuses this cut point. -/
theorem exists_bound_im_logDeriv_ftCofactorAlong_at_collision_left {Q : Polynomial ℂ}
    {r : ℕ} {z τ : ℝ → ℝ} {dγ dS : ℝ → ℂ} {dτ : ℝ → ℝ} {b L c : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) (hL : 0 ≤ L)
    (hd0 : HasDerivWithinAt (ftPrincipal τ) (dγ c) (Iic c) c)
    (hd : ∀ θ ∈ Ico (c - b) c, HasDerivAt (ftPrincipal τ) (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (c - b) c, ‖dγ θ - dγ c‖ ≤ L * (c - θ))
    (h0 : dγ c ≠ 0)
    (hτd : ∀ θ ∈ Ioo (c - b) c, HasDerivAt τ (dτ θ) θ)
    (hSd : ∀ θ ∈ Ioo (c - b) c, HasDerivAt (ftCofactorAlong Q r z τ) (dS θ) θ)
    (hstate : ∀ θ ∈ Ioo (c - b) c, ftPrincipal τ θ ≠ 0
      ∧ (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0
      ∧ ftCriticalAlong Q r τ θ ≠ 0)
    (hsep : ∀ θ ∈ Ioo (c - b) c, ftPrincipal τ θ ≠ ftPrincipal τ c)
    (hγc : ContinuousWithinAt (ftPrincipal τ) (Iio c) c) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧ ∀ θ ∈ Ioo (c - b') c,
      |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ κ := by
  classical
  have hE : ftCritical Q r ≠ 0 := by
    intro h
    obtain ⟨θ, hθ⟩ : ∃ θ, θ ∈ Ioo (c - b) c := ⟨c - b / 2, by constructor <;> linarith⟩
    exact (hstate θ hθ).2.2 (by rw [ftCriticalAlong, h]; simp)
  set ν : ℕ := ftCollisionOrder Q r τ c with hν
  set H := ftCriticalReduced Q r τ c with hH
  obtain ⟨bc, hbc0, hbcb, hchord⟩ :=
    exists_bound_im_chord_at_collision_left (γ := ftPrincipal τ) (dγ := dγ)
      (β := ftPrincipal τ c) hb hL rfl hd0 hd hlip h0
  obtain ⟨bk, K, hbk0, hK0, hratio⟩ :=
    exists_bound_ftCriticalReduced_ratio_left (Q := Q) (r := r) (τ := τ) (θ₀ := c) hE hγc
  set D : ℝ := ‖dγ c‖ + L * b with hD
  have hD0 : 0 ≤ D := by positivity
  set κ : ℝ := (ν : ℝ) * (3 * L / ‖dγ c‖) + D * K + 1 with hκ
  refine ⟨min bc bk, κ, lt_min hbc0 hbk0, le_trans (min_le_left _ _) hbcb, ?_, ?_⟩
  · have h1 : 0 ≤ (ν : ℝ) * (3 * L / ‖dγ c‖) := by positivity
    have h2 : 0 ≤ D * K := mul_nonneg hD0 hK0
    rw [hκ]; positivity
  intro θ hθ
  have hθb : θ ∈ Ioo (c - b) c :=
    ⟨by have := le_trans (min_le_left bc bk) hbcb; linarith [hθ.1], hθ.2⟩
  obtain ⟨hγ0, hroot, hEne⟩ := hstate θ hθb
  have hτ0 : τ θ ≠ 0 := fun h => hγ0 (by rw [ftPrincipal, h]; simp)
  have hγd := hd θ ⟨hθb.1.le, hθ.2⟩
  have hsplit := logDeriv_ftCriticalAlong_split (Q := Q) (r := r) (τ := τ) (θ₀ := c)
    hγd (hsep θ hθb) hEne
  have hbdγ : ‖dγ θ‖ ≤ D := by
    have h := hlip θ ⟨hθb.1.le, hθ.2.le⟩
    have h1 : ‖dγ θ‖ - ‖dγ c‖ ≤ ‖dγ θ - dγ c‖ := norm_sub_norm_le _ _
    have h2 : L * (c - θ) ≤ L * b := mul_le_mul_of_nonneg_left (by linarith [hθb.1]) hL
    rw [hD]; linarith
  have hchordθ : |(dγ θ / (ftPrincipal τ θ - ftPrincipal τ c)).im| ≤ 3 * L / ‖dγ c‖ := by
    refine hchord θ ⟨?_, hθ.2.le⟩ (ne_of_lt hθ.2)
    have := min_le_left bc bk
    linarith [hθ.1]
  have hratioθ : ‖(derivative H).eval (ftPrincipal τ θ)‖ / ‖H.eval (ftPrincipal τ θ)‖ ≤ K := by
    refine hratio θ ⟨?_, hθ.2⟩
    have := min_le_right bc bk
    linarith [hθ.1]
  have hsecond : |(dγ θ * (derivative H).eval (ftPrincipal τ θ)
      / H.eval (ftPrincipal τ θ)).im| ≤ D * K := by
    refine le_trans (Complex.abs_im_le_norm _) ?_
    rw [norm_div, norm_mul, mul_div_assoc]
    exact mul_le_mul hbdγ hratioθ (by positivity) hD0
  have hbd : |(logDeriv (ftCriticalAlong Q r τ) θ).im|
      ≤ (ν : ℝ) * (3 * L / ‖dγ c‖) + D * K := by
    rw [hsplit, Complex.add_im]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ hsecond)
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left hchordθ (Nat.cast_nonneg _)
  have hnbhd : ∀ᶠ s in nhds θ, ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hθb] with s hs
    exact ⟨(hstate s hs).1, (hstate s hs).2.1⟩
  rw [hκ]
  exact abs_im_logDeriv_ftCofactorAlong_le hr hnbhd (hτd θ hθb) hτ0 hγd hEne
    (hSd θ hθb) hbd

/-! ### The amplitude's own collar, at the same endpoint

`ArcPhaseBound.exists_bound_im_logDeriv_ftAmp_endpoint` divides the numerator's own vanishing
out of `Im(W'/W)` and so covers a root of `B` **at** the endpoint, which the cofactor split
cannot.  It is anchored at `0` like everything else here, and `ArcPhaseBound.im_logDeriv_reflect`
is the observation that reflecting the arc contributes a sign the absolute value cannot see —
so the mirror is a substitution at the call site rather than a second proof. -/

/-- **The amplitude's collar at an endpoint the arc reaches from the LEFT.**  At `r = 1` the
principal pair collides at `-L`, and the numerator may vanish there; this is the estimate that
covers it, and it is `exists_bound_im_logDeriv_ftAmp_endpoint` read through `s ↦ c - s`. -/
theorem exists_bound_im_logDeriv_ftAmp_endpoint_left {Q B : Polynomial ℂ} (hB : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) {γ dγ zf : ℝ → ℂ} {te : ℂ} {H : Polynomial ℂ} {m : ℕ} {b L c : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hEfac : ftCritical Q r = (X - C te) ^ m * H)
    (hH0 : H.eval te ≠ 0) (hte : te ≠ 0) (hγc : γ c = te)
    (hd0 : HasDerivWithinAt γ (dγ c) (Iic c) c)
    (hd : ∀ θ ∈ Ico (c - b) c, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (c - b) c, ‖dγ θ - dγ c‖ ≤ L * (c - θ))
    (h0 : dγ c ≠ 0)
    (hroot : ∀ θ ∈ Ico (c - b) c, (ftDen Q r (zf θ)).eval (γ θ) = 0) :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ C ∧
      ∀ θ ∈ Ico (c - b') c,
        |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
            / ftAmp Q B r (zf θ) (γ θ)).im| ≤ C := by
  have hd0' : HasDerivWithinAt (fun s : ℝ => γ (c - s)) (-dγ (c - 0)) (Ici (0 : ℝ)) 0 := by
    rw [sub_zero]
    have hmaps : MapsTo (fun t : ℝ => c - t) (Ici (0 : ℝ)) (Iic c) :=
      fun t ht => by simp only [mem_Iic]; linarith [mem_Ici.1 ht]
    have hg : HasDerivWithinAt γ (dγ c) (Iic c) ((fun t : ℝ => c - t) 0) := by
      simpa using hd0
    have hf : HasDerivWithinAt (fun t : ℝ => c - t) (-1 : ℝ) (Ici (0 : ℝ)) 0 := by
      simpa using (hasDerivWithinAt_id (0 : ℝ) (Ici (0 : ℝ))).const_sub c
    have h := hg.scomp (0 : ℝ) hf hmaps
    simpa [Function.comp_def] using h
  have hd' : ∀ s ∈ Ioc (0 : ℝ) b,
      HasDerivAt (fun t : ℝ => γ (c - t)) (-dγ (c - s)) s := by
    intro s hs
    have hmem : c - s ∈ Ico (c - b) c := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact HasDerivAt.comp_const_sub c s (hd (c - s) hmem)
  have hlip' : ∀ s ∈ Icc (0 : ℝ) b, ‖-dγ (c - s) - -dγ (c - 0)‖ ≤ L * s := by
    intro s hs
    have hmem : c - s ∈ Icc (c - b) c := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h := hlip (c - s) hmem
    rw [show c - (c - s) = s from by ring] at h
    have he : -dγ (c - s) - -dγ (c - 0) = -(dγ (c - s) - dγ c) := by
      rw [sub_zero]; ring
    rw [he, norm_neg]
    exact h
  have h0' : -dγ (c - 0) ≠ 0 := by rw [sub_zero]; simpa using h0
  have hroot' : ∀ δ ∈ Ioc (0 : ℝ) b,
      (ftDen Q r ((fun s : ℝ => zf (c - s)) δ)).eval ((fun s : ℝ => γ (c - s)) δ) = 0 := by
    intro δ hδ
    exact hroot (c - δ) ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
  obtain ⟨b', C, hb'0, hb'b, hC0, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_endpoint (Q := Q) (B := B) (r := r)
      (γ := fun s : ℝ => γ (c - s)) (dγ := fun s : ℝ => -dγ (c - s))
      (zf := fun s : ℝ => zf (c - s)) (te := te) (H := H) (m := m) (b := b) (L := L)
      hB hr hb hL hEfac hH0 hte (by simpa using hγc) hd0' hd' hlip' h0' hroot'
  exact ⟨b', C, hb'0, hb'b, hC0,
    forall_Ico_of_reflected (W := fun θ : ℝ => ftAmp Q B r (zf θ) (γ θ)) hbd⟩

end ForgacsTran
