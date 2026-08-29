/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.Rouche

/-!
# Counts at nested radii, and the multiplicity of one root

`ArgumentPrinciple` produces a factorization `F = (∏_{j<n}(z - a_j))·G` over a closed disk and
reads the zero count off it.  Three things that count needs, and does not yet have, are proved
here.

**The count belongs to the disk, not to the factorization.**  Any two factorizations over the
same disk display the same number of roots, because both compute the same contour integral.

**A concentric subdisk inherits a factorization.**  Keep the roots inside the smaller circle and
absorb the rest into the cofactor: a root *outside* the smaller circle contributes a factor with
no zero there, which is exactly what the cofactor is allowed to carry.  The count drops to the
number of roots displayed inside, so the count for an annulus is a difference of two disk
counts.

**Multiplicity at a point does not depend on the disk.**  Two factorizations over two
*different* disks, both containing `w`, list `w` the same number of times.  The mechanism is
`eq_of_pow_mul_eq`: a function cannot be both `(z-w)^k·A` and `(z-w)^l·B` with `A w ≠ 0 ≠ B w`
unless `k = l`, since otherwise dividing out the common power sends the surviving factor to `0`
at `w`.

## Main results

* `FactoredOn.card_eq` — the count is a function of the disk.
* `FactoredOn.restrict` — restriction to a concentric subdisk, with the filtered count.
* `FactoredOn.exists_pow_mul` — the multiplicity presentation at one point.
* `FactoredOn.count_eq` — multiplicity is independent of the factorization and of the disk.
* `FactoredOn.count_eq_one_of_deriv_ne_zero` — a simple zero is listed once.

## Tags

zero count, disc, analytic factorization, multiplicity
-/

open Complex Filter Metric Set Topology

namespace Shields

/-! ### The count is a function of the disk -/

/-- **The displayed root count depends only on the disk.**  Both factorizations compute
`∮ F'/F`, which does not know how `F` was presented. -/
theorem FactoredOn.card_eq {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n n' : ℕ} {a a' : ℕ → ℂ} {G G' : ℂ → ℂ}
    (h : FactoredOn F c R n a G) (h' : FactoredOn F c R n' a' G') : n = n' := by
  have h₁ := circleIntegral_logDeriv_eq_of_factoredOn hR h
  have h₂ := circleIntegral_logDeriv_eq_of_factoredOn hR h'
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero (h₁.symm.trans h₂)

/-! ### Restriction to a concentric subdisk

Listing the roots of the subdisk means re-indexing a `Finset` of indices onto an initial segment
of `ℕ`.  `nthOf` does that in increasing order, and `prod_range_nthOf` is the only fact about it
the restriction needs. -/

/-- The `i`-th element of a finite set of naturals, in increasing order. -/
noncomputable def nthOf (s : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < s.card then s.orderEmbOfFin rfl ⟨i, hi⟩ else 0

theorem nthOf_mem (s : Finset ℕ) {i : ℕ} (hi : i < s.card) : nthOf s i ∈ s := by
  rw [nthOf, dif_pos hi]
  exact s.orderEmbOfFin_mem rfl _

/-- Reindexing an initial segment onto the set it enumerates. -/
theorem prod_range_nthOf {M : Type*} [CommMonoid M] (s : Finset ℕ) (f : ℕ → M) :
    ∏ i ∈ Finset.range s.card, f (nthOf s i) = ∏ j ∈ s, f j := by
  have h1 : ∏ i ∈ Finset.range s.card, f (nthOf s i) = ∏ i : Fin s.card, f (nthOf s i) :=
    (Fin.prod_univ_eq_prod_range (fun i => f (nthOf s i)) s.card).symm
  have h2 : ∏ j ∈ s, f j = ∏ i : Fin s.card, f (s.orderEmbOfFin rfl i) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ s rfl]
    rw [Finset.prod_map]
    rfl
  rw [h1, h2]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  rw [nthOf, dif_pos i.isLt]

/-- **A concentric subdisk inherits the factorization.**  The roots inside the smaller circle
stay displayed; those outside it join the cofactor, where they are legitimate because a point
strictly outside contributes no zero inside.  The hypothesis is only that no root sits *on* the
smaller circle. -/
theorem FactoredOn.restrict {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (h : FactoredOn F c R n a G) {r : ℝ} (hrR : r ≤ R) (hne : ∀ j < n, ‖a j - c‖ ≠ r) :
    FactoredOn F c r (((Finset.range n).filter fun j => ‖a j - c‖ < r).card)
      (fun i => a (nthOf ((Finset.range n).filter fun j => ‖a j - c‖ < r) i))
      (fun z => (∏ j ∈ (Finset.range n).filter (fun j => ¬ ‖a j - c‖ < r), (z - a j)) * G z) := by
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall hrR
  -- a root not displayed inside is strictly outside, so it contributes no zero there
  have hout : ∀ j ∈ (Finset.range n).filter (fun j => ¬ ‖a j - c‖ < r),
      ∀ z ∈ Metric.closedBall c r, z - a j ≠ 0 := by
    intro j hj z hz hzero
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have h1 : r ≤ ‖a j - c‖ := not_lt.mp hj.2
    have h2 : r < ‖a j - c‖ := lt_of_le_of_ne h1 (Ne.symm (hne j hj.1))
    rw [sub_eq_zero] at hzero
    subst hzero
    exact absurd (Metric.mem_closedBall.mp hz) (by rwa [dist_eq_norm, not_le])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hm := nthOf_mem _ hi
    rw [Finset.mem_filter, Finset.mem_range] at hm
    exact Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hm.2)
  · exact (Finset.analyticOnNhd_fun_prod _ fun j _ => fun z _ => by fun_prop).mul
      (h.analytic.mono hsub)
  · intro z hz
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => hout j hj z hz) ?_
    exact h.ne_zero z (hsub hz)
  · intro z
    rw [prod_range_nthOf _ (fun j => z - a j), h.eq z, ← mul_assoc,
      Finset.prod_filter_mul_prod_filter_not (Finset.range n) (fun j => ‖a j - c‖ < r)]

/-- A displayed root is a zero. -/
theorem FactoredOn.root_eq_zero {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (h : FactoredOn F c R n a G) {i : ℕ} (hi : i < n) : F (a i) = 0 := by
  rw [h.eq (a i)]
  exact mul_eq_zero_of_left
    (Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by simp)) _

/-! ### The count in an open disk

`FactoredOn` speaks about a *closed* disk, and the level count at the critical radius is about
an open one — the boundary is exactly where the interesting root sits.  The bridge is a slightly
smaller closed disk that already holds every zero. -/

/-- `F` has exactly `n` zeros, with multiplicity, in the open disk `‖z‖ < ρ`: some smaller
closed disk carries a factorization with `n` roots displayed, and the annulus between the two
radii is zero-free. -/
def ZeroCountOn (F : ℂ → ℂ) (ρ : ℝ) (n : ℕ) : Prop :=
  ∃ (r : ℝ) (b : ℕ → ℂ) (H : ℂ → ℂ), 0 < r ∧ r < ρ ∧ FactoredOn F 0 r n b H ∧
    ∀ z, r ≤ ‖z‖ → ‖z‖ < ρ → F z ≠ 0

/-- **The open-disk count is well defined.**  The smaller of two witnessing radii sees the same
roots as the larger, because the annulus between them is zero-free. -/
theorem ZeroCountOn.unique {F : ℂ → ℂ} {ρ : ℝ} {n n' : ℕ}
    (h : ZeroCountOn F ρ n) (h' : ZeroCountOn F ρ n') : n = n' := by
  have key : ∀ (s s' : ℝ) (c c' : ℕ → ℂ) (K K' : ℂ → ℂ) (m m' : ℕ), 0 < s → s ≤ s' → s' < ρ →
      FactoredOn F 0 s m c K → FactoredOn F 0 s' m' c' K' →
      (∀ z, s ≤ ‖z‖ → ‖z‖ < ρ → F z ≠ 0) → m = m' := by
    intro s s' c c' K K' m m' hs hss' hs'ρ hm hm' hann
    have hlow : ∀ i < m', ‖c' i‖ < s := by
      intro i hi
      by_contra hcon
      have hin : ‖c' i‖ < s' := by
        simpa [dist_zero_right] using Metric.mem_ball.mp (hm'.mem_ball i hi)
      exact hann (c' i) (not_lt.mp hcon) (lt_trans hin hs'ρ) (hm'.root_eq_zero hi)
    have hres := hm'.restrict hss' (fun i hi => by rw [sub_zero]; exact ne_of_lt (hlow i hi))
    have hfilter : ((Finset.range m').filter fun i => ‖c' i - 0‖ < s) = Finset.range m' :=
      Finset.filter_true_of_mem fun i hi => by
        rw [sub_zero]; exact hlow i (Finset.mem_range.mp hi)
    rw [hfilter, Finset.card_range] at hres
    exact hm.card_eq hs hres
  obtain ⟨r, b, H, hr0, hrρ, hfac, hann⟩ := h
  obtain ⟨r', b', H', hr0', hrρ', hfac', hann'⟩ := h'
  rcases le_total r r' with hle | hle
  · exact key r r' b b' H H' n n' hr0 hle hrρ' hfac hfac' hann
  · exact (key r' r b' b H' H n' n hr0' hle hrρ hfac' hfac hann').symm

/-- **A radius clear of the displayed roots below a threshold.**  Finitely many roots have
modulus below `R`, so some `r < R` exceeds all of them; the annulus `r ≤ ‖z‖ < R` then contains
no displayed root at all. -/
theorem exists_radius_below {F : ℂ → ℂ} {ρ : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (_h : FactoredOn F 0 ρ n a G) {R : ℝ} (hR : 0 < R) :
    ∃ r, 0 < r ∧ r < R ∧ ∀ i < n, ‖a i‖ < R → ‖a i‖ < r := by
  set S : Finset ℝ :=
    insert 0 (((Finset.range n).filter fun i => ‖a i‖ < R).image fun i => ‖a i‖) with hS
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set M := S.max' hSne with hM
  have hM0 : 0 ≤ M := S.le_max' 0 (Finset.mem_insert_self _ _)
  have hMR : M < R := by
    refine (Finset.max'_lt_iff S hSne).mpr fun y hy => ?_
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hR
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
  refine ⟨(M + R) / 2, by linarith, by linarith, fun i hi hiR => ?_⟩
  have : ‖a i‖ ≤ M :=
    S.le_max' _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hiR⟩)))
  linarith

/-- **The zeros of an entire function in a closed disk are finite**, provided it is not
identically zero.  `finite_zeros_of_ne_zero_on_sphere` gets the same conclusion from
nonvanishing on the circle; here the witness may sit anywhere, which is what a function that
*does* vanish on the circle needs. -/
theorem finite_zeros_of_entire {c : ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {w₀ : ℂ} (hne : F w₀ ≠ 0) : {z ∈ Metric.closedBall c R | F z = 0}.Finite := by
  have hA : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  refine finite_zeros_of_analyticOnNhd (fun z _ => hF.analyticAt z) fun w _ hw => hne ?_
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ w) hw (mem_univ w₀)

/-! ### Multiplicity at a point -/

/-- **Two power presentations at one point have the same exponent.**  If `k < l`, dividing the
common factor out makes `A` agree with `(z-w)^{l-k}·B` off `w`, which tends to `0`; continuity
then forces `A w = 0`. -/
theorem eq_of_pow_mul_eq {w : ℂ} {k l : ℕ} {A B : ℂ → ℂ}
    (hA : ContinuousAt A w) (hB : ContinuousAt B w) (hA0 : A w ≠ 0) (hB0 : B w ≠ 0)
    (heq : ∀ z, (z - w) ^ k * A z = (z - w) ^ l * B z) : k = l := by
  have main : ∀ (p q : ℕ) (C D : ℂ → ℂ), ContinuousAt C w → ContinuousAt D w → C w ≠ 0 →
      (∀ z, (z - w) ^ p * C z = (z - w) ^ q * D z) → p ≤ q → p = q := by
    intro p q C D hC hD hC0 hpq hle
    by_contra hne
    have hlt : p < q := lt_of_le_of_ne hle hne
    have hev : C =ᶠ[𝓝[≠] w] fun z => (z - w) ^ (q - p) * D z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hp : (z - w) ^ p ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
      have hz' := hpq z
      rw [show q = p + (q - p) by omega, pow_add, mul_assoc] at hz'
      exact mul_left_cancel₀ hp hz'
    have h1 : Tendsto C (𝓝[≠] w) (𝓝 (C w)) := hC.continuousWithinAt
    have hpow : Tendsto (fun z : ℂ => (z - w) ^ (q - p)) (𝓝[≠] w) (𝓝 0) := by
      have hc : Continuous fun z : ℂ => (z - w) ^ (q - p) := by fun_prop
      have := (hc.tendsto w).mono_left (nhdsWithin_le_nhds (s := {w}ᶜ))
      simpa [sub_self, zero_pow (show q - p ≠ 0 by omega)] using this
    have h2 : Tendsto (fun z => (z - w) ^ (q - p) * D z) (𝓝[≠] w) (𝓝 0) := by
      simpa using hpow.mul hD.continuousWithinAt
    exact hC0 (tendsto_nhds_unique (Filter.Tendsto.congr' hev h1) h2)
  rcases le_total k l with hle | hle
  · exact main k l A B hA hB hA0 heq hle
  · exact (main l k B A hB hA hB0 (fun z => (heq z).symm) hle).symm

/-- **The multiplicity presentation.**  Splitting the copies of `w` out of the displayed list
writes `F = (z-w)^k·H` with `H w ≠ 0`, where `k` is the number of times `w` occurs. -/
theorem FactoredOn.exists_pow_mul {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (h : FactoredOn F c R n a G) {w : ℂ} (hw : w ∈ Metric.closedBall c R) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H w ∧ H w ≠ 0 ∧
      ∀ z, F z = (z - w) ^ (((Finset.range n).filter fun j => a j = w).card) * H z := by
  refine ⟨fun z => (∏ j ∈ (Finset.range n).filter (fun j => ¬ a j = w), (z - a j)) * G z,
    ?_, ?_, ?_⟩
  · exact (Finset.analyticAt_fun_prod _ fun j _ => by fun_prop).fun_mul (h.analytic w hw)
  · refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) (h.ne_zero w hw)
    rw [Finset.mem_filter] at hj
    exact sub_ne_zero.mpr (Ne.symm hj.2)
  · intro z
    rw [h.eq z, ← Finset.prod_filter_mul_prod_filter_not (Finset.range n) (fun j => a j = w),
      ← mul_assoc]
    congr 2
    rw [Finset.prod_congr rfl (fun j hj => by
      rw [(Finset.mem_filter.mp hj).2]), Finset.prod_const]

/-- **Multiplicity is independent of the factorization and of the disk.**  Two factorizations
over two disks both containing `w` list `w` the same number of times. -/
theorem FactoredOn.count_eq {F : ℂ → ℂ} {c c' : ℂ} {R R' : ℝ} {n n' : ℕ} {a a' : ℕ → ℂ}
    {G G' : ℂ → ℂ} (h : FactoredOn F c R n a G) (h' : FactoredOn F c' R' n' a' G')
    {w : ℂ} (hw : w ∈ Metric.closedBall c R) (hw' : w ∈ Metric.closedBall c' R') :
    ((Finset.range n).filter fun j => a j = w).card
      = ((Finset.range n').filter fun j => a' j = w).card := by
  obtain ⟨H, hH, hH0, hHeq⟩ := h.exists_pow_mul hw
  obtain ⟨K, hK, hK0, hKeq⟩ := h'.exists_pow_mul hw'
  exact eq_of_pow_mul_eq hH.continuousAt hK.continuousAt hH0 hK0
    fun z => (hHeq z).symm.trans (hKeq z)

/-- A point of the closed disk is displayed at least once exactly when it is a zero. -/
theorem FactoredOn.one_le_count_iff {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ}
    (h : FactoredOn F c R n a G) {w : ℂ} (hw : w ∈ Metric.closedBall c R) :
    1 ≤ ((Finset.range n).filter fun j => a j = w).card ↔ F w = 0 := by
  rw [Finset.one_le_card, Finset.filter_nonempty_iff, h.eq_zero_iff hw]
  constructor
  · rintro ⟨j, hj, hjw⟩
    exact ⟨j, Finset.mem_range.mp hj, hjw⟩
  · rintro ⟨j, hj, hjw⟩
    exact ⟨j, Finset.mem_range.mpr hj, hjw⟩

/-- **A simple zero is displayed exactly once.**  The multiplicity is at least one because `w`
is a zero, and at most one because a double factor would kill the derivative. -/
theorem FactoredOn.count_eq_one_of_deriv_ne_zero {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℕ} {a : ℕ → ℂ}
    {G : ℂ → ℂ} (h : FactoredOn F c R n a G) {w : ℂ} (hw : w ∈ Metric.closedBall c R)
    (h0 : F w = 0) (h1 : deriv F w ≠ 0) :
    ((Finset.range n).filter fun j => a j = w).card = 1 := by
  obtain ⟨H, hH, hH0, hHeq⟩ := h.exists_pow_mul hw
  set k := ((Finset.range n).filter fun j => a j = w).card with hk
  have hk1 : 1 ≤ k := (h.one_le_count_iff hw).mpr h0
  by_contra hne
  have hk2 : 2 ≤ k := by omega
  -- with a double factor the derivative vanishes at `w`
  have hFd : HasDerivAt F 0 w := by
    have hid : HasDerivAt (fun z : ℂ => z - w) 1 w := (hasDerivAt_id w).sub_const w
    have hmul := (hid.pow k).mul hH.differentiableAt.hasDerivAt
    have hval : (k : ℂ) * (w - w) ^ (k - 1) * 1 * H w
        + ((fun z : ℂ => z - w) ^ k) w * deriv H w = 0 := by
      simp [zero_pow (show k - 1 ≠ 0 by omega), zero_pow (show k ≠ 0 by omega)]
    rw [hval] at hmul
    have hFeq : F = (fun z : ℂ => z - w) ^ k * H := by
      funext z
      rw [hHeq z]
      simp
    rw [hFeq]
    exact hmul
  exact h1 hFd.deriv


/-! ### Axiom footprint -/

/-- info: 'Shields.FactoredOn.card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FactoredOn.card_eq

/-- info: 'Shields.FactoredOn.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FactoredOn.restrict

/-- info: 'Shields.FactoredOn.count_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FactoredOn.count_eq

/-- info: 'Shields.FactoredOn.count_eq_one_of_deriv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FactoredOn.count_eq_one_of_deriv_ne_zero

end Shields
