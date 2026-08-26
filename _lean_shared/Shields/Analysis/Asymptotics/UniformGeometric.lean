/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Shields.Topology.CompactDirected

/-!
# A locally geometric remainder is uniformly negligible on a compact set

A family `r m` measured against a scale `d m` obeys a *geometric* bound when

`‖r m y‖ ≤ C · q ^ m · ‖d m y‖`  with  `q < 1`.

Such a bound makes the ratio `r m / d m` tend to `0` **uniformly** in `y`, at the rate `q ^ m`.
The point of this file is that the hypothesis need only hold *locally*: on a compact set, one
pair `(C, q)` serves every point, by `Shields.exists_forall_of_isCompact_of_directedOn` with the
pointwise maxima.

Two things come out with fewer hypotheses than expected.

* **No non-vanishing of the scale.**  Where `d m y = 0` the bound forces `r m y = 0` as well, and
  `0 / 0 = 0`, so the ratio is `0` exactly where it would otherwise be undefined.
* **No sign condition on `C`.**  A negative `C` makes the bound say `r m y = 0`, which is
  stronger, not ill-formed; `max C 0` absorbs it.

## Main results

* `Shields.norm_div_le_of_norm_le_mul` — a bound against a scale bounds the ratio.
* `Shields.norm_le_mul_of_le` — the bound is monotone in `C` and in `q`.
* `Shields.tendstoUniformlyOn_div_of_geometric` — a geometric bound gives uniform negligibility.
* `Shields.exists_uniform_geometric_of_local` — a locally geometric bound on a compact set is
  geometric with one pair of constants.
* `Shields.tendstoUniformlyOn_div_of_local_geometric` — the two composed.

## Tags

uniform convergence, geometric, compact, negligible
-/

open Filter Topology Set

namespace Shields

variable {X E : Type*}

/-- **A bound against a scale bounds the ratio.**  Where the scale vanishes the hypothesis forces
the numerator to vanish too, so no non-vanishing is assumed. -/
theorem norm_div_le_of_norm_le_mul [NormedDivisionRing E] {a b : E} {c : ℝ}
    (h : ‖a‖ ≤ c * ‖b‖) : ‖a / b‖ ≤ max c 0 := by
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a = 0 := by
      have : ‖a‖ ≤ 0 := by simpa using h
      simpa using le_antisymm this (norm_nonneg a)
    simp [ha]
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hb)]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg b))

/-- **The geometric bound is monotone in its constants.**  Raising either `C` or `q` weakens the
bound, which is why the componentwise maximum of two admissible pairs dominates both -- the
directedness `Shields.exists_uniform_geometric_of_local` collapses on a compact set. -/
theorem norm_le_mul_of_le [SeminormedAddGroup E] {a b : E} {C C' q q' : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hCC : C ≤ C') (hqq : q ≤ q')
    (h : ‖a‖ ≤ C * q ^ m * ‖b‖) : ‖a‖ ≤ C' * q' ^ m * ‖b‖ :=
  h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hCC (pow_le_pow_left₀ hq hqq m) (pow_nonneg hq m) (hC.trans hCC))
    (norm_nonneg _))

/-- **A geometric bound is uniform negligibility.**  The rate is `q ^ m`, carried by the constant
sequence `max C 0 * q ^ m`, which is where the sign of `C` is absorbed. -/
theorem tendstoUniformlyOn_div_of_geometric [NormedDivisionRing E] {K : Set X}
    {r d : ℕ → X → E} {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ y ∈ K, ∀ m, ‖r m y‖ ≤ C * q ^ m * ‖d m y‖) :
    TendstoUniformlyOn (fun m y => r m y / d m y) (fun _ => 0) atTop K := by
  have hpt : ∀ y ∈ K, ∀ m, ‖r m y / d m y‖ ≤ max C 0 * q ^ m := by
    intro y hy m
    refine (norm_div_le_of_norm_le_mul (c := C * q ^ m) (hbd y hy m)).trans
      (le_of_eq ?_)
    rw [max_mul_of_nonneg _ _ (pow_nonneg hq0 m), zero_mul]
  have h0 : Tendsto (fun m : ℕ => max C 0 * q ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (max C 0)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with m hm y hy
  rw [dist_zero_left]
  exact lt_of_le_of_lt (hpt y hy m) hm

/-- **A locally geometric bound on a compact set is geometric.**  The constants are collapsed by
`Shields.exists_forall_of_isCompact_of_directedOn`, the admissible set being the pairs `(C, q)`
with `0 ≤ C`, `0 ≤ q` and `q < 1` and the dominating pair the componentwise maximum. -/
theorem exists_uniform_geometric_of_local [TopologicalSpace X] [NormedDivisionRing E]
    {K : Set X} (hK : IsCompact K) {r d : ℕ → X → E}
    (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ y ∈ U, ∀ m, ‖r m y‖ ≤ C * q ^ m * ‖d m y‖) :
    ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ y ∈ K, ∀ m, ‖r m y‖ ≤ C * q ^ m * ‖d m y‖ := by
  set s : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 < 1} with hs_def
  set p : ℝ × ℝ → X → Prop := fun z y => ∀ m, ‖r m y‖ ≤ z.1 * z.2 ^ m * ‖d m y‖ with hp_def
  have hsne : s.Nonempty := ⟨(0, 0), by norm_num [hs_def]⟩
  have hdir : ∀ c ∈ s, ∀ d' ∈ s, ∃ e ∈ s, ∀ x, p c x ∨ p d' x → p e x := by
    rintro ⟨C₁, q₁⟩ ⟨hC₁, hq₁, hq₁'⟩ ⟨C₂, q₂⟩ ⟨hC₂, hq₂, hq₂'⟩
    refine ⟨(max C₁ C₂, max q₁ q₂),
      ⟨le_trans hC₁ (le_max_left _ _), le_trans hq₁ (le_max_left _ _), max_lt hq₁' hq₂'⟩, ?_⟩
    rintro x (hx | hx) m
    · exact norm_le_mul_of_le hC₁ hq₁ (le_max_left _ _) (le_max_left _ _) (hx m)
    · exact norm_le_mul_of_le hC₂ hq₂ (le_max_right _ _) (le_max_right _ _) (hx m)
  have hloc' : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, ∃ c ∈ s, ∀ y ∈ U, p c y := by
    intro x hx
    obtain ⟨U, hU, C, q, hC, hq, hq1, hbd⟩ := hloc x hx
    exact ⟨U, hU, (C, q), ⟨hC, hq, hq1⟩, hbd⟩
  obtain ⟨⟨C, q⟩, ⟨hC, hq, hq1⟩, hall⟩ :=
    exists_forall_of_isCompact_of_directedOn hsne hK hdir hloc'
  exact ⟨C, q, hC, hq, hq1, hall⟩

/-- **A locally geometric remainder is uniformly negligible.**  The two steps composed: the local
constants are collapsed on the compact set, then the geometric bound is read as a uniform
limit. -/
theorem tendstoUniformlyOn_div_of_local_geometric [TopologicalSpace X] [NormedDivisionRing E]
    {K : Set X} (hK : IsCompact K) {r d : ℕ → X → E}
    (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ y ∈ U, ∀ m, ‖r m y‖ ≤ C * q ^ m * ‖d m y‖) :
    TendstoUniformlyOn (fun m y => r m y / d m y) (fun _ => 0) atTop K := by
  obtain ⟨C, q, _, hq, hq1, hbd⟩ := exists_uniform_geometric_of_local hK hloc
  exact tendstoUniformlyOn_div_of_geometric hq hq1 hbd

/-! ### Axiom footprint -/

/-- info: 'Shields.norm_div_le_of_norm_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_div_le_of_norm_le_mul

/-- info: 'Shields.tendstoUniformlyOn_div_of_geometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendstoUniformlyOn_div_of_geometric

/-- info: 'Shields.exists_uniform_geometric_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_uniform_geometric_of_local

/-- info: 'Shields.tendstoUniformlyOn_div_of_local_geometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendstoUniformlyOn_div_of_local_geometric

end Shields
