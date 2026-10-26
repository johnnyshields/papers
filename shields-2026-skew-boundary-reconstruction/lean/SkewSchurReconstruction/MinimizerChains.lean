/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.ConvexWeights

/-!
# Saturated minimizing chains

Generic counting and convex-cost lemmas underlying “Marching minima”
(`subsec:marching`, `lem:marching`) and “Adjacent-edge rigidity at a fixed cap”
(`thm:cap-fixed-rigidity`).  The manuscript assembly must supply the support
bounds, two-member condition, and interlacing; those conclusions are not
assumed or derived from a determinant in this module.  Supported finite
argmin sets also give interlacing directly for convex tilted assignment
costs.  Sorry-free.
-/

namespace SkewSchurReconstruction

private theorem fin_step_distance {N : ℕ} (f : Fin N → ℕ)
    (hstep : ∀ i j : Fin N, i.val + 1 = j.val → f i < f j)
    (i : Fin N) (t : ℕ) (ht : i.val + t < N) :
    f i + t ≤ f ⟨i.val + t, ht⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : i.val + t < N := by omega
    have hprev := ih ht'
    have hnext := hstep ⟨i.val + t, ht'⟩ ⟨i.val + (t + 1), ht⟩
      (by change i.val + t + 1 = i.val + (t + 1); omega)
    omega

/-- Interlacing and two distinct members in the next row force strict marching
of the rightmost members, as in `lem:marching`. -/
theorem interlacing_max_strict (s t : Finset ℕ) (hs : s.Nonempty)
    (ht : 2 ≤ t.card) (hinter : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    s.max' hs < t.max' (Finset.card_pos.mp (by omega)) := by
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  have hsep : s.max' hs ≤ t.min' htne :=
    hinter _ (Finset.max'_mem s hs) _ (Finset.min'_mem t htne)
  have hgap : t.min' htne < t.max' htne :=
    Finset.min'_lt_max'_of_card t (by omega)
  exact hsep.trans_lt hgap

/-- Two-member adjacent-interlacing sets in a saturated interval are forced to be
consecutive pairs.  The left endpoint is a genuine supplied support bound. -/
theorem saturated_interlacing_chain {N : ℕ} (hN : 0 < N) (b : ℕ)
    (M : Fin N → Finset ℕ)
    (hcard : ∀ i, 2 ≤ (M i).card)
    (hupper : ∀ i, ∀ x ∈ M i, x ≤ b + N)
    (hfirst : ∀ x ∈ M ⟨0, hN⟩, b ≤ x)
    (hinter : ∀ i j : Fin N, i.val + 1 = j.val →
      ∀ x ∈ M i, ∀ y ∈ M j, x ≤ y) :
    ∀ i, M i = {b + i.val, b + i.val + 1} := by
  classical
  have hne : ∀ i, (M i).Nonempty := by
    intro i
    apply Finset.card_pos.mp
    have := hcard i
    omega
  let lo : Fin N → ℕ := fun i => (M i).min' (hne i)
  let hi : Fin N → ℕ := fun i => (M i).max' (hne i)
  have hlo_mem : ∀ i, lo i ∈ M i := fun i => Finset.min'_mem _ _
  have hhi_mem : ∀ i, hi i ∈ M i := fun i => Finset.max'_mem _ _
  have hgap : ∀ i, lo i < hi i := by
    intro i
    exact Finset.min'_lt_max'_of_card (M i) (by have := hcard i; omega)
  have hsep : ∀ i j : Fin N, i.val + 1 = j.val → hi i ≤ lo j := by
    intro i j hij
    exact hinter i j hij (hi i) (hhi_mem i) (lo j) (hlo_mem j)
  have hlo_step : ∀ i j : Fin N, i.val + 1 = j.val → lo i < lo j := by
    intro i j hij
    exact (hgap i).trans_le (hsep i j hij)
  have hhi_step : ∀ i j : Fin N, i.val + 1 = j.val → hi i < hi j := by
    intro i j hij
    exact (hsep i j hij).trans_lt (hgap j)
  have hlo_bound : ∀ i, b + i.val ≤ lo i := by
    intro i
    have hbase := hfirst (lo ⟨0, hN⟩) (hlo_mem ⟨0, hN⟩)
    have hdist := fin_step_distance lo hlo_step ⟨0, hN⟩ i.val
      (by change 0 + i.val < N; simpa only [zero_add] using i.isLt)
    have he : (⟨0 + i.val, by omega⟩ : Fin N) = i := by
      apply Fin.ext
      simp
    rw [he] at hdist
    omega
  have hhi_bound : ∀ i, hi i ≤ b + i.val + 1 := by
    intro i
    have ht : i.val + (N - 1 - i.val) < N := by omega
    have hdist := fin_step_distance hi hhi_step i (N - 1 - i.val) ht
    have hend := hupper ⟨i.val + (N - 1 - i.val), ht⟩
      (hi ⟨i.val + (N - 1 - i.val), ht⟩)
      (hhi_mem ⟨i.val + (N - 1 - i.val), ht⟩)
    omega
  have hlo_eq : ∀ i, lo i = b + i.val := by
    intro i
    have := hlo_bound i
    have := hhi_bound i
    have := hgap i
    omega
  have hhi_eq : ∀ i, hi i = b + i.val + 1 := by
    intro i
    have := hlo_bound i
    have := hhi_bound i
    have := hgap i
    omega
  intro i
  ext x
  constructor
  · intro hx
    have hl : lo i ≤ x := Finset.min'_le _ _ hx
    have hh : x ≤ hi i := Finset.le_max' _ _ hx
    rw [hlo_eq i] at hl
    rw [hhi_eq i] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx, ← hlo_eq i]
      exact hlo_mem i
    · rw [hx, ← hhi_eq i]
      exact hhi_mem i

/-- Cap-fixed saturation: zero is excluded from the first row's support. -/
theorem cap_fixed_interlacing_chain {v : ℕ} (hv : 0 < v)
    (M : Fin v → Finset ℕ) (hcard : ∀ i, 2 ≤ (M i).card)
    (hupper : ∀ i, ∀ x ∈ M i, x ≤ v + 1)
    (hzero : 0 ∉ M ⟨0, hv⟩)
    (hinter : ∀ i j : Fin v, i.val + 1 = j.val →
      ∀ x ∈ M i, ∀ y ∈ M j, x ≤ y) :
    ∀ i, M i = {i.val + 1, i.val + 2} := by
  have h := saturated_interlacing_chain hv 1 M hcard
    (by intro i x hx; have := hupper i x hx; omega)
    (by
      intro x hx
      by_contra hn
      have hxzero : x = 0 := by omega
      apply hzero
      simpa only [hxzero] using hx)
    hinter
  intro i
  simpa only [Nat.add_comm 1 i.val, Nat.add_assoc] using h i

/-- The virtual row removes the exclusion of zero and adds one row. -/
theorem virtual_interlacing_chain (v : ℕ)
    (M : Fin (v + 1) → Finset ℕ) (hcard : ∀ i, 2 ≤ (M i).card)
    (hupper : ∀ i, ∀ x ∈ M i, x ≤ v + 1)
    (hinter : ∀ i j : Fin (v + 1), i.val + 1 = j.val →
      ∀ x ∈ M i, ∀ y ∈ M j, x ≤ y) :
    ∀ i, M i = {i.val, i.val + 1} := by
  simpa only [Nat.zero_add] using
    saturated_interlacing_chain (by omega) 0 M hcard
      (by simpa only [Nat.zero_add] using hupper)
      (by intro x _; omega) hinter

/-- Minima over an explicitly finite support; unsupported coordinates are excluded. -/
noncomputable def supportedArgmin {α : Type*}
    (s : Finset α) (cost : α → ℝ) : Finset α := by
  classical
  exact s.filter (fun x => ∀ y ∈ s, cost x ≤ cost y)

@[simp] theorem mem_supportedArgmin {α : Type*}
    {s : Finset α} {cost : α → ℝ} {x : α} :
    x ∈ supportedArgmin s cost ↔ x ∈ s ∧ ∀ y ∈ s, cost x ≤ cost y := by
  classical
  simp [supportedArgmin]

theorem supportedArgmin_nonempty {α : Type*}
    (s : Finset α) (cost : α → ℝ) (hs : s.Nonempty) :
    (supportedArgmin s cost).Nonempty := by
  classical
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image (s : Set α) cost s.finite_toSet hs
  exact ⟨x, mem_supportedArgmin.mpr ⟨hx, hmin⟩⟩

theorem supportedArgmin_cost_eq {α : Type*}
    {s : Finset α} {cost : α → ℝ} {x y : α}
    (hx : x ∈ supportedArgmin s cost) (hy : y ∈ supportedArgmin s cost) :
    cost x = cost y := by
  obtain ⟨hxs, hxmin⟩ := mem_supportedArgmin.mp hx
  obtain ⟨hys, hymin⟩ := mem_supportedArgmin.mp hy
  exact le_antisymm (hxmin y hys) (hymin x hxs)

/-- Feasible columns for an integer row parameter. -/
def feasibleColumnSupport {n : ℕ} (s : Finset (Fin n)) (d : Fin n → ℤ)
    (A : ℤ) : Finset (Fin n) := s.filter (fun j => A ≤ d j)

/-- Convex assignment cost with a common linear column tilt. -/
def tiltedAssignmentCost {n : ℕ} (w : ConvexWeight) (d : Fin n → ℤ)
    (A : ℤ) (t : ℝ) (j : Fin n) : ℝ :=
  w.weight (d j - A).toNat - t * (d j : ℝ)

/-- Strict-Monge interlacing of supported minimizers for two ordered rows.
Feasibility of the two swapped columns is derived, not assumed. -/
theorem tilted_argmin_interlacing {n : ℕ} (w : ConvexWeight)
    (d : Fin n → ℤ) (hd : StrictMono d) (s : Finset (Fin n))
    {A A' : ℤ} (hA : A < A') (t : ℝ) {x y : Fin n}
    (hx : x ∈ supportedArgmin (feasibleColumnSupport s d A) (tiltedAssignmentCost w d A t))
    (hy : y ∈ supportedArgmin (feasibleColumnSupport s d A') (tiltedAssignmentCost w d A' t)) :
    x ≤ y := by
  obtain ⟨hxs, hxmin⟩ := mem_supportedArgmin.mp hx
  obtain ⟨hys, hymin⟩ := mem_supportedArgmin.mp hy
  obtain ⟨hxs, hxf⟩ := Finset.mem_filter.mp hxs
  obtain ⟨hys, hyf⟩ := Finset.mem_filter.mp hys
  by_contra hn
  have hyx : y < x := lt_of_not_ge hn
  have hdxy := hd hyx
  have hys' : y ∈ feasibleColumnSupport s d A :=
    Finset.mem_filter.mpr ⟨hys, hA.le.trans hyf⟩
  have hxs' : x ∈ feasibleColumnSupport s d A' :=
    Finset.mem_filter.mpr ⟨hxs, hyf.trans hdxy.le⟩
  have h₁ := hxmin y hys'
  have h₂ := hymin x hxs'
  have hmonge := w.strict_monge_int hA hdxy hyf
  unfold tiltedAssignmentCost at h₁ h₂
  linarith

end SkewSchurReconstruction
