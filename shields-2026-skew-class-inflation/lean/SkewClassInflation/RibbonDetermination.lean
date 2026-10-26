/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ReflectedCutTypes
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Determined and undetermined cuts among actual normalized mates

The determination data in the nonsymmetric ribbon factorization input
to `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Every family member is an
actual composition with equal coarsening inventory.  Nonreconstructibility
produces a proper undetermined coordinate, and its reflection is again
undetermined.  Sorry-free.
-/

namespace SkewClassInflation

/-- Actual inventory mates with a selected orientation cut present. -/
def normalizedInventoryMates {N : ℕ} (α : Composition N) (k : ℕ) : Set (Composition N) :=
  {β | coarseningInventory β = coarseningInventory α ∧ k ∈ properCuts β}

/-- The normalized family contains the actual source whenever its orientation cut is present. -/
theorem source_mem_normalizedInventoryMates {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) : α ∈ normalizedInventoryMates α k := ⟨rfl, hk⟩

/-- Membership at a coordinate is fixed throughout the actual normalized inventory class. -/
def cutDetermined {N : ℕ} (α : Composition N) (k j : ℕ) : Prop :=
  ∀ β ∈ normalizedInventoryMates α k, (j ∈ properCuts β ↔ j ∈ properCuts α)

/-- Even-type cut membership is determined without needing the orientation condition. -/
theorem cutDetermined_of_not_one {N : ℕ} (α : Composition N) (k j : ℕ)
    (hj : compositionCutType α j ≠ 1) : cutDetermined α k j := by
  intro β hβ
  exact (coarseningInventory_cut_membership_of_not_one α β hβ.1.symm j hj).symm

/-- The chosen source orientation coordinate is determined by its actual normalized family. -/
theorem cutDetermined_first {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) : cutDetermined α k k := by
  intro β hβ
  exact iff_of_true hβ.2 hk

/-- Undetermined proper coordinates of the actual normalized class. -/
noncomputable def undeterminedCuts {N : ℕ} (α : Composition N) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioo 0 N).filter (fun j => ¬ cutDetermined α k j)

/-- Every undetermined coordinate has type one; no even-type uncertainty is assumed. -/
theorem undeterminedCuts_type_one {N : ℕ} (α : Composition N) (k j : ℕ)
    (hj : j ∈ undeterminedCuts α k) : compositionCutType α j = 1 := by
  classical
  by_contra he
  exact (Finset.mem_filter.mp hj).2 (cutDetermined_of_not_one α k j he)

/-- Failure of reconstruction supplies a genuinely nonempty set of proper undetermined cuts. -/
theorem undeterminedCuts_nonempty {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α) :
    (undeterminedCuts α k).Nonempty := by
  classical
  obtain ⟨β, hInv, hcut, _, hne, _⟩ := exists_oriented_nonrotation_mate α hn k hk hkr
  have hex : ∃ j, ¬ cutDetermined α k j := by
    by_contra hnone
    apply hne
    apply properCuts_injective
    ext j
    have hj : cutDetermined α k j := by
      by_contra he
      exact hnone ⟨j, he⟩
    exact hj β ⟨hInv, hcut⟩
  obtain ⟨j, hj⟩ := hex
  have ht : compositionCutType α j = 1 := by
    by_contra he
    exact hj (cutDetermined_of_not_one α k j he)
  have hp : 0 < j ∧ j < N := by
    by_contra he
    have hout : j = 0 ∨ N ≤ j := by omega
    have hz := compositionCutType_outside α j hout
    omega
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr hp, hj⟩⟩

/-- At a single-type coordinate, determination of either reflected cut is equivalent. -/
theorem cutDetermined_reflect {N : ℕ} (α : Composition N) (k j : ℕ)
    (hj : compositionCutType α j = 1) :
    cutDetermined α k j ↔ cutDetermined α k (N - j) := by
  classical
  have hagree : ∀ β : Composition N, coarseningInventory β = coarseningInventory α →
      ((j ∈ properCuts β ↔ j ∈ properCuts α) ↔
        (N - j ∈ properCuts β ↔ N - j ∈ properCuts α)) := by
    intro β hβ
    have ht := (coarseningInventory_cut_type β α hβ j).trans hj
    rcases (compositionCutType_one_iff α j).mp hj with ⟨ha, har⟩ | ⟨ha, har⟩ <;>
      rcases (compositionCutType_one_iff β j).mp ht with ⟨hb, hbr⟩ | ⟨hb, hbr⟩ <;>
      simp only [ha, har, hb, hbr, iff_true, iff_false, not_true_eq_false]
  constructor
  · intro h β hβ
    exact (hagree β hβ.1).mp (h β hβ)
  · intro h β hβ
    exact (hagree β hβ.1).mpr (h β hβ)

/-- The actual undetermined set is closed under reflection across the total weight. -/
theorem undeterminedCuts_reflect {N : ℕ} (α : Composition N) (k j : ℕ)
    (hj : j ∈ undeterminedCuts α k) : N - j ∈ undeterminedCuts α k := by
  classical
  obtain ⟨hproper, hnot⟩ := Finset.mem_filter.mp hj
  have hb := Finset.mem_Ioo.mp hproper
  have ht := undeterminedCuts_type_one α k j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, ?_⟩
  intro hd
  exact hnot ((cutDetermined_reflect α k j ht).mpr hd)

/-- Every undetermined coordinate lies strictly beyond the actual first single-type cut. -/
theorem undeterminedCuts_after_first {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hmin : ∀ j < k, compositionCutType α j ≠ 1)
    (j : ℕ) (hj : j ∈ undeterminedCuts α k) : k < j := by
  classical
  have ht := undeterminedCuts_type_one α k j hj
  have hne : j ≠ k := by
    intro he
    subst j
    exact (Finset.mem_filter.mp hj).2 (cutDetermined_first α k hk)
  have hle : k ≤ j := by
    by_contra he
    have hlt : j < k := by omega
    exact hmin j hlt ht
  omega

/-- The finite gcd of all actual undetermined proper coordinates. -/
noncomputable def undeterminedGcd {N : ℕ} (α : Composition N) (k : ℕ) : ℕ :=
  (undeterminedCuts α k).gcd id

/-- The actual gcd divides each undetermined coordinate. -/
theorem undeterminedGcd_dvd {N : ℕ} (α : Composition N) (k j : ℕ)
    (hj : j ∈ undeterminedCuts α k) : undeterminedGcd α k ∣ j :=
  Finset.gcd_dvd hj

/-- A genuine nonempty undetermined set has a positive gcd. -/
theorem undeterminedGcd_pos {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) : 0 < undeterminedGcd α k := by
  classical
  apply Nat.pos_of_ne_zero
  intro he
  obtain ⟨j, hj⟩ := hne
  have hz := Finset.gcd_eq_zero_iff.mp he j hj
  have hp := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj).1
  change j = 0 at hz
  omega

/-- The actual gcd is a proper positive candidate period rather than the full weight. -/
theorem undeterminedGcd_lt_weight {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) : undeterminedGcd α k < N := by
  classical
  obtain ⟨j, hj⟩ := hne
  have hp := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj).1
  exact (Nat.le_of_dvd hp.1 (undeterminedGcd_dvd α k j hj)).trans_lt hp.2

/-- Reflection closure makes the actual gcd divide the whole weight. -/
theorem undeterminedGcd_dvd_weight {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) : undeterminedGcd α k ∣ N := by
  classical
  obtain ⟨j, hj⟩ := hne
  have hp := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj).1
  have hd := Nat.dvd_add (undeterminedGcd_dvd α k j hj)
    (undeterminedGcd_dvd α k (N - j) (undeterminedCuts_reflect α k j hj))
  have he : j + (N - j) = N := Nat.add_sub_of_le hp.2.le
  rw [he] at hd
  exact hd

/-- The finite gcd has exactly the common divisors of the paper's integer-periodic extension. -/
theorem undeterminedGcd_periodic_divisors {N : ℕ} (α : Composition N) (k d : ℕ) :
    d ∣ undeterminedGcd α k ↔
      ∀ j ∈ undeterminedCuts α k, ∀ z : ℤ, (d : ℤ) ∣ (j : ℤ) + z * (N : ℤ) := by
  constructor
  · intro hd j hj z
    have hjd := hd.trans (undeterminedGcd_dvd α k j hj)
    have hNd := hd.trans (undeterminedGcd_dvd_weight α k ⟨j, hj⟩)
    exact Int.dvd_add (Int.natCast_dvd_natCast.mpr hjd)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hNd) z)
  · intro hd
    apply Finset.dvd_gcd
    intro j hj
    have hh : (d : ℤ) ∣ (j : ℤ) := by
      simpa only [zero_mul, add_zero] using hd j hj 0
    exact Int.natCast_dvd_natCast.mp hh

/-- A normalized nonreconstructible source produces all elementary gcd input data. -/
theorem nonreconstructible_undeterminedGcd_properties {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α) :
    0 < undeterminedGcd α k ∧ undeterminedGcd α k < N ∧
      undeterminedGcd α k ∣ N ∧ ∀ j ∈ undeterminedCuts α k, undeterminedGcd α k ∣ j := by
  have hne := undeterminedCuts_nonempty α hn k hk hkr
  exact ⟨undeterminedGcd_pos α k hne, undeterminedGcd_lt_weight α k hne,
    undeterminedGcd_dvd_weight α k hne, fun j hj => undeterminedGcd_dvd α k j hj⟩

end SkewClassInflation
