/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedWindowPoles

/-!
# Signed defects of actual cyclic class inventories

Supports `shields-2026-skew-corner-descent.tex`
(`lem:peeling`, `thm:dual-period`, `thm:dual-general`).
The signed exponent inventory is computed from the complete period and its literal short
prefix. Its total and inactive-class average follow from position counts. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- The actual complete-period count minus the signed literal-prefix contribution. -/
def classDefect {G α : Type*} [AddCommGroup G] [Fintype G] [DecidableEq α]
    (word : G → α) (step : G) (d s prefixLength : ℕ) (start : G) (a : α) : ℤ :=
  (s : ℤ) * (∑ i, classMask word a i) -
    (d : ℤ) * ((windowSum (classMask word a) step prefixLength start : ℕ) : ℤ)

/-- Each actual position contributes to exactly one class, without deduplicating starts. -/
theorem sum_classDefect {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α]
    (word : G → α) (step : G) (d s prefixLength : ℕ) (start : G) :
    (∑ a, classDefect word step d s prefixLength start a) =
      (s : ℤ) * Fintype.card G - (d : ℤ) * prefixLength := by
  classical
  have hmask (i : G) : (∑ a, classMask word a i) = 1 := by simp [classMask]
  have hperiod : (∑ a, ∑ i, classMask word a i) = Fintype.card G := by
    rw [Finset.sum_comm]
    simp only [hmask, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  have hprefix := sum_class_window_counts word step prefixLength start
  simp only [classDefect, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Nat.cast_sum, hperiod, hprefix]

/-- The reduced period and the prefix of length `rs-1` produce total exponent `d`. -/
theorem sum_reduced_classDefect {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hs : 0 < s)
    (word : ZMod (r * d) → α) :
    (∑ a, classDefect word 1 d s (r * s - 1) 0 a) = (d : ℤ) := by
  rw [sum_classDefect, ZMod.card]
  have hm : 1 ≤ r * s := Nat.mul_pos hr hs
  rw [Nat.cast_sub hm]
  push_cast
  ring

/-- A zero actual class defect makes its short-window prefix count the exact cyclic average. -/
theorem inactive_class_average {α : Type*} [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (word : ZMod (r * d) → α) (a : α)
    (he : classDefect word 1 d s (r * s - 1) 0 a = 0) :
    (r * s) * (∑ i, classMask word a i) =
      Fintype.card (ZMod (r * d)) * windowSum (classMask word a) 1 (r * s - 1) 0 := by
  have hbalanceZ : (s : ℤ) * (∑ i, classMask word a i) =
      (d : ℤ) * ((windowSum (classMask word a) 1 (r * s - 1) 0 : ℕ) : ℤ) :=
    sub_eq_zero.mp he
  have hbalance : s * (∑ i, classMask word a i) =
      d * windowSum (classMask word a) 1 (r * s - 1) 0 := by exact_mod_cast hbalanceZ
  rw [ZMod.card]
  calc
    _ = r * (s * ∑ i, classMask word a i) := by ring
    _ = r * (d * windowSum (classMask word a) 1 (r * s - 1) 0) := by rw [hbalance]
    _ = _ := by ring

/-- A full positive remainder has only the omitted position's class as active support. -/
theorem full_remainder_classDefect {α : Type*} [DecidableEq α]
    {r d : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d)
    (word : ZMod (r * d) → α) (a : α) :
    classDefect word 1 d d (r * d - 1) 0 a =
      (d : ℤ) * classMask word a ((r * d - 1 : ℕ) : ZMod (r * d)) := by
  exact omitted_phase_defect hr hd (classMask word a) _
    (fun i => zmod_windowSum_cycle _ i)

/-- In the divisible positive-remainder case no two distinct classes can both be active. -/
theorem full_remainder_active_iff {α : Type*} [DecidableEq α]
    {r d : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d)
    (word : ZMod (r * d) → α) (a : α) :
    classDefect word 1 d d (r * d - 1) 0 a ≠ 0 ↔
      a = word ((r * d - 1 : ℕ) : ZMod (r * d)) := by
  rw [full_remainder_classDefect hr hd]
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases ha : word ((r * d - 1 : ℕ) : ZMod (r * d)) = a
  · simp only [classMask, ite_eq_left ha, Nat.cast_one, mul_one]
    exact ⟨fun _ => ha.symm, fun _ => hdZ⟩
  · have han := Ne.symm ha
    simp only [classMask, ite_eq_right ha, Nat.cast_zero, mul_zero, ne_eq,
      not_true_eq_false, han]

/-- Summing by full response class retains the multiplicity of every literal position. -/
theorem sum_class_inventory_weight {G α R : Type*}
    [Fintype G] [Fintype α] [DecidableEq α] [Semiring R]
    (word : G → α) (weight : α → R) :
    (∑ a, ((∑ i, classMask word a i : ℕ) : R) * weight a) =
      ∑ i, weight (word i) := by
  classical
  simp only [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [classMask]

/-- For a one-position short window and empty prefix, the short detector vanishes
identically. This is the scalar identity in `cor:automatic-open`, not an exposure
or nonvanishing assumption. -/
theorem one_position_short_detector_zero {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Field R]
    (word : G → α) (response : α → R) (step : G) (d : ℕ) (start : G) :
    (∑ i, (windowProduct (response ∘ word) step 1 i)⁻¹) -
      (windowProduct (response ∘ word) step 0 start)⁻¹ *
        (∑ a, (classDefect word step d 1 0 start a : R) * (response a)⁻¹) = 0 := by
  have hcount (a : α) :
      (classDefect word step d 1 0 start a : R) =
        ((∑ i, classMask word a i : ℕ) : R) := by
    simp [classDefect, windowSum]
  simp only [windowProduct, Finset.range_one, Finset.prod_singleton, zero_nsmul,
    add_zero, Function.comp_apply, Finset.range_zero, Finset.prod_empty, inv_one,
    one_mul, hcount]
  rw [sum_class_inventory_weight]
  exact sub_self _

/-- Every outer size strictly larger than the period admits the positive remainder
convention, with a full remainder exactly when the period divides the outer size. -/
theorem positive_remainder_exists {b d : ℕ} (hd : 0 < d) (hdb : d < b) :
    ∃ k s : ℕ, 0 < k ∧ 0 < s ∧ s ≤ d ∧ b = k * d + s ∧ (d ∣ b ↔ s = d) := by
  let k := (b - 1) / d
  let s := (b - 1) % d + 1
  have hk : 0 < k := Nat.div_pos (by omega) hd
  have hs : 0 < s := by omega
  have hsd : s ≤ d := by have := Nat.mod_lt (b - 1) hd; omega
  have hb : b = k * d + s := by
    have he := Nat.mod_add_div (b - 1) d
    rw [Nat.mul_comm d ((b - 1) / d)] at he
    dsimp only [k, s]
    omega
  refine ⟨k, s, hk, hs, hsd, hb, ?_⟩
  constructor
  · intro h
    have hsum : d ∣ k * d + s := hb ▸ h
    have hsdvd : d ∣ s := (Nat.dvd_add_iff_left (Nat.dvd_mul_left d k)).mpr
      (by simpa only [Nat.add_comm] using hsum)
    exact Nat.le_antisymm hsd (Nat.le_of_dvd hs hsdvd)
  · intro he
    rw [hb, he]
    exact dvd_add (Nat.dvd_mul_left d k) (dvd_refl d)

/-- A full positive remainder leaves only the class at the one omitted position active. -/
theorem full_remainder_active_unique {α : Type*} [DecidableEq α]
    {r d : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d)
    (word : ZMod (r * d) → α) {a b : α}
    (ha : classDefect word 1 d d (r * d - 1) 0 a ≠ 0)
    (hb : classDefect word 1 d d (r * d - 1) 0 b ≠ 0) : a = b := by
  exact ((full_remainder_active_iff hr hd word a).mp ha).trans
    ((full_remainder_active_iff hr hd word b).mp hb).symm

end SkewCornerDescent.CyclicWindows
