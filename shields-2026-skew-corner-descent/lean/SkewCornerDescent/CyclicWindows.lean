/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Cyclic window inventories with all starts retained

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original
coefficients» (`sec:dual`, `lem:dual-identities`, `lem:peeling`). Window lengths may
exceed the cycle length; repeated wraps and every start remain in the sums.
The sliding identity and the exact inventory average are independent of response
functions and their valuations. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {G R : Type*} [AddCommGroup G] [Fintype G]

/-- Sum along a window, retaining positions even when the window wraps repeatedly. -/
def windowSum [AddCommMonoid R] (f : G → R) (step : G) (j : ℕ) (i : G) : R :=
  ∑ a ∈ Finset.range j, f (i + a • step)

/-- The exact total over all starts: each position occurs once at each offset. -/
theorem sum_windowSum [AddCommMonoid R] (f : G → R) (step : G) (j : ℕ) :
    ∑ i, windowSum f step j i = j • ∑ i, f i := by
  classical
  unfold windowSum
  rw [Finset.sum_comm]
  have he (a : ℕ) : (∑ i, f (i + a • step)) = ∑ i, f i := by
    exact Equiv.sum_comp (Equiv.addRight (a • step)) f
  simp only [he, Finset.sum_const, Finset.card_range]

omit [Fintype G] in
/-- Sliding loses the old first position and gains the next final position. -/
theorem windowSum_slide [AddCommMonoid R] (f : G → R) (step : G) (j : ℕ) (i : G) :
    windowSum f step j (i + step) + f i =
      windowSum f step j i + f (i + j • step) := by
  unfold windowSum
  have he : (∑ a ∈ Finset.range j, f (i + step + a • step)) =
      ∑ a ∈ Finset.range j, f (i + (a + 1) • step) := by
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    simp [add_nsmul, add_assoc, add_comm, add_left_comm]
  rw [he]
  have hfirst := Finset.sum_range_succ' (fun a => f (i + a • step)) j
  have hlast := Finset.sum_range_succ (fun a => f (i + a • step)) j
  simpa only [zero_nsmul, add_zero] using hfirst.symm.trans hlast

omit [Fintype G] in
/-- Equal window sums force the occurrence mask itself to have the window-length period. -/
theorem periodic_of_constant_windows [AddCancelCommMonoid R] (f : G → R)
    (step : G) (j : ℕ) (c : R) (h : ∀ i, windowSum f step j i = c) :
    Function.Periodic f (j • step) := by
  intro i
  have hs := windowSum_slide f step j i
  rw [h, h] at hs
  exact (add_left_cancel hs).symm

/-- Two integer periods give their gcd period, by Bézout rather than a finite-window heuristic. -/
theorem periodic_gcd {α : Type*} {f : ℤ → α} {m n : ℕ}
    (hm : Function.Periodic f (m : ℤ)) (hn : Function.Periodic f (n : ℤ)) :
    Function.Periodic f (Nat.gcd m n : ℤ) := by
  rw [Nat.gcd_eq_gcd_ab]
  simpa only [zsmul_eq_mul, Int.cast_id, mul_comm] using
    (hm.zsmul (Nat.gcdA m n)).add_period (hn.zsmul (Nat.gcdB m n))

/-- An actual cyclic word with an `m`-period has the gcd period, including repeated wraps. -/
theorem zmod_periodic_gcd {α : Type*} {n m : ℕ} [NeZero n]
    (f : ZMod n → α) (h : Function.Periodic f (m : ZMod n)) :
    Function.Periodic f (Nat.gcd m n : ZMod n) := by
  have hm : Function.Periodic (fun z : ℤ => f (z : ZMod n)) (m : ℤ) := by
    intro z
    simpa only [Int.cast_add, Int.cast_natCast] using h (z : ZMod n)
  have hn : Function.Periodic (fun z : ℤ => f (z : ZMod n)) (n : ℤ) := by
    intro z
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  have hgcd := periodic_gcd hm hn
  intro i
  simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] using
    hgcd (i.val : ℤ)

/-- One complete cyclic sum is the full inventory, independently of the starting position. -/
theorem zmod_windowSum_cycle {n : ℕ} [NeZero n] [AddCommMonoid R]
    (f : ZMod n → R) (i : ZMod n) :
    windowSum f 1 n i = ∑ x, f x := by
  classical
  unfold windowSum
  rw [← Fin.sum_univ_eq_sum_range]
  have hf : ∀ a : Fin n, (a.val : ZMod n) = ZMod.finEquiv n a := by
    intro a
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact Fin.cast_val_eq_self a
  simp only [nsmul_eq_mul, mul_one, hf]
  exact ((ZMod.finEquiv n).toEquiv.trans (Equiv.addLeft i)).sum_comp f

/-- A uniform lower window bound is at most the actual average inventory. -/
theorem inventory_ge_of_window_bound (f : G → ℕ) (step : G) (j m : ℕ)
    (h : ∀ i, m ≤ windowSum f step j i) :
    Fintype.card G * m ≤ j * ∑ i, f i := by
  calc
    Fintype.card G * m = ∑ _ : G, m := by simp
    _ ≤ ∑ i, windowSum f step j i := Finset.sum_le_sum fun i _ => h i
    _ = j * ∑ i, f i := by simpa using sum_windowSum f step j

/-- Constant counts have the exact average, with no division or divisibility convention. -/
theorem constant_window_count (f : G → ℕ) (step : G) (j c : ℕ)
    (h : ∀ i, windowSum f step j i = c) :
    Fintype.card G * c = j * ∑ i, f i := by
  have he := sum_windowSum f step j
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  exact he

/-- A uniform upper bound is at least the average inventory. -/
theorem inventory_le_of_window_bound (f : G → ℕ) (step : G) (j M : ℕ)
    (h : ∀ i, windowSum f step j i ≤ M) :
    j * ∑ i, f i ≤ Fintype.card G * M := by
  calc
    j * ∑ i, f i = ∑ i, windowSum f step j i := by
      simpa using (sum_windowSum f step j).symm
    _ ≤ ∑ _ : G, M := Finset.sum_le_sum fun i _ => h i
    _ = Fintype.card G * M := by simp

/-- If the common upper bound is exactly the average, every window attains it. -/
theorem windows_constant_of_maximum_eq_average (f : G → ℕ) (step : G) (j M : ℕ)
    (h : ∀ i, windowSum f step j i ≤ M)
    (he : j * ∑ i, f i = Fintype.card G * M) :
    ∀ i, windowSum f step j i = M := by
  classical
  have hs : (∑ i, windowSum f step j i) = ∑ _ : G, M := by
    rw [sum_windowSum]
    simpa using he
  have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => h i)).mp hs
  exact fun i => hall i (Finset.mem_univ i)

omit [Fintype G] in
/-- Splitting an inventory preserves every position, including all repeated wraps. -/
theorem windowSum_add [AddCommMonoid R] (f : G → R) (step : G) (j k : ℕ) (i : G) :
    windowSum f step (j + k) i =
      windowSum f step j i + windowSum f step k (i + j • step) := by
  unfold windowSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [add_nsmul, add_assoc]

/-- Full repeated cycles and the short remainder give their exact additive inventory. -/
theorem zmod_windowSum_mul_add {n : ℕ} [NeZero n] [AddCommMonoid R]
    (f : ZMod n → R) (k m : ℕ) (i : ZMod n) :
    windowSum f 1 (k * n + m) i =
      k • (∑ x, f x) + windowSum f 1 m i := by
  induction k with
  | zero => simp [windowSum]
  | succ k ih =>
    have he : (k + 1) * n + m = n + (k * n + m) := by ring
    rw [he, windowSum_add, zmod_windowSum_cycle]
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_self, add_zero]
    rw [ih, succ_nsmul]
    ac_rfl

/-- Product along a window, with repeated wraps retained. -/
def windowProduct [CommMonoid R] (f : G → R) (step : G) (j : ℕ) (i : G) : R :=
  ∏ a ∈ Finset.range j, f (i + a • step)

omit [Fintype G] in
/-- Splitting a window never loses a repeated start or wrap. -/
theorem windowProduct_add [CommMonoid R] (f : G → R) (step : G) (j k : ℕ) (i : G) :
    windowProduct f step (j + k) i =
      windowProduct f step j i * windowProduct f step k (i + j • step) := by
  unfold windowProduct
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  congr 1
  simp [add_nsmul, add_assoc]

/-- Whole-cycle products are independent of the starting position. -/
theorem zmod_windowProduct_cycle {n : ℕ} [NeZero n] [CommMonoid R]
    (f : ZMod n → R) (i : ZMod n) :
    windowProduct f 1 n i = ∏ x, f x := by
  classical
  unfold windowProduct
  rw [← Fin.prod_univ_eq_prod_range]
  have hf : ∀ a : Fin n, (a.val : ZMod n) = ZMod.finEquiv n a := by
    intro a
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact Fin.cast_val_eq_self a
  simp only [nsmul_eq_mul, mul_one, hf]
  exact ((ZMod.finEquiv n).toEquiv.trans (Equiv.addLeft i)).prod_comp f

/-- Repeated whole cycles retain their full power, with an arbitrary shorter remainder. -/
theorem zmod_windowProduct_mul_add {n : ℕ} [NeZero n] [CommMonoid R]
    (f : ZMod n → R) (k m : ℕ) (i : ZMod n) :
    windowProduct f 1 (k * n + m) i =
      (∏ x, f x) ^ k * windowProduct f 1 m i := by
  induction k with
  | zero => simp [windowProduct]
  | succ k ih =>
    have he : (k + 1) * n + m = n + (k * n + m) := by ring
    rw [he, windowProduct_add, zmod_windowProduct_cycle]
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_self, add_zero]
    rw [ih, pow_succ]
    ac_rfl

/-- The reciprocal cyclic inventory used in the period detectors. -/
def inverseWindowSum {n : ℕ} [NeZero n] [Semifield R] (f : ZMod n → R) (j : ℕ) : R :=
  ∑ i, (windowProduct f 1 j i)⁻¹

/-- The long-window inventory factors through its remainder even with repeated wraps. -/
theorem inverseWindowSum_mul_add {n : ℕ} [NeZero n] [Semifield R]
    (f : ZMod n → R) (k m : ℕ) :
    inverseWindowSum f (k * n + m) =
      (∏ x, f x)⁻¹ ^ k * inverseWindowSum f m := by
  unfold inverseWindowSum
  simp_rw [zmod_windowProduct_mul_add]
  simp only [mul_inv_rev, inv_pow]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- A full cycle counted from every start has its full cardinal multiplicity. -/
theorem zmod_sum_inverse_full_cycle {n : ℕ} [NeZero n] [Semifield R]
    (f : ZMod n → R) :
    (∑ i, (windowProduct f 1 n i)⁻¹) = n • (∏ x, f x)⁻¹ := by
  simp only [zmod_windowProduct_cycle, Finset.sum_const, Finset.card_univ,
    ZMod.card]

end SkewCornerDescent.CyclicWindows
