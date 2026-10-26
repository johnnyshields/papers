/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicGapPeriod

/-!
# Exact positional vertex and pair charges on a cycle

Supports `shields-2026-skew-corner-descent.tex`
(`prop:normal-interface`, `eq:normal-interface`).
A directed pair touches a state window exactly at one of its internal or two
exterior positions. Counts and weighted sums keep every directed position,
including the full-cycle boundary, without reversed-edge symmetry. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {B : ℕ}

private theorem residue_natCast_injective_below {a b : ℕ} (ha : a < B) (hb : b < B)
    (h : (a : ZMod B) = b) : a = b := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- The finite state positions of an interval. -/
def stateWindow (n : ℕ) (s : ZMod B) : Finset (ZMod B) :=
  (Finset.range n).image fun a : ℕ => s + (a : ZMod B)

/-- Directed pair positions touching a nonempty state interval, including both ends. -/
def pairOverlap (n : ℕ) (s : ZMod B) : Finset (ZMod B) :=
  (Finset.range (n + 1)).image fun a : ℕ => s - 1 + (a : ZMod B)

/-- The internal directed pair positions. -/
def internalPairs (n : ℕ) (s : ZMod B) : Finset (ZMod B) :=
  (Finset.range (n - 1)).image fun a : ℕ => s + (a : ZMod B)

private theorem shifted_range_injOn (length : ℕ) (hlen : length ≤ B) (s : ZMod B) :
    Set.InjOn (fun a : ℕ => s + (a : ZMod B)) (Finset.range length : Set ℕ) := by
  intro a ha b hb h
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  exact residue_natCast_injective_below (by omega) (by omega) (add_left_cancel h)

/-- A pair touches the interval exactly when either of its two directed
endpoint states lies in the interval. Nonemptiness excludes a false zero-state edge. -/
theorem mem_pairOverlap_iff (n : ℕ) (hn : 0 < n) (s p : ZMod B) :
    p ∈ pairOverlap n s ↔ p ∈ stateWindow n s ∨ p + 1 ∈ stateWindow n s := by
  simp only [pairOverlap, stateWindow, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hp⟩
    have han := Finset.mem_range.mp ha
    by_cases ha0 : a = 0
    · subst a
      right
      refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      simp only [Nat.cast_zero, add_zero] at hp ⊢
      calc s = (s - 1) + 1 := by ring
        _ = p + 1 := by rw [hp]
    · left
      refine ⟨a - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_one]
      calc s + ((a : ZMod B) - 1) = s - 1 + a := by ring
        _ = p := hp
  · rintro (⟨a, ha, hp⟩ | ⟨a, ha, hp⟩)
    · refine ⟨a + 1, Finset.mem_range.mpr (by have := Finset.mem_range.mp ha; omega), ?_⟩
      rw [Nat.cast_add, Nat.cast_one]
      calc s - 1 + ((a : ZMod B) + 1) = s + a := by ring
        _ = p := hp
    · refine ⟨a, Finset.mem_range.mpr (by have := Finset.mem_range.mp ha; omega), ?_⟩
      calc s - 1 + (a : ZMod B) = (s + a) - 1 := by ring
        _ = (p + 1) - 1 := by rw [hp]
        _ = p := by ring

/-- State occurrences remain distinct below the cycle length. -/
theorem card_stateWindow (n : ℕ) (hB : n < B) (s : ZMod B) :
    (stateWindow n s).card = n := by
  rw [stateWindow, Finset.card_image_of_injOn (shifted_range_injOn n hB.le s), Finset.card_range]

/-- The complete overlap count is n+1, including the B=n+1 boundary. -/
theorem card_pairOverlap (n : ℕ) (hB : n < B) (s : ZMod B) :
    (pairOverlap n s).card = n + 1 := by
  rw [pairOverlap, Finset.card_image_of_injOn
    (shifted_range_injOn (n + 1) (by omega) (s - 1)), Finset.card_range]

/-- All n-1 internal directed positions are counted separately. -/
theorem card_internalPairs (n : ℕ) (hB : n < B) (s : ZMod B) :
    (internalPairs n s).card = n - 1 := by
  rw [internalPairs, Finset.card_image_of_injOn
    (shifted_range_injOn (n - 1) (by omega) s), Finset.card_range]

/-- The two exterior directed positions and all internal positions form the
complete pair charge, including n=2. -/
theorem pairOverlap_sum {R : Type*} [AddCommMonoid R] (n : ℕ) (hB : n < B) (hn : 2 ≤ n)
    (f : ZMod B → R) (s : ZMod B) :
    ∑ p ∈ pairOverlap n s, f p =
      f (s - 1) + (∑ a ∈ Finset.range (n - 1), f (s + (a : ZMod B))) +
        f (s - 1 + (n : ZMod B)) := by
  rw [pairOverlap, Finset.sum_image (shifted_range_injOn (n + 1) (by omega) (s - 1))]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hm : m + 2 - 1 = m + 1 := by omega
  rw [hm]
  have hshift (a : ℕ) : s - 1 + ((a + 1 : ℕ) : ZMod B) = s + (a : ZMod B) := by
    push_cast
    ring
  simp only [hshift, Nat.cast_zero, add_zero]
  ac_rfl

variable [NeZero B]

/-- Over all starts, each cyclic vertex is charged exactly n times. -/
theorem sum_stateWindow {R : Type*} [AddCommGroup R] (n : ℕ) (hB : n < B) (f : ZMod B → R) :
    ∑ s : ZMod B, ∑ v ∈ stateWindow n s, f v = n • ∑ v, f v := by
  have hwin (s : ZMod B) : ∑ v ∈ stateWindow n s, f v = windowSum f 1 n s := by
    rw [stateWindow, Finset.sum_image (shifted_range_injOn n hB.le s)]
    unfold windowSum
    simp only [nsmul_eq_mul, mul_one]
  simp only [hwin]
  exact sum_windowSum f 1 n

/-- Over all starts, each directed pair is charged exactly n+1 times. -/
theorem sum_pairOverlap {R : Type*} [AddCommGroup R] (n : ℕ) (hB : n < B) (f : ZMod B → R) :
    ∑ s : ZMod B, ∑ p ∈ pairOverlap n s, f p = (n + 1) • ∑ p, f p := by
  have hwin (s : ZMod B) : ∑ p ∈ pairOverlap n s, f p = windowSum f 1 (n + 1) (s - 1) := by
    rw [pairOverlap, Finset.sum_image (shifted_range_injOn (n + 1) (by omega) (s - 1))]
    unfold windowSum
    simp only [nsmul_eq_mul, mul_one]
  simp only [hwin]
  have hshift := (Equiv.subRight (1 : ZMod B)).sum_comp
    (fun i : ZMod B => windowSum f 1 (n + 1) i)
  simp only [Equiv.subRight_apply] at hshift
  rw [hshift]
  exact sum_windowSum f 1 (n + 1)

/-- At the full overlap boundary every directed cyclic position occurs. -/
theorem pairOverlap_eq_univ_of_boundary (n : ℕ) (hB : B = n + 1) (s : ZMod B) :
    pairOverlap n s = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_pairOverlap n (by omega) s, ZMod.card]
  omega

/-- A scalar weighted pair charge retains the complete n+1 multiplicity. -/
theorem scaled_pair_charge {R : Type*} [CommRing R] (n : ℕ) (hB : n < B) (a : R)
    (f : ZMod B → R) :
    ∑ s : ZMod B, a * ∑ p ∈ pairOverlap n s, f p =
      ((n : R) + 1) * (a * ∑ p, f p) := by
  rw [← Finset.mul_sum, sum_pairOverlap n hB f, nsmul_eq_mul]
  push_cast
  ring

/-- Internal and both exterior pair occurrences give the full n+1 charge on
any nonempty cycle. There is no shorter-than-cycle restriction: equal cyclic
labels still count separately, including a full-period state window. -/
theorem cyclic_pair_position_multiplicity {R : Type*} [AddCommGroup R]
    (n : ℕ) (hn : 0 < n) (f : ZMod B → R) :
    (∑ s : ZMod B, windowSum f 1 (n - 1) s) +
      (∑ s : ZMod B, f s) +
      (∑ s : ZMod B, f (s + ((n - 1 : ℕ) : ZMod B))) =
      (n + 1) • ∑ s : ZMod B, f s := by
  have hshift : (∑ s : ZMod B, f (s + ((n - 1 : ℕ) : ZMod B))) =
      ∑ s : ZMod B, f s := by
    apply Fintype.sum_equiv (Equiv.addRight (((n - 1 : ℕ) : ZMod B)))
    intro s
    rfl
  have hc : n - 1 + 1 + 1 = n + 1 := by omega
  rw [sum_windowSum f 1 (n - 1), hshift, ← hc]
  simp only [add_nsmul, one_nsmul]

end SkewCornerDescent.CyclicWindows
