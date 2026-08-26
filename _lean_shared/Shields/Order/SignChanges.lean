/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Fin

/-!
# Sign changes of a real vector

The **sign-change count** `S^-(x)` of a finite real vector is the number of sign changes in the
sequence obtained by deleting the zero entries.  It is the quantity a totally nonnegative matrix
cannot increase, and this file gives it two descriptions:

* `Shields.AltIndices x k` -- `x` alternates in sign along some strictly increasing family of
  `k + 1` indices.  `Shields.signChanges x` is the largest such `k`.
* `Shields.jumpCount u j` -- the number of adjacent sign changes strictly before index `j`.
  On a vector with no zero entry the two agree, and the jump count is the one that carries an
  induction: `Shields.jumpCount_parity` says the sign of `u j` relative to `u 0` is the parity
  of `jumpCount u j`.

The parity statement is what turns a sign pattern into a block decomposition, which is how the
variation-diminishing property is proved.

## Main results

* `Shields.jumpCount_parity` -- the sign of an entry is the parity of the jump count before it
* `Shields.altIndices_jumpCount` -- a nonvanishing vector alternates along its block starts
* `Shields.le_signChanges`, `Shields.signChanges_le`

## Implementation notes

`jumpCount` takes a sequence `\mathbb{N} \to \mathbb{R}`, not a `Fin n` vector, so that the pair
`(u p, u (p+1))` needs no bound arithmetic; `Shields.vecExt` extends a vector by zero.  Only
indices below the vector's length are ever read.

## Tags

sign change, variation, alternating, totally nonnegative
-/

open Finset

namespace Shields

variable {n : ℕ}

/-! ### Extension by zero -/

/-- A `Fin n` vector read as a sequence, zero past the end. -/
noncomputable def vecExt {n : ℕ} (x : Fin n → ℝ) (p : ℕ) : ℝ :=
  if h : p < n then x ⟨p, h⟩ else 0

theorem vecExt_of_lt {x : Fin n → ℝ} {p : ℕ} (h : p < n) : vecExt x p = x ⟨p, h⟩ := dif_pos h

@[simp] theorem vecExt_coe (x : Fin n → ℝ) (j : Fin n) : vecExt x (j : ℕ) = x j := by
  rw [vecExt_of_lt j.isLt]

theorem vecExt_ne_zero {x : Fin n → ℝ} (hx : ∀ j, x j ≠ 0) {p : ℕ} (hp : p < n) :
    vecExt x p ≠ 0 := by
  rw [vecExt_of_lt hp]; exact hx _

/-! ### The adjacent jump count -/

/-- The number of adjacent sign changes of `u` at positions strictly below `j`. -/
noncomputable def jumpCount (u : ℕ → ℝ) (j : ℕ) : ℕ :=
  ((Finset.range j).filter fun p => u p * u (p + 1) < 0).card

@[simp] theorem jumpCount_zero (u : ℕ → ℝ) : jumpCount u 0 = 0 := by
  simp [jumpCount]

theorem jumpCount_succ (u : ℕ → ℝ) (j : ℕ) :
    jumpCount u (j + 1) = jumpCount u j + if u j * u (j + 1) < 0 then 1 else 0 := by
  rw [jumpCount, jumpCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : u j * u (j + 1) < 0
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, add_zero]

theorem monotone_jumpCount (u : ℕ → ℝ) : Monotone (jumpCount u) :=
  monotone_nat_of_le_succ fun j => by rw [jumpCount_succ]; split <;> omega

theorem jumpCount_succ_le (u : ℕ → ℝ) (j : ℕ) : jumpCount u (j + 1) ≤ jumpCount u j + 1 := by
  rw [jumpCount_succ]; split <;> omega

/-- **The sign of an entry is the parity of the jump count before it.**  On a stretch where `u`
never vanishes, `u j` has the sign of `u 0` exactly when `jumpCount u j` is even. -/
theorem jumpCount_parity {u : ℕ → ℝ} {N : ℕ} (hu : ∀ p ≤ N, u p ≠ 0) :
    ∀ j ≤ N, 0 < (-1 : ℝ) ^ jumpCount u j * (u 0 * u j) := by
  intro j
  induction j with
  | zero =>
      intro _
      simpa using mul_self_pos.mpr (hu 0 (Nat.zero_le N))
  | succ j ih =>
      intro hj
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      have hprev := ih hjN
      have hsq : 0 < u j * u j := mul_self_pos.mpr (hu j hjN)
      rw [jumpCount_succ]
      by_cases h : u j * u (j + 1) < 0
      · rw [if_pos h, pow_add, pow_one]
        nlinarith [mul_pos hprev (neg_pos.mpr h)]
      · rw [if_neg h, add_zero]
        have h' : 0 < u j * u (j + 1) :=
          lt_of_le_of_ne (not_lt.mp h)
            (Ne.symm (mul_ne_zero (hu j hjN) (hu (j + 1) hj)))
        nlinarith [mul_pos hprev h']

/-- Two entries of a nonvanishing vector have opposite signs exactly when their jump counts
have opposite parity. -/
theorem mul_neg_of_jumpCount_odd {u : ℕ → ℝ} {N : ℕ} (hu : ∀ p ≤ N, u p ≠ 0)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (hpar : Odd (jumpCount u a + jumpCount u b)) : u a * u b < 0 := by
  have h1 := jumpCount_parity hu a ha
  have h2 := jumpCount_parity hu b hb
  have hsign : ((-1 : ℝ) ^ jumpCount u a) * ((-1 : ℝ) ^ jumpCount u b) = -1 := by
    rw [← pow_add, hpar.neg_one_pow]
  have h0 : 0 < u 0 * u 0 := mul_self_pos.mpr (hu 0 (Nat.zero_le N))
  generalize hA : ((-1 : ℝ) ^ jumpCount u a) = A at h1 hsign
  generalize hB : ((-1 : ℝ) ^ jumpCount u b) = B at h2 hsign
  have hprod : 0 < (A * (u 0 * u a)) * (B * (u 0 * u b)) := mul_pos h1 h2
  have hexp : (A * (u 0 * u a)) * (B * (u 0 * u b))
      = (A * B) * ((u 0 * u 0) * (u a * u b)) := by ring
  rw [hexp, hsign] at hprod
  nlinarith [hprod, h0]

/-! ### Block starts -/

/-- The least index at which the jump count reaches `t`. -/
noncomputable def blockStart (u : ℕ → ℝ) (t : ℕ) : ℕ := sInf {j | t ≤ jumpCount u j}

theorem blockStart_le {u : ℕ → ℝ} {t N : ℕ} (h : t ≤ jumpCount u N) : blockStart u t ≤ N :=
  Nat.sInf_le (Set.mem_ofPred.mpr h)

theorem le_jumpCount_blockStart {u : ℕ → ℝ} {t N : ℕ} (h : t ≤ jumpCount u N) :
    t ≤ jumpCount u (blockStart u t) :=
  Set.mem_ofPred.mp (Nat.sInf_mem (s := {j | t ≤ jumpCount u j}) ⟨N, Set.mem_ofPred.mpr h⟩)

/-- At its block start the jump count is exactly `t`: it cannot have overshot, because it grows
by at most one per step and the previous index was below `t`. -/
theorem jumpCount_blockStart {u : ℕ → ℝ} {t N : ℕ} (h : t ≤ jumpCount u N) :
    jumpCount u (blockStart u t) = t := by
  have hmem := le_jumpCount_blockStart h
  rcases Nat.eq_zero_or_pos (blockStart u t) with h0 | h0
  · rw [h0] at hmem ⊢
    simp only [jumpCount_zero] at hmem ⊢
    omega
  · obtain ⟨j, hj⟩ : ∃ j, blockStart u t = j + 1 := ⟨blockStart u t - 1, by omega⟩
    have hlt : jumpCount u j < t := by
      by_contra hc
      have hle : blockStart u t ≤ j := Nat.sInf_le (Set.mem_ofPred.mpr (not_lt.mp hc))
      omega
    have hstep := jumpCount_succ_le u j
    rw [hj] at hmem ⊢
    omega

theorem blockStart_strictMono {u : ℕ → ℝ} {N : ℕ} {t t' : ℕ} (ht : t ≤ jumpCount u N)
    (ht' : t' ≤ jumpCount u N) (h : t < t') : blockStart u t < blockStart u t' := by
  by_contra hc
  have := monotone_jumpCount u (not_lt.mp hc)
  rw [jumpCount_blockStart ht, jumpCount_blockStart ht'] at this
  omega

/-! ### The alternation relation and the sign-change count -/

/-- `x` alternates in sign along some strictly increasing family of `k + 1` indices. -/
def AltIndices {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ i : Fin (k + 1) → Fin n, StrictMono i ∧
    ∀ s : Fin k, x (i s.castSucc) * x (i s.succ) < 0

theorem AltIndices.lt {x : Fin n → ℝ} {k : ℕ} (h : AltIndices x k) : k < n := by
  obtain ⟨i, hi, -⟩ := h
  have hcard := Fintype.card_le_of_injective i hi.injective
  simp only [Fintype.card_fin] at hcard
  exact hcard

open scoped Classical in
/-- `S^-(x)`: the largest `k` for which `x` alternates along `k + 1` indices. -/
noncomputable def signChanges {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  Nat.findGreatest (AltIndices x) n

open scoped Classical in
theorem le_signChanges {x : Fin n → ℝ} {k : ℕ} (h : AltIndices x k) : k ≤ signChanges x :=
  Nat.le_findGreatest h.lt.le h

open scoped Classical in
theorem signChanges_le {x : Fin n → ℝ} {B : ℕ} (h : ∀ k, AltIndices x k → k ≤ B) :
    signChanges x ≤ B := by
  rcases Nat.eq_zero_or_pos (signChanges x) with h0 | h0
  · omega
  · exact h _ (Nat.findGreatest_of_ne_zero rfl (by omega))

/-- **A nonvanishing vector alternates along its block starts.**  The block starts are strictly
increasing and their jump counts are `0, 1, \dots, q`, so consecutive entries have opposite
parity and hence opposite sign. -/
theorem altIndices_jumpCount {x : Fin n → ℝ} (hx : ∀ j, x j ≠ 0) (hn : 0 < n) :
    AltIndices x (jumpCount (vecExt x) (n - 1)) := by
  have hune : ∀ p ≤ n - 1, vecExt x p ≠ 0 := fun p hp => vecExt_ne_zero hx (by omega)
  have hbound : ∀ t : Fin (jumpCount (vecExt x) (n - 1) + 1),
      blockStart (vecExt x) (t : ℕ) < n := fun t =>
    lt_of_le_of_lt (blockStart_le (N := n - 1) (by have := t.isLt; omega)) (by omega)
  refine ⟨fun t => ⟨blockStart (vecExt x) (t : ℕ), hbound t⟩, ?_, ?_⟩
  · intro a b hab
    refine Fin.mk_lt_mk.mpr (blockStart_strictMono (N := n - 1) ?_ ?_ ?_)
    · have := a.isLt; omega
    · have := b.isLt; omega
    · exact_mod_cast hab
  · intro s
    have hs := s.isLt
    have hcs : (s.castSucc : ℕ) = (s : ℕ) := Fin.val_castSucc s
    have hss : (s.succ : ℕ) = (s : ℕ) + 1 := Fin.val_succ s
    have h1 : jumpCount (vecExt x) (blockStart (vecExt x) (s.castSucc : ℕ))
        = (s.castSucc : ℕ) := jumpCount_blockStart (N := n - 1) (by omega)
    have h2 : jumpCount (vecExt x) (blockStart (vecExt x) (s.succ : ℕ))
        = (s.succ : ℕ) := jumpCount_blockStart (N := n - 1) (by omega)
    have hodd : Odd (jumpCount (vecExt x) (blockStart (vecExt x) (s.castSucc : ℕ))
        + jumpCount (vecExt x) (blockStart (vecExt x) (s.succ : ℕ))) := by
      rw [h1, h2, hcs, hss]; exact ⟨(s : ℕ), by omega⟩
    have hneg := mul_neg_of_jumpCount_odd (N := n - 1) hune
      (a := blockStart (vecExt x) (s.castSucc : ℕ))
      (b := blockStart (vecExt x) (s.succ : ℕ))
      (by have := hbound s.castSucc; omega) (by have := hbound s.succ; omega) hodd
    rw [vecExt_of_lt (hbound s.castSucc), vecExt_of_lt (hbound s.succ)] at hneg
    exact hneg

/-- Two sequences agreeing up to `N` have the same jump count at `N`. -/
theorem jumpCount_congr {u v : ℕ → ℝ} {N : ℕ} (h : ∀ p ≤ N, u p = v p) :
    jumpCount u N = jumpCount v N := by
  unfold jumpCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hlt⟩
    exact ⟨hp, by rwa [← h p (by omega), ← h (p + 1) (by omega)]⟩
  · rintro ⟨hp, hlt⟩
    exact ⟨hp, by rwa [h p (by omega), h (p + 1) (by omega)]⟩

/-- Two sequences agreeing in sign up to `N` have the same jump count at `N`. -/
theorem jumpCount_congr_of_sign {u v : ℕ → ℝ} {N : ℕ} (h : ∀ p ≤ N, 0 < u p * v p) :
    jumpCount u N = jumpCount v N := by
  unfold jumpCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hlt⟩
    refine ⟨hp, ?_⟩
    nlinarith [mul_pos (h p (by omega)) (h (p + 1) (by omega))]
  · rintro ⟨hp, hlt⟩
    refine ⟨hp, ?_⟩
    nlinarith [mul_pos (h p (by omega)) (h (p + 1) (by omega))]

end Shields
