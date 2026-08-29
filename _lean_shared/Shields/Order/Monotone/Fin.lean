/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Strictly monotone tuples of naturals, and their gaps

A strictly monotone `Fin r → ℕ` dominates its own index, and one with a gap is a longer strictly
monotone tuple with an interior entry deleted.  The second is what an induction on the
**dispersion** of an index set runs on: the tuple either has a gap, in which case it is an
insertion, or it has none, in which case it is consecutive.

## Main results

* `Shields.val_le_of_strictMono`: `i ≤ ρ i` for a strictly monotone `ρ : Fin r → ℕ`.
* `Shields.exists_insert_of_gap`: a strictly monotone `ρ : Fin (m + 1) → ℕ` with a gap at `j`
  is `r` composed with `(j.castSucc.succ).succAbove` for a strictly monotone
  `r : Fin (m + 2) → ℕ` -- insert the value `ρ j.castSucc + 1` into the gap.
* `Shields.eq_consecutive_of_no_gap`: with no gap left, `ρ a = a + ρ 0`.

## Implementation notes

The insertion is `Fin.insertNth` at `j.castSucc.succ`, and the deleted position is recorded as a
`succAbove` composition rather than as a `Finset` difference, so that the three-term determinant
identities which consume it need no reindexing.

## Tags

strictly monotone, Fin, tuple, insertNth, succAbove, dispersion
-/

namespace Shields

/-- A strictly monotone selection dominates its own index. -/
theorem val_le_of_strictMono {r : ℕ} {ρ : Fin r → ℕ} (hρ : StrictMono ρ) (i : Fin r) :
    (i : ℕ) ≤ ρ i := by
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => exact Nat.zero_le _
  | succ m ih =>
      have hm : m < r := by omega
      have hstep : ρ ⟨m, hm⟩ < ρ ⟨m + 1, hn⟩ := hρ (by simp [Fin.lt_def])
      have hprev : m ≤ ρ ⟨m, hm⟩ := ih hm
      change m + 1 ≤ ρ ⟨m + 1, hn⟩
      omega

/-- A strictly monotone family with a gap is a strictly monotone family one
longer with an interior entry deleted. -/
theorem exists_insert_of_gap {m : ℕ} (ρ : Fin (m + 1) → ℕ) (hρ : StrictMono ρ)
    (j : Fin m) (hgap : ρ j.castSucc + 1 < ρ j.succ) :
    ∃ r : Fin (m + 2) → ℕ, StrictMono r
      ∧ r ∘ (j.castSucc.succ).succAbove = ρ := by
  refine ⟨(j.castSucc.succ).insertNth (ρ j.castSucc + 1) ρ, ?_, ?_⟩
  · rw [Fin.strictMono_insertNth_iff]
    refine ⟨hρ, fun k hk => ?_, fun k hk => ?_⟩
    · -- below the insertion point `k ≤ j.castSucc`, so `ρ k ≤ ρ j.castSucc`
      refine lt_of_le_of_lt (hρ.monotone (a := k) (b := j.castSucc) ?_) (Nat.lt_succ_self _)
      simp only [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hk ⊢
      omega
    · -- above it `j.succ ≤ k`, and the gap separates `ρ j.castSucc + 1` from `ρ j.succ`
      refine hgap.trans_le (hρ.monotone (a := j.succ) (b := k) ?_)
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hk ⊢
      omega
  · funext k
    simp [Fin.insertNth_apply_succAbove]

/-- If no gap is left, the family is the consecutive one. -/
theorem eq_consecutive_of_no_gap {m : ℕ} (ρ : Fin (m + 1) → ℕ) (hρ : StrictMono ρ)
    (hno : ∀ j : Fin m, ¬ ρ j.castSucc + 1 < ρ j.succ) :
    ρ = fun a : Fin (m + 1) => (a : ℕ) + ρ 0 := by
  funext a
  induction a using Fin.induction with
  | zero => simp
  | succ j ih =>
      have h1 : ρ j.castSucc < ρ j.succ := hρ (by
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
      have h2 := hno j
      rw [not_lt] at h2
      have h3 : ρ j.castSucc = (j : ℕ) + ρ 0 := by
        simpa [Fin.val_castSucc] using ih
      rw [Fin.val_succ]
      omega


/-! ### Axiom footprint -/

/-- info: 'Shields.val_le_of_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms val_le_of_strictMono

/-- info: 'Shields.exists_insert_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_insert_of_gap

/-- info: 'Shields.eq_consecutive_of_no_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eq_consecutive_of_no_gap

end Shields
