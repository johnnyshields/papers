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

private theorem le_val_of_strictMono {r : ℕ} {s : Fin r → ℕ} (hs : StrictMono s) :
    ∀ (n : ℕ) (h : n < r), n ≤ s ⟨n, h⟩ := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
      intro h
      have hm : m < r := by omega
      have h1 := hs (show (⟨m, hm⟩ : Fin r) < ⟨m + 1, h⟩ from by simp)
      have h2 := ih hm
      omega

/-- A strictly monotone selection dominates its own index. -/
theorem val_le_of_strictMono {r : ℕ} {ρ : Fin r → ℕ} (hρ : StrictMono ρ) (i : Fin r) :
    (i : ℕ) ≤ ρ i := by
  have := le_val_of_strictMono hρ (i : ℕ) i.isLt
  simp only [Fin.eta] at this
  exact this

/-- A strictly monotone family with a gap is a strictly monotone family one
longer with an interior entry deleted. -/
theorem exists_insert_of_gap {m : ℕ} (ρ : Fin (m + 1) → ℕ) (hρ : StrictMono ρ)
    (j : Fin m) (hgap : ρ j.castSucc + 1 < ρ j.succ) :
    ∃ r : Fin (m + 2) → ℕ, StrictMono r
      ∧ r ∘ (j.castSucc.succ).succAbove = ρ := by
  set i : Fin (m + 2) := j.castSucc.succ with hi
  refine ⟨i.insertNth (ρ j.castSucc + 1) ρ, ?_, ?_⟩
  · intro a b hab
    rcases eq_or_ne a i with rfl | ha
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm (ne_of_lt hab))
      rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      have hk : j.castSucc < k := by
        have := (Fin.lt_succAbove_iff_le_castSucc i k).mp hab
        rw [hi, Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_castSucc] at this
        rw [Fin.lt_def, Fin.val_castSucc]; omega
      have : ρ j.succ ≤ ρ k := hρ.monotone (by
        rw [Fin.le_def, Fin.val_succ]
        rw [Fin.lt_def, Fin.val_castSucc] at hk
        omega)
      omega
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq ha
      rcases eq_or_ne b i with rfl | hb
      · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        have hk : k ≤ j.castSucc := by
          by_contra hcon
          rw [not_le] at hcon
          exact absurd hab (not_lt.mpr ((Fin.lt_succAbove_iff_le_castSucc i k).mpr (by
            rw [hi, Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_castSucc]
            rw [Fin.lt_def, Fin.val_castSucc] at hcon
            omega)).le)
        have : ρ k ≤ ρ j.castSucc := hρ.monotone hk
        omega
      · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hb
        rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        exact hρ (Fin.succAbove_lt_succAbove_iff.mp hab)
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

end Shields
