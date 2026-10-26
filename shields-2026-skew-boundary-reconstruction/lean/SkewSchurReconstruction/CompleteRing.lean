/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic
import Mathlib.Data.PNat.Basic

/-!
# The free ring of complete generators

Formalizes `shields-2026-skew-boundary-reconstruction.tex`,
«Capped cofactors and admissible convex weights» (`sec:coordinates`).
The positive complete generators are independent polynomial variables; index zero is one,
and negative indices are zero.  Sorry-free.
-/

namespace SkewSchurReconstruction

/-- The manuscript's free integral polynomial ring in the positive complete generators. -/
abbrev CompleteRing := MvPolynomial ℕ+ ℤ

/-- A complete generator with the manuscript's zero and negative index conventions. -/
noncomputable def complete (k : ℤ) : CompleteRing :=
  if k = 0 then 1 else if hk : 0 < k then
    MvPolynomial.X ⟨k.toNat, by omega⟩ else 0

@[simp]
theorem complete_zero : complete 0 = 1 := by
  simp [complete]

@[simp]
theorem complete_of_neg {k : ℤ} (hk : k < 0) : complete k = 0 := by
  simp [complete, ne_of_lt hk, not_lt_of_ge hk.le]

@[simp]
theorem complete_of_pos {k : ℤ} (hk : 0 < k) :
    complete k = MvPolynomial.X ⟨k.toNat, by omega⟩ := by
  simp [complete, ne_of_gt hk, hk]

theorem complete_nat (k : ℕ+) : complete (k : ℕ) = MvPolynomial.X k := by
  rw [complete_of_pos (by exact_mod_cast k.pos)]
  congr 1

/-- Negative matrix subscripts vanish, and every nonnegative subscript is nonzero. -/
theorem complete_ne_zero_iff (k : ℤ) : complete k ≠ 0 ↔ 0 ≤ k := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [complete_of_neg hk, not_le_of_gt hk]
  · simp
  · rw [complete_of_pos hk]
    exact iff_of_true (MvPolynomial.X_ne_zero _) hk.le

/-- Polynomial substitution determined by the images of the positive complete generators. -/
noncomputable def specialize {R : Type*} [CommRing R] (a : ℕ+ → R) :
    CompleteRing →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) a

theorem specialize_complete {R : Type*} [CommRing R] (a : ℕ+ → R) (k : ℕ+) :
    specialize a (complete (k : ℕ)) = a k := by
  change MvPolynomial.eval₂ (Int.castRingHom R) a (complete (k : ℕ)) = a k
  rw [complete_nat, MvPolynomial.eval₂_X]

/-- A complete generator cannot contain a variable above its nonnegative subscript. -/
theorem complete_vars_bound (a D : ℤ) (h : a ≤ D)
    (k : ℕ+) (hk : k ∈ (complete a).vars) : (k.val : ℤ) ≤ D := by
  by_cases ha : 0 < a
  · let p : ℕ+ := ⟨a.toNat, by omega⟩
    have hc : complete a = (MvPolynomial.X p : CompleteRing) := complete_of_pos ha
    rw [hc] at hk
    have hv : (MvPolynomial.X p : CompleteRing).vars = ({p} : Finset ℕ+) :=
      MvPolynomial.vars_X
    have hkp : k = p := Finset.mem_singleton.mp (hv ▸ hk)
    subst k
    change (a.toNat : ℤ) ≤ D
    omega
  · have ha' : a ≤ 0 := by omega
    rcases eq_or_lt_of_le ha' with hz | hn
    · rw [hz, complete_zero] at hk
      simp at hk
    · rw [complete_of_neg hn] at hk
      simp at hk

end SkewSchurReconstruction
