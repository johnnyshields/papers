/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Deviation.lean`. -/
import GluingCore.MixedFold.Generic

/-!
# Generic bits, deviations and the generic height

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `eq:gluing-mixed-phases`; the generic words `A⁰`, `B⁰` of
`lem:gluing-periods` (ii)).

For a periodic comparison pair `(Ā, B̄)` of period `g`, the height word of `(A, B)` splits as the
generic height `H̄ = mixFold_ht Ā B̄` plus the sum of the deviations `δ_y = (A_y - Ā_y) -
(B_y - B̄_y)` (`mixFold_ht_eq_add_dev`), and `H̄(n + g) = H̄(n) + Δ` with `Δ = H̄(g) - 1`
(`mixFold_gen_ht_add`).  `MixFoldPair.exists_gen` supplies the generic words of a pair of charts.

Sorry-free.
-/

namespace GluingCore

open PeriodWords

/-- The deviation of `(A, B)` from the comparison pair `(Ā, B̄)` at the position `y`. -/
def mixFold_dev (A B Ab Bb : ℤ → ℤ) (y : ℤ) : ℤ := (A y - Ab y) - (B y - Bb y)

/-- The sum of the deviations over the positions `1, …, n`. -/
def mixFold_devSum (A B Ab Bb : ℤ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, mixFold_dev A B Ab Bb ((k : ℤ) + 1)

theorem mixFold_ht_eq_add_dev (A B Ab Bb : ℤ → ℤ) (n : ℕ) :
    mixFold_ht A B n = mixFold_ht Ab Bb n + mixFold_devSum A B Ab Bb n := by
  induction n with
  | zero => simp [mixFold_ht_zero, mixFold_devSum]
  | succ n ih =>
    rw [mixFold_ht_succ, mixFold_ht_succ, ih]
    simp only [mixFold_devSum, Finset.sum_range_succ, mixFold_dev] at *
    ring

theorem mixFold_devSum_succ (A B Ab Bb : ℤ → ℤ) (n : ℕ) :
    mixFold_devSum A B Ab Bb (n + 1) =
      mixFold_devSum A B Ab Bb n + mixFold_dev A B Ab Bb ((n : ℤ) + 1) := by
  simp [mixFold_devSum, Finset.sum_range_succ]

/-- The difference of two deviation sums is the sum over the positions in between. -/
theorem mixFold_devSum_add (A B Ab Bb : ℤ → ℤ) (n j : ℕ) :
    mixFold_devSum A B Ab Bb (n + j) = mixFold_devSum A B Ab Bb n +
      ∑ k ∈ Finset.range j, mixFold_dev A B Ab Bb (((n + k : ℕ) : ℤ) + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, mixFold_devSum_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- If the deviations vanish outside a finite set `S`, the deviation sum is the sum over `S`. -/
theorem mixFold_devSum_eq_of_support (A B Ab Bb : ℤ → ℤ) (n : ℕ) (S : Finset ℤ)
    (hS : ∀ y : ℤ, 1 ≤ y → y ≤ (n : ℤ) → y ∉ S → mixFold_dev A B Ab Bb y = 0) :
    mixFold_devSum A B Ab Bb n =
      ∑ y ∈ S.filter (fun y => 1 ≤ y ∧ y ≤ (n : ℤ)), mixFold_dev A B Ab Bb y := by
  unfold mixFold_devSum
  have : ∑ k ∈ Finset.range n, mixFold_dev A B Ab Bb ((k : ℤ) + 1) =
      ∑ y ∈ (Finset.Icc (1 : ℤ) (n : ℤ)), mixFold_dev A B Ab Bb y := by
    refine Finset.sum_bij (fun k _ => (k : ℤ) + 1) (fun k hk => ?_) (fun a _ b _ h => ?_)
      (fun y hy => ?_) (fun k _ => rfl)
    · simp only [Finset.mem_range] at hk
      rw [Finset.mem_Icc]; omega
    · omega
    · rw [Finset.mem_Icc] at hy
      refine ⟨(y - 1).toNat, ?_, by omega⟩
      simp only [Finset.mem_range]; omega
  rw [this]
  symm
  refine Finset.sum_subset (fun y hy => ?_) (fun y hy hy' => ?_)
  · simp only [Finset.mem_filter] at hy
    rw [Finset.mem_Icc]; exact hy.2
  · rw [Finset.mem_Icc] at hy
    exact hS y hy.1 hy.2 (fun h => hy' (Finset.mem_filter.mpr ⟨h, hy.1, hy.2⟩))

section Periodic

variable {Ab Bb : ℤ → ℤ} {g : ℕ}

/-- The generic height of a `g`-periodic pair grows by `Δ = H̄(g) - 1` over every block of `g`
positions. -/
theorem mixFold_gen_ht_add (hA : ∀ x, Ab (x + g) = Ab x) (hB : ∀ x, Bb (x + g) = Bb x) (n : ℕ) :
    mixFold_ht Ab Bb (n + g) = mixFold_ht Ab Bb n + (mixFold_ht Ab Bb g - 1) := by
  induction n with
  | zero => simp [mixFold_ht_zero]
  | succ n ih =>
    have e : n + 1 + g = (n + g) + 1 := by ring
    rw [e, mixFold_ht_succ, mixFold_ht_succ, ih]
    have h1 := hA ((n : ℤ) + 1)
    have h2 := hB ((n : ℤ) + 1)
    have e2 : ((n + g : ℕ) : ℤ) + 1 = ((n : ℤ) + 1) + g := by push_cast; ring
    rw [e2, h1, h2]
    ring

theorem mixFold_gen_ht_mul (hA : ∀ x, Ab (x + g) = Ab x) (hB : ∀ x, Bb (x + g) = Bb x) (n k : ℕ) :
    mixFold_ht Ab Bb (n + k * g) = mixFold_ht Ab Bb n + k * (mixFold_ht Ab Bb g - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : n + (k + 1) * g = (n + k * g) + g := by ring
    rw [e, mixFold_gen_ht_add hA hB, ih]
    push_cast
    ring

end Periodic

end GluingCore
