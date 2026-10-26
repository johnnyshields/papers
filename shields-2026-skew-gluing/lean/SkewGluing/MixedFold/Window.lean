import SkewGluing.MixedFold.Drift

/-!
# Window sums of deviations

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`), as bookkeeping for the drift argument.

`mixFold_winSum A B Ab Bb n j` is the sum of the deviations over the `j` positions
`n + 1, …, n + j`.  It splits (`mixFold_winSum_add`), it is the sum over the support when the
deviations vanish elsewhere (`mixFold_winSum_pair`, `mixFold_winSum_single`), and a sum of terms of
one sign that vanishes has all its terms zero (`mixFold_winSum_terms_zero`).

Sorry-free.
-/

namespace SkewGluing

/-- The sum of the deviations over the positions `n + 1, …, n + j`. -/
def mixFold_winSum (A B Ab Bb : ℤ → ℤ) (n j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range j, mixFold_dev A B Ab Bb (((n + k : ℕ) : ℤ) + 1)

theorem mixFold_devSum_add' (A B Ab Bb : ℤ → ℤ) (n j : ℕ) :
    mixFold_devSum A B Ab Bb (n + j) =
      mixFold_devSum A B Ab Bb n + mixFold_winSum A B Ab Bb n j :=
  mixFold_devSum_add A B Ab Bb n j

theorem mixFold_winSum_add (A B Ab Bb : ℤ → ℤ) (n j₁ j₂ : ℕ) :
    mixFold_winSum A B Ab Bb n (j₁ + j₂) =
      mixFold_winSum A B Ab Bb n j₁ + mixFold_winSum A B Ab Bb (n + j₁) j₂ := by
  unfold mixFold_winSum
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [add_assoc]

theorem mixFold_winSum_eq_Icc (A B Ab Bb : ℤ → ℤ) (n j : ℕ) :
    mixFold_winSum A B Ab Bb n j =
      ∑ y ∈ Finset.Icc ((n : ℤ) + 1) ((n : ℤ) + j), mixFold_dev A B Ab Bb y := by
  unfold mixFold_winSum
  refine Finset.sum_bij (fun k _ => ((n + k : ℕ) : ℤ) + 1) (fun k hk => ?_) (fun a _ b _ h => ?_)
    (fun y hy => ?_) (fun k _ => rfl)
  · simp only [Finset.mem_range] at hk
    rw [Finset.mem_Icc]; push_cast; omega
  · have h' : ((n + a : ℕ) : ℤ) + 1 = ((n + b : ℕ) : ℤ) + 1 := h
    omega
  · rw [Finset.mem_Icc] at hy
    refine ⟨(y - 1 - n).toNat, ?_, by omega⟩
    simp only [Finset.mem_range]; omega

theorem mixFold_winSum_pair (A B Ab Bb : ℤ → ℤ) (n j : ℕ) (x₁ x₂ : ℤ) (hne : x₁ ≠ x₂)
    (h1 : (n : ℤ) + 1 ≤ x₁) (h1' : x₁ ≤ (n : ℤ) + j) (h2 : (n : ℤ) + 1 ≤ x₂)
    (h2' : x₂ ≤ (n : ℤ) + j)
    (hS : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → y ≠ x₁ → y ≠ x₂ →
      mixFold_dev A B Ab Bb y = 0) :
    mixFold_winSum A B Ab Bb n j = mixFold_dev A B Ab Bb x₁ + mixFold_dev A B Ab Bb x₂ := by
  rw [mixFold_winSum_eq_Icc, ← Finset.sum_pair hne]
  symm
  refine Finset.sum_subset (fun y hy => ?_) (fun y hy hy' => ?_)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_Icc]
    rcases hy with rfl | rfl <;> omega
  · rw [Finset.mem_Icc] at hy
    exact hS y hy.1 hy.2 (fun h => hy' (by simp [h])) (fun h => hy' (by simp [h]))

theorem mixFold_winSum_single (A B Ab Bb : ℤ → ℤ) (n j : ℕ) (x : ℤ) (h1 : (n : ℤ) + 1 ≤ x)
    (h2 : x ≤ (n : ℤ) + j)
    (hS : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → y ≠ x → mixFold_dev A B Ab Bb y = 0) :
    mixFold_winSum A B Ab Bb n j = mixFold_dev A B Ab Bb x := by
  rw [mixFold_winSum_eq_Icc, ← Finset.sum_singleton (fun y => mixFold_dev A B Ab Bb y) x]
  symm
  refine Finset.sum_subset (fun y hy => ?_) (fun y hy hy' => ?_)
  · rw [Finset.mem_singleton] at hy
    rw [Finset.mem_Icc]; omega
  · rw [Finset.mem_Icc] at hy
    exact hS y hy.1 hy.2 (fun h => hy' (by simp [h]))

theorem mixFold_winSum_zero (A B Ab Bb : ℤ → ℤ) (n j : ℕ)
    (hS : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → mixFold_dev A B Ab Bb y = 0) :
    mixFold_winSum A B Ab Bb n j = 0 := by
  rw [mixFold_winSum_eq_Icc]
  exact Finset.sum_eq_zero (fun y hy => by rw [Finset.mem_Icc] at hy; exact hS y hy.1 hy.2)

/-- A vanishing sum of nonnegative terms has all its terms zero. -/
theorem mixFold_winSum_terms_zero (A B Ab Bb : ℤ → ℤ) (n j : ℕ)
    (hnn : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → 0 ≤ mixFold_dev A B Ab Bb y)
    (h0 : mixFold_winSum A B Ab Bb n j = 0) :
    ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → mixFold_dev A B Ab Bb y = 0 := by
  rw [mixFold_winSum_eq_Icc] at h0
  intro y h1 h2
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun z hz => by
    rw [Finset.mem_Icc] at hz; exact hnn z hz.1 hz.2)).mp h0 y
    (by rw [Finset.mem_Icc]; exact ⟨h1, h2⟩)

/-- A vanishing sum of nonpositive terms has all its terms zero. -/
theorem mixFold_winSum_terms_zero' (A B Ab Bb : ℤ → ℤ) (n j : ℕ)
    (hnn : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → mixFold_dev A B Ab Bb y ≤ 0)
    (h0 : mixFold_winSum A B Ab Bb n j = 0) :
    ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → mixFold_dev A B Ab Bb y = 0 := by
  rw [mixFold_winSum_eq_Icc] at h0
  intro y h1 h2
  have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.Icc ((n : ℤ) + 1) ((n : ℤ) + j))
    (f := fun z => - mixFold_dev A B Ab Bb z) (fun z hz => by
      rw [Finset.mem_Icc] at hz; have := hnn z hz.1 hz.2; omega)).mp
    (by rw [Finset.sum_neg_distrib, h0]; ring) y (by rw [Finset.mem_Icc]; exact ⟨h1, h2⟩)
  simpa using this

theorem mixFold_winSum_nonneg (A B Ab Bb : ℤ → ℤ) (n j : ℕ)
    (hnn : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → 0 ≤ mixFold_dev A B Ab Bb y) :
    0 ≤ mixFold_winSum A B Ab Bb n j := by
  rw [mixFold_winSum_eq_Icc]
  exact Finset.sum_nonneg (fun z hz => by rw [Finset.mem_Icc] at hz; exact hnn z hz.1 hz.2)

theorem mixFold_winSum_nonpos (A B Ab Bb : ℤ → ℤ) (n j : ℕ)
    (hnn : ∀ y : ℤ, (n : ℤ) + 1 ≤ y → y ≤ (n : ℤ) + j → mixFold_dev A B Ab Bb y ≤ 0) :
    mixFold_winSum A B Ab Bb n j ≤ 0 := by
  rw [mixFold_winSum_eq_Icc]
  exact Finset.sum_nonpos (fun z hz => by rw [Finset.mem_Icc] at hz; exact hnn z hz.1 hz.2)

end SkewGluing
