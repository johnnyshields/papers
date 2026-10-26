import SkewGluing.SmallOverlap.Drift

/-!
# The drift of a private class

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the case of two case-(d) roots: "Only one bit varies within a
private block, giving two consecutive possible integer drifts `d, d + 1`.  The first `p / g`
blocks begin and end at height one.  Their drifts sum to zero and cannot have opposite strict
signs, so every drift is zero.  The bit at `R` is constant."

* `blockSum a b g j`: the height change of the private steps of the block `j`.
* `heightWord_blocks`: the heights at the block starts, and the vanishing of the total drift of the
  first `n` blocks when the heights at `1` and at `n g - 1` are one and the joining bits cancel.
* `drift_class_const`: if every private class but `R` repeats and the bits at `R` are `0` or `1`,
  vanishing total drift makes the class `R` constant on the first `n` blocks.

Sorry-free.
-/

namespace SkewGluing
namespace SmallOverlap

/-- The height change of the private steps `j g + 2, …, j g + g - 1` of the block `j`. -/
def blockSum (a b : ℕ → ℤ) (g j : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (g - 2), (a (j * g + 1 + m + 1) - b (j * g + 1 + m + 1))

theorem heightWord_block_step' {a b : ℕ → ℤ} {g j : ℕ} (hg : 2 ≤ g) :
    heightWord a b ((j + 1) * g + 1) = heightWord a b (j * g + 1) + blockSum a b g j +
      ((a ((j + 1) * g) - b ((j + 1) * g)) + (a ((j + 1) * g + 1) - b ((j + 1) * g + 1))) := by
  have e : (j + 1) * g + 1 = (j * g + 1) + g := by ring
  conv_lhs => rw [e, heightWord_add]
  unfold blockSum
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 2 := ⟨g - 2, by omega⟩
  have hn' : n + 2 - 2 = n := by omega
  rw [hn', Finset.sum_range_succ, Finset.sum_range_succ]
  have e1 : j * (n + 2) + 1 + n + 1 = (j + 1) * (n + 2) := by ring
  have e2 : j * (n + 2) + 1 + (n + 1) + 1 = (j + 1) * (n + 2) + 1 := by ring
  rw [e1, e2]
  ring

/-- The heights at the block starts, when the joining bits cancel. -/
theorem heightWord_blocks {a b : ℕ → ℤ} {g n : ℕ} (hg : 2 ≤ g)
    (hjoin : ∀ j, 1 ≤ j → j < n →
      (a (j * g) - b (j * g)) + (a (j * g + 1) - b (j * g + 1)) = 0)
    (h1 : heightWord a b 1 = 1) :
    ∀ j, j < n → heightWord a b (j * g + 1) = 1 + ∑ i ∈ Finset.range j, blockSum a b g i := by
  intro j
  induction j with
  | zero => intro _; simpa using h1
  | succ j ih =>
    intro hj
    rw [heightWord_block_step' hg, ih (by omega), Finset.sum_range_succ, hjoin (j + 1) (by omega)
      (by omega)]
    ring

/-- **The total drift of the first `n` blocks vanishes.** -/
theorem total_drift_zero {a b : ℕ → ℤ} {g n : ℕ} (hg : 2 ≤ g) (hn : 1 ≤ n)
    (hjoin : ∀ j, 1 ≤ j → j < n →
      (a (j * g) - b (j * g)) + (a (j * g + 1) - b (j * g + 1)) = 0)
    (h1 : heightWord a b 1 = 1) (hp : heightWord a b (n * g - 1) = 1) :
    ∑ i ∈ Finset.range n, blockSum a b g i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hb := heightWord_blocks hg hjoin h1 j (by omega)
  have e : (j + 1) * g - 1 = (j * g + 1) + (g - 2) := by
    have : (j + 1) * g = j * g + g := by ring
    omega
  rw [e, heightWord_add] at hp
  have hbs : blockSum a b g j = ∑ m ∈ Finset.range (g - 2),
      (a (j * g + 1 + m + 1) - b (j * g + 1 + m + 1)) := rfl
  rw [← hbs, hb] at hp
  rw [Finset.sum_range_succ]
  omega

/-- **The bit at the exceptional private class is constant.**  **Differs from the paper's route.**
The paper compares the signs of the consecutive drifts `d, d + 1`; here the vanishing total drift
is read as a multiple of the number of blocks.  Let `a (i g + z) = a z` for every
private `z ≠ R` and `b` repeat on the private classes, with `a (i g + R) ∈ {0, 1}`.  If the total
drift of the first `n` blocks vanishes, then `a (i g + R) = a R` for `i < n`. -/
theorem drift_class_const {a b : ℕ → ℤ} {g n R : ℕ} (hg : 2 ≤ g) (hR : 2 ≤ R) (hRg : R < g)
    (hn : 1 ≤ n) (hbits : ∀ i, i < n → a (i * g + R) = 0 ∨ a (i * g + R) = 1)
    (hpa : ∀ i z, i < n → 2 ≤ z → z < g → z ≠ R → a (i * g + z) = a z)
    (hpb : ∀ i z, i < n → 2 ≤ z → z < g → b (i * g + z) = b z)
    (hsum : ∑ i ∈ Finset.range n, blockSum a b g i = 0) :
    ∀ i, i < n → a (i * g + R) = a R := by
  have hbs : ∀ i, i < n → blockSum a b g i = blockSum a b g 0 + (a (i * g + R) - a R) := by
    intro i hi
    unfold blockSum
    have : ∀ m ∈ Finset.range (g - 2), (a (i * g + 1 + m + 1) - b (i * g + 1 + m + 1)) =
        (a (0 * g + 1 + m + 1) - b (0 * g + 1 + m + 1)) +
          (if m + 2 = R then a (i * g + R) - a R else 0) := by
      intro m hm
      rw [Finset.mem_range] at hm
      have e1 : i * g + 1 + m + 1 = i * g + (m + 2) := by ring
      have e2 : 0 * g + 1 + m + 1 = m + 2 := by ring
      rw [e1, e2, hpb i (m + 2) hi (by omega) (by omega)]
      by_cases hm2 : m + 2 = R
      · simp only [hm2, ite_true]
        ring
      · simp only [hm2, ite_false]
        rw [hpa i (m + 2) hi (by omega) (by omega) hm2]
        ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (R - 2)]
    · have : R - 2 + 2 = R := by omega
      simp [this]
    · intro m _ hm
      have : m + 2 ≠ R := by omega
      simp [this]
    · intro hm
      exfalso; apply hm
      rw [Finset.mem_range]; omega
  have htot : (n : ℤ) * blockSum a b g 0 +
      (∑ i ∈ Finset.range n, a (i * g + R) - n * a R) = 0 := by
    have := hsum
    rw [Finset.sum_congr rfl (fun i hi => hbs i (Finset.mem_range.mp hi)),
      Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
    simpa using this
  have hS0 : 0 ≤ ∑ i ∈ Finset.range n, a (i * g + R) :=
    Finset.sum_nonneg (fun i hi => by have := hbits i (Finset.mem_range.mp hi); omega)
  have hSn : ∑ i ∈ Finset.range n, a (i * g + R) ≤ n :=
    calc ∑ i ∈ Finset.range n, a (i * g + R) ≤ ∑ _i ∈ Finset.range n, (1 : ℤ) :=
          Finset.sum_le_sum (fun i hi => by have := hbits i (Finset.mem_range.mp hi); omega)
      _ = n := by simp
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have h0 := hbits 0 (by omega)
  simp only [zero_mul, zero_add] at h0
  -- the sum is `n κ` with `κ = a R - blockSum 0`
  set κ : ℤ := a R - blockSum a b g 0 with hκ
  have hsκ : ∑ i ∈ Finset.range n, a (i * g + R) = n * κ := by
    rw [hκ]; linarith
  have hκ0 : 0 ≤ κ := by
    by_contra h; push Not at h
    nlinarith
  have hκ1 : κ ≤ 1 := by
    by_contra h; push Not at h
    nlinarith
  intro i hi
  have hκc : κ = 0 ∨ κ = 1 := by omega
  rcases hκc with h | h
  · rw [h] at hsκ
    have hz : ∀ j ∈ Finset.range n, a (j * g + R) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => ?_)).1 (by simpa using hsκ)
      have := hbits j (Finset.mem_range.mp hj); omega
    have := hz i (Finset.mem_range.mpr hi)
    have h00 := hz 0 (Finset.mem_range.mpr (by omega))
    simp only [zero_mul, zero_add] at h00
    rw [this, h00]
  · rw [h] at hsκ
    have hz : ∀ j ∈ Finset.range n, a (j * g + R) = 1 := by
      have hle : ∀ j ∈ Finset.range n, a (j * g + R) ≤ 1 := fun j hj => by
        have := hbits j (Finset.mem_range.mp hj); omega
      have := (Finset.sum_eq_sum_iff_of_le hle).1 (by simpa using hsκ.trans (by simp))
      exact this
    have := hz i (Finset.mem_range.mpr hi)
    have h00 := hz 0 (Finset.mem_range.mpr (by omega))
    simp only [zero_mul, zero_add] at h00
    rw [this, h00]

end SmallOverlap
end SkewGluing
