import SkewGluing.PeriodWords
import SkewGluing.Diagram

/-!
# Boundary words: heights along a gcd class

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`lem:gluing-collision`).

Word-level lemmas about two bit words `A, B : ℤ → ℤ` on the positions `1, …, N - 1` and their height
word `H_n = 1 + ∑_{m ≤ n} (A_m - B_m)` (`mixFold_ht`).  If `B` has period `g` and `A` has period `g`
except at one residue `R`, every complete `g`-block raises the height by `D + x`, with one fixed
integer `D` and the bit `x` of `A` at the position of residue `R` in the block
(`mixFold_window_increment`); the monotonicity this gives, with positivity and the end values of the
heights, is the engine of `lem:gluing-collision` (`mixFold_collision_core`).

Sorry-free.
-/

namespace SkewGluing

/-- The height word `H_n = 1 + ∑_{m ≤ n} (A_m - B_m)` of a pair of bit words on the positions
`1, 2, …`.  It is `heightWord` of the words read on the natural numbers. -/
def mixFold_ht (A B : ℤ → ℤ) (n : ℕ) : ℤ :=
  heightWord (fun k : ℕ => A k) (fun k : ℕ => B k) n

theorem mixFold_ht_zero (A B : ℤ → ℤ) : mixFold_ht A B 0 = 1 := by
  simp [mixFold_ht, heightWord]

theorem mixFold_ht_succ (A B : ℤ → ℤ) (n : ℕ) :
    mixFold_ht A B (n + 1) = mixFold_ht A B n + (A (n + 1) - B (n + 1)) := by
  unfold mixFold_ht
  rw [heightWord_succ]
  push_cast
  rfl

/-- The increment of the height over one block of `g` positions starting after `n`. -/
def mixFold_inc (A B : ℤ → ℤ) (g n : ℕ) : ℤ := mixFold_ht A B (n + g) - mixFold_ht A B n

theorem mixFold_inc_succ (A B : ℤ → ℤ) (g n : ℕ) :
    mixFold_inc A B g (n + 1) - mixFold_inc A B g n =
      (A ((n + g : ℕ) + 1) - B ((n + g : ℕ) + 1)) - (A (n + 1) - B (n + 1)) := by
  unfold mixFold_inc
  have e : n + 1 + g = (n + g) + 1 := by ring
  rw [e, mixFold_ht_succ, mixFold_ht_succ]
  push_cast
  ring

theorem mixFold_ht_add_nat (A B : ℤ → ℤ) (n : ℕ) (j : ℕ) :
    mixFold_ht A B (n + j) = mixFold_ht A B n + ∑ m ∈ Finset.range j,
      (A ((n + m : ℕ) + 1) - B ((n + m : ℕ) + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, mixFold_ht_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- A block increment: with `B` of full period `g` and `A` of period `g` except at the residue
`R ∈ [0, g)`, there is an integer `D` such that every block of `g` consecutive positions raises the
height by `D + A(y)`, where `y` is the unique position of the block with residue `R`. -/
theorem mixFold_window_increment {A B : ℤ → ℤ} {g L : ℕ} {R : ℤ} (hg : 0 < g)
    (hR : 0 ≤ R ∧ R < g) (hB : PeriodWords.PeriodExcept L g ∅ B)
    (hA : PeriodWords.PeriodExcept L g {R} A) :
    ∃ D : ℤ, ∀ n : ℕ, n + g ≤ L → ∃ y : ℤ, (n : ℤ) + 1 ≤ y ∧ y ≤ (n : ℤ) + g ∧
      y % (g : ℤ) = R ∧ mixFold_inc A B g n = D + A y := by
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  -- the position of residue `R` in the first block
  obtain ⟨y0, hy01, hy02, hy0⟩ : ∃ y : ℤ, 1 ≤ y ∧ y ≤ g ∧ y % (g : ℤ) = R := by
    by_cases h0 : R = 0
    · exact ⟨g, by omega, le_refl _, by simp [h0]⟩
    · refine ⟨R, by omega, by omega, Int.emod_eq_of_lt hR.1 hR.2⟩
  refine ⟨mixFold_inc A B g 0 - A y0, ?_⟩
  have key : ∀ n : ℕ, n + g ≤ L → ∃ y : ℤ, (n : ℤ) + 1 ≤ y ∧ y ≤ (n : ℤ) + g ∧
      y % (g : ℤ) = R ∧ mixFold_inc A B g n = mixFold_inc A B g 0 - A y0 + A y := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨y0, by push_cast; omega, by push_cast; omega, hy0, by ring⟩
    | succ n ih =>
      intro hn
      obtain ⟨y, hy1, hy2, hy3, hy4⟩ := ih (by omega)
      have hstep := mixFold_inc_succ A B g n
      by_cases hyn : y = (n : ℤ) + 1
      · -- the exceptional position leaves the block
        have hmod : ((n : ℤ) + 1) % (g : ℤ) = R := by rw [← hyn]; exact hy3
        refine ⟨(n : ℤ) + 1 + g, by push_cast; omega, by push_cast; omega, ?_, ?_⟩
        · rw [Int.add_emod_right]; exact hmod
        · have hB1 : B ((n : ℤ) + 1 + g) = B ((n : ℤ) + 1) := by
            have := hB ((n : ℤ) + 1) (by
              simp only [Finset.mem_Icc]; omega) (by simp)
            exact this.symm
          have e1 : ((n + g : ℕ) : ℤ) + 1 = (n : ℤ) + 1 + g := by push_cast; ring
          have e2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
          rw [e1] at hstep
          rw [hyn] at hy4
          rw [e2] at *
          linarith
      · have hmod : ((n : ℤ) + 1) % (g : ℤ) ≠ R := by
          intro hm
          have h1 : (g : ℤ) ∣ y - ((n : ℤ) + 1) := PeriodWords.dvd_sub_of_emod_eq (by rw [hy3, hm])
          have h2 := Int.eq_zero_of_abs_lt_dvd h1 (by rw [abs_lt]; constructor <;> omega)
          omega
        refine ⟨y, by omega, by push_cast; omega, hy3, ?_⟩
        have hA1 : A ((n : ℤ) + 1) = A ((n : ℤ) + 1 + g) := by
          have := hA ((n : ℤ) + 1) (by
            simp only [Finset.mem_Icc]; omega) (by simpa using hmod)
          exact this
        have hB1 : B ((n : ℤ) + 1 + g) = B ((n : ℤ) + 1) := by
          have := hB ((n : ℤ) + 1) (by
            simp only [Finset.mem_Icc]; omega) (by simp)
          exact this.symm
        have e1 : ((n + g : ℕ) : ℤ) + 1 = (n : ℤ) + 1 + g := by push_cast; ring
        rw [e1] at hstep
        linarith
  exact key

/-- The positive, nonnegative-drift branch of the block increments: along the positions
`n₀, n₀ + g, …, n₀ + M g`, the heights are nondecreasing when every increment is `≥ 0`. -/
theorem mixFold_ht_monotone_of_inc {A B : ℤ → ℤ} {g n₀ M : ℕ}
    (h : ∀ k : ℕ, k < M → 0 ≤ mixFold_inc A B g (n₀ + k * g)) :
    ∀ j k : ℕ, k + j ≤ M → mixFold_ht A B (n₀ + k * g) ≤ mixFold_ht A B (n₀ + (k + j) * g) := by
  intro j
  induction j with
  | zero => intro k _; simp
  | succ j ih =>
    intro k hk
    have h1 := ih k (by omega)
    have h2 := h (k + j) (by omega)
    unfold mixFold_inc at h2
    have e : n₀ + (k + j) * g + g = n₀ + (k + (j + 1)) * g := by ring
    rw [e] at h2
    linarith

theorem mixFold_ht_antitone_of_inc {A B : ℤ → ℤ} {g n₀ M : ℕ}
    (h : ∀ k : ℕ, k < M → mixFold_inc A B g (n₀ + k * g) ≤ 0) :
    ∀ j k : ℕ, k + j ≤ M → mixFold_ht A B (n₀ + (k + j) * g) ≤ mixFold_ht A B (n₀ + k * g) := by
  intro j
  induction j with
  | zero => intro k _; simp
  | succ j ih =>
    intro k hk
    have h1 := ih k (by omega)
    have h2 := h (k + j) (by omega)
    unfold mixFold_inc at h2
    have e : n₀ + (k + j) * g + g = n₀ + (k + (j + 1)) * g := by ring
    rw [e] at h2
    linarith

/-- **The core of `lem:gluing-collision`.**  Let the words `A, B` on `1, …, N - 1`, `N = M g + w_g`
with `0 < w_g`, be bit words whose heights are positive and end at one, with `B` of full period
`g` and `A` of period `g` except at one residue `R ∈ [0, g)`.  Then either the bit `A` is zero at
every position of residue `R` in `[w_g, N - 1]` (nonnegative drift), or it is one at every position
of residue `R` in `[1, M g]` (negative drift). -/
theorem mixFold_collision_core {A B : ℤ → ℤ} {g M wg : ℕ} {R : ℤ} (hg : 0 < g) (hwg0 : 0 < wg)
    (hR : 0 ≤ R ∧ R < g)
    (hbit : ∀ k : ℤ, 1 ≤ k → k ≤ ((M * g + wg : ℕ) : ℤ) - 1 → A k = 0 ∨ A k = 1)
    (hpos : ∀ n : ℕ, n < M * g + wg → 0 < mixFold_ht A B n)
    (hlast : mixFold_ht A B (M * g + wg - 1) = 1)
    (hB : PeriodWords.PeriodExcept (M * g + wg - 1) g ∅ B)
    (hA : PeriodWords.PeriodExcept (M * g + wg - 1) g {R} A) :
    (∀ y : ℤ, (wg : ℤ) ≤ y → y ≤ ((M * g + wg : ℕ) : ℤ) - 1 → y % (g : ℤ) = R → A y = 0) ∨
    (∀ y : ℤ, 1 ≤ y → y ≤ ((M * g : ℕ) : ℤ) → y % (g : ℤ) = R → A y = 1) := by
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  obtain ⟨D, hD⟩ := mixFold_window_increment (L := M * g + wg - 1) hg hR hB hA
  by_cases hD0 : 0 ≤ D
  · left
    -- residue `wg - 1`
    have hinc : ∀ k : ℕ, k < M → 0 ≤ mixFold_inc A B g ((wg - 1) + k * g) := by
      intro k hk
      obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hD ((wg - 1) + k * g) (by
        have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
        have : (k + 1) * g = k * g + g := by ring
        omega)
      have hb : A y = 0 ∨ A y = 1 := hbit y (by push_cast at hy1; omega) (by
        push_cast at hy2 ⊢
        have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
        have h3 : ((k + 1 : ℕ) * g : ℕ) = k * g + g := by ring
        have : ((k + 1) * g : ℕ) ≤ M * g := this
        omega)
      omega
    have hmono := mixFold_ht_monotone_of_inc hinc
    have hend : mixFold_ht A B ((wg - 1) + M * g) = 1 := by
      have : (wg - 1) + M * g = M * g + wg - 1 := by omega
      rw [this]; exact hlast
    have hone : ∀ k : ℕ, k ≤ M → mixFold_ht A B ((wg - 1) + k * g) = 1 := by
      intro k hk
      have h1 := hmono (M - k) k (by omega)
      have e : k + (M - k) = M := by omega
      rw [e, hend] at h1
      have h2 := hpos ((wg - 1) + k * g) (by
        have := Nat.mul_le_mul_right g hk
        omega)
      omega
    intro y hy1 hy2 hy3
    -- the block containing `y`
    set k : ℕ := ((y - wg) / g).toNat with hk
    have hyk : 0 ≤ (y - wg) / (g : ℤ) := Int.ediv_nonneg (by omega) hg'.le
    have hkz : (k : ℤ) = (y - wg) / g := by rw [hk]; exact Int.toNat_of_nonneg hyk
    have hq1 := Int.mul_ediv_add_emod (y - wg) g
    have hq2 := Int.emod_nonneg (y - wg) hg'.ne'
    have hq3 := Int.emod_lt_of_pos (y - wg) hg'
    have hkM : k < M := by
      by_contra hcon
      have : (M : ℤ) ≤ k := by exact_mod_cast (by omega : M ≤ k)
      have h5 : (g : ℤ) * M ≤ g * k := by nlinarith
      push_cast at hy2
      nlinarith
    obtain ⟨y', hy'1, hy'2, hy'3, hy'4⟩ := hD ((wg - 1) + k * g) (by
      have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
      have : (k + 1) * g = k * g + g := by ring
      omega)
    have hyy : y = y' := by
      have h1 : (g : ℤ) ∣ y - y' := PeriodWords.dvd_sub_of_emod_eq (by rw [hy3, hy'3])
      have hn0 : ((wg - 1 : ℕ) : ℤ) = (wg : ℤ) - 1 := by omega
      have h2 := Int.eq_zero_of_abs_lt_dvd h1 (by
        rw [abs_lt]
        push_cast at hy'1 hy'2
        rw [hn0] at hy'1 hy'2
        constructor <;> nlinarith)
      omega
    subst hyy
    have h0 := hone k (by omega)
    have h1 := hone (k + 1) (by omega)
    have e : (wg - 1) + (k + 1) * g = (wg - 1) + k * g + g := by ring
    rw [e] at h1
    have : mixFold_inc A B g ((wg - 1) + k * g) = 0 := by
      unfold mixFold_inc; rw [h0, h1]; ring
    have hb := hbit y (by omega) (by omega)
    omega
  · right
    push Not at hD0
    have hinc : ∀ k : ℕ, k < M → mixFold_inc A B g (0 + k * g) ≤ 0 := by
      intro k hk
      obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hD (0 + k * g) (by
        have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
        have : (k + 1) * g = k * g + g := by ring
        omega)
      have hb : A y = 0 ∨ A y = 1 := hbit y (by push_cast at hy1; omega) (by
        push_cast at hy2 ⊢
        have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
        have h3 : ((k + 1 : ℕ) * g : ℕ) = k * g + g := by ring
        have : ((k + 1) * g : ℕ) ≤ M * g := this
        omega)
      omega
    have hanti := mixFold_ht_antitone_of_inc hinc
    have hone : ∀ k : ℕ, k ≤ M → mixFold_ht A B (0 + k * g) = 1 := by
      intro k hk
      have h1 := hanti k 0 (by omega)
      have h0 : mixFold_ht A B (0 + 0 * g) = 1 := by simp [mixFold_ht_zero]
      rw [zero_add] at h1
      simp only [zero_add, zero_mul] at h1 h0
      have h2 := hpos (k * g) (by
        have := Nat.mul_le_mul_right g hk
        omega)
      simp only [zero_add]
      omega
    intro y hy1 hy2 hy3
    set k : ℕ := ((y - 1) / g).toNat with hk
    have hyk : 0 ≤ (y - 1) / (g : ℤ) := Int.ediv_nonneg (by omega) hg'.le
    have hkz : (k : ℤ) = (y - 1) / g := by rw [hk]; exact Int.toNat_of_nonneg hyk
    have hq1 := Int.mul_ediv_add_emod (y - 1) g
    have hq2 := Int.emod_nonneg (y - 1) hg'.ne'
    have hq3 := Int.emod_lt_of_pos (y - 1) hg'
    have hkM : k < M := by
      by_contra hcon
      have : (M : ℤ) ≤ k := by exact_mod_cast (by omega : M ≤ k)
      have h5 : (g : ℤ) * M ≤ g * k := by nlinarith
      push_cast at hy2
      nlinarith
    obtain ⟨y', hy'1, hy'2, hy'3, hy'4⟩ := hD (0 + k * g) (by
      have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
      have : (k + 1) * g = k * g + g := by ring
      omega)
    have hyy : y = y' := by
      have h1 : (g : ℤ) ∣ y - y' := PeriodWords.dvd_sub_of_emod_eq (by rw [hy3, hy'3])
      have h2 := Int.eq_zero_of_abs_lt_dvd h1 (by
        rw [abs_lt]
        push_cast at hy'1 hy'2
        constructor <;> nlinarith)
      omega
    subst hyy
    have h0 := hone k (by omega)
    have h1 := hone (k + 1) (by omega)
    have e : 0 + (k + 1) * g = 0 + k * g + g := by ring
    rw [e] at h1
    have : mixFold_inc A B g (0 + k * g) = 0 := by
      unfold mixFold_inc; rw [h0, h1]; ring
    have hb := hbit y (by omega) (by
      push_cast at hy2 ⊢
      have := Nat.mul_le_mul_right g (show k + 1 ≤ M by omega)
      omega)
    omega

end SkewGluing
