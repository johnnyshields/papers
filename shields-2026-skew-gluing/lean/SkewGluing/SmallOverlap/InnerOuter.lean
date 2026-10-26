import SkewGluing.SmallOverlap.HoleFormulas
import SkewGluing.SmallOverlap.SingletonInner
import SkewGluing.SmallOverlap.Blocks

/-!
# The inner and outer bit data of a period-`g` singleton root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the singleton construction.

For a connected skew `F` of span `N = M g + 1`, the inner of the root is read from the first
`g - 1` bits of the words of `F`, with the terminal singleton bit `υ` appended
(`innerBits`); the outer is read from the block starts (`outerBitsA`, `outerBitsB`).  This file
checks the bit-data conditions:

* `innerData`: the inner bits are `SingletonInnerData` when `A_1 = B_1` and the height at
  `g - 1` is one;
* `outerData`: the outer bits are bit data of span `M` when the heights of `F` at the positions
  `j g + 1` are the heights of the outer.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

/-- The words of `F` as sequences. -/
def wA (F : Diagram) : ℕ → ℤ := fun k => wordA F k

/-- The words of `F` as sequences. -/
def wB (F : Diagram) : ℕ → ℤ := fun k => wordB F k

/-- The bits of the inner: the first `g - 1` bits of `F`, then the terminal bit `υ`. -/
def innerBits (_F : Diagram) (g : ℕ) (u : ℤ) (w : ℕ → ℤ) : ℕ → ℤ :=
  fun k => if k = g then u else w k

theorem heightWord_innerBits {F : Diagram} {g : ℕ} {u : ℤ} {k : ℕ} (hk : k < g) :
    heightWord (innerBits F g u (wA F)) (innerBits F g u (wB F)) k =
      heightWord (wA F) (wB F) k := by
  induction k with
  | zero => simp [heightWord]
  | succ k ih =>
    rw [heightWord_succ, heightWord_succ, ih (by omega)]
    simp only [innerBits, show k + 1 ≠ g by omega, ite_false]

theorem SingletonInnerData.of_F {F : Diagram} (hF : IsConnectedSkew F) {g M : ℕ} {u : ℤ}
    (hg : 2 ≤ g) (hN : span F = M * g + 1) (hM : 1 ≤ M) (hu : u = 0 ∨ u = 1)
    (hfirst : wordA F 1 = wordB F 1) (hpen : heightWord (wA F) (wB F) (g - 1) = 1) :
    SingletonInnerData g (innerBits F g u (wA F)) (innerBits F g u (wB F)) := by
  have hbd := isBitData_of_isConnectedSkew hF
  obtain ⟨hpos, hbits, hh, hl⟩ := hbd
  have hMg : g ≤ M * g := Nat.le_mul_of_pos_left g hM
  have hheight : heightWord (innerBits F g u (wA F)) (innerBits F g u (wB F)) g = 1 := by
    have e : g = g - 1 + 1 := by omega
    conv_lhs => rw [e, heightWord_succ]
    rw [heightWord_innerBits (by omega), hpen]
    simp only [innerBits, show g - 1 + 1 = g by omega, ite_true]
    ring
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, hg, ?_, ?_⟩
  · intro k hk1 hk2
    by_cases hkg : k = g
    · subst hkg; simp only [innerBits, ite_true]; exact ⟨hu, hu⟩
    · simp only [innerBits, hkg, ite_false]
      have := hbits k hk1 (by omega)
      exact this
  · intro k hk
    by_cases hkg : k = g
    · subst hkg; rw [hheight]; omega
    · rw [heightWord_innerBits (by omega)]
      exact hh k (by omega)
  · have e : g + 1 - 1 = g := by omega
    rw [e, hheight]
  · simp only [innerBits, show (1 : ℕ) ≠ g by omega, ite_false]
    exact hfirst
  · rw [heightWord_innerBits (by omega)]
    exact hpen

/-! ### The heights at the block starts -/

/-- The sum of the `g - 2` private steps of a block is zero when the height at `g - 1` is the
height at `1`, and the private bits repeat from block to block. -/
theorem private_sum_zero {A B : ℕ → ℤ} {g j : ℕ} (hg : 2 ≤ g)
    (hp : ∀ z, 2 ≤ z → z < g → A (j * g + z) = A z ∧ B (j * g + z) = B z)
    (hzero : heightWord A B (g - 1) = heightWord A B 1) :
    ∑ m ∈ Finset.range (g - 2), (A (j * g + 1 + m + 1) - B (j * g + 1 + m + 1)) = 0 := by
  have h1 := heightWord_add A B 1 (g - 2)
  have e : 1 + (g - 2) = g - 1 := by omega
  rw [e, hzero] at h1
  have h2 : ∑ m ∈ Finset.range (g - 2), (A (1 + m + 1) - B (1 + m + 1)) = 0 := by omega
  rw [← h2]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have e1 : j * g + 1 + m + 1 = j * g + (m + 2) := by ring
  have e2 : 1 + m + 1 = m + 2 := by ring
  rw [e1, e2, (hp (m + 2) (by omega) (by omega)).1, (hp (m + 2) (by omega) (by omega)).2]

theorem heightWord_block_step {A B : ℕ → ℤ} {g j : ℕ} (hg : 2 ≤ g)
    (hp : ∀ z, 2 ≤ z → z < g → A (j * g + z) = A z ∧ B (j * g + z) = B z)
    (hzero : heightWord A B (g - 1) = heightWord A B 1) :
    heightWord A B ((j + 1) * g + 1) = heightWord A B (j * g + 1) +
      ((A ((j + 1) * g) - B ((j + 1) * g)) + (A ((j + 1) * g + 1) - B ((j + 1) * g + 1))) := by
  have hsum := private_sum_zero (j := j) hg hp hzero
  have e : (j + 1) * g + 1 = (j * g + 1) + g := by ring
  conv_lhs => rw [e, heightWord_add]
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 2 := ⟨g - 2, by omega⟩
  have hn' : n + 2 - 2 = n := by omega
  rw [hn'] at hsum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum]
  have e1 : j * (n + 2) + 1 + n + 1 = (j + 1) * (n + 2) := by ring
  have e2 : j * (n + 2) + 1 + (n + 1) + 1 = (j + 1) * (n + 2) + 1 := by ring
  rw [e1, e2]
  ring

/-- **The heights of the outer are the heights of `F` at the block starts.** -/
theorem heightWord_outer_eq {A B fA fB : ℕ → ℤ} {g M : ℕ} (hg : 2 ≤ g)
    (hp : ∀ j z, j + 1 ≤ M → 2 ≤ z → z < g → A (j * g + z) = A z ∧ B (j * g + z) = B z)
    (hzero : heightWord A B (g - 1) = heightWord A B 1) (hfirst : A 1 = B 1)
    (hstep : ∀ j, 1 ≤ j → j + 1 ≤ M →
      fA j - fB j = (A (j * g) - B (j * g)) + (A (j * g + 1) - B (j * g + 1))) :
    ∀ j, j + 1 ≤ M → heightWord fA fB j = heightWord A B (j * g + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [heightWord, Finset.range_zero, Finset.sum_empty, add_zero, zero_mul, zero_add,
      Finset.range_one, Finset.sum_singleton]
    omega
  | succ j ih =>
    intro hj
    rw [heightWord_succ, ih (by omega),
      heightWord_block_step hg (fun z h1 h2 => hp j z (by omega) h1 h2) hzero,
      hstep (j + 1) (by omega) hj]

/-- The height at the start of the last block is the height at the end, when the last two bits
agree. -/
theorem heightWord_last_block {A B : ℕ → ℤ} {g j : ℕ} (hg : 2 ≤ g)
    (hp : ∀ z, 2 ≤ z → z < g → A (j * g + z) = A z ∧ B (j * g + z) = B z)
    (hzero : heightWord A B (g - 1) = heightWord A B 1)
    (hend : A ((j + 1) * g) = B ((j + 1) * g)) :
    heightWord A B ((j + 1) * g) = heightWord A B (j * g + 1) := by
  have hsum := private_sum_zero (j := j) hg hp hzero
  have e : (j + 1) * g = (j * g + 1) + (g - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, g = n + 2 := ⟨g - 2, by omega⟩
    have : n + 2 - 1 = n + 1 := by omega
    rw [this]
    ring
  conv_lhs => rw [e, heightWord_add]
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 2 := ⟨g - 2, by omega⟩
  have hn' : n + 2 - 2 = n := by omega
  have hn'' : n + 2 - 1 = n + 1 := by omega
  rw [hn'] at hsum
  rw [hn'', Finset.sum_range_succ, hsum]
  have e1 : j * (n + 2) + 1 + n + 1 = (j + 1) * (n + 2) := by ring
  rw [e1, hend]
  ring

theorem IsBitData.outer_of_heights {F : Diagram} (hF : IsConnectedSkew F) {g M : ℕ} {fA fB : ℕ → ℤ}
    (hN : span F = M * g + 1) (hM : 2 ≤ M) (hg : 2 ≤ g)
    (hbits : ∀ j, 1 ≤ j → j + 1 ≤ M → (fA j = 0 ∨ fA j = 1) ∧ (fB j = 0 ∨ fB j = 1))
    (hH : ∀ j, j + 1 ≤ M → heightWord fA fB j = heightWord (wA F) (wB F) (j * g + 1))
    (hlast : heightWord (wA F) (wB F) ((M - 1) * g + 1) = 1) : IsBitData M fA fB := by
  obtain ⟨-, -, hh, -⟩ := isBitData_of_isConnectedSkew hF
  refine ⟨by omega, fun k hk1 hk2 => hbits k hk1 (by omega), fun k hk => ?_, ?_⟩
  · rw [hH k (by omega)]
    have : k * g + 1 < span F := by
      rw [hN]
      have : k * g < M * g := Nat.mul_lt_mul_of_pos_right hk (by omega)
      omega
    exact hh (k * g + 1) this
  · rw [hH (M - 1) (by omega)]
    exact hlast

end SmallOverlap
end SkewGluing
