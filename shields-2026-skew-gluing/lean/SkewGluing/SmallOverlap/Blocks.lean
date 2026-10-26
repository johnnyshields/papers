import SkewGluing.Diagram

/-!
# Block decomposition of bit words

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the construction of the period-`g` inner and outer from the
boundary words of an empty root.

A pair of bit words `a, b` of span `N` that has period `g` except at the multiples of `g`
(`BlockPeriodic`) is cut into the `N / g` blocks of `g` diagonals.  The internal height change of
a block is the same for every block (`heightWord_block`); for a diagram this change is zero
(`BlockData.internal_zero`), so the first block is the bit data of an inner with singleton ends
(`BlockData.isBitData_inner`) and the heights at the block starts are the heights of an outer
(`BlockData.isBitData_outer`).

Sorry-free.
-/

namespace SkewGluing
namespace SmallOverlap

theorem heightWord_add (a b : ℕ → ℤ) (k n : ℕ) :
    heightWord a b (k + n) =
      heightWord a b k + ∑ m ∈ Finset.range n, (a (k + m + 1) - b (k + m + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, heightWord_succ, ih, Finset.sum_range_succ]
    ring

/-- The words `a, b` of span `N` have period `g` except at the multiples of `g`. -/
def BlockPeriodic (g N : ℕ) (a b : ℕ → ℤ) : Prop :=
  ∀ n, 1 ≤ n → n + g ≤ N - 1 → n % g ≠ 0 → a n = a (n + g) ∧ b n = b (n + g)

theorem BlockPeriodic.eq_of_lt {g N : ℕ} {a b : ℕ → ℤ} (h : BlockPeriodic g N a b) {c j : ℕ}
    (hc1 : 1 ≤ c) (hcg : c < g) (hj : j * g + c ≤ N - 1) :
    a (j * g + c) = a c ∧ b (j * g + c) = b c := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j * g + c ≤ N - 1 := by
      have : j * g + c ≤ (j + 1) * g + c := by nlinarith
      omega
    have e : (j + 1) * g + c = (j * g + c) + g := by ring
    have hmod : (j * g + c) % g ≠ 0 := by
      rw [Nat.mul_comm, Nat.mul_add_mod]
      rw [Nat.mod_eq_of_lt hcg]
      omega
    have := h (j * g + c) (by omega) (by omega) hmod
    rw [e, ← this.1, ← this.2]
    exact ih hj'

/-- The sum of `a - b` over the positions `j g + 1, …, j g + c` of the block `j`, for `c < g`, is
that of the first block. -/
theorem BlockPeriodic.sum_block {g N : ℕ} {a b : ℕ → ℤ} (h : BlockPeriodic g N a b) {j c : ℕ}
    (hcg : c < g) (hj : j * g + c ≤ N - 1) :
    ∑ m ∈ Finset.range c, (a (j * g + m + 1) - b (j * g + m + 1)) =
      ∑ m ∈ Finset.range c, (a (m + 1) - b (m + 1)) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have e : j * g + m + 1 = j * g + (m + 1) := by ring
  have := h.eq_of_lt (c := m + 1) (j := j) (by omega) (by omega) (by omega)
  rw [e, this.1, this.2]

/-- The height at the position `j g + c` of a block is the height at the block start plus the
height gain of the first `c` steps of the first block. -/
theorem BlockPeriodic.heightWord_block {g N : ℕ} {a b : ℕ → ℤ} (h : BlockPeriodic g N a b)
    {j c : ℕ} (hcg : c < g) (hj : j * g + c ≤ N - 1) :
    heightWord a b (j * g + c) = heightWord a b (j * g) + (heightWord a b c - 1) := by
  rw [heightWord_add, h.sum_block hcg hj]
  simp [heightWord]

/-- **The block data of a diagram.**  Bit data of span `N` with period `g` except at the multiples
of `g`, `g ∣ N` and `g < N`: the internal height change of a block vanishes, so the first block
and the sequence of block starts are again bit data. -/
structure BlockData (g N : ℕ) (a b : ℕ → ℤ) : Prop where
  bits : IsBitData N a b
  periodic : BlockPeriodic g N a b
  dvd : g ∣ N
  two_le : 2 ≤ g
  lt : g < N

namespace BlockData

variable {g N : ℕ} {a b : ℕ → ℤ}

/-- The internal height change of a block is zero: nonnegative in the first block, nonpositive in
the last block, and equal in all blocks. -/
theorem internal_zero (h : BlockData g N a b) : heightWord a b (g - 1) = 1 := by
  obtain ⟨M, hM⟩ := h.dvd
  have hg := h.two_le
  have hNg := h.lt
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have : M ≤ 1 := by omega
    have : g * M ≤ g * 1 := Nat.mul_le_mul_left g this
    omega
  have hpos1 := h.bits.2.2.1 (g - 1) (by omega)
  have hlast := h.bits.2.2.2
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  have hKg : K * g + g = N := by rw [hM]; ring
  have hpos2 := h.bits.2.2.1 (K * g) (by omega)
  have hN1 : K * g + (g - 1) = N - 1 := by omega
  have hblk := h.periodic.heightWord_block (j := K) (c := g - 1) (by omega) (by omega)
  rw [hN1, hlast] at hblk
  omega

theorem bits_inner (h : BlockData g N a b) : IsBitData g a b := by
  obtain ⟨hpos, hbits, hh, hl⟩ := h.bits
  refine ⟨by have := h.two_le; omega, fun k hk1 hk2 => hbits k hk1 (by have := h.lt; omega),
    fun k hk => hh k (by have := h.lt; omega), h.internal_zero⟩

/-- The block starts: the outer bit words `a' j = a (j g)`, `b' j = b (j g)`. -/
def outerA (g : ℕ) (a : ℕ → ℤ) : ℕ → ℤ := fun j => a (j * g)

theorem heightWord_outer (h : BlockData g N a b) {j : ℕ} (hj : j * g ≤ N - 1) :
    heightWord (outerA g a) (outerA g b) j = heightWord a b (j * g) := by
  induction j with
  | zero => simp [heightWord]
  | succ j ih =>
    have hj' : j * g ≤ N - 1 := by
      have : j * g ≤ (j + 1) * g := by nlinarith
      omega
    have e : (j + 1) * g = (j * g + (g - 1)) + 1 := by
      have := h.two_le
      ring_nf
      omega
    have hblk := h.periodic.heightWord_block (j := j) (c := g - 1) (by have := h.two_le; omega)
      (by have := h.two_le; nlinarith)
    rw [heightWord_succ, ih hj', e, heightWord_succ, hblk, h.internal_zero]
    simp only [outerA]
    rw [← e]
    ring

theorem isBitData_outer (h : BlockData g N a b) :
    IsBitData (N / g) (outerA g a) (outerA g b) := by
  obtain ⟨M, hM⟩ := h.dvd
  have hg := h.two_le
  have hNM : N / g = M := by rw [hM]; exact Nat.mul_div_cancel_left M (by omega)
  have hM1 : 1 ≤ M := by
    by_contra hcon
    have : M = 0 := by omega
    subst this
    have := h.lt
    omega
  rw [hNM]
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  have hKg : K * g + g = N := by rw [hM]; ring
  have hjg : ∀ j, j < K + 1 → j * g ≤ N - 1 := by
    intro j hj
    have : j * g ≤ K * g := Nat.mul_le_mul_right g (by omega)
    omega
  obtain ⟨hpos, hbits, hh, hl⟩ := h.bits
  refine ⟨by omega, fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
  · have h1 : 1 * g ≤ k * g := Nat.mul_le_mul_right g hk1
    have h2 := hjg k hk2
    exact hbits (k * g) (by omega) (by omega)
  · rw [h.heightWord_outer (hjg k hk)]
    exact hh _ (by have := hjg k hk; omega)
  · simp only [Nat.add_sub_cancel]
    rw [h.heightWord_outer (hjg K (by omega))]
    have hN1 : K * g + (g - 1) = N - 1 := by omega
    have hblk := h.periodic.heightWord_block (j := K) (c := g - 1) (by omega) (by omega)
    rw [hN1, hl, h.internal_zero] at hblk
    omega

end BlockData

end SmallOverlap
end SkewGluing
