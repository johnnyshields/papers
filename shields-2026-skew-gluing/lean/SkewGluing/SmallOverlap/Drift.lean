import SkewGluing.SmallOverlap.InnerOuter

/-!
# The private drift of a block

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the step "the private interval has common drift zero".

For bit words with a private block of `g - 2` steps that repeats from block to block, the height
change of the block is zero as soon as the first occurrence begins at height one and the last
occurrence ends at height one (`drift_zero`).

Sorry-free.
-/

namespace SkewGluing
namespace SmallOverlap

theorem sum_block_eq {A B : ℕ → ℤ} {g j : ℕ} (hg : 2 ≤ g)
    (hp : ∀ z, 2 ≤ z → z < g → A (j * g + z) = A z ∧ B (j * g + z) = B z) :
    ∑ m ∈ Finset.range (g - 2), (A (j * g + 1 + m + 1) - B (j * g + 1 + m + 1)) =
      ∑ m ∈ Finset.range (g - 2), (A (1 + m + 1) - B (1 + m + 1)) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have e1 : j * g + 1 + m + 1 = j * g + (m + 2) := by ring
  have e2 : 1 + m + 1 = m + 2 := by ring
  rw [e1, e2, (hp (m + 2) (by omega) (by omega)).1, (hp (m + 2) (by omega) (by omega)).2]

/-- **The private drift is zero.**  If the private steps of a block repeat, the first block begins
at height one and the block ending at the position `p - 1` ends at height one, with heights
positive, the height at `g - 1` is one. -/
theorem drift_zero {A B : ℕ → ℤ} {g p : ℕ} (hg : 2 ≤ g) (hgp : g ∣ p) (hlt : g < p)
    (hpriv : ∀ j z, (j + 1) * g ≤ p → 2 ≤ z → z < g →
      A (j * g + z) = A z ∧ B (j * g + z) = B z)
    (hpos : ∀ k, k ≤ p - 1 → 0 < heightWord A B k) (h1 : heightWord A B 1 = 1)
    (hp : heightWord A B (p - 1) = 1) : heightWord A B (g - 1) = 1 := by
  obtain ⟨n, hn⟩ := hgp
  obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; omega
    · omega⟩
  subst hj
  have hpj : p = (j + 1) * g := by rw [hn]; ring
  have hjg : 1 ≤ j := by
    by_contra hc
    have : j = 0 := by omega
    subst this
    omega
  have e0 := heightWord_add A B 1 (g - 2)
  have e1 := heightWord_add A B (j * g + 1) (g - 2)
  have hsum := sum_block_eq (A := A) (B := B) (g := g) (j := j) hg
    (fun z h1 h2 => hpriv j z (by omega) h1 h2)
  have ea : 1 + (g - 2) = g - 1 := by omega
  have eb : j * g + 1 + (g - 2) = p - 1 := by
    rw [hpj]
    have : (j + 1) * g = j * g + g := by ring
    omega
  rw [ea] at e0
  rw [eb] at e1
  have hp1 := hpos (g - 1) (by omega)
  have hp2 := hpos (j * g + 1) (by
    have : (j + 1) * g = j * g + g := by ring
    omega)
  rw [hsum] at e1
  omega

end SmallOverlap
end SkewGluing
