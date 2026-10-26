import SkewGluing.SmallOverlap.RotateRoot
import SkewGluing.SmallOverlap.SmallCases

/-!
# The arithmetic of a width-one root and a second root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`): "now `N - 1` is divisible by `g`, the other width is `1 + b g`".

For a diagram `F` with a proper root of period `p` and width one and a proper root of period `Q`,
`g = gcd p Q > 1`: `N = r p + 1 = m Q + u` with `r, m ≥ 2`, `g ∣ u - 1`, hence `1 ≤ u < Q` (the
partner has a nonempty copy).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

theorem _root_.SkewGluing.Chart.IsProperRoot.small_arith {χ₁ χ₂ : Chart} {F : Diagram}
    {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q) (hw₁ : χ₁.ω.width = 1)
    (hg : 1 < Nat.gcd p Q) :
    ∃ r m u : ℕ, 2 ≤ r ∧ 2 ≤ m ∧ 1 ≤ u ∧ u < Q ∧ 2 ≤ p ∧ 2 ≤ Q ∧ span F = r * p + 1 ∧
      span F = m * Q + u ∧ χ₂.ω.width = u ∧ (Nat.gcd p Q : ℤ) ∣ (u : ℤ) - 1 := by
  obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
  obtain ⟨hm, hN2, hwQ, hQ2⟩ := h₂.arith
  have hgp : (Nat.gcd p Q : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hgQ : (Nat.gcd p Q : ℤ) ∣ Q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)
  have hNp : (span F : ℤ) = span χ₁.D * p + 1 := by rw [hN1, hw₁]; push_cast; ring
  have hdvd : (Nat.gcd p Q : ℤ) ∣ (χ₂.ω.width : ℤ) - 1 := by
    have : (χ₂.ω.width : ℤ) - 1 = (span χ₁.D : ℤ) * p - span χ₂.D * Q := by linarith
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left hgp _) (Dvd.dvd.mul_left hgQ _)
  have hu1 : 1 ≤ χ₂.ω.width := by
    by_contra hc
    have h0 : χ₂.ω.width = 0 := by omega
    rw [h0] at hdvd
    have : (Nat.gcd p Q : ℤ) ∣ 1 := by simpa using dvd_neg.2 hdvd
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  refine ⟨span χ₁.D, span χ₂.D, χ₂.ω.width, hr, hm, hu1, by exact_mod_cast hwQ, hp2, hQ2, ?_, ?_,
    rfl, hdvd⟩
  · exact_mod_cast hNp
  · exact_mod_cast hN2

end SmallOverlap
end SkewGluing
