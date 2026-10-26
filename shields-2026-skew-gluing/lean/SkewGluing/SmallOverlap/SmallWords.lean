import SkewGluing.SmallOverlap.PartnerCaps

/-!
# The singleton coding at period `g`: the cases on words

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the case analysis for a singleton root of period `p` (positions
`1, …, L`, `L = N - 1 = r p`) against a second root of period `Q` (`N = m Q + u`, `1 ≤ u < Q`,
`g = gcd p Q`, `g ∣ u - 1`).

* `ordinary_ordinary`, `d_ordinary`: an ordinary partner gives the coding at period `g`
  (`lem:gluing-periods` (ii) and the class-restricted (i)).
* `ordinary_c_false`, `ordinary_d_false`, `d_c_false`: a mixed partner of an ordinary singleton, and
  the opposite mixed partner of a case-(d) singleton, are impossible.

Sorry-free.
-/

namespace SkewGluing
namespace SmallOverlap

open PeriodWords

/-- The numerical data of a width-one root of period `p` and a second root of period `Q`. -/
structure Nums (p Q r m u N L : ℕ) : Prop where
  hr : 2 ≤ r
  hm : 2 ≤ m
  hu1 : 1 ≤ u
  huQ : u < Q
  hp2 : 2 ≤ p
  hNp : N = r * p + 1
  hNQ : N = m * Q + u
  hL : L + 1 = N
  hg : 1 < Nat.gcd p Q
  hpQ : ¬ p ∣ Q
  hQp : ¬ Q ∣ p
  hgu : (Nat.gcd p Q : ℤ) ∣ (u : ℤ) - 1

namespace Nums

variable {p Q r m u N L : ℕ}

theorem len_p (h : Nums p Q r m u N L) : 2 * p ≤ L := by
  have := Nat.mul_le_mul_right p h.hr
  have := h.hNp; have := h.hL; omega

theorem len_Q (h : Nums p Q r m u N L) : 2 * Q ≤ L := by
  have := Nat.mul_le_mul_right Q h.hm
  have := h.hNQ; have := h.hL; have := h.hu1; omega

theorem len_QL (h : Nums p Q r m u N L) : 2 * Q + u ≤ L + 1 := by
  have := Nat.mul_le_mul_right Q h.hm
  have := h.hNQ; have := h.hL; omega

theorem gdvd_N (h : Nums p Q r m u N L) : (Nat.gcd p Q : ℤ) ∣ (L : ℤ) := by
  have hgp : (Nat.gcd p Q : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have : (L : ℤ) = r * p := by
    have := h.hNp; have := h.hL
    have : L = r * p := by omega
    rw [this]; push_cast; ring
  rw [this]; exact Dvd.dvd.mul_left hgp _

theorem gdvd_p (_h : Nums p Q r m u N L) : (Nat.gcd p Q : ℤ) ∣ (p : ℤ) :=
  Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)

theorem gdvd_Q (_h : Nums p Q r m u N L) : (Nat.gcd p Q : ℤ) ∣ (Q : ℤ) :=
  Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)

theorem gdvd_Nu (h : Nums p Q r m u N L) : (Nat.gcd p Q : ℤ) ∣ (N : ℤ) - u := by
  have : (N : ℤ) - u = m * Q := by have := h.hNQ; push_cast [this]; ring
  rw [this]; exact Dvd.dvd.mul_left h.gdvd_Q _

theorem gdvd_NQ (h : Nums p Q r m u N L) : (Nat.gcd p Q : ℤ) ∣ ((N : ℤ) - Q) - 1 := by
  have h1 : ((N : ℤ) - Q) - 1 = (L : ℤ) - Q := by have := h.hL; push_cast [← this]; ring
  rw [h1]; exact dvd_sub h.gdvd_N h.gdvd_Q


end Nums

/-- Ordinary root against ordinary root (`lem:gluing-periods` (ii)). -/
theorem ordinary_ordinary {A B : ℤ → ℤ} {p Q r m u N L : ℕ} (hn : Nums p Q r m u N L)
    {a₁ b₁ a₂ b₂ : ℤ} (ha₁ : 0 ≤ a₁ ∧ a₁ ≤ 1) (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1)
    (ha₂ : 0 ≤ a₂ ∧ a₂ ≤ u) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ u)
    (pA : PeriodExcept L p {a₁} A) (pB : PeriodExcept L p {b₁} B)
    (qA : PeriodExcept L Q {a₂} A) (qB : PeriodExcept L Q {b₂} B) :
    PeriodExcept L (Nat.gcd p Q) {a₁} A ∧ PeriodExcept L (Nat.gcd p Q) {b₁} B := by
  have hg := hn.hg
  have hp := hn.hp2
  have hQ : 0 < Q := by have := hn.huQ; have := hn.hu1; omega
  refine ⟨periodExcept_gcd_two_holes_word (w := 1) (u := u) (N := N) (r := r) (m := m) (by omega)
    hQ hn.hr hn.hm (by omega) hn.huQ hn.hNp hn.hNQ hn.hpQ hn.hQp ha₁ ha₂ hn.hL
    (by omega) pA qA, periodExcept_gcd_two_holes_word (w := 1) (u := u) (N := N) (r := r)
    (m := m) (by omega) hQ hn.hr hn.hm (by omega) hn.huQ hn.hNp hn.hNQ hn.hpQ hn.hQp hb₁ hb₂
    hn.hL (by omega) pB qB⟩

/-- Case-(d) singleton against an ordinary root. -/
theorem d_ordinary {A B : ℤ → ℤ} {p Q r m u N L : ℕ} (hn : Nums p Q r m u N L) {a₂ b₂ : ℤ}
    (pA : PeriodExcept L p {0, 1} A) (pB : PeriodExcept L p ∅ B)
    (qA : PeriodExcept L Q {a₂} A) (qB : PeriodExcept L Q {b₂} B) :
    PeriodExcept L (Nat.gcd p Q) {0, 1} A ∧ PeriodExcept L (Nat.gcd p Q) ∅ B := by
  have hg := hn.hg
  have hp := hn.hp2
  have hQ : 0 < Q := by have := hn.huQ; have := hn.hu1; omega
  have hlp := hn.len_p
  have hlQ := hn.len_Q
  refine ⟨?_, periodExcept_gcd_full_hole (by omega) hQ hn.hpQ hn.hQp b₂ (by omega) hlp pB qB⟩
  intro x hx hS
  have hxm : x ∈ Finset.Icc (1 : ℤ) L := by
    simp only [Finset.mem_Icc] at hx ⊢; omega
  have hym : x + (Nat.gcd p Q : ℤ) ∈ Finset.Icc (1 : ℤ) L := by
    simp only [Finset.mem_Icc] at hx ⊢; omega
  refine eq_of_class_one_hole (h := a₂) (by omega) hQ hn.hpQ hn.hQp (by omega) pA qA
    hxm hym ⟨1, by ring⟩ ?_ (by simp)
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  intro hc
  apply hS
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hs with rfl | rfl
  · left; rw [Int.emod_eq_of_lt (by omega) (by omega)] at hc; omega
  · right; rw [Int.emod_eq_of_lt (by omega) (by omega)] at hc; omega

theorem contra_full_hole {f : ℤ → ℤ} {p Q r m u N L : ℕ} (hn : Nums p Q r m u N L) {h : ℤ}
    (pf : PeriodExcept L p {h} f) (qf : PeriodExcept L Q ∅ f) {x y : ℤ} (hx : 1 ≤ x)
    (hxL : x ≤ L) (hy : 1 ≤ y) (hyL : y ≤ L) (hd : (Nat.gcd p Q : ℤ) ∣ y - x)
    (hne : f x ≠ f y) : False := by
  have hQ : 0 < Q := by have := hn.huQ; have := hn.hu1; omega
  exact hne (eq_of_full_hole (by have := hn.hp2; omega) hQ hn.hpQ hn.hQp h hn.len_p hn.len_Q qf pf
    hx hxL hy hyL (by rw [Nat.gcd_comm]; exact hd))

end SmallOverlap
end SkewGluing
