import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import SkewGluing.Tactics

/-!
# Residue lengths after restricting to a gcd class

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-periods`, the paragraph on residue lengths after the lemma).

Let `g = gcd p Q`, `Q = c g`, `u = d g + w_g`, and `N = M g + w_g` with `0 ≤ w_g < g`.  The
statements formalized here are the arithmetic ones: `M ≥ 2c + d` (`residue_length_bound`); the
length of the residue word of each gcd class (`residueClass_card`); the bound on the reindexed
overlap phases (`residue_phase_index_le`); and the resulting comparison with the length required by
`lem:gluing-periods` (iii) for the reduced periods, including the normalization modulo `c` when
`d = c - 1` (`residue_two_hole_length`).  The graph statements of `lem:gluing-periods` are proved
directly on each gcd class, so the reduction of the words themselves to words of the reduced periods
is not carried out here.

Sorry-free.
-/

namespace SkewGluing
namespace PeriodWords

/-- With `Q = c g`, `u = d g + w_g`, `N = M g + w_g`, `w_g < g` and `N = m Q + u`, `m ≥ 2`, the
reduced length satisfies `M ≥ 2c + d`; in fact `M = m c + d`. -/
theorem residue_length_bound {g c d wg m Q u N M : ℕ} (hg : 0 < g) (hQ : Q = c * g)
    (hu : u = d * g + wg) (hN : N = M * g + wg) (hNQ : N = m * Q + u) (hm : 2 ≤ m) :
    M = m * c + d ∧ 2 * c + d ≤ M := by
  have h1 : M * g = (m * c + d) * g := by
    rw [hQ, hu] at hNQ
    nlinarith
  have h2 : M = m * c + d := Nat.eq_of_mul_eq_mul_right hg h1
  refine ⟨h2, ?_⟩
  have := Nat.mul_le_mul_right c hm
  omega

/-- The residue word of the class `j` modulo `g`, on the positions `1, …, n` with `n + 1 = N`,
has `M` positions or `M + 1` positions, except that the zero class has `M - 1` positions when
`w_g = 0`; here `M = N / g` and `w_g = N % g`. -/
theorem residueClass_card {g n : ℕ} (hg : 0 < g) {j : ℕ} (hj : j < g) :
    ((Finset.Icc 1 n).filter fun x => x % g = j).card =
      (n + 1) / g + (if j < (n + 1) % g then 1 else 0) - (if j = 0 then 1 else 0) := by
  have hcount := Nat.count_modEq_card (r := g) hg (b := n + 1) j
  rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hj] at hcount
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hfil : (Finset.range (n + 1)).filter (fun x => x ≡ j [MOD g]) =
      (if j = 0 then {0} else ∅) ∪ (Finset.Icc 1 n).filter (fun x => x % g = j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Icc,
      Nat.ModEq, Nat.mod_eq_of_lt hj]
    split_ifs with h0
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = 0
        · exact Or.inl hx
        · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
      · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨by omega, by simp [h0]⟩
        · exact ⟨by omega, h3⟩
    · simp only [Finset.notMem_empty, false_or]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, by omega⟩, h2⟩
        rcases Nat.eq_zero_or_pos x with rfl | hx
        · simp at h2; omega
        · exact hx
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨by omega, h3⟩
  rw [hfil] at hcount
  have hdisj : Disjoint (if j = 0 then ({0} : Finset ℕ) else ∅)
      ((Finset.Icc 1 n).filter fun x => x % g = j) := by
    split_ifs
    · rw [Finset.disjoint_singleton_left]
      simp
    · simp
  rw [Finset.card_union_of_disjoint hdisj] at hcount
  by_cases h0 : j = 0
  · simp only [h0, ite_true, Finset.card_singleton] at hcount ⊢
    omega
  · simp only [h0, ite_false, Finset.card_empty] at hcount ⊢
    omega

/-- The index in its residue word of a position `h` with `0 ≤ h ≤ u = d g + w_g`: the word of a
class starts at the position of that class in `1, …, g`, so the index of `h` is `(h - 1) / g + 1`.
It is at most `d` when `w_g = 0` and at most `d + 1` otherwise. -/
theorem residue_phase_index_le {g d wg : ℕ} (hg : 0 < g) (hwg : wg < g) {h : ℤ}
    (hh : 0 ≤ h ∧ h ≤ (d * g + wg : ℕ)) :
    (h - 1) / (g : ℤ) + 1 ≤ d + (if wg = 0 then 0 else 1) := by
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  have hq : (h - 1) / (g : ℤ) * g ≤ h - 1 := Int.ediv_mul_le _ hg'.ne'
  obtain ⟨hh0, hh1⟩ := hh
  push_cast at hh1
  by_cases hw0 : wg = 0
  · subst hw0
    simp only [ite_true, Nat.cast_zero] at hh1 ⊢
    by_contra hcon
    have : (d : ℤ) ≤ (h - 1) / g := by omega
    nlinarith [mul_le_mul_of_nonneg_right this hg'.le]
  · simp only [hw0, ite_false]
    by_contra hcon
    have h1 : (d : ℤ) + 1 ≤ (h - 1) / g := by omega
    have hwg' : (wg : ℤ) < g := by exact_mod_cast hwg
    nlinarith

/-- **Length for the reduced two-hole bound.**  On a residue word of length at least
`M ≥ 2c + d`, a reindexed overlap phase `u' ≤ d + 1` of a reduced period `c` with `d + 1 ≤ c` can be
normalized modulo `c` to a phase `u'' < c` for which the length bound `2c + u'' - 1` of
`lem:gluing-periods` (iii) holds.  When `d + 1 < c` no normalization is needed
(`u'' = u'`); when `d = c - 1` it is `u' = c ↦ 0`, and `M ≥ 3c - 1`. -/
theorem residue_two_hole_length {c d M u' : ℕ} (hc : 0 < c) (hM : 2 * c + d ≤ M)
    (hu : u' ≤ d + 1) (hd : d + 1 ≤ c) :
    ∃ u'' : ℕ, u'' < c ∧ u'' ≡ u' [MOD c] ∧ 2 * c + u'' ≤ M + 1 := by
  by_cases h : u' < c
  · exact ⟨u', h, Nat.ModEq.refl _, by omega⟩
  · have hu' : u' = c := by omega
    subst hu'
    exact ⟨0, hc, by simp [Nat.ModEq], by omega⟩

/-- Worked instance of `residueClass_card`: `g = 3`, `N = 6`, `w_g = 0`, `M = 2`; the zero class has
`M - 1 = 1` positions among `1, …, 5` and the other classes have `M = 2`. -/
example : ((Finset.Icc 1 5).filter fun x => x % 3 = 0).card = 1 ∧
    ((Finset.Icc 1 5).filter fun x => x % 3 = 1).card = 2 ∧
    ((Finset.Icc 1 5).filter fun x => x % 3 = 2).card = 2 := by decide

/-- Worked instance of `residueClass_card`: `g = 3`, `N = 8`, `w_g = 2`, `M = 2`; only the class
`1`, which lies in `[1, w_g)`, has `M + 1` positions. -/
example : ((Finset.Icc 1 7).filter fun x => x % 3 = 0).card = 2 ∧
    ((Finset.Icc 1 7).filter fun x => x % 3 = 1).card = 3 ∧
    ((Finset.Icc 1 7).filter fun x => x % 3 = 2).card = 2 := by decide

end PeriodWords
end SkewGluing
