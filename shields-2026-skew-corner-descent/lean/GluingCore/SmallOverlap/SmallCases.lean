/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/SmallCases.lean`. -/
import GluingCore.SmallOverlap.GcdWords
import GluingCore.SmallOverlap.Drift

/-!
# The cases of the singleton coding at period `g`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the case analysis for a singleton root of period `p` and a second
root of period `Q`, on the level of the boundary words.

* `eq_of_full`: a word with the full period `g` is constant along the classes modulo `g`.
* `eq_of_full_hole`: a full period `Q` and a period `p` except at one residue give a full period
  `gcd Q p` (`lem:gluing-periods` (i)).
* `eq_of_full_two_holes_lt`, `eq_of_full_two_holes_gt`: the same against two exceptional residues
  (`lem:gluing-periods` (iii)).

Sorry-free.
-/

namespace GluingCore
namespace SmallOverlap

open PeriodWords

theorem eq_of_full {f : ℤ → ℤ} {L g : ℕ} (hg : 0 < g) (hf : PeriodExcept L g ∅ f) {x y : ℤ}
    (hx : 1 ≤ x) (hxL : x ≤ L) (hy : 1 ≤ y) (hyL : y ≤ L) (hd : (g : ℤ) ∣ y - x) :
    f x = f y := by
  rcases le_total x y with h | h
  · exact periodExcept_eq_of_dvd hf hg hx hyL h hd (by simp)
  · have hd' : (g : ℤ) ∣ x - y := by simpa using dvd_neg.2 hd
    exact (periodExcept_eq_of_dvd hf hg hy hxL h hd' (by simp)).symm

/-- **`lem:gluing-periods` (i).**  A full period `Q` and a period `p` except at one residue, neither
dividing the other, on a word of length `L ≥ 2 max (p, Q)`, make the word constant along the
classes modulo `gcd Q p`. -/
theorem eq_of_full_hole {f : ℤ → ℤ} {p Q L : ℕ} (hp : 0 < p) (hQ : 0 < Q) (hpQ : ¬ p ∣ Q)
    (hQp : ¬ Q ∣ p) (h : ℤ) (hLp : 2 * p ≤ L) (hLQ : 2 * Q ≤ L)
    (hfQ : PeriodExcept L Q ∅ f) (hfp : PeriodExcept L p {h} f) {x y : ℤ} (hx : 1 ≤ x)
    (hxL : x ≤ L) (hy : 1 ≤ y) (hyL : y ≤ L) (hd : ((Nat.gcd Q p : ℕ) : ℤ) ∣ y - x) :
    f x = f y :=
  eq_of_full (Nat.gcd_pos_of_pos_left _ hQ)
    (periodExcept_gcd_full_hole hQ hp hQp hpQ h (by omega) hLQ hfQ hfp) hx hxL hy hyL hd

/-- **`lem:gluing-periods` (iii)**, full smaller period `a` against a period `b` with at most two
exceptional residues in `[0, u]`. -/
theorem eq_of_full_two_holes {f : ℤ → ℤ} {a b u L : ℕ} {T : Finset ℤ} (ha : 0 < a) (hab : a < b)
    (hu : u < b) (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ u) (hc : T.card ≤ 2) (hL : 2 * b + u ≤ L + 1)
    (hfa : PeriodExcept L a ∅ f) (hfb : PeriodExcept L b T f) {x y : ℤ} (hx : 1 ≤ x)
    (hxL : x ≤ L) (hy : 1 ≤ y) (hyL : y ≤ L) (hd : ((Nat.gcd a b : ℕ) : ℤ) ∣ y - x) :
    f x = f y :=
  eq_of_full (Nat.gcd_pos_of_pos_left _ ha)
    (periodExcept_gcd_full_two_holes ha hab hu hT hc hL hfa hfb) hx hxL hy hyL hd

end SmallOverlap
end GluingCore
