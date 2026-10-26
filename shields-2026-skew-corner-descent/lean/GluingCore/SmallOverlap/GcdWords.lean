/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/GcdWords.lean`. -/
import GluingCore.SmallOverlap.Periodic

/-!
# Words with two periods: the period `g = gcd p Q` off the holes of the singleton chart

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the use of `lem:gluing-periods` on the boundary words of a diagram
with a singleton root of period `p` and a root of period `Q`.

* `periodExcept_gcd_two_holes_word`: one exceptional residue modulo each period (ordinary root
  against ordinary root, `lem:gluing-periods` (ii)): the word has period `gcd p Q` except at the
  exceptional residue of the singleton root.
* `periodJoined_of_class`: the period graph of a word with exceptional residues `S` contains the
  period graph with fewer exceptional residues, on the gcd classes that avoid `S`.
* `periodExcept_gcd_of_class_one_hole`: a full period against one exceptional residue gives
  `gcd`-periodicity on the classes that avoid the exceptional residues of the first period.

Sorry-free.
-/

namespace GluingCore
namespace SmallOverlap

open PeriodWords

/-- **`lem:gluing-periods` (ii), word form, one exceptional residue `h₁ < g` modulo `p`.**  The word
has period `gcd p Q` except at the residue `h₁`. -/
theorem periodExcept_gcd_two_holes_word {α : Type*} {f : ℤ → α} {p Q N r m w u L : ℕ}
    {h₁ h₂ : ℤ} (hp : 0 < p) (hQ : 0 < Q) (hr : 2 ≤ r) (hm : 2 ≤ m) (hw : w < p) (hu : u < Q)
    (hNp : N = r * p + w) (hNQ : N = m * Q + u) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p)
    (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ w) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ u) (hL : L + 1 = N)
    (hh₁g : h₁ < (Nat.gcd p Q : ℤ)) (hfp : PeriodExcept L p {h₁} f)
    (hfQ : PeriodExcept L Q {h₂} f) : PeriodExcept L (Nat.gcd p Q) {h₁} f := by
  intro x hx hS
  have hgp : (Nat.gcd p Q : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hg0 : 0 < Nat.gcd p Q := Nat.gcd_pos_of_pos_left _ hp
  have hxg : x ∈ Finset.Icc (1 : ℤ) (L : ℤ) := by
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hyg : x + (Nat.gcd p Q : ℤ) ∈ Finset.Icc (1 : ℤ) (L : ℤ) := by
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hnh : ∀ y : ℤ, y % (Nat.gcd p Q : ℤ) ≠ h₁ → ¬ IsSimultaneousHole p Q {h₁} {h₂} y := by
    intro y hy hsim
    apply hy
    have h1 : y % (p : ℤ) = h₁ := by simpa using hsim.1
    have : y % (Nat.gcd p Q : ℤ) = (y % (p : ℤ)) % (Nat.gcd p Q : ℤ) :=
      (Int.emod_emod_of_dvd y hgp).symm
    rw [this, h1]
    exact Int.emod_eq_of_lt hh₁.1 hh₁g
  have hx0 : x % (Nat.gcd p Q : ℤ) ≠ h₁ := by simpa using hS
  have hx1 : (x + (Nat.gcd p Q : ℤ)) % (Nat.gcd p Q : ℤ) ≠ h₁ := by simpa using hS
  exact eq_of_periods_two_holes hp hQ hr hm hw hu hNp hNQ hpQ hQp hh₁ hh₂ hL hfp hfQ hxg hyg
    ⟨1, by ring⟩ (hnh x hx0) (hnh _ hx1)

/-- The period graph with the exceptional residues `S₀, T₀` is contained in that with `S ⊇ S₀`,
`T ⊇ T₀`, on the gcd classes that avoid `S \ S₀` and `T \ T₀`. -/
theorem periodJoined_of_class {L p Q : ℕ} {S₀ S T₀ T : Finset ℤ} {x y : ℤ}
    (hxy : PeriodJoined L p S₀ Q T₀ x y)
    (hcl : ∀ s ∈ S, s ∉ S₀ → s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ))
    (hcl' : ∀ s ∈ T, s ∉ T₀ → s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ)) :
    PeriodJoined L p S Q T x y := by
  have hgp : (Nat.gcd p Q : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hgQ : (Nat.gcd p Q : ℤ) ∣ Q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)
  have key : ∀ a b : ℤ, PeriodJoined L p S₀ Q T₀ a b →
      (∀ s ∈ S, s ∉ S₀ → s % (Nat.gcd p Q : ℤ) ≠ a % (Nat.gcd p Q : ℤ)) →
      (∀ s ∈ T, s ∉ T₀ → s % (Nat.gcd p Q : ℤ) ≠ a % (Nat.gcd p Q : ℤ)) →
      PeriodJoined L p S Q T a b := by
    intro a b hab
    induction hab with
    | rel a b h =>
      intro hc hc'
      rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · refine Relation.EqvGen.rel _ _ (Or.inl ⟨h1, ?_, h3⟩)
        intro hmem
        by_cases hm0 : a % (p : ℤ) ∈ S₀
        · exact h2 hm0
        · exact hc _ hmem hm0 (Int.emod_emod_of_dvd a hgp)
      · refine Relation.EqvGen.rel _ _ (Or.inr ⟨h1, ?_, h3⟩)
        intro hmem
        by_cases hm0 : a % (Q : ℤ) ∈ T₀
        · exact h2 hm0
        · exact hc' _ hmem hm0 (Int.emod_emod_of_dvd a hgQ)
    | refl a => intro _ _; exact Relation.EqvGen.refl _
    | symm a b hab ih =>
      intro hc hc'
      have hd := PeriodJoined.gcd_dvd_sub hab
      have e : a % (Nat.gcd p Q : ℤ) = b % (Nat.gcd p Q : ℤ) := emod_eq_of_dvd_sub (by
        have := dvd_neg.2 hd
        simpa using this)
      exact (ih (fun s hs hs0 => by rw [e]; exact hc s hs hs0)
        (fun s hs hs0 => by rw [e]; exact hc' s hs hs0)).symm
    | trans a b c hab hbc ih1 ih2 =>
      intro hc hc'
      have hd := PeriodJoined.gcd_dvd_sub hab
      have e : b % (Nat.gcd p Q : ℤ) = a % (Nat.gcd p Q : ℤ) := emod_eq_of_dvd_sub hd
      exact (ih1 hc hc').trans (ih2 (fun s hs hs0 => by rw [e]; exact hc s hs hs0)
        (fun s hs hs0 => by rw [e]; exact hc' s hs hs0))
  exact key x y hxy hcl hcl'

/-- **Class-restricted `lem:gluing-periods` (i).**  A word with period `p` except at the residues
`S` and period `Q` except at `T`, `g = gcd p Q`, neither period dividing the other, is
constant along a class modulo `g` that avoids the residues `S` and contains at most the one
residue `h ∈ T` of `T`. -/
theorem eq_of_class_one_hole {α : Type*} {f : ℤ → α} {p Q L : ℕ} {S T : Finset ℤ} {h : ℤ}
    (hp : 0 < p) (hQ : 0 < Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hL : 2 * max p Q ≤ L)
    (hfp : PeriodExcept L p S f) (hfQ : PeriodExcept L Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x)
    (hxS : ∀ s ∈ S, s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ))
    (hT : ∀ s ∈ T, s ≠ h → s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ)) : f x = f y := by
  have hj := periods_one_hole hp hQ hpQ hQp h hL hx hy hxy
  have hj' := periodJoined_of_class (S₀ := ∅) (S := S) (T₀ := {h}) (T := T) hj
    (fun s hs _ => hxS s hs) (fun s hs hs0 => by
        simp only [Finset.mem_singleton] at hs0
        exact hT s hs hs0)
  exact hj'.eq_of_periodExcept hfp hfQ

/-- The same with the roles of the periods exchanged: the period `Q` is a full period on the class
of `x`, the period `p` has one exceptional residue on it. -/
theorem eq_of_class_one_hole_swap {α : Type*} {f : ℤ → α} {p Q L : ℕ} {S T : Finset ℤ} {h : ℤ}
    (hp : 0 < p) (hQ : 0 < Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hL : 2 * max p Q ≤ L)
    (hfp : PeriodExcept L p S f) (hfQ : PeriodExcept L Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x)
    (hxT : ∀ s ∈ T, s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ))
    (hS : ∀ s ∈ S, s ≠ h → s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ)) : f x = f y := by
  have hc : Nat.gcd Q p = Nat.gcd p Q := Nat.gcd_comm Q p
  refine eq_of_class_one_hole (p := Q) (Q := p) (S := T) (T := S) (h := h) hQ hp hQp hpQ
    (by rw [max_comm]; exact hL) hfQ hfp hx hy (by rw [hc]; exact hxy) ?_ ?_
  · intro s hs; rw [hc]; exact hxT s hs
  · intro s hs hsh; rw [hc]; exact hS s hs hsh

end SmallOverlap
end GluingCore
