/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/PeriodWords.lean
import SkewMarkedFactor.Gluing.PeriodWords.Cases
import SkewMarkedFactor.Gluing.PeriodWords.Residues

/-!
# Period words

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-periods`).

A word on the positions `1, …, L` is a function `ℤ → α`.  `PeriodExcept L p S f` says it has period
`p` except at the residues `S`; `PeriodJoined L p S Q T` is the period graph of two such
constraints, so that two positions are joined exactly when every word satisfying both constraints
takes equal values there (`periodJoined_iff_forall_word`).

* `lem:gluing-periods` (i): `periods_one_hole`, `periods_one_hole_of_lt` (the shorter clause), and
  word-level forms `periodExcept_gcd_one_hole`, `periodExcept_gcd_one_hole_of_lt`.
* `lem:gluing-periods` (ii): `periods_two_holes` (one component on each gcd residue apart from
  simultaneous holes), `PeriodJoined.eq_of_isSimultaneousHole` (each simultaneous hole is isolated),
  `isSimultaneousHole_iff_lcm_dvd` (simultaneous holes form one progression of spacing
  `lcm p Q`), `PeriodJoined.gcd_dvd_sub` (components do not mix gcd residues).
* `lem:gluing-periods` (iii): `periods_full_two_holes`, `periodExcept_gcd_full_two_holes`.
* Sharpness witnesses and worked instances at the end of this file.

The paragraph on residue lengths after the lemma is in `SkewMarkedFactor.Gluing.PeriodWords.Residues`.

The proofs run the paper's cycle argument once, for an arbitrary equivalence relation containing the
edges (`related_of_gcd_dvd`); the three cases only verify its two hypotheses.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing
namespace PeriodWords

/-- A position at which both periods are exceptional: it has no edge of the period graph. -/
def IsSimultaneousHole (p Q : ℕ) (S T : Finset ℤ) (x : ℤ) : Prop :=
  x % (p : ℤ) ∈ S ∧ x % (Q : ℤ) ∈ T

theorem periodJoined_edge_left {L p Q : ℕ} {S T : Finset ℤ} :
    ∀ x y, periodEdge L p S x y → PeriodJoined L p S Q T x y :=
  fun _ _ h => Relation.EqvGen.rel _ _ (Or.inl h)

theorem periodJoined_edge_right {L p Q : ℕ} {S T : Finset ℤ} :
    ∀ x y, periodEdge L Q T x y → PeriodJoined L p S Q T x y :=
  fun _ _ h => Relation.EqvGen.rel _ _ (Or.inr h)

/-- A word with the stated period constraints has period `gcd` as soon as all positions of one gcd
class are joined. -/
theorem periodExcept_gcd_of_joined {α : Type*} {L p Q : ℕ} {S T : Finset ℤ} {f : ℤ → α}
    (hp : PeriodExcept L p S f) (hQ : PeriodExcept L Q T f)
    (hjoin : ∀ x ∈ Finset.Icc (1 : ℤ) L, ∀ y ∈ Finset.Icc (1 : ℤ) L,
      ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x → PeriodJoined L p S Q T x y) :
    PeriodExcept L (Nat.gcd p Q) ∅ f := by
  intro x hx _
  simp only [Finset.mem_Icc] at hx
  refine (hjoin x ?_ (x + (Nat.gcd p Q : ℕ)) ?_ ⟨1, by ring⟩).eq_of_periodExcept hp hQ <;>
    simp only [Finset.mem_Icc] <;> omega

/-! ### (i): a full period against a period with one exceptional residue -/

/-- **`lem:gluing-periods` (i), shorter clause.**  A full period `a` and a period `b > a` except at
one residue `h`, on a word of length at least `2b - 1`, join all positions of each class modulo
`gcd a b`. -/
theorem periods_one_hole_of_lt {a b L : ℕ} (ha : 0 < a) (hab : a < b) (hnd : ¬ a ∣ b) (h : ℤ)
    (hL : 2 * b ≤ L + 1) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L)
    (hy : y ∈ Finset.Icc (1 : ℤ) L) (hxy : ((Nat.gcd a b : ℕ) : ℤ) ∣ y - x) :
    PeriodJoined L a ∅ b {h} x y :=
  related_full_one_hole (periodJoined_equivalence L a ∅ b {h}) ha hab hnd
    (by simp) hL periodJoined_edge_left periodJoined_edge_right hx hy hxy

/-- **`lem:gluing-periods` (i), full period larger.**  A full period `a` and a smaller period
`b` except at one residue `h`, on a word of length at least `2a`, join all positions of each class
modulo `gcd a b`. -/
theorem periods_one_hole_of_gt {a b L : ℕ} (hb : 0 < b) (hba : b < a) (hnd : ¬ b ∣ a) (h : ℤ)
    (hL : 2 * a ≤ L) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L)
    (hy : y ∈ Finset.Icc (1 : ℤ) L) (hxy : ((Nat.gcd a b : ℕ) : ℤ) ∣ y - x) :
    PeriodJoined L a ∅ b {h} x y := by
  rw [periodJoined_comm]
  refine related_hole_one_hole (periodJoined_equivalence L b {h} a ∅) (u := 0) hb hba hnd
    (by simp) (by simp) (by simp) (by omega) (Or.inl hL) periodJoined_edge_left
    periodJoined_edge_right hx hy (by rwa [Nat.gcd_comm]) (by simp) (by simp)

/-- **`lem:gluing-periods` (i).**  If neither of `a, b` divides the other, a full period `a` and a
period `b` except at one residue `h`, on a word of length at least `2 max a b`, join all positions
of each class modulo `gcd a b`. -/
theorem periods_one_hole {a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : ¬ a ∣ b) (hba : ¬ b ∣ a)
    (h : ℤ) (hL : 2 * max a b ≤ L) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L)
    (hy : y ∈ Finset.Icc (1 : ℤ) L) (hxy : ((Nat.gcd a b : ℕ) : ℤ) ∣ y - x) :
    PeriodJoined L a ∅ b {h} x y := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact periods_one_hole_of_lt ha hlt hab h (by have := le_max_right a b; omega) hx hy hxy
  · exact absurd (heq ▸ dvd_refl a) hab
  · exact periods_one_hole_of_gt hb hgt hba h (by have := le_max_left a b; omega) hx hy hxy

/-- **`lem:gluing-periods` (i)**, word form: the word has period `gcd a b`. -/
theorem periodExcept_gcd_one_hole {α : Type*} {a b L : ℕ} {f : ℤ → α} (ha : 0 < a) (hb : 0 < b)
    (hab : ¬ a ∣ b) (hba : ¬ b ∣ a) (h : ℤ) (hL : 2 * max a b ≤ L)
    (hfa : PeriodExcept L a ∅ f) (hfb : PeriodExcept L b {h} f) :
    PeriodExcept L (Nat.gcd a b) ∅ f :=
  periodExcept_gcd_of_joined hfa hfb fun _ hx _ hy hxy =>
    periods_one_hole ha hb hab hba h hL hx hy hxy

/-- **`lem:gluing-periods` (i)**, shorter clause, word form. -/
theorem periodExcept_gcd_one_hole_of_lt {α : Type*} {a b L : ℕ} {f : ℤ → α} (ha : 0 < a)
    (hab : a < b) (hnd : ¬ a ∣ b) (h : ℤ) (hL : 2 * b ≤ L + 1)
    (hfa : PeriodExcept L a ∅ f) (hfb : PeriodExcept L b {h} f) :
    PeriodExcept L (Nat.gcd a b) ∅ f :=
  periodExcept_gcd_of_joined hfa hfb fun _ hx _ hy hxy =>
    periods_one_hole_of_lt ha hab hnd h hL hx hy hxy

/-- With coprime periods, `lem:gluing-periods` (i) makes the whole word constant. -/
theorem periods_one_hole_coprime {a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : ¬ a ∣ b)
    (hba : ¬ b ∣ a) (hcop : Nat.Coprime a b) (h : ℤ) (hL : 2 * max a b ≤ L) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L) :
    PeriodJoined L a ∅ b {h} x y :=
  periods_one_hole ha hb hab hba h hL hx hy (by rw [hcop]; simp)

/-! ### (ii): one exceptional phase in each period -/

theorem periods_two_holes_of_lt {p Q N m u L : ℕ} {h₁ h₂ : ℤ} (hp : 0 < p) (hpQ : p < Q)
    (hnd : ¬ p ∣ Q) (hm : 2 ≤ m) (hNQ : N = m * Q + u) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ u)
    (hL : L + 1 = N) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) (hx' : ¬ IsSimultaneousHole p Q {h₁} {h₂} x)
    (hy' : ¬ IsSimultaneousHole p Q {h₁} {h₂} y) : PeriodJoined L p {h₁} Q {h₂} x y := by
  have hmQ : 2 * Q ≤ m * Q := Nat.mul_le_mul_right Q hm
  refine related_hole_one_hole (periodJoined_equivalence L p {h₁} Q {h₂}) hp hpQ hnd
    (by simp) (by simpa using hh₂) (by simp) (by omega) ?_ periodJoined_edge_left
    periodJoined_edge_right hx hy hxy hx' hy'
  by_cases hu0 : u = 0
  · right
    simp only [Finset.mem_singleton]
    omega
  · left
    omega

/-- **`lem:gluing-periods` (ii).**  Let `N = r p + w = m Q + u` with `r, m ≥ 2`, `w < p`,
`u < Q`, neither period dividing the other, and one exceptional phase `h₁ ∈ [0, w]` modulo `p` and
`h₂ ∈ [0, u]` modulo `Q`, on a word of the positions `1, …, N - 1` (here `L + 1 = N`).  Any two
positions of the same class modulo `gcd p Q` that are not simultaneous holes are joined in the
period graph, so such a word is constant on them.  Combined with
`PeriodJoined.gcd_dvd_sub`, each gcd residue has one component apart from the simultaneous
holes. -/
theorem periods_two_holes {p Q N r m w u L : ℕ} {h₁ h₂ : ℤ} (hp : 0 < p) (hQ : 0 < Q)
    (hr : 2 ≤ r) (hm : 2 ≤ m) (_hw : w < p) (_hu : u < Q) (hNp : N = r * p + w)
    (hNQ : N = m * Q + u) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ w)
    (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ u) (hL : L + 1 = N) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L)
    (hy : y ∈ Finset.Icc (1 : ℤ) L) (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x)
    (hx' : ¬ IsSimultaneousHole p Q {h₁} {h₂} x) (hy' : ¬ IsSimultaneousHole p Q {h₁} {h₂} y) :
    PeriodJoined L p {h₁} Q {h₂} x y := by
  rcases lt_trichotomy p Q with hlt | heq | hgt
  · exact periods_two_holes_of_lt hp hlt hpQ hm hNQ hh₂ hL hx hy hxy hx' hy'
  · exact absurd (heq ▸ dvd_refl p) hpQ
  · rw [periodJoined_comm]
    exact periods_two_holes_of_lt hQ hgt hQp hr hNp hh₁ hL hx hy (by rwa [Nat.gcd_comm])
      (fun h => hx' ⟨h.2, h.1⟩) (fun h => hy' ⟨h.2, h.1⟩)

/-- **`lem:gluing-periods` (ii)**, word form. -/
theorem eq_of_periods_two_holes {α : Type*} {p Q N r m w u L : ℕ} {h₁ h₂ : ℤ} {f : ℤ → α}
    (hp : 0 < p) (hQ : 0 < Q) (hr : 2 ≤ r) (hm : 2 ≤ m) (hw : w < p) (hu : u < Q)
    (hNp : N = r * p + w) (hNQ : N = m * Q + u) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p)
    (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ w) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ u) (hL : L + 1 = N)
    (hfp : PeriodExcept L p {h₁} f) (hfQ : PeriodExcept L Q {h₂} f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) (hx' : ¬ IsSimultaneousHole p Q {h₁} {h₂} x)
    (hy' : ¬ IsSimultaneousHole p Q {h₁} {h₂} y) : f x = f y :=
  (periods_two_holes hp hQ hr hm hw hu hNp hNQ hpQ hQp hh₁ hh₂ hL hx hy hxy hx'
    hy').eq_of_periodExcept hfp hfQ

/-- **`lem:gluing-periods` (ii)**, width zero: the exceptional phase in `[0, w]` is zero. -/
theorem phase_eq_zero_of_width_zero {h : ℤ} (hh : 0 ≤ h ∧ h ≤ ((0 : ℕ) : ℤ)) : h = 0 := by
  simp only [Nat.cast_zero] at hh
  omega

/-- **`lem:gluing-periods` (ii)**, simultaneous holes are isolated: a position at which both periods
are exceptional has no edge, so it is joined only to itself. -/
theorem PeriodJoined.eq_of_isSimultaneousHole {L p Q : ℕ} {S T : Finset ℤ} {x y : ℤ}
    (hx : IsSimultaneousHole p Q S T x) (h : PeriodJoined L p S Q T x y) : y = x := by
  have noedge : ∀ z : ℤ, IsSimultaneousHole p Q S T z → ∀ w : ℤ,
      ¬ (periodEdge L p S z w ∨ periodEdge L Q T z w) ∧
      ¬ (periodEdge L p S w z ∨ periodEdge L Q T w z) := by
    intro z hz w
    refine ⟨?_, ?_⟩
    · rintro (⟨_, h1, _⟩ | ⟨_, h1, _⟩)
      · exact h1 hz.1
      · exact h1 hz.2
    · rintro (⟨_, h1, rfl⟩ | ⟨_, h1, rfl⟩)
      · apply h1
        have := hz.1
        rwa [Int.add_emod_right] at this
      · apply h1
        have := hz.2
        rwa [Int.add_emod_right] at this
  have key : ∀ a b : ℤ, Relation.EqvGen
      (fun x y => periodEdge L p S x y ∨ periodEdge L Q T x y) a b →
      (IsSimultaneousHole p Q S T a → a = b) ∧ (IsSimultaneousHole p Q S T b → a = b) := by
    intro a b hab
    induction hab with
    | rel a b hr =>
      exact ⟨fun ha => absurd hr (noedge a ha b).1, fun hb => absurd hr (noedge b hb a).2⟩
    | refl a => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | symm a b _ ih => exact ⟨fun hb => (ih.2 hb).symm, fun ha => (ih.1 ha).symm⟩
    | trans a b c _ _ ih1 ih2 =>
      refine ⟨fun ha => ?_, fun hc => ?_⟩
      · have hab := ih1.1 ha
        subst hab
        exact ih2.1 ha
      · have hbc := ih2.2 hc
        subst hbc
        exact ih1.2 hc
  exact ((key x y h).1 hx).symm

/-- **`lem:gluing-periods` (ii)**, simultaneous holes form one progression: with one exceptional
phase `h₁` modulo `p` and `h₂` modulo `Q`, the simultaneous holes are exactly the positions in one
class modulo `lcm p Q`, once one exists. -/
theorem isSimultaneousHole_iff_lcm_dvd {p Q : ℕ} {h₁ h₂ x y : ℤ}
    (hx : IsSimultaneousHole p Q {h₁} {h₂} x) :
    IsSimultaneousHole p Q {h₁} {h₂} y ↔ ((Nat.lcm p Q : ℕ) : ℤ) ∣ y - x := by
  obtain ⟨hx1, hx2⟩ := hx
  simp only [Finset.mem_singleton] at hx1 hx2
  unfold IsSimultaneousHole
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hy1, hy2⟩
    have h1 : (p : ℤ) ∣ y - x := dvd_sub_of_emod_eq (by rw [hy1, hx1])
    have h2 : (Q : ℤ) ∣ y - x := dvd_sub_of_emod_eq (by rw [hy2, hx2])
    exact Int.natCast_dvd.2 (Nat.lcm_dvd (Int.natCast_dvd.1 h1) (Int.natCast_dvd.1 h2))
  · intro h
    have h1 : (p : ℤ) ∣ y - x :=
      dvd_trans (Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_left p Q)) h
    have h2 : (Q : ℤ) ∣ y - x :=
      dvd_trans (Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_right p Q)) h
    exact ⟨by rw [emod_eq_of_dvd_sub h1, hx1], by rw [emod_eq_of_dvd_sub h2, hx2]⟩

/-! ### (iii): a full smaller period against a larger period with two exceptional residues -/

/-- **`lem:gluing-periods` (iii).**  If `p < Q`, a full period `p` and a period `Q` except at at
most two residues in `[0, u]`, `u < Q`, on a word of length at least `2Q + u - 1`, join all
positions of each class modulo `gcd p Q`.  (When `p ∣ Q` the statement is immediate from the full
period, and the paper's hypothesis that neither divides the other is not needed.)

**Differs from the paper's route.** The paper rules out two lost cyclic edges by forcing `Q = 2p`;
here the two multiples of `Q` in `(0, 2Q)` that the exchange produces are compared directly. -/
theorem periods_full_two_holes {p Q u L : ℕ} {T : Finset ℤ} (hp : 0 < p) (hpQ : p < Q)
    (_hu : u < Q) (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ u) (hc : T.card ≤ 2) (hL : 2 * Q + u ≤ L + 1)
    {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) : PeriodJoined L p ∅ Q T x y := by
  by_cases hd : p ∣ Q
  · rw [Nat.gcd_eq_left hd] at hxy
    exact related_of_dvd (periodJoined_equivalence L p ∅ Q T) hp periodJoined_edge_left hx hy hxy
      (by simp)
  · exact related_full_two_holes (periodJoined_equivalence L p ∅ Q T) hp hpQ hd hT hc hL
      periodJoined_edge_left periodJoined_edge_right hx hy hxy

/-- **`lem:gluing-periods` (iii)**, word form: the word has period `gcd p Q`. -/
theorem periodExcept_gcd_full_two_holes {α : Type*} {p Q u L : ℕ} {T : Finset ℤ} {f : ℤ → α}
    (hp : 0 < p) (hpQ : p < Q) (_hu : u < Q) (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ u) (hc : T.card ≤ 2)
    (hL : 2 * Q + u ≤ L + 1) (hfp : PeriodExcept L p ∅ f) (hfQ : PeriodExcept L Q T f) :
    PeriodExcept L (Nat.gcd p Q) ∅ f :=
  periodExcept_gcd_of_joined hfp hfQ fun _ hx _ hy hxy =>
    periods_full_two_holes hp hpQ _hu hT hc hL hx hy hxy

/-! ### Sharpness witnesses and worked instances -/

/-- `lem:gluing-periods` (i), shorter clause, is sharp: at length `2b - 2` with `a = 2`, `b = 3`
a word with full period `2` and period `3` except at the residue `1` need not have period
`gcd 2 3 = 1`. -/
theorem periods_one_hole_of_lt_length_sharp :
    ∃ f : ℤ → Bool, PeriodExcept 4 2 ∅ f ∧ PeriodExcept 4 3 {1} f ∧
      ¬ PeriodExcept 4 (Nat.gcd 2 3) ∅ f :=
  ⟨fun x => decide (x % 2 = 1), by decide⟩

/-- `lem:gluing-periods` (i) is sharp when the full period is larger: at length `2a - 1` with
`a = 3`, `b = 2` the bound `2 max a b = 6` cannot be lowered to `2a - 1 = 5`. -/
theorem periods_one_hole_of_gt_length_sharp :
    ∃ f : ℤ → Bool, PeriodExcept 5 3 ∅ f ∧ PeriodExcept 5 2 {1} f ∧
      ¬ PeriodExcept 5 (Nat.gcd 3 2) ∅ f :=
  ⟨fun x => decide (x = 3), by decide⟩

/-- Non-vacuity of (i): the lemma applied at `a = 2`, `b = 3`, length `6 = 2 max a b`. -/
example : PeriodJoined 6 2 ∅ 3 {1} 1 6 :=
  periods_one_hole (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num)
    (by simp) (by simp) (by norm_num)

/-- A simultaneous hole is a genuine exception to (ii): at `p = 2`, `Q = 3`, `N = 7` (so `r = 3`,
`w = 1`, `m = 2`, `u = 1`) the exceptional phases `0, 0` make position `6` a simultaneous hole,
and the word that is `1` there and `0` elsewhere satisfies both constraints but is not constant. -/
theorem simultaneous_hole_necessary :
    ∃ f : ℤ → Bool, PeriodExcept 6 2 {0} f ∧ PeriodExcept 6 3 {0} f ∧
      IsSimultaneousHole 2 3 {0} {0} 6 ∧ f 6 ≠ f 4 :=
  ⟨fun x => decide (x = 6), by decide, by decide, by unfold IsSimultaneousHole; decide,
    by decide⟩

/-- Non-vacuity of (ii): the lemma applied at `p = 2`, `Q = 3`, `N = 7`, phases `0, 0`. -/
example : PeriodJoined 6 2 {0} 3 {0} 1 4 :=
  periods_two_holes (p := 2) (Q := 3) (N := 7) (r := 3) (m := 2) (w := 1) (u := 1)
    (h₁ := 0) (h₂ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    (by norm_num) rfl (by simp) (by simp) (by simp)
    (by unfold IsSimultaneousHole; decide) (by unfold IsSimultaneousHole; decide)

/-- Non-vacuity of (iii): `p = 2`, `Q = 5`, `u = 3`, holes `{1, 3}`, length `2Q + u - 1 = 12`. -/
example : PeriodJoined 12 2 ∅ 5 {1, 3} 1 12 :=
  periods_full_two_holes (u := 3) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; simp at ht; omega) (by decide) (by norm_num) (by simp) (by simp)
    (by simp)

end PeriodWords
end SkewMarkedFactor.Gluing
