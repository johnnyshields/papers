import SkewGluing.MixedPairs

/-!
# Period words on one gcd class, with a general hole pattern

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`), as the application of `lem:gluing-periods` (i)–(iii) to the words of
two case-(d) charts, one gcd class at a time.

For words with period `p` except at `S` and period `Q` except at `T`, and a gcd class `ρ` modulo
`g = gcd p Q`, let `S_ρ`, `T_ρ` be the exceptional residues lying in the class.  The word is
constant on the class (apart from simultaneous holes) in each of the situations the proposition
needs: at most one residue on one side and none on the other (`mixFold_class_eq_S`,
`mixFold_class_eq_T`), none on one side and two on the larger-period side
(`mixFold_class_eq_T_two`), and at most one on each side
(`mixFold_class_eq_two_holes`).

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

/-- The residues of `S` in the class of `x` modulo `g`. -/
def mixFoldClass (g : ℕ) (S : Finset ℤ) (x : ℤ) : Finset ℤ :=
  S.filter fun a => a % (g : ℤ) = x % (g : ℤ)

theorem mixFold_gcd_dvd_left (p Q : ℕ) : ((Nat.gcd p Q : ℕ) : ℤ) ∣ p :=
  Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)

theorem mixFold_gcd_dvd_right (p Q : ℕ) : ((Nat.gcd p Q : ℕ) : ℤ) ∣ Q :=
  Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)

variable {f : ℤ → ℤ} {L p Q : ℕ} {S T : Finset ℤ}

/-- A period `Q` with no exceptional residue in the class and a period `p` with at most one. -/
theorem mixFold_class_eq_S (hp : 0 < p) (hQ : 0 < Q) (hnd1 : ¬ p ∣ Q) (hnd2 : ¬ Q ∣ p)
    (hL : 2 * max p Q ≤ L) (hfp : PeriodExcept L p S f) (hfQ : PeriodExcept L Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) (hS : (mixFoldClass (Nat.gcd p Q) S x).card ≤ 1)
    (hT : mixFoldClass (Nat.gcd p Q) T x = ∅) : f x = f y := by
  obtain ⟨h, hh⟩ := Finset.card_le_one_iff_subset_singleton.mp hS
  have hj := periods_one_hole hQ hp hnd2 hnd1 h (by rwa [max_comm]) hx hy
    (by rwa [Nat.gcd_comm])
  rw [periodJoined_comm] at hj
  have hj' := mixFold_periodJoined_mono (S := {h}) (S' := mixFoldClass (Nat.gcd p Q) S x)
    (T := ∅) (T' := mixFoldClass (Nat.gcd p Q) T x) hh (by rw [hT]) hj
  exact mixFold_eq_of_joined_class (mixFold_gcd_dvd_left p Q) (mixFold_gcd_dvd_right p Q) hfp hfQ
    (x % ((Nat.gcd p Q : ℕ) : ℤ)) rfl hj'

/-- A period `p` with no exceptional residue in the class and a period `Q` with at most one. -/
theorem mixFold_class_eq_T (hp : 0 < p) (hQ : 0 < Q) (hnd1 : ¬ p ∣ Q) (hnd2 : ¬ Q ∣ p)
    (hL : 2 * max p Q ≤ L) (hfp : PeriodExcept L p S f) (hfQ : PeriodExcept L Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) (hT : (mixFoldClass (Nat.gcd p Q) T x).card ≤ 1)
    (hS : mixFoldClass (Nat.gcd p Q) S x = ∅) : f x = f y := by
  obtain ⟨h, hh⟩ := Finset.card_le_one_iff_subset_singleton.mp hT
  have hj := periods_one_hole hp hQ hnd1 hnd2 h hL hx hy hxy
  have hj' := mixFold_periodJoined_mono (S := ∅) (S' := mixFoldClass (Nat.gcd p Q) S x)
    (T := {h}) (T' := mixFoldClass (Nat.gcd p Q) T x) (by rw [hS]) hh hj
  exact mixFold_eq_of_joined_class (mixFold_gcd_dvd_left p Q) (mixFold_gcd_dvd_right p Q) hfp hfQ
    (x % ((Nat.gcd p Q : ℕ) : ℤ)) rfl hj'

/-- A smaller full period `p` and a larger period `Q` with at most two exceptional residues in
`[0, u]` in the class (`lem:gluing-periods` (iii)). -/
theorem mixFold_class_eq_T_two {u : ℕ} (hp : 0 < p) (hpQ : p < Q) (hu : u < Q)
    (hTu : ∀ a ∈ T, 0 ≤ a ∧ a ≤ (u : ℤ)) (hT2 : T.card ≤ 2) (hL : 2 * Q + u ≤ L + 1)
    (hfp : PeriodExcept L p S f) (hfQ : PeriodExcept L Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) (hS : mixFoldClass (Nat.gcd p Q) S x = ∅) :
    f x = f y := by
  have hj := periods_full_two_holes (T := mixFoldClass (Nat.gcd p Q) T x) hp hpQ hu
    (fun a ha => hTu a (Finset.mem_filter.mp ha).1)
    ((Finset.card_filter_le _ _).trans hT2) hL hx hy hxy
  have hj' := mixFold_periodJoined_mono (S := ∅) (S' := mixFoldClass (Nat.gcd p Q) S x)
    (T := mixFoldClass (Nat.gcd p Q) T x) (T' := mixFoldClass (Nat.gcd p Q) T x)
    (by rw [hS]) (Finset.Subset.refl _) hj
  exact mixFold_eq_of_joined_class (mixFold_gcd_dvd_left p Q) (mixFold_gcd_dvd_right p Q) hfp hfQ
    (x % ((Nat.gcd p Q : ℕ) : ℤ)) rfl hj'

theorem mixFold_pick {g : ℕ} {S : Finset ℤ} (hS0 : S.Nonempty) (x : ℤ)
    (hS : (mixFoldClass g S x).card ≤ 1) :
    ∃ h ∈ S, mixFoldClass g S x ⊆ {h} := by
  by_cases hne : (mixFoldClass g S x).Nonempty
  · obtain ⟨h, hh⟩ := Finset.card_le_one_iff_subset_singleton.mp hS
    obtain ⟨a, ha⟩ := hne
    have := hh ha
    rw [Finset.mem_singleton] at this
    subst this
    exact ⟨a, (Finset.mem_filter.mp ha).1, hh⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨h, hh⟩ := hS0
    exact ⟨h, hh, by rw [hne]; exact Finset.empty_subset _⟩

/-- One residue at most in the class on each side, away from simultaneous holes
(`lem:gluing-periods` (ii)). -/
theorem mixFold_class_eq_two_holes {N r m w u : ℕ} (hp : 0 < p) (hQ : 0 < Q) (hr : 2 ≤ r)
    (hm : 2 ≤ m) (hw : w < p) (hu : u < Q) (hNp : N = r * p + w) (hNQ : N = m * Q + u)
    (hnd1 : ¬ p ∣ Q) (hnd2 : ¬ Q ∣ p) (hSw : ∀ a ∈ S, 0 ≤ a ∧ a ≤ (w : ℤ))
    (hTu : ∀ a ∈ T, 0 ≤ a ∧ a ≤ (u : ℤ)) (hS0 : S.Nonempty) (hT0 : T.Nonempty)
    (hfp : PeriodExcept (N - 1) p S f) (hfQ : PeriodExcept (N - 1) Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ))
    (hy : y ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ))
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x)
    (hS : (mixFoldClass (Nat.gcd p Q) S x).card ≤ 1)
    (hT : (mixFoldClass (Nat.gcd p Q) T x).card ≤ 1)
    (hx' : ¬ (x % (p : ℤ) ∈ S ∧ x % (Q : ℤ) ∈ T))
    (hy' : ¬ (y % (p : ℤ) ∈ S ∧ y % (Q : ℤ) ∈ T)) : f x = f y := by
  have hN1 : 1 ≤ N := by nlinarith
  obtain ⟨h₁, hh₁S, hh₁⟩ := mixFold_pick hS0 x hS
  obtain ⟨h₂, hh₂T, hh₂⟩ := mixFold_pick hT0 x hT
  have hj := periods_two_holes (h₁ := h₁) (h₂ := h₂) (L := N - 1) hp hQ hr hm hw hu hNp hNQ hnd1
    hnd2 (hSw h₁ hh₁S) (hTu h₂ hh₂T) (by omega) hx hy hxy
    (fun hh => hx' ⟨by rw [Finset.mem_singleton.mp hh.1]; exact hh₁S,
      by rw [Finset.mem_singleton.mp hh.2]; exact hh₂T⟩)
    (fun hh => hy' ⟨by rw [Finset.mem_singleton.mp hh.1]; exact hh₁S,
      by rw [Finset.mem_singleton.mp hh.2]; exact hh₂T⟩)
  have hj' := mixFold_periodJoined_mono (S := {h₁}) (S' := mixFoldClass (Nat.gcd p Q) S x)
    (T := {h₂}) (T' := mixFoldClass (Nat.gcd p Q) T x) hh₁ hh₂ hj
  exact mixFold_eq_of_joined_class (mixFold_gcd_dvd_left p Q) (mixFold_gcd_dvd_right p Q) hfp hfQ
    (x % ((Nat.gcd p Q : ℕ) : ℤ)) rfl hj'

end SkewGluing
