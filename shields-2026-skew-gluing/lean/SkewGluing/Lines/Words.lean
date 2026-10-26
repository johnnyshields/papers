import SkewGluing.PeriodWords

/-!
# Words with two periods: the generic value and the mixed contradictions

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), first assertion, the part that concerns the boundary words only.

A word is a function `ℤ → ℤ` on the positions `1, …, L`.  This file collects what the proof of
`lem:gluing-lines` needs of two period constraints with coprime periods `p`, `Q`:

* `generic_word`: a `{0, 1}`-valued word with period `p` except at the residue `h₁` and period `Q`
  except at the residue `h₂` is constant off the simultaneous holes (`periods_two_holes`), and the
  few simultaneous holes (one progression of spacing `p Q`) leave the constant visible in the sum of
  the word;
* `generic_eq`: two such words with the same sum have the same constant;
* `eq_of_one_hole_not_const`, `not_const_of_full_two_holes`: a full period `p` against a period `Q`
  with one hole, respectively with at most two holes, forces a constant word (`lem:gluing-periods`
  (i), (iii)).

Sorry-free.
-/

namespace SkewGluing

namespace Lines

open PeriodWords

/-- A set of integers in `[1, L]` whose elements are pairwise congruent modulo `M > 0` has at most
`(L - 1) / M + 1` elements. -/
theorem card_le_of_dvd_sub {L M : ℤ} (hL : 1 ≤ L) (hM : 0 < M) {S : Finset ℤ}
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ L) (hd : ∀ x ∈ S, ∀ y ∈ S, M ∣ x - y) :
    (S.card : ℤ) ≤ (L - 1) / M + 1 := by
  have hmaps : Set.MapsTo (fun x => (x - 1) / M) (S : Set ℤ)
      (Finset.Icc (0 : ℤ) ((L - 1) / M)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hS x hx
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by omega) hM.le, Int.ediv_le_ediv hM (by omega)⟩
  have hinj : Set.InjOn (fun x => (x - 1) / M) (S : Set ℤ) := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨k, hk⟩ := hd x hx y hy
    have e : x - 1 = (y - 1) + M * k := by omega
    rw [e, Int.add_mul_ediv_left _ _ hM.ne'] at hxy
    have : k = 0 := by omega
    subst this
    omega
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at this
  have h0 : 0 ≤ (L - 1) / M := Int.ediv_nonneg (by omega) hM.le
  omega

theorem six_le_mul_of_coprime {p Q : ℕ} (hp : 2 ≤ p) (hQ : 2 ≤ Q) (hcop : Nat.Coprime p Q) :
    6 ≤ p * Q := by
  have hne : p ≠ Q := fun h => by
    subst h
    have := Nat.Coprime.eq_one_of_dvd hcop (dvd_refl p)
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h <;> nlinarith

theorem six_mul_div_le {L M : ℤ} (hL : 1 ≤ L) (hM : 6 ≤ M) : 6 * ((L - 1) / M) ≤ L - 1 := by
  have hM0 : 0 < M := by omega
  have h1 := Int.ediv_mul_le (L - 1) hM0.ne'
  have h2 : 0 ≤ (L - 1) / M := Int.ediv_nonneg (by omega) hM0.le
  nlinarith

/-- The constant value off the simultaneous holes, and the bounds it forces on the sum of the word.

Let `f` be a `{0, 1}`-valued word on `1, …, L` (`L + 1 = N`) with period `p` except at the residue
`h₁`, and period `Q` except at the residue `h₂`, where `N = r p + w = m Q + u`, `r, m ≥ 2`, `p`, `Q`
coprime, `h₁ ∈ [0, w]` and `h₂ ∈ [0, u]`.  Then `f` takes one value `a` at every position that is
not a simultaneous hole, and the sum of `f` is at most `c` when `a = 0` and at least `L - c` when
`a = 1`, where `c = (L - 1) / (p Q) + 1` bounds the number of simultaneous holes. -/
theorem generic_word {f : ℤ → ℤ} {p Q N r m w u L : ℕ} {h₁ h₂ : ℤ} (hp : 2 ≤ p) (hQ : 2 ≤ Q)
    (hr : 2 ≤ r) (hm : 2 ≤ m) (hw : w < p) (hu : u < Q) (hNp : N = r * p + w)
    (hNQ : N = m * Q + u) (hcop : Nat.Coprime p Q) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ w)
    (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ u) (hL : L + 1 = N) (hL5 : 5 ≤ L)
    (hfp : PeriodExcept L p {h₁} f) (hfQ : PeriodExcept L Q {h₂} f)
    (hbit : ∀ x ∈ Finset.Icc (1 : ℤ) L, f x = 0 ∨ f x = 1) :
    ∃ a : ℤ, (a = 0 ∨ a = 1) ∧
      (∀ x ∈ Finset.Icc (1 : ℤ) L, (x % (p : ℤ) ≠ h₁ ∨ x % (Q : ℤ) ≠ h₂) → f x = a) ∧
      (a = 0 → ∑ x ∈ Finset.Icc (1 : ℤ) L, f x ≤ ((L : ℤ) - 1) / (p * Q) + 1) ∧
      (a = 1 → (L : ℤ) - (((L : ℤ) - 1) / (p * Q) + 1) ≤ ∑ x ∈ Finset.Icc (1 : ℤ) L, f x) := by
  classical
  have hpQ : ¬ p ∣ Q := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop h
    omega
  have hQp : ¬ Q ∣ p := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop.symm h
    omega
  set S : Finset ℤ := (Finset.Icc (1 : ℤ) L).filter
    (fun x => IsSimultaneousHole p Q {h₁} {h₂} x) with hSdef
  have hconst : ∀ x ∈ Finset.Icc (1 : ℤ) L, ∀ y ∈ Finset.Icc (1 : ℤ) L, x ∉ S → y ∉ S →
      f x = f y := by
    intro x hx y hy hxS hyS
    have hx' : ¬ IsSimultaneousHole p Q {h₁} {h₂} x := fun h =>
      hxS (Finset.mem_filter.mpr ⟨hx, h⟩)
    have hy' : ¬ IsSimultaneousHole p Q {h₁} {h₂} y := fun h =>
      hyS (Finset.mem_filter.mpr ⟨hy, h⟩)
    exact eq_of_periods_two_holes (by omega) (by omega) hr hm hw hu hNp hNQ hpQ hQp hh₁ hh₂ hL
      hfp hfQ hx hy (by rw [hcop.gcd_eq_one]; simp) hx' hy'
  have hpQ0 : (0 : ℤ) < (p : ℤ) * Q := by positivity
  have hScard : (S.card : ℤ) ≤ ((L : ℤ) - 1) / (p * Q) + 1 := by
    refine card_le_of_dvd_sub (by omega) hpQ0 (fun x hx => ?_) (fun x hx y hy => ?_)
    · have := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_Icc] at this
      exact this
    · have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have := (isSimultaneousHole_iff_lcm_dvd hx').mp hy'
      rw [Nat.Coprime.lcm_eq_mul hcop] at this
      have h2 : ((p * Q : ℕ) : ℤ) ∣ x - y := by
        have := dvd_neg.mpr this
        simpa using this
      simpa using h2
  have hM : (6 : ℤ) ≤ (p : ℤ) * Q := by exact_mod_cast six_le_mul_of_coprime hp hQ hcop
  have hq0 : 0 ≤ ((L : ℤ) - 1) / (p * Q) := Int.ediv_nonneg (by omega) hpQ0.le
  have hq6 := six_mul_div_le (L := (L : ℤ)) (M := (p : ℤ) * Q) (by omega) hM
  have hcL : (S.card : ℤ) < L := by omega
  have hSsub : S ⊆ Finset.Icc (1 : ℤ) L := Finset.filter_subset _ _
  have hcardIcc : (Finset.Icc (1 : ℤ) L).card = L := by simp
  have hnon : ((Finset.Icc (1 : ℤ) L) \ S).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hSsub, hcardIcc]
    omega
  obtain ⟨x₀, hx₀⟩ := hnon
  rw [Finset.mem_sdiff] at hx₀
  have ha : f x₀ = 0 ∨ f x₀ = 1 := hbit x₀ hx₀.1
  have hgen : ∀ x ∈ Finset.Icc (1 : ℤ) L, x ∉ S → f x = f x₀ := fun x hx hxS =>
    hconst x hx x₀ hx₀.1 hxS hx₀.2
  have hSsum : ∑ x ∈ Finset.Icc (1 : ℤ) L, f x =
      ∑ x ∈ (Finset.Icc (1 : ℤ) L) \ S, f x + ∑ x ∈ S, f x :=
    (Finset.sum_sdiff hSsub).symm
  have hsumdiff : ∑ x ∈ (Finset.Icc (1 : ℤ) L) \ S, f x =
      ((Finset.Icc (1 : ℤ) L) \ S).card • f x₀ := by
    rw [← Finset.sum_const]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Finset.mem_sdiff] at hx; exact hgen x hx.1 hx.2
  have hcd : (((Finset.Icc (1 : ℤ) L) \ S).card : ℤ) = L - S.card := by
    rw [Finset.card_sdiff_of_subset hSsub, hcardIcc]
    omega
  have hSnn : 0 ≤ ∑ x ∈ S, f x := Finset.sum_nonneg fun x hx => by
    rcases hbit x (hSsub hx) with h | h <;> omega
  have hSle : ∑ x ∈ S, f x ≤ S.card := by
    have := Finset.sum_le_sum (s := S) (f := f) (g := fun _ => (1 : ℤ)) fun x hx => by
      rcases hbit x (hSsub hx) with h | h <;> omega
    simpa using this
  refine ⟨f x₀, ha, ?_, ?_, ?_⟩
  · intro x hx hne
    refine hgen x hx fun hxS => ?_
    have := (Finset.mem_filter.mp hxS).2
    rcases hne with h | h
    · exact h (by simpa using this.1)
    · exact h (by simpa using this.2)
  · intro h0
    rw [hSsum, hsumdiff, h0]
    simp only [smul_zero, zero_add]
    omega
  · intro h1
    rw [hSsum, hsumdiff, h1]
    simp only [nsmul_eq_mul, mul_one]
    rw [hcd]
    omega

/-- Two `{0, 1}`-valued words with the same sum have the same constant value off their
simultaneous holes, if the holes are fewer than a third of the positions. -/
theorem generic_eq {A B : ℤ → ℤ} {L : ℕ} {a b : ℤ} {c : ℤ} (hc : 2 * c < L)
    (hsum : ∑ x ∈ Finset.Icc (1 : ℤ) L, A x = ∑ x ∈ Finset.Icc (1 : ℤ) L, B x)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hA0 : a = 0 → ∑ x ∈ Finset.Icc (1 : ℤ) L, A x ≤ c)
    (hA1 : a = 1 → (L : ℤ) - c ≤ ∑ x ∈ Finset.Icc (1 : ℤ) L, A x)
    (hB0 : b = 0 → ∑ x ∈ Finset.Icc (1 : ℤ) L, B x ≤ c)
    (hB1 : b = 1 → (L : ℤ) - c ≤ ∑ x ∈ Finset.Icc (1 : ℤ) L, B x) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · have := hA0 rfl
    have := hB1 rfl
    omega
  · have := hA1 rfl
    have := hB0 rfl
    omega
  · rfl

/-- **The first period of a word with a generic constant.**  Let `A`, `B` be `{0, 1}`-valued words
on `[1, n]` with equal sums, equal to the constant `a` off the single positions `hA`, `hB`, and
with the initial exceptional bits `A hA = 1`, `B hB = 0` (when the position is positive).  Then
both words are the constant `a` on `[1, n]`. -/
theorem prefix_of_generic {A B : ℤ → ℤ} {n a hA hB : ℤ} (ha : a = 0 ∨ a = 1)
    (hbitA : ∀ x ∈ Finset.Icc (1 : ℤ) n, A x = 0 ∨ A x = 1)
    (hbitB : ∀ x ∈ Finset.Icc (1 : ℤ) n, B x = 0 ∨ B x = 1)
    (hsum : ∑ x ∈ Finset.Icc (1 : ℤ) n, A x = ∑ x ∈ Finset.Icc (1 : ℤ) n, B x)
    (hgenA : ∀ x ∈ Finset.Icc (1 : ℤ) n, x ≠ hA → A x = a)
    (hgenB : ∀ x ∈ Finset.Icc (1 : ℤ) n, x ≠ hB → B x = a)
    (capA : 1 ≤ hA → A hA = 1) (capB : 1 ≤ hB → B hB = 0) :
    ∀ x ∈ Finset.Icc (1 : ℤ) n, A x = a ∧ B x = a := by
  rcases ha with rfl | rfl
  · have hB0 : ∀ x ∈ Finset.Icc (1 : ℤ) n, B x = 0 := by
      intro x hx
      by_cases hxB : x = hB
      · subst hxB
        exact capB (Finset.mem_Icc.mp hx).1
      · exact hgenB x hx hxB
    have hs : ∑ x ∈ Finset.Icc (1 : ℤ) n, A x = 0 := by
      rw [hsum]; exact Finset.sum_eq_zero hB0
    have hA0 := (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => by
      rcases hbitA x hx with h | h <;> omega)).mp hs
    exact fun x hx => ⟨hA0 x hx, hB0 x hx⟩
  · have hA1 : ∀ x ∈ Finset.Icc (1 : ℤ) n, A x = 1 := by
      intro x hx
      by_cases hxA : x = hA
      · subst hxA
        exact capA (Finset.mem_Icc.mp hx).1
      · exact hgenA x hx hxA
    have hs : ∑ x ∈ Finset.Icc (1 : ℤ) n, (1 - B x) = 0 := by
      rw [Finset.sum_sub_distrib, ← hsum, Finset.sum_congr rfl hA1]
      simp
    have hB1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => by
      rcases hbitB x hx with h | h <;> omega)).mp hs
    exact fun x hx => ⟨hA1 x hx, by have := hB1 x hx; omega⟩

/-- A word with full period `1` on `[1, L]` is constant. -/
theorem const_of_period_one {f : ℤ → ℤ} {L : ℕ} (h : PeriodExcept L 1 ∅ f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L) : f x = f y := by
  have key : ∀ x y : ℤ, x ∈ Finset.Icc (1 : ℤ) L → y ∈ Finset.Icc (1 : ℤ) L → x ≤ y →
      f x = f y := by
    intro x y hx hy hxy
    rw [Finset.mem_Icc] at hx hy
    induction y, hxy using Int.leInduction with
    | base => rfl
    | succ n hn ih =>
      have h1 := h n (by rw [Finset.mem_Icc]; push_cast; omega) (by simp)
      rw [ih (by omega)]
      simpa using h1
  rcases le_total x y with hxy | hxy
  · exact key x y hx hy hxy
  · exact (key y x hy hx hxy).symm

theorem periodExcept_mono {f : ℤ → ℤ} {L p : ℕ} {S T : Finset ℤ} (hST : S ⊆ T)
    (h : PeriodExcept L p S f) : PeriodExcept L p T f :=
  fun x hx hT => h x hx fun hS => hT (hST hS)

/-- **`lem:gluing-lines`, a full period against one hole.**  A word with full period `p` and period
`Q` except at one residue, for coprime `p`, `Q ≥ 2`, on the positions `1, …, N - 1` with
`N = r p + w = m Q + u`, `r, m ≥ 2` and `w ≥ 1`, is constant.  (`lem:gluing-periods` (i), with the
shorter clause when the full period is the smaller one.) -/
theorem const_of_full_one_hole {f : ℤ → ℤ} {p Q N r m w u L : ℕ} {h : ℤ} (hp : 2 ≤ p)
    (hQ : 2 ≤ Q) (hr : 2 ≤ r) (hm : 2 ≤ m) (hw : 1 ≤ w) (hNp : N = r * p + w)
    (hNQ : N = m * Q + u) (hcop : Nat.Coprime p Q) (hL : L + 1 = N)
    (hfp : PeriodExcept L p ∅ f) (hfQ : PeriodExcept L Q {h} f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L) : f x = f y := by
  have hpQ : ¬ p ∣ Q := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop h
    omega
  have hQp : ¬ Q ∣ p := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop.symm h
    omega
  have hmQ : 2 * Q ≤ m * Q := Nat.mul_le_mul_right Q hm
  have hrp : 2 * p ≤ r * p := Nat.mul_le_mul_right p hr
  have hper : PeriodExcept L (Nat.gcd p Q) ∅ f := by
    rcases lt_trichotomy p Q with hlt | heq | hgt
    · exact periodExcept_gcd_one_hole_of_lt (by omega) hlt hpQ h (by omega) hfp hfQ
    · exact absurd (heq ▸ dvd_refl p) hpQ
    · exact periodExcept_gcd_one_hole (by omega) (by omega) hpQ hQp h (by
        have := le_max_left p Q
        have := max_le_iff.mpr (⟨by omega, by omega⟩ : p ≤ p ∧ Q ≤ p)
        rw [max_eq_left hgt.le]; omega) hfp hfQ
  rw [hcop.gcd_eq_one] at hper
  exact const_of_period_one hper hx hy

/-- **`lem:gluing-lines`, a full period against a period with two holes** (`lem:gluing-periods`
(iii)): with `p < Q` coprime, a word with full period `p` and period `Q` except at the residues
`T ⊆ [0, u]`, `|T| ≤ 2`, on `1, …, N - 1` with `N = m Q + u`, `m ≥ 2`, is constant. -/
theorem const_of_full_two_holes {f : ℤ → ℤ} {p Q N m u L : ℕ} {T : Finset ℤ} (hp : 2 ≤ p)
    (hpQ : p < Q) (hu : u < Q) (hm : 2 ≤ m) (hNQ : N = m * Q + u) (hcop : Nat.Coprime p Q)
    (hL : L + 1 = N) (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ u) (hc : T.card ≤ 2)
    (hfp : PeriodExcept L p ∅ f) (hfQ : PeriodExcept L Q T f) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L) : f x = f y := by
  have hmQ : 2 * Q ≤ m * Q := Nat.mul_le_mul_right Q hm
  have hper := periodExcept_gcd_full_two_holes (by omega) hpQ hu hT hc (by omega) hfp hfQ
  rw [hcop.gcd_eq_one] at hper
  exact const_of_period_one hper hx hy

end Lines

end SkewGluing
