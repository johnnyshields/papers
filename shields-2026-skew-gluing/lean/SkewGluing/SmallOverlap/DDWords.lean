import SkewGluing.SmallOverlap.SmallWords
import SkewGluing.SmallOverlap.DriftClass

/-!
# Two case-(d) roots: the singleton coding at period `g`

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the drift argument for two case-(d) charts.

For a case-(d) singleton root of period `p` and a case-(d) root of period `Q`, the southeast word
`B` is `g`-periodic; the first-row word `A` is `g`-periodic on every private class off the
exceptional residues `0, 1`.  A private class is exceptional only when both phases of the partner
project onto it; its constancy follows from the zero total drift of the first `p / g` blocks
(`dd_periodic`).

Sorry-free.
-/

namespace SkewGluing
namespace SmallOverlap

open PeriodWords

theorem dd_periodic {A B : ℤ → ℤ} {p Q r m u N L : ℕ} (hn : Nums p Q r m u N L) {t₂ s₂ : ℤ}
    (pA : PeriodExcept L p {0, 1} A) (pB : PeriodExcept L p ∅ B)
    (qA : PeriodExcept L Q {t₂, s₂} A) (qB : PeriodExcept L Q ∅ B)
    (hA1 : A 1 = 1) (hB1 : B 1 = 1) (hAL : A (L : ℤ) = 0) (hBp : B (p : ℤ) = 0)
    (hbits : ∀ x : ℤ, 1 ≤ x → x ≤ L → (A x = 0 ∨ A x = 1) ∧ (B x = 0 ∨ B x = 1))
    (hh1 : heightWord (fun k : ℕ => A k) (fun k : ℕ => B k) 1 = 1)
    (hhp : heightWord (fun k : ℕ => A k) (fun k : ℕ => B k) (p - 1) = 1) :
    PeriodExcept L (Nat.gcd p Q) {0, 1} A ∧ PeriodExcept L (Nat.gcd p Q) ∅ B := by
  have hg := hn.hg
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd p Q := ⟨_, rfl⟩
  rw [← hgdef] at hg ⊢
  have hgZ : (2 : ℤ) ≤ g := by exact_mod_cast hg
  have hp2 := hn.hp2
  have hp0 : 0 < p := by omega
  have hQ0 : 0 < Q := by have := hn.huQ; have := hn.hu1; omega
  have hgp : (g : ℤ) ∣ p := by rw [hgdef]; exact hn.gdvd_p
  have hgL : (g : ℤ) ∣ L := by rw [hgdef]; exact hn.gdvd_N
  have hlp := hn.len_p
  have hlQ := hn.len_Q
  have hqB : PeriodExcept L Q {0} B := fun x hx _ => qB x hx (by simp)
  have hBg : PeriodExcept L g ∅ B := by
    rw [hgdef]
    exact periodExcept_gcd_full_hole hp0 hQ0 hn.hpQ hn.hQp 0 (by omega) hlp pB hqB
  refine ⟨?_, hBg⟩
  have hmem : ∀ x : ℤ, 1 ≤ x → x ≤ L → x ∈ Finset.Icc (1 : ℤ) L := fun x h1 h2 => by
    simp [h1, h2]
  -- case 1: at most one partner hole on the class
  have hc1 : ∀ x : ℤ, 1 ≤ x → x + g ≤ L → x % g ≠ 0 → x % g ≠ 1 →
      ¬ (t₂ % g = x % g ∧ s₂ % g = x % g) → A x = A (x + g) := by
    intro x hx1 hx2 hx0 hx1' hboth
    have hxS : ∀ s ∈ ({0, 1} : Finset ℤ), s % (Nat.gcd p Q : ℤ) ≠ x % (Nat.gcd p Q : ℤ) := by
      intro s hs
      rw [← hgdef]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · rw [Int.zero_emod]; exact fun h => hx0 h.symm
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact fun h => hx1' h.symm
    by_cases ht : t₂ % g = x % g
    · refine eq_of_class_one_hole (h := t₂) hp0 hQ0 hn.hpQ hn.hQp (by omega) pA qA
        (hmem x hx1 (by omega)) (hmem (x + g) (by omega) hx2) ?_ hxS ?_
      · rw [← hgdef]; exact ⟨1, by ring⟩
      · intro s hs hst
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rw [← hgdef]
        rcases hs with rfl | rfl
        · exact absurd rfl hst
        · intro h; exact hboth ⟨ht, h⟩
    · refine eq_of_class_one_hole (h := s₂) hp0 hQ0 hn.hpQ hn.hQp (by omega) pA qA
        (hmem x hx1 (by omega)) (hmem (x + g) (by omega) hx2) ?_ hxS ?_
      · rw [← hgdef]; exact ⟨1, by ring⟩
      · intro s hs hst
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rw [← hgdef]
        rcases hs with rfl | rfl
        · exact ht
        · exact absurd rfl hst
  -- the classes `0` and `1` of `B`
  have hB0 : ∀ y : ℤ, 1 ≤ y → y ≤ L → y % g = 0 → B y = 0 := by
    intro y hy1 hy2 hy0
    have hyd : (g : ℤ) ∣ (p : ℤ) - y := dvd_sub hgp (Int.dvd_of_emod_eq_zero hy0)
    rw [eq_of_full (by omega) hBg hy1 hy2 (by omega) (by omega) hyd, hBp]
  have hB1' : ∀ y : ℤ, 1 ≤ y → y ≤ L → y % g = 1 → B y = 1 := by
    intro y hy1 hy2 hy0
    have hyd : (g : ℤ) ∣ y - 1 :=
      dvd_sub_of_emod_eq (by rw [hy0, Int.emod_eq_of_lt (by omega) (by omega)])
    rw [← hB1]
    exact eq_of_full (by omega) hBg hy1 hy2 le_rfl (by omega) (by simpa using dvd_neg.2 hyd)
  -- main step
  intro x hx hS
  simp only [Finset.mem_Icc] at hx
  have hx0 : x % g ≠ 0 := fun h => hS (by simp [h])
  have hx1' : x % g ≠ 1 := fun h => hS (by simp [h])
  by_cases hboth : t₂ % g = x % g ∧ s₂ % g = x % g
  swap
  · exact hc1 x hx.1 (by omega) hx0 hx1' hboth
  -- the class of `x` carries both partner phases
  obtain ⟨R, hRx⟩ : ∃ R : ℕ, (R : ℤ) = x % g := ⟨(x % g).toNat, by
    have := Int.emod_nonneg x (by omega : (g : ℤ) ≠ 0); omega⟩
  have hRlt : (R : ℤ) < g := by rw [hRx]; exact Int.emod_lt_of_pos x (by omega)
  have hR2 : 2 ≤ R := by
    have := Int.emod_nonneg x (by omega : (g : ℤ) ≠ 0); omega
  have hRg : R < g := by exact_mod_cast hRlt
  -- classes `0` and `1` of `A` (the partner has no exceptional residue there)
  have hA0 : ∀ y : ℤ, 1 ≤ y → y ≤ L → y % g = 0 → A y = 0 := by
    intro y hy1 hy2 hy0
    have hyd : (g : ℤ) ∣ (L : ℤ) - y := dvd_sub hgL (Int.dvd_of_emod_eq_zero hy0)
    have := eq_of_class_one_hole_swap (h := 0) hp0 hQ0 hn.hpQ hn.hQp (by omega) pA qA
      (hmem y hy1 hy2) (hmem L (by omega) le_rfl) (by rw [← hgdef]; exact hyd) ?_ ?_
    · rw [this, hAL]
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rw [← hgdef, hy0]
      rcases hs with rfl | rfl
      · rw [hboth.1]; exact hx0
      · rw [hboth.2]; exact hx0
    · intro s hs hs0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rw [← hgdef, hy0]
      rcases hs with rfl | rfl
      · exact absurd rfl hs0
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
  have hA1' : ∀ y : ℤ, 1 ≤ y → y ≤ L → y % g = 1 → A y = 1 := by
    intro y hy1 hy2 hy0
    have hyd : (g : ℤ) ∣ y - 1 :=
      dvd_sub_of_emod_eq (by rw [hy0, Int.emod_eq_of_lt (by omega) (by omega)])
    have := eq_of_class_one_hole_swap (h := 1) hp0 hQ0 hn.hpQ hn.hQp (by omega) pA qA
      (hmem y hy1 hy2) (hmem 1 le_rfl (by omega)) (by rw [← hgdef]; simpa using dvd_neg.2 hyd) ?_ ?_
    · rw [this, hA1]
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rw [← hgdef, hy0]
      rcases hs with rfl | rfl
      · rw [hboth.1]; exact hx1'
      · rw [hboth.2]; exact hx1'
    · intro s hs hs0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rw [← hgdef, hy0]
      rcases hs with rfl | rfl
      · rw [Int.zero_emod]; omega
      · exact absurd rfl hs0
  obtain ⟨n, hpn⟩ : ∃ n, p = g * n := by
    have := Nat.gcd_dvd_left p Q
    rw [← hgdef] at this
    exact ⟨p / g, (Nat.mul_div_cancel' this).symm⟩
  have hgQd : g ∣ Q := by have := Nat.gcd_dvd_right p Q; rwa [← hgdef] at this
  have hgpd : g ∣ p := ⟨n, hpn⟩
  have hgp_lt : g < p := by
    have hle : g ≤ p := Nat.le_of_dvd hp0 hgpd
    rcases eq_or_lt_of_le hle with h | h
    · exfalso; apply hn.hpQ; rw [← h]; exact hgQd
    · exact h
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hpn; omega
    · exact h0
  have hnp : p = n * g := by rw [hpn]; ring
  -- all private classes but `R` repeat
  have hPA : PeriodExcept L g {0, 1, (R : ℤ)} A := by
    intro y hy hyS
    simp only [Finset.mem_Icc] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyS
    refine hc1 y hy.1 (by omega) hyS.1 hyS.2.1 ?_
    intro hb
    apply hyS.2.2
    rw [hRx]
    exact (hb.1.symm.trans hboth.1)
  have hcl : ∀ i z : ℕ, i < n → 2 ≤ z → z < g → z ≠ R → A ((i * g + z : ℕ) : ℤ) = A (z : ℤ) := by
    intro i z hi hz1 hz2 hzR
    have hlt : i * g + z < p := by
      have : (i + 1) * g ≤ n * g := Nat.mul_le_mul_right g hi
      have : (i + 1) * g = i * g + g := by ring
      omega
    have hdvd : (g : ℤ) ∣ ((i * g + z : ℕ) : ℤ) - z := ⟨i, by push_cast; ring⟩
    refine (periodExcept_eq_of_dvd hPA (by omega) (x := (z : ℤ)) (y := ((i * g + z : ℕ) : ℤ))
      (by omega) (by omega) (by push_cast; nlinarith) hdvd ?_).symm
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨by omega, by omega, by omega⟩
  have hclB : ∀ i z : ℕ, i < n → 2 ≤ z → z < g → B ((i * g + z : ℕ) : ℤ) = B (z : ℤ) := by
    intro i z hi hz1 hz2
    have hlt : i * g + z < p := by
      have : (i + 1) * g ≤ n * g := Nat.mul_le_mul_right g hi
      have : (i + 1) * g = i * g + g := by ring
      omega
    have hdvd : (g : ℤ) ∣ ((i * g + z : ℕ) : ℤ) - z := ⟨i, by push_cast; ring⟩
    exact (eq_of_full (by omega) hBg (by omega) (by omega) (by omega) (by omega) hdvd).symm
  -- the zero total drift
  have hjoin : ∀ j : ℕ, 1 ≤ j → j < n →
      ((fun k : ℕ => A k) (j * g) - (fun k : ℕ => B k) (j * g)) +
        ((fun k : ℕ => A k) (j * g + 1) - (fun k : ℕ => B k) (j * g + 1)) = 0 := by
    intro j hj1 hj2
    have hlt : j * g + 1 < p := by
      have : (j + 1) * g ≤ n * g := Nat.mul_le_mul_right g hj2
      have : (j + 1) * g = j * g + g := by ring
      omega
    have hj0 : 1 ≤ j * g := by nlinarith
    have m0 : ((j * g : ℕ) : ℤ) % g = 0 := by push_cast; exact Int.mul_emod_left _ _
    have m1 : ((j * g + 1 : ℕ) : ℤ) % g = 1 := by
      push_cast
      rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
        Int.emod_eq_of_lt (by omega) (by omega)]
    simp only
    rw [hA0 _ (by omega) (by omega) m0, hB0 _ (by omega) (by omega) m0,
      hA1' _ (by omega) (by omega) m1, hB1' _ (by omega) (by omega) m1]
    ring
  have hsum := total_drift_zero (a := fun k : ℕ => A k) (b := fun k : ℕ => B k) (g := g)
    (n := n) (by omega) hn1 hjoin hh1 (by rw [← hnp]; exact hhp)
  have hdrift := drift_class_const (a := fun k : ℕ => A k) (b := fun k : ℕ => B k) (g := g)
    (n := n) (R := R) (by omega) hR2 hRg hn1 (fun i hi => by
      have hlt : i * g + R < p := by
        have : (i + 1) * g ≤ n * g := Nat.mul_le_mul_right g hi
        have : (i + 1) * g = i * g + g := by ring
        omega
      have := (hbits ((i * g + R : ℕ) : ℤ) (by omega) (by omega)).1
      exact this)
    (fun i z hi hz1 hz2 hzR => hcl i z hi hz1 hz2 hzR)
    (fun i z hi hz1 hz2 => hclB i z hi hz1 hz2) hsum
  have hext : ∀ i : ℕ, i * g + R ≤ L → A ((i * g + R : ℕ) : ℤ) = A (R : ℤ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hiL
      by_cases hin : i < n
      · exact hdrift i hin
      · have hi' : n ≤ i := by omega
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + n := ⟨i - n, by omega⟩
        have hlt : i' < i' + n := by omega
        have e1 : i' * g + R + p = (i' + n) * g + R := by rw [hnp]; ring
        have hxy : A ((i' * g + R : ℕ) : ℤ) = A (((i' + n) * g + R : ℕ) : ℤ) := by
          refine periodExcept_eq_of_dvd pA hp0 (x := ((i' * g + R : ℕ) : ℤ))
            (y := (((i' + n) * g + R : ℕ) : ℤ)) (by omega) (by omega) (by omega) ?_ ?_
          · refine ⟨1, ?_⟩
            have : ((((i' + n) * g + R : ℕ) : ℤ)) = ((i' * g + R : ℕ) : ℤ) + p := by
              rw [← Nat.cast_add]; congr 1; omega
            rw [this]; ring
          · intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            have hmg : ((i' * g + R : ℕ) : ℤ) % (g : ℤ) = R := by
              push_cast
              rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
                Int.emod_eq_of_lt (by omega) (by omega)]
            have hq : (((i' * g + R : ℕ) : ℤ) % (p : ℤ)) % (g : ℤ) =
                ((i' * g + R : ℕ) : ℤ) % (g : ℤ) := Int.emod_emod_of_dvd _ hgp
            rcases hm with h | h
            · rw [h, hmg] at hq; simp at hq; omega
            · rw [h, hmg, Int.emod_eq_of_lt (by omega) (by omega)] at hq; omega
        rw [← hxy]
        exact ih i' hlt (by omega)
  -- conclusion for the class of `x`
  have hxd : x = ((x / g).toNat : ℤ) * g + R := by
    have h0 : 0 ≤ x / g := Int.ediv_nonneg (by omega) (by omega)
    rw [Int.toNat_of_nonneg h0, hRx]
    have := Int.mul_ediv_add_emod x g
    linarith
  obtain ⟨i, hi⟩ : ∃ i : ℕ, x = (i : ℤ) * g + R := ⟨_, hxd⟩
  have e1 : x = ((i * g + R : ℕ) : ℤ) := by rw [hi]; push_cast; ring
  have e2 : x + g = (((i + 1) * g + R : ℕ) : ℤ) := by rw [hi]; push_cast; ring
  have h1 := hext i (by omega)
  have h2 := hext (i + 1) (by omega)
  rw [e2, e1, h1, h2]

end SmallOverlap
end SkewGluing
