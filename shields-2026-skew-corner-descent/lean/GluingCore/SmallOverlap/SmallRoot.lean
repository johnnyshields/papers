/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/SmallRoot.lean`. -/
import GluingCore.SmallOverlap.SmallWords
import GluingCore.SmallOverlap.ConstructA
import GluingCore.SmallOverlap.ConstructB
import GluingCore.SmallOverlap.ConstructD

/-!
# `lem:gluing-small`: the period-`g` root of a width-one root and a second root

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`).

For a diagram with a proper root of width one and period `p` and another proper root of period
`Q`, neither period dividing the other, `g = gcd p Q > 1`:

* `Chart.IsProperRoot.singleton_gperiodic`: the boundary words have period `g` except at the
  exceptional residues of the singleton root (`eq:gluing-singleton` at period `g`), for a
  singleton root of case (a), (b) or (d), unless both roots have case (d).

Sorry-free.
-/

namespace GluingCore

open MarkedInner

namespace SmallOverlap

open PeriodWords

theorem _root_.GluingCore.Chart.IsProperRoot.singleton_gperiodic {χ₁ χ₂ : Chart} {F : Diagram}
    {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q) (hw₁ : χ₁.ω.width = 1)
    (hg : 1 < Nat.gcd p Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hc : χ₁.ω.case ≠ .c)
    (hdd : ¬ (χ₁.ω.case = .d ∧ χ₂.ω.case = .d)) :
    PeriodExcept (span F - 1) (Nat.gcd p Q) (holesA χ₁.ω.case 1 0) (wordA F) ∧
    PeriodExcept (span F - 1) (Nat.gcd p Q) (holesB χ₁.ω.case 1 0) (wordB F) := by
  obtain ⟨r, m, u, hr, hm, hu1, huQ, hp2, hQ2, hNp, hNQ, hwu, hgu⟩ := h₁.small_arith h₂ hw₁ hg
  have hn : Nums p Q r m u (span F) (span F - 1) :=
    ⟨hr, hm, hu1, huQ, hp2, hNp, hNQ, by omega, hg, hpQ, hQp, hgu⟩
  have hW₁ := h₁.W_nonempty_of_width_one hw₁
  have hW₂ : χ₂.ω.W.Nonempty := by
    by_contra hne
    have : χ₂.ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have := width_eq_zero_of_eq_empty this
    omega
  have hlegal₁ : χ₁.ω.IsLegalNonempty := ⟨h₁.1.2.2.2, hW₁⟩
  have hlegal₂ : χ₂.ω.IsLegalNonempty := ⟨h₂.1.2.2.2, hW₂⟩
  have hwZ₁ : χ₁.ω.widthZ = 1 := by unfold MarkedInner.widthZ; omega
  have hwZ₂ : χ₂.ω.widthZ = (u : ℤ) := by unfold MarkedInner.widthZ; omega
  have hph₁ := hlegal₁.isPhases_one hwZ₁
  obtain ⟨s₂, t₂, hph₂⟩ := hlegal₂.exists_phases
  have per₁ := h₁.periodic_nonempty hW₁ hph₁
  have per₂ := h₂.periodic_nonempty hW₂ hph₂
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph₂
  rw [hwZ₂] at hs2 ht2
  obtain ⟨l, u', hbits, e1, e2, e3, e4⟩ := h₁.singleton_ends hw₁
  have hLz : ((span F - 1 : ℕ) : ℤ) = (span F : ℤ) - 1 := by
    have : 1 ≤ span F := by omega
    push_cast [Nat.cast_sub this]; rfl
  have hNZ : (span F : ℤ) = r * p + 1 := by rw [hNp]; push_cast; ring
  have hNQZ : (span F : ℤ) = m * Q + u := by rw [hNQ]; push_cast; ring
  have hlen_p := hn.len_p
  have hlen_Q := hn.len_Q
  have hLge : (u : ℤ) ≤ ((span F - 1 : ℕ) : ℤ) := by
    have := hn.len_Q; have : 2 ≤ Q := by omega
    omega
  have hwuZ : (χ₂.ω.width : ℤ) = u := by exact_mod_cast hwu
  have hg2 : (2 : ℤ) ≤ (Nat.gcd p Q : ℤ) := by exact_mod_cast hg
  -- notation: `L` is `span F - 1`
  have hLe : ∀ x : ℤ, 1 ≤ x → x ≤ (span F : ℤ) - 1 → x ≤ ((span F - 1 : ℕ) : ℤ) := by
    intro x _ h; rw [hLz]; exact h
  cases hc1 : χ₁.ω.case
  · -- the singleton root has case (a)
    rw [hc1] at per₁ hbits
    simp only [holesA, holesB] at per₁
    simp only [holesA, holesB]
    simp only [CaseBits] at hbits
    cases hc2 : χ₂.ω.case
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      exact ordinary_ordinary hn (a₁ := 0) (b₁ := 1) (a₂ := t₂) (b₂ := s₂) (by omega) (by omega)
        (by omega) (by omega) per₁.1 per₁.2 per₂.1 per₂.2
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      exact ordinary_ordinary hn (a₁ := 0) (b₁ := 1) (a₂ := s₂) (b₂ := t₂) (by omega) (by omega)
        (by omega) (by omega) per₁.1 per₁.2 per₂.1 per₂.2
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      obtain ⟨k1, k2, -⟩ := h₂.caps_c_F hW₂ hc2 hph₂
      rw [hwuZ] at k1
      exfalso
      refine contra_full_hole hn (f := wordA F) (h := 0) per₁.1 per₂.1 (x := (span F : ℤ) - u)
        (y := (span F : ℤ) - 1) (by omega) (hLe _ (by omega) (by omega)) (by omega)
        (hLe _ (by omega) (le_refl _)) ?_ ?_
      · have : (span F : ℤ) - 1 - ((span F : ℤ) - u) = u - 1 := by ring
        rw [this]; exact hgu
      · rw [k1, e3]; omega
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      obtain ⟨k1, k2⟩ := h₂.caps_d_F hW₂ hc2 hph₂
      rw [hwuZ] at k1
      exfalso
      refine contra_full_hole hn (f := wordB F) (h := 1) per₁.2 per₂.2 (x := 1) (y := u)
        le_rfl (hLe _ (by omega) (by omega)) (by omega) (hLe _ (by omega) (by omega)) hgu ?_
      rw [k1, e2]; omega
  · -- case (b)
    rw [hc1] at per₁ hbits
    simp only [holesA, holesB] at per₁
    simp only [holesA, holesB]
    simp only [CaseBits] at hbits
    cases hc2 : χ₂.ω.case
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      exact ordinary_ordinary hn (a₁ := 1) (b₁ := 0) (a₂ := t₂) (b₂ := s₂) (by omega) (by omega)
        (by omega) (by omega) per₁.1 per₁.2 per₂.1 per₂.2
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      exact ordinary_ordinary hn (a₁ := 1) (b₁ := 0) (a₂ := s₂) (b₂ := t₂) (by omega) (by omega)
        (by omega) (by omega) per₁.1 per₁.2 per₂.1 per₂.2
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      obtain ⟨k1, k2, -⟩ := h₂.caps_c_F hW₂ hc2 hph₂
      exfalso
      refine contra_full_hole hn (f := wordA F) (h := 1) per₁.1 per₂.1 (x := 1)
        (y := (span F : ℤ) - Q) le_rfl (hLe _ (by omega) (by omega)) (by omega)
        (hLe _ (by omega) (by omega)) ?_ ?_
      · have := hn.gdvd_NQ
        have e : ((span F : ℤ) - Q) - 1 = ((span F : ℤ) - Q) - 1 := rfl
        exact this
      · rw [k2, e1]; omega
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      obtain ⟨k1, k2⟩ := h₂.caps_d_F hW₂ hc2 hph₂
      exfalso
      refine contra_full_hole hn (f := wordB F) (h := 0) per₁.2 per₂.2 (x := Q)
        (y := (span F : ℤ) - 1) (by omega) (hLe _ (by omega) (by omega)) (by omega)
        (hLe _ (by omega) (le_refl _)) ?_ ?_
      · have := dvd_sub hn.gdvd_N hn.gdvd_Q
        rwa [hLz] at this
      · rw [k2, e4]; omega
  · exact absurd hc1 hc
  · -- case (d)
    rw [hc1] at per₁ hbits
    simp only [holesA, holesB] at per₁
    simp only [holesA, holesB]
    simp only [CaseBits] at hbits
    cases hc2 : χ₂.ω.case
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      exact d_ordinary hn (a₂ := t₂) (b₂ := s₂) per₁.1 per₁.2 per₂.1 per₂.2
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      exact d_ordinary hn (a₂ := s₂) (b₂ := t₂) per₁.1 per₁.2 per₂.1 per₂.2
    · rw [hc2] at per₂; simp only [holesA, holesB] at per₂
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h₂.caps_c_F hW₂ hc2 hph₂
      rw [hwuZ] at k1 k5 k6
      exfalso
      have hpQ' : p < Q ∨ Q < p := by
        rcases lt_trichotomy p Q with h | h | h
        · exact Or.inl h
        · exact absurd (h ▸ dvd_rfl) hpQ
        · exact Or.inr h
      rcases hpQ' with hlt | hlt
      · -- `B` has the full period `p` against two exceptional residues of `Q`
        have hT : ∀ t ∈ ({t₂, s₂} : Finset ℤ), 0 ≤ t ∧ t ≤ (u : ℤ) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> omega
        have hcd : ({t₂, s₂} : Finset ℤ).card ≤ 2 := Finset.card_le_two
        have key : ∀ x y : ℤ, 1 ≤ x → x ≤ (span F : ℤ) - 1 → 1 ≤ y → y ≤ (span F : ℤ) - 1 →
            (Nat.gcd p Q : ℤ) ∣ y - x → wordB F x = wordB F y := fun x y hx hxL hy hyL hd =>
          eq_of_full_two_holes (by omega) hlt huQ hT hcd (by have := hn.len_QL; omega) per₁.2
            per₂.2 hx (hLe _ hx hxL) hy (hLe _ hy hyL) hd
        have hd0 : (Nat.gcd p Q : ℤ) ∣ (span F : ℤ) - u := by
          have := hn.gdvd_Nu; exact this
        rcases Nat.eq_zero_or_pos t₂.toNat with ht0 | ht0
        · have ht0' : t₂ = 0 := by omega
          rcases eq_or_lt_of_le hs2 with hsu | hsu
          · -- `s₂ = u`
            have := key 1 u le_rfl (by omega) (by omega) (by omega) hgu
            rw [e2, ← hsu, k4] at this
            omega
          · have := key s₂ ((span F : ℤ) - u + s₂) (by omega) (by omega) (by omega) (by omega)
              (by have e : (span F : ℤ) - u + s₂ - s₂ = (span F : ℤ) - u := by ring
                  rw [e]; exact hd0)
            rw [k4, k6 hsu] at this
            omega
        · have := key t₂ ((span F : ℤ) - u + t₂) (by omega) (by omega) (by omega) (by omega)
            (by have e : (span F : ℤ) - u + t₂ - t₂ = (span F : ℤ) - u := by ring
                rw [e]; exact hd0)
          rw [k3 (by omega), k5] at this
          omega
      · -- `A` has the full period `Q` against the two exceptional residues `0, 1` of `p`
        have hT : ∀ t ∈ ({0, 1} : Finset ℤ), 0 ≤ t ∧ t ≤ ((1 : ℕ) : ℤ) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> simp
        have hcd : ({0, 1} : Finset ℤ).card ≤ 2 := Finset.card_le_two
        have hx := eq_of_full_two_holes (a := Q) (b := p) (u := 1) (L := span F - 1) (by omega)
          hlt (by omega) hT hcd (by have := hn.len_p; omega) per₂.1 per₁.1
          (x := (span F : ℤ) - u) (y := (span F : ℤ) - 1) (by omega)
          (hLe _ (by omega) (by omega)) (by omega) (hLe _ (by omega) (le_refl _))
          (by
            rw [Nat.gcd_comm]
            have : (span F : ℤ) - 1 - ((span F : ℤ) - u) = u - 1 := by ring
            rw [this]; exact hgu)
        rw [k1, e3] at hx
        omega
    · exact absurd ⟨hc1, hc2⟩ hdd

end SmallOverlap
end GluingCore
