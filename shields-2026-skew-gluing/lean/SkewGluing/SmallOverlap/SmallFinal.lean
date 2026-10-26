import SkewGluing.SmallOverlap.SmallRoot
import SkewGluing.SmallOverlap.DDWords

/-!
# `lem:gluing-small`: a proper root of period `g` and width one

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`).

* `Chart.IsProperRoot.singleton_gperiodic_dd`: the period-`g` coding for two case-(d) roots, by the
  drift argument.
* `Chart.IsProperRoot.exists_singletonRoot_gcd_abd`: a diagram with a proper root of width one,
  period `p` and case (a), (b) or (d), and a proper root of period `Q`, neither period dividing
  the other, `g = gcd p Q > 1`, has a proper root of period `g` and width one.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

open PeriodWords

theorem _root_.SkewGluing.Chart.IsProperRoot.singleton_gperiodic_dd {χ₁ χ₂ : Chart}
    {F : Diagram} {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q)
    (hw₁ : χ₁.ω.width = 1) (hg : 1 < Nat.gcd p Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p)
    (hc1 : χ₁.ω.case = .d) (hc2 : χ₂.ω.case = .d) :
    PeriodExcept (span F - 1) (Nat.gcd p Q) {0, 1} (wordA F) ∧
    PeriodExcept (span F - 1) (Nat.gcd p Q) ∅ (wordB F) := by
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
  rw [hc1] at per₁
  rw [hc2] at per₂
  simp only [holesA, holesB] at per₁ per₂
  obtain ⟨l, u', hbits, e1, e2, e3, e4⟩ := h₁.singleton_ends hw₁
  rw [hc1] at hbits
  simp only [CaseBits] at hbits
  have htab := h₁.singleton_table hw₁
  rw [hc1] at htab
  obtain ⟨-, -, -, hBp⟩ := htab
  have hLz : ((span F - 1 : ℕ) : ℤ) = (span F : ℤ) - 1 := by
    have : 1 ≤ span F := by omega
    push_cast [Nat.cast_sub this]; rfl
  have hbd := isBitData_of_isConnectedSkew h₁.isConnectedSkew
  obtain ⟨-, hbits', hpos, -⟩ := hbd
  have hh1 : heightWord (fun k : ℕ => wordA F k) (fun k : ℕ => wordB F k) 1 = 1 := by
    simp [heightWord]
    omega
  have hhp := h₁.heightWord_pen hw₁
  refine dd_periodic hn (t₂ := t₂) (s₂ := s₂) per₁.1 per₁.2 per₂.1 per₂.2 (by omega) (by omega)
    (by rw [hLz, e3]; omega) hBp ?_ hh1 hhp
  intro x hx1 hx2
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = k := ⟨x.toNat, by omega⟩
  exact hbits' k (by omega) (by omega)

/-- Class zero of a word with period `g` except at residues avoiding `0`: `f g = f p` for a
multiple `p` of `g`. -/
theorem class_zero_eq {f : ℤ → ℤ} {L g p : ℕ} {S : Finset ℤ} (hf : PeriodExcept L g S f)
    (hg : 2 ≤ g) (h0 : (0 : ℤ) ∉ S) (hgp : g ∣ p) (hpL : p ≤ L) (hgp' : g ≤ p) :
    f (g : ℤ) = f (p : ℤ) := by
  obtain ⟨n, hn⟩ := hgp
  refine periodExcept_eq_of_dvd hf (by omega) (by omega) (by exact_mod_cast hpL)
    (by exact_mod_cast hgp') ⟨(n - 1 : ℤ), ?_⟩ (by simpa using h0)
  rw [hn]; push_cast; ring

/-- Class one of a word with period `g` except at residues avoiding `1`: `f 1 = f y` for
`y ≡ 1 (mod g)`. -/
theorem class_one_eq {f : ℤ → ℤ} {L g : ℕ} {S : Finset ℤ} (hf : PeriodExcept L g S f)
    (hg : 2 ≤ g) (h1 : (1 : ℤ) ∉ S) {y : ℤ} (hy1 : 1 ≤ y) (hyL : y ≤ L) (hd : (g : ℤ) ∣ y - 1) :
    f 1 = f y :=
  periodExcept_eq_of_dvd hf (by omega) le_rfl hyL hy1 hd
    (by rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact h1)

/-- **`lem:gluing-small`, the singleton construction.**  A diagram with a proper root of width one,
period `p` and case (a), (b) or (d), and a proper root of period `Q`, neither period dividing the
other, with `g = gcd p Q > 1`, has a proper root of period `g` and width one. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.exists_singletonRoot_gcd_abd {χ₁ χ₂ : Chart}
    {F : Diagram} {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q)
    (hw₁ : χ₁.ω.width = 1) (hg : 1 < Nat.gcd p Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p)
    (hc : χ₁.ω.case ≠ .c) :
    ∃ χ : Chart, χ.IsProperRoot F (Nat.gcd p Q) ∧ χ.ω.width = 1 := by
  have hper : PeriodExcept (span F - 1) (Nat.gcd p Q) (holesA χ₁.ω.case 1 0) (wordA F) ∧
      PeriodExcept (span F - 1) (Nat.gcd p Q) (holesB χ₁.ω.case 1 0) (wordB F) := by
    by_cases hdd : χ₁.ω.case = .d ∧ χ₂.ω.case = .d
    · have := h₁.singleton_gperiodic_dd h₂ hw₁ hg hpQ hQp hdd.1 hdd.2
      rw [hdd.1]
      simpa [holesA, holesB] using this
    · exact h₁.singleton_gperiodic h₂ hw₁ hg hpQ hQp hc hdd
  obtain ⟨r, m, u, hr, hm, hu1, huQ, hp2, hQ2, hNp, hNQ, hwu, hgu⟩ := h₁.small_arith h₂ hw₁ hg
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd p Q := ⟨_, rfl⟩
  rw [← hgdef] at hg hper ⊢
  have hgpd : g ∣ p := by rw [hgdef]; exact Nat.gcd_dvd_left p Q
  have hgQd : g ∣ Q := by rw [hgdef]; exact Nat.gcd_dvd_right p Q
  obtain ⟨n, hpn⟩ := hgpd
  have hgp0 : 0 < p := by omega
  have hgp_lt : g < p := by
    have hle : g ≤ p := Nat.le_of_dvd hgp0 ⟨n, hpn⟩
    rcases eq_or_lt_of_le hle with h | h
    · exact absurd (h ▸ hgQd) hpQ
    · exact h
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have : n ≤ 1 := by omega
    have : g * n ≤ g * 1 := Nat.mul_le_mul_left g this
    omega
  have hg2 : 2 ≤ g := hg
  have hMg : span F = (r * n) * g + 1 := by rw [hNp, hpn]; ring
  have hM2 : 2 ≤ r * n := by nlinarith
  have hLM : span F - 1 = (r * n) * g := by omega
  have hLz : ((span F - 1 : ℕ) : ℤ) = (span F : ℤ) - 1 := by
    have : 1 ≤ span F := by omega
    push_cast [Nat.cast_sub this]; rfl
  have hMgZ : (((r * n) * g : ℕ) : ℤ) = (span F : ℤ) - 1 := by rw [← hLz, hLM]
  obtain ⟨l, u', hbits, e1, e2, e3, e4⟩ := h₁.singleton_ends hw₁
  have htab := h₁.singleton_table hw₁
  have hpL : p ≤ span F - 1 := by
    have := Nat.mul_le_mul_right p hr
    omega
  have hbd := isBitData_of_isConnectedSkew h₁.isConnectedSkew
  obtain ⟨-, hbits', hpos, -⟩ := hbd
  have hhp := h₁.heightWord_pen hw₁
  have hpen : ∀ {SA SB : Finset ℤ}, PeriodExcept (span F - 1) g SA (wordA F) →
      PeriodExcept (span F - 1) g SB (wordB F) → (∀ s ∈ SA, s = 0 ∨ s = 1) →
      (∀ s ∈ SB, s = 0 ∨ s = 1) → wordA F 1 = wordB F 1 →
      heightWord (wA F) (wB F) (g - 1) = 1 := by
    intro SA SB hA hB hSA hSB hfirst
    refine drift_zero (A := wA F) (B := wB F) hg2 ⟨n, hpn⟩ hgp_lt (fun j z hjz hz1 hz2 => ?_)
      (fun k hk => hpos k (by omega)) ?_ hhp
    · have hjz' : j * g + z ≤ span F - 1 := by
        have : (j + 1) * g = j * g + g := by ring
        omega
      exact ⟨priv_const hg2 hA hSA hz1 hz2 hjz', priv_const hg2 hB hSB hz1 hz2 hjz'⟩
    · simp only [wA, wB, heightWord, Finset.range_one, Finset.sum_singleton, zero_add]
      simp only [Nat.cast_one]
      rw [hfirst]; ring
  cases hc1 : χ₁.ω.case
  · -- case (a)
    rw [hc1] at hper hbits htab
    simp only [holesA, holesB] at hper
    simp only [CaseBits] at hbits
    obtain ⟨-, -, hA1', hBp⟩ := htab
    have hBg : wordB F g = 0 := by
      rw [class_zero_eq hper.2 hg2 (by simp) ⟨n, hpn⟩ hpL hgp_lt.le]; exact hBp
    obtain ⟨χ, hχ1, hχ2, hχ3, hχ4, -⟩ := exists_singletonRoot_a h₁.isConnectedSkew hg2 hM2 hMg
      ⟨hper.1, hper.2, hA1', hBg⟩ (by rw [e1, hbits.1]) (by rw [e2, hbits.1])
      (by rw [hMgZ, e3, hbits.2]) (by rw [hMgZ, e4, hbits.2])
      (hpen hper.1 hper.2 (by simp) (by simp) (by rw [e1, e2]))
    exact ⟨χ, ⟨hχ1, hχ2, hχ3⟩, hχ4⟩
  · -- case (b)
    rw [hc1] at hper hbits htab
    simp only [holesA, holesB] at hper
    simp only [CaseBits] at hbits
    obtain ⟨-, -, hAp, hB1'⟩ := htab
    have hAg : wordA F g = 1 := by
      rw [class_zero_eq hper.1 hg2 (by simp) ⟨n, hpn⟩ hpL hgp_lt.le]; exact hAp
    obtain ⟨χ, hχ1, hχ2, hχ3, hχ4, -⟩ := exists_singletonRoot_b h₁.isConnectedSkew hg2 hM2 hMg
      ⟨hper.1, hper.2, hAg, hB1'⟩ (by rw [e1, hbits.1]) (by rw [e2, hbits.1])
      (by rw [hMgZ, e3, hbits.2]) (by rw [hMgZ, e4, hbits.2])
      (hpen hper.1 hper.2 (by simp) (by simp) (by rw [e1, e2]))
    exact ⟨χ, ⟨hχ1, hχ2, hχ3⟩, hχ4⟩
  · exact absurd hc1 hc
  · -- case (d)
    rw [hc1] at hper hbits htab
    simp only [holesA, holesB] at hper
    simp only [CaseBits] at hbits
    obtain ⟨-, -, hB1', hBp⟩ := htab
    have hBg : wordB F g = 0 := by
      have := eq_of_full (by omega) hper.2 (x := (g : ℤ)) (y := (p : ℤ)) (by omega)
        (by exact_mod_cast le_trans hgp_lt.le hpL) (by omega) (by exact_mod_cast hpL)
        (by
          obtain ⟨n', hn'⟩ := (⟨n, hpn⟩ : g ∣ p)
          exact ⟨(n' - 1 : ℤ), by rw [hn']; push_cast; ring⟩)
      rw [this]; exact hBp
    obtain ⟨χ, hχ1, hχ2, hχ3, hχ4, -⟩ := exists_singletonRoot_d h₁.isConnectedSkew hg2 hM2 hMg
      ⟨hper.1, hper.2, hB1', hBg⟩ (by rw [e1, hbits.1]) (by rw [e2, hbits.1])
      (by rw [hMgZ, e3, hbits.2]) (by rw [hMgZ, e4, hbits.2])
      (hpen hper.1 hper.2 (by intro s hs; simpa using hs) (by simp) (by rw [e1, e2]))
    exact ⟨χ, ⟨hχ1, hχ2, hχ3⟩, hχ4⟩

/-- **`lem:gluing-small`, first assertion, width one.**  A diagram with a proper root of width one
and period `p` and another proper root of period `Q`, with `g = gcd p Q > 1`, has a proper root of
period `g` and width one.  **Differs from the paper's route.**  Case (c) is obtained from case (d)
by rotation of the diagram, not by antitransposition. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.exists_singletonRoot_gcd {χ₁ χ₂ : Chart}
    {F : Diagram} {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q)
    (hw₁ : χ₁.ω.width = 1) (hg : 1 < Nat.gcd p Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) :
    ∃ χ : Chart, χ.IsProperRoot F (Nat.gcd p Q) ∧ χ.ω.width = 1 := by
  by_cases hc : χ₁.ω.case = .c
  · have hr₁ := h₁.rotate
    have hr₂ := h₂.rotate
    have hcr : χ₁.rotate.ω.case ≠ .c := by
      rw [Chart.rotate_ω, rotate_case, hc]; decide
    obtain ⟨χ, hχ, hχw⟩ := hr₁.exists_singletonRoot_gcd_abd hr₂
      (by rw [Chart.rotate_width]; exact hw₁) hg hpQ hQp hcr
    have := hχ.rotate
    rw [SkewGluing.rotate_rotate] at this
    exact ⟨χ.rotate, this, by rw [Chart.rotate_width]; exact hχw⟩
  · exact h₁.exists_singletonRoot_gcd_abd h₂ hw₁ hg hpQ hQp hc

end SmallOverlap
end SkewGluing
