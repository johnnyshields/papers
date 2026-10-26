/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/WordsEq.lean`. -/
import GluingCore.SmallOverlap.ConstructBasic

/-!
# The words of the composite of a width-one mark with an outer

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the singleton construction.

For a legal width-one mark `ω` of period `g`, case (a), (b) or (d), and a connected outer `D` of
span `M` whose bits are sampled from the words of `F` at the holes, the boundary words of
`D ∘_ω E` and of `F` agree at every position `1, …, M g`, provided `F` has the period-`g` coding
of `eq:gluing-singleton` and the two words agree on the first block
(`words_eq_a`, `words_eq_b`, `words_eq_d`).

Sorry-free.
-/

namespace GluingCore

open MarkedInner

namespace SmallOverlap

/-- A position in `[1, M g]` with `x % g = 0` is `j g` with `1 ≤ j ≤ M`. -/
theorem exists_mul_of_emod_zero {g M : ℕ} (hg : 0 < g) {x : ℤ} (hx1 : 1 ≤ x)
    (hx2 : x ≤ (M : ℤ) * g) (h : x % (g : ℤ) = 0) : ∃ j : ℤ, x = j * g ∧ 1 ≤ j ∧ j ≤ M := by
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero h
  refine ⟨j, by rw [hj]; ring, ?_, ?_⟩
  · by_contra hc
    have : (g : ℤ) * j ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hgZ.le (by omega)
    omega
  · by_contra hc
    have : (g : ℤ) * (M + 1) ≤ g * j := Int.mul_le_mul_of_nonneg_left (by omega) hgZ.le
    nlinarith

/-- A position in `[1, M g]` with `x % g = 1` and `g ≥ 2` is `j g + 1` with `0 ≤ j ≤ M - 1`. -/
theorem exists_mul_add_one_of_emod_one {g M : ℕ} (hg : 2 ≤ g) {x : ℤ} (hx1 : 1 ≤ x)
    (hx2 : x ≤ (M : ℤ) * g) (h : x % (g : ℤ) = 1) :
    ∃ j : ℤ, x = j * g + 1 ∧ 0 ≤ j ∧ j + 1 ≤ M := by
  have hgZ : (2 : ℤ) ≤ g := by exact_mod_cast hg
  have h1 := Int.mul_ediv_add_emod x g
  have h0 : 0 ≤ x / g := Int.ediv_nonneg (by omega) (by omega)
  refine ⟨x / g, by rw [h] at h1; linarith, h0, ?_⟩
  by_contra hc
  have : (g : ℤ) * (M : ℤ) ≤ g * (x / g) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [h] at h1
  nlinarith

theorem words_eq_a {ω : MarkedInner} {D F : Diagram} {g M : ℕ} (hg : 2 ≤ g) (hM : 2 ≤ M)
    (hlegal : ω.IsLegalNonempty) (hca : ω.case = .a) (hwZ : ω.widthZ = 1)
    (hq : ω.period = g) (hD : IsConnectedSkew D) (hDsp : span D = M)
    (hcsp : span (ω.compose D) = M * g + 1)
    (hfirst : ∀ x : ℤ, 1 ≤ x → x < g →
      wordA (ω.compose D) x = wordA F x ∧ wordB (ω.compose D) x = wordB F x)
    (hDA : ∀ j : ℤ, 1 ≤ j → j < M → wordA D j = wordA F (j * g))
    (hDB : ∀ j : ℤ, 1 ≤ j → j < M → wordB D j = wordB F (j * g + 1))
    (hA : PeriodWords.PeriodExcept (M * g) g {0} (wordA F))
    (hB : PeriodWords.PeriodExcept (M * g) g {1} (wordB F))
    (hBg : wordB F g = 0) (hAN : wordA F ((M : ℤ) * g) = 0) :
    ∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) * g →
      wordA (ω.compose D) x = wordA F x ∧ wordB (ω.compose D) x = wordB F x := by
  have hgp : 0 < g := by omega
  have hgZ : (2 : ℤ) ≤ g := by exact_mod_cast hg
  have hph := hlegal.isPhases_one hwZ
  obtain ⟨pA, pB⟩ := hlegal.gluing_coding_periodic hD hph
  have hpt : ω.period.toNat = g := by rw [hq]; simp
  rw [hpt, hcsp, hca] at pA pB
  simp only [holesA, holesB, Nat.add_sub_cancel] at pA pB
  obtain ⟨hlo, hup⟩ := hlegal.attach.1 hca
  have hu := hlegal.upperH_bits_one hwZ hup
  have hl := hlegal.lowerH_bits_one hwZ hlo
  obtain ⟨-, -, cp3, -⟩ := hlegal.caps_a hD hca hph
  have hgM : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
  have hAeq : ∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) * g → wordA (ω.compose D) x = wordA F x := by
    refine eq_of_periodExcept_base hgp pA hA ?_ ?_
    · intro x hx1 hx2 hx3
      have : x < g := by
        rcases lt_or_eq_of_le hx2 with h | h
        · exact h
        · subst h; simp at hx3
      exact (hfirst x hx1 this).1
    · intro x hx1 hx2 hx3
      simp only [Finset.mem_singleton] at hx3
      obtain ⟨j, rfl, hj1, hj2⟩ := exists_mul_of_emod_zero hgp hx1 (by exact_mod_cast hx2) hx3
      rcases lt_or_eq_of_le hj2 with hjM | hjM
      · obtain ⟨c1, -, -⟩ := hlegal.ordinary_word_hole_a hD hca hwZ (j := j) hj1
          (by rw [hDsp]; exact_mod_cast hjM)
        rw [hq] at c1
        have hu1 : ω.lo ((g : ℤ) - 1) - ω.lo g = 0 := by rw [← hq]; exact hu.1
        rw [c1, hDA j hj1 hjM, hu1]
        ring
      · subst hjM
        have e : ((span (ω.compose D) : ℕ) : ℤ) - ω.widthZ + 0 = (M : ℤ) * g := by
          rw [hcsp, hwZ]; push_cast; ring
        rw [e] at cp3
        rw [cp3, hAN]
  refine fun x hx1 hx2 => ⟨hAeq x hx1 hx2, ?_⟩
  refine eq_of_periodExcept_base hgp pB hB ?_ ?_ x hx1 hx2
  · intro x hx1 hx2 hx3
    rcases lt_or_eq_of_le hx2 with h | h
    · exact (hfirst x hx1 h).2
    · subst h
      have hj := (hlegal.ordinary_word_hole_a hD hca hwZ (j := 1) le_rfl
        (by rw [hDsp]; exact_mod_cast hM)).2.2
      rw [hq] at hj
      simpa [hBg] using hj
  · intro x hx1 hx2 hx3
    simp only [Finset.mem_singleton] at hx3
    obtain ⟨j, rfl, hj1, hj2⟩ := exists_mul_add_one_of_emod_one hg hx1 (by exact_mod_cast hx2) hx3
    rcases eq_or_lt_of_le hj1 with hj0 | hj0
    · subst hj0
      simpa using (hfirst 1 le_rfl (by omega)).2
    · obtain ⟨-, c2, -⟩ := hlegal.ordinary_word_hole_a hD hca hwZ (j := j) (by omega)
        (by rw [hDsp]; exact_mod_cast (by omega : j < M))
      rw [hq] at c2
      rw [c2, hDB j (by omega) (by omega), hl.2]
      ring

theorem words_eq_b {ω : MarkedInner} {D F : Diagram} {g M : ℕ} (hg : 2 ≤ g) (hM : 2 ≤ M)
    (hlegal : ω.IsLegalNonempty) (hcb : ω.case = .b) (hwZ : ω.widthZ = 1)
    (hq : ω.period = g) (hD : IsConnectedSkew D) (hDsp : span D = M)
    (hcsp : span (ω.compose D) = M * g + 1)
    (hfirst : ∀ x : ℤ, 1 ≤ x → x < g →
      wordA (ω.compose D) x = wordA F x ∧ wordB (ω.compose D) x = wordB F x)
    (hDA : ∀ j : ℤ, 1 ≤ j → j < M → wordA D j = 1 - wordB F (j * g))
    (hDB : ∀ j : ℤ, 1 ≤ j → j < M → wordB D j = 1 - wordA F (j * g + 1))
    (hA : PeriodWords.PeriodExcept (M * g) g {1} (wordA F))
    (hB : PeriodWords.PeriodExcept (M * g) g {0} (wordB F))
    (hAg : wordA F g = 1) (hBN : wordB F ((M : ℤ) * g) = 1) :
    ∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) * g →
      wordA (ω.compose D) x = wordA F x ∧ wordB (ω.compose D) x = wordB F x := by
  have hgp : 0 < g := by omega
  have hgZ : (2 : ℤ) ≤ g := by exact_mod_cast hg
  have hph := hlegal.isPhases_one hwZ
  obtain ⟨pA, pB⟩ := hlegal.gluing_coding_periodic hD hph
  have hpt : ω.period.toNat = g := by rw [hq]; simp
  rw [hpt, hcsp, hcb] at pA pB
  simp only [holesA, holesB, Nat.add_sub_cancel] at pA pB
  obtain ⟨hlo, hup⟩ := hlegal.attach.2.1 hcb
  have hu := hlegal.upperV_bits_one hwZ hup
  have hl := hlegal.lowerV_bits_one hwZ hlo
  obtain ⟨-, -, cp3, -⟩ := hlegal.caps_b hD hcb hph
  have hgM : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
  have hBeq : ∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) * g → wordB (ω.compose D) x = wordB F x := by
    refine eq_of_periodExcept_base hgp pB hB ?_ ?_
    · intro x hx1 hx2 hx3
      have : x < g := by
        rcases lt_or_eq_of_le hx2 with h | h
        · exact h
        · subst h; simp at hx3
      exact (hfirst x hx1 this).2
    · intro x hx1 hx2 hx3
      simp only [Finset.mem_singleton] at hx3
      obtain ⟨j, rfl, hj1, hj2⟩ := exists_mul_of_emod_zero hgp hx1 (by exact_mod_cast hx2) hx3
      rcases lt_or_eq_of_le hj2 with hjM | hjM
      · obtain ⟨-, c2, -⟩ := hlegal.ordinary_word_hole_b hD hcb hwZ (j := j) hj1
          (by rw [hDsp]; exact_mod_cast hjM)
        rw [hq] at c2
        have hu1 : ω.hi ((g : ℤ) - 1) - ω.hi g = 1 := by rw [← hq]; exact hu.2
        rw [c2, hDA j hj1 hjM, hu1]
        ring
      · subst hjM
        have e : ((span (ω.compose D) : ℕ) : ℤ) - ω.widthZ + 0 = (M : ℤ) * g := by
          rw [hcsp, hwZ]; push_cast; ring
        rw [e] at cp3
        rw [cp3, hBN]
  refine fun x hx1 hx2 => ⟨?_, hBeq x hx1 hx2⟩
  refine eq_of_periodExcept_base hgp pA hA ?_ ?_ x hx1 hx2
  · intro x hx1 hx2 hx3
    rcases lt_or_eq_of_le hx2 with h | h
    · exact (hfirst x hx1 h).1
    · subst h
      have hj := (hlegal.ordinary_word_hole_b hD hcb hwZ (j := 1) le_rfl
        (by rw [hDsp]; exact_mod_cast hM)).2.2
      rw [hq] at hj
      simpa [hAg] using hj
  · intro x hx1 hx2 hx3
    simp only [Finset.mem_singleton] at hx3
    obtain ⟨j, rfl, hj1, hj2⟩ := exists_mul_add_one_of_emod_one hg hx1 (by exact_mod_cast hx2) hx3
    rcases eq_or_lt_of_le hj1 with hj0 | hj0
    · subst hj0
      simpa using (hfirst 1 le_rfl (by omega)).1
    · obtain ⟨c1, -, -⟩ := hlegal.ordinary_word_hole_b hD hcb hwZ (j := j) (by omega)
        (by rw [hDsp]; exact_mod_cast (by omega : j < M))
      rw [hq] at c1
      have hl1 : ω.lo 0 - ω.lo 1 = 1 := hl.1
      rw [c1, hDB j (by omega) (by omega), hl1]
      ring

theorem words_eq_d {ω : MarkedInner} {D F : Diagram} {g M : ℕ} (hg : 2 ≤ g) (hM : 2 ≤ M)
    (hlegal : ω.IsLegalNonempty) (hcd : ω.case = .d) (hwZ : ω.widthZ = 1)
    (hq : ω.period = g) (hD : IsConnectedSkew D) (hDsp : span D = M)
    (hcsp : span (ω.compose D) = M * g + 1)
    (hfirst : ∀ x : ℤ, 1 ≤ x → x < g →
      wordA (ω.compose D) x = wordA F x ∧ wordB (ω.compose D) x = wordB F x)
    (hDA : ∀ j : ℤ, 1 ≤ j → j < M → wordA D j = wordA F (j * g))
    (hDB : ∀ j : ℤ, 1 ≤ j → j < M → wordB D j = 1 - wordA F (j * g + 1))
    (hA : PeriodWords.PeriodExcept (M * g) g {0, 1} (wordA F))
    (hB : PeriodWords.PeriodExcept (M * g) g ∅ (wordB F))
    (hBg : wordB F g = 0) (hAN : wordA F ((M : ℤ) * g) = 0) :
    ∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) * g →
      wordA (ω.compose D) x = wordA F x ∧ wordB (ω.compose D) x = wordB F x := by
  have hgp : 0 < g := by omega
  have hgZ : (2 : ℤ) ≤ g := by exact_mod_cast hg
  have hph := hlegal.isPhases_one hwZ
  obtain ⟨pA, pB⟩ := hlegal.gluing_coding_periodic hD hph
  have hpt : ω.period.toNat = g := by rw [hq]; simp
  rw [hpt, hcsp, hcd] at pA pB
  simp only [holesA, holesB, Nat.add_sub_cancel] at pA pB
  obtain ⟨-, -, cp3, -, -, cp6⟩ := hlegal.caps_d hD hcd hph
  have hgM : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
  refine fun x hx1 hx2 => ⟨?_, ?_⟩
  · refine eq_of_periodExcept_base hgp pA hA ?_ ?_ x hx1 hx2
    · intro x hx1 hx2 hx3
      have : x < g := by
        rcases lt_or_eq_of_le hx2 with h | h
        · exact h
        · subst h; simp at hx3
      exact (hfirst x hx1 this).1
    · intro x hx1 hx2 hx3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx3
      rcases hx3 with hx3 | hx3
      · obtain ⟨j, rfl, hj1, hj2⟩ := exists_mul_of_emod_zero hgp hx1 (by exact_mod_cast hx2) hx3
        rcases lt_or_eq_of_le hj2 with hjM | hjM
        · obtain ⟨c1, -⟩ := hlegal.interface_d hD hcd hph (j := j) hj1
            (by rw [hDsp]; exact_mod_cast hjM)
          rw [hq] at c1
          have e : j * (g : ℤ) + 0 = j * g := by ring
          rw [e] at c1
          rw [c1, hDA j hj1 hjM]
        · subst hjM
          have e : ((span (ω.compose D) : ℕ) : ℤ) - ω.widthZ + 0 = (M : ℤ) * g := by
            rw [hcsp, hwZ]; push_cast; ring
          rw [e] at cp3
          rw [cp3, hAN]
      · obtain ⟨j, rfl, hj1, hj2⟩ := exists_mul_add_one_of_emod_one hg hx1
          (by exact_mod_cast hx2) hx3
        rcases eq_or_lt_of_le hj1 with hj0 | hj0
        · subst hj0
          simpa using (hfirst 1 le_rfl (by omega)).1
        · obtain ⟨-, c2⟩ := hlegal.interface_d hD hcd hph (j := j) (by omega)
            (by rw [hDsp]; exact_mod_cast (by omega : j < M))
          rw [hq] at c2
          have hs : (1 : ℤ) = 1 := rfl
          rw [c2, hDB j (by omega) (by omega)]
          ring
  · refine eq_of_periodExcept_base hgp pB hB ?_ ?_ x hx1 hx2
    · intro x hx1 hx2 hx3
      rcases lt_or_eq_of_le hx2 with h | h
      · exact (hfirst x hx1 h).2
      · subst h
        rw [hq] at cp6
        rw [cp6, hBg]
    · intro x _ _ hx3
      simp at hx3

end SmallOverlap
end GluingCore
