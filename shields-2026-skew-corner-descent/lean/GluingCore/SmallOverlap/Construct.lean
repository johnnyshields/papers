/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/Construct.lean`. -/
import GluingCore.SmallOverlap.InnerOuter

/-!
# The singleton root of period `g`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the singleton construction: from the period-`g` singleton coding
`eq:gluing-singleton` of the boundary words of a diagram `F` a legal width-one mark and a connected
outer are read off and compose to `F`.

* `eq_of_periodExcept_base`: two words with the same period-`g` constraints are equal as soon as
  they agree on the first `g` positions off the exceptional residues and at the exceptional
  positions.
* `priv_const`, `PrivateData`: the bookkeeping of the private classes.

Sorry-free.
-/

namespace GluingCore

open MarkedInner

namespace SmallOverlap

theorem eq_of_periodExcept_base {L g : ℕ} {S : Finset ℤ} {W₁ W₂ : ℤ → ℤ} (hg : 0 < g)
    (h1 : PeriodWords.PeriodExcept L g S W₁)
    (h2 : PeriodWords.PeriodExcept L g S W₂)
    (hbase : ∀ x : ℤ, 1 ≤ x → x ≤ g → x % (g : ℤ) ∉ S → W₁ x = W₂ x)
    (hhole : ∀ x : ℤ, 1 ≤ x → x ≤ L → x % (g : ℤ) ∈ S → W₁ x = W₂ x) :
    ∀ x : ℤ, 1 ≤ x → x ≤ L → W₁ x = W₂ x := by
  intro x hx1 hx2
  by_cases hS : x % (g : ℤ) ∈ S
  · exact hhole x hx1 hx2 hS
  · have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
    obtain ⟨b, hb1, hb2, hbm, hbd⟩ : ∃ b : ℤ, 1 ≤ b ∧ b ≤ g ∧ b % (g : ℤ) = x % (g : ℤ) ∧
        (g : ℤ) ∣ x - b ∧ b ≤ x := by
      by_cases h0 : x % (g : ℤ) = 0
      · refine ⟨g, by omega, le_rfl, by simp [h0], ?_, ?_⟩
        · exact Int.dvd_of_emod_eq_zero (by omega) |> fun hh => by
            have : (g : ℤ) ∣ x := Int.dvd_of_emod_eq_zero h0
            exact dvd_sub this dvd_rfl
        · have : (g : ℤ) ∣ x := Int.dvd_of_emod_eq_zero h0
          obtain ⟨k, hk⟩ := this
          have : 0 < k := by
            by_contra hk0
            have : (g : ℤ) * k ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hgZ.le (by omega)
            omega
          nlinarith
      · refine ⟨x % (g : ℤ), by have := Int.emod_nonneg x hgZ.ne'; omega,
          (Int.emod_lt_of_pos x hgZ).le, by rw [Int.emod_emod_of_dvd _ dvd_rfl], ?_,
          by
            have h3 := Int.mul_ediv_add_emod x g
            have h4 : 0 ≤ x / g := Int.ediv_nonneg (by omega) hgZ.le
            nlinarith⟩
        exact ⟨x / g, by have := Int.mul_ediv_add_emod x g; linarith⟩
    have hbS : b % (g : ℤ) ∉ S := by rw [hbm]; exact hS
    have e1 := periodExcept_eq_of_dvd h1 hg hb1 hx2 hbd.2 hbd.1 hbS
    have e2 := periodExcept_eq_of_dvd h2 hg hb1 hx2 hbd.2 hbd.1 hbS
    rw [← e1, ← e2]
    exact hbase b hb1 hb2 hbS

/-- Class constants: a word with period `g` except at residues in `{0, 1}` repeats its values at
the private residues `2, …, g - 1` from block to block. -/
theorem priv_const {L g : ℕ} {S : Finset ℤ} {W : ℤ → ℤ} (hg : 2 ≤ g)
    (hW : PeriodWords.PeriodExcept L g S W) (hS : ∀ s ∈ S, s = 0 ∨ s = 1) {j z : ℕ}
    (hz1 : 2 ≤ z) (hz2 : z < g) (hjz : j * g + z ≤ L) :
    W ((j * g + z : ℕ) : ℤ) = W (z : ℤ) := by
  have hdvd : (g : ℤ) ∣ ((j * g + z : ℕ) : ℤ) - z := ⟨j, by push_cast; ring⟩
  have hnS : (z : ℤ) % (g : ℤ) ∉ S := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    intro hh
    have := hS _ hh
    omega
  exact (periodExcept_eq_of_dvd hW (by omega) (x := (z : ℤ)) (y := ((j * g + z : ℕ) : ℤ))
    (by omega) (by omega) (by push_cast; nlinarith) hdvd hnS).symm

/-- The outer bits sampled at the block starts form bit data of span `M`. -/
theorem outer_isBitData {F : Diagram} (hF : IsConnectedSkew F) {g M : ℕ} (hg : 2 ≤ g)
    (hM : 2 ≤ M) (hN : span F = M * g + 1) {SA SB : Finset ℤ}
    (hA : PeriodWords.PeriodExcept (span F - 1) g SA (wordA F))
    (hB : PeriodWords.PeriodExcept (span F - 1) g SB (wordB F))
    (hSA : ∀ s ∈ SA, s = 0 ∨ s = 1) (hSB : ∀ s ∈ SB, s = 0 ∨ s = 1)
    (hfirst : wordA F 1 = wordB F 1) (hpen : heightWord (wA F) (wB F) (g - 1) = 1)
    (hend : wordA F ((M * g : ℕ) : ℤ) = wordB F ((M * g : ℕ) : ℤ)) {fA fB : ℕ → ℤ}
    (hbits : ∀ j, 1 ≤ j → j + 1 ≤ M → (fA j = 0 ∨ fA j = 1) ∧ (fB j = 0 ∨ fB j = 1))
    (hstep : ∀ j, 1 ≤ j → j + 1 ≤ M → fA j - fB j =
      (wordA F ((j * g : ℕ) : ℤ) - wordB F ((j * g : ℕ) : ℤ)) +
        (wordA F ((j * g + 1 : ℕ) : ℤ) - wordB F ((j * g + 1 : ℕ) : ℤ))) :
    IsBitData M fA fB := by
  have hL : span F - 1 = M * g := by omega
  have hp : ∀ j z, j + 1 ≤ M → 2 ≤ z → z < g →
      wA F (j * g + z) = wA F z ∧ wB F (j * g + z) = wB F z := by
    intro j z hj hz1 hz2
    have hjz : j * g + z ≤ span F - 1 := by
      have : (j + 1) * g ≤ M * g := Nat.mul_le_mul_right g hj
      have : (j + 1) * g = j * g + g := by ring
      omega
    exact ⟨priv_const hg hA hSA hz1 hz2 hjz, priv_const hg hB hSB hz1 hz2 hjz⟩
  have h1 : heightWord (wA F) (wB F) 1 = 1 + (wA F 1 - wB F 1) := by
    simp [heightWord]
  have hzero : heightWord (wA F) (wB F) (g - 1) = heightWord (wA F) (wB F) 1 := by
    rw [hpen, h1]
    have : wA F 1 = wB F 1 := by simpa [wA, wB] using hfirst
    omega
  have hH := heightWord_outer_eq (A := wA F) (B := wB F) (fA := fA) (fB := fB) (g := g) (M := M)
    hg hp hzero (by simpa [wA, wB] using hfirst) hstep
  have hlast : heightWord (wA F) (wB F) ((M - 1) * g + 1) = 1 := by
    have hh := heightWord_last_block (A := wA F) (B := wB F) (g := g) (j := M - 1) hg
      (fun z h1 h2 => hp (M - 1) z (by omega) h1 h2) hzero (by
        have e : M - 1 + 1 = M := by omega
        rw [e]; simpa [wA, wB] using hend)
    have e : M - 1 + 1 = M := by omega
    rw [e] at hh
    obtain ⟨-, -, -, hl⟩ := isBitData_of_isConnectedSkew hF
    have hl' : heightWord (wA F) (wB F) (M * g) = 1 := by
      have := hl
      rw [hL] at this
      exact this
    rw [← hh]; exact hl'
  exact IsBitData.outer_of_heights hF hN hM hg hbits hH hlast

end SmallOverlap
end GluingCore
