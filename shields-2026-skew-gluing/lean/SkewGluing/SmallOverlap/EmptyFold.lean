import SkewGluing.SmallOverlap.EmptyBuild

/-!
# A proper root of width zero: the period-`g` root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the case of an empty root.

* `Chart.IsProperRoot.exists_emptyRoot_gcd`: if a diagram has a proper root of width zero and
  period `p` and another proper root of period `Q`, neither period dividing the other and
  `g = gcd p Q > 1`, then it has a proper root of period `g` and width zero.  (A mixed partner is
  excluded by `Chart.IsProperRoot.empty_mixed_false`; the other partners give the block
  periodicity of `Chart.IsProperRoot.empty_ordinary_periodic`.)

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

/-- A legal mark with empty copy has the attachment case (a), so it is not mixed. -/
theorem MarkedInner.not_isMixed_of_W_eq_empty {ω : MarkedInner} (h : ω.IsLegal) (hW : ω.W = ∅) :
    ¬ ω.case.IsMixed := by
  have : ω.case = .a := by
    rcases h.1.2 with he | hn
    · exact he.2.2
    · exact absurd hW hn.1.ne_empty
  simp [AttachCase.IsMixed, this]

/-- The parent presented by a proper root is connected skew, and so is `F`. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.isConnectedSkew {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) : IsConnectedSkew F := by
  obtain ⟨t, ht⟩ := h.2.1
  rw [ht]
  exact isConnectedSkew_translate t h.parent_conn

/-- The block data of the boundary words of `F` from period-`g` periodicity except at the
residue zero. -/
theorem blockData_of_periodExcept {F : Diagram} (hF : IsConnectedSkew F) {g : ℕ} (hg : 2 ≤ g)
    (hdvd : g ∣ span F) (hlt : g < span F)
    (hA : PeriodWords.PeriodExcept (span F - 1) g {0} (wordA F))
    (hB : PeriodWords.PeriodExcept (span F - 1) g {0} (wordB F)) :
    BlockData g (span F) (fun k : ℕ => wordA F k) (fun k : ℕ => wordB F k) := by
  refine ⟨isBitData_of_isConnectedSkew hF, ?_, hdvd, hg, hlt⟩
  intro n hn1 hn2 hmod
  have hmem : (n : ℤ) ∈ Finset.Icc (1 : ℤ) (((span F - 1 : ℕ) : ℤ) - g) := by
    rw [Finset.mem_Icc]; push_cast [Nat.cast_sub (by omega : 1 ≤ span F)]; omega
  have hS : (n : ℤ) % (g : ℤ) ∉ ({0} : Finset ℤ) := by
    simp only [Finset.mem_singleton]
    intro h
    apply hmod
    omega
  have e : ((n + g : ℕ) : ℤ) = (n : ℤ) + g := by push_cast; ring
  refine ⟨?_, ?_⟩
  · change wordA F n = wordA F ((n + g : ℕ) : ℤ)
    rw [e]; exact hA n hmem hS
  · change wordB F n = wordB F ((n + g : ℕ) : ℤ)
    rw [e]; exact hB n hmem hS

/-- **`lem:gluing-small`, empty root.**  A diagram with a proper root of width zero and period `p`
and another proper root of period `Q`, neither period dividing the other, with `g = gcd p Q > 1`,
has a proper root of period `g` and width zero. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.exists_emptyRoot_gcd {χ₁ χ₂ : Chart} {F : Diagram}
    {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q) (hW₁ : χ₁.ω.W = ∅)
    (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hg : 1 < Nat.gcd p Q) :
    ∃ χ : Chart, χ.IsProperRoot F (Nat.gcd p Q) ∧ χ.ω.W = ∅ := by
  have hord : χ₂.ω.W = ∅ ∨ ¬ χ₂.ω.case.IsMixed := by
    by_cases hW₂ : χ₂.ω.W = ∅
    · exact Or.inl hW₂
    · refine Or.inr fun hmix => ?_
      exact h₁.empty_mixed_false h₂ hW₁ (Finset.nonempty_iff_ne_empty.mpr hW₂) hmix hpQ hQp
  have hper := h₁.empty_ordinary_periodic h₂ hW₁ hord hpQ hQp
  obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
  have hw1 : χ₁.ω.width = 0 := width_eq_zero_of_eq_empty hW₁
  have hNp : span F = span χ₁.D * p := by
    have : (span F : ℤ) = (span χ₁.D : ℤ) * p := by rw [hN1, hw1]; simp
    exact_mod_cast this
  have hgp : Nat.gcd p Q ∣ p := Nat.gcd_dvd_left p Q
  have hgle : Nat.gcd p Q ≤ p := Nat.le_of_dvd (by omega) hgp
  have hrp : 2 * p ≤ span χ₁.D * p := Nat.mul_le_mul_right p hr
  have hdvd : Nat.gcd p Q ∣ span F := by rw [hNp]; exact Dvd.dvd.mul_left hgp _
  have hbd := blockData_of_periodExcept h₁.isConnectedSkew hg hdvd (by omega) hper.1 hper.2
  obtain ⟨χ, hχ, hch, hper', hW⟩ := exists_emptyRoot_of_blockData h₁.isConnectedSkew hbd
  exact ⟨χ, ⟨hχ, hch, hper'⟩, hW⟩

end SmallOverlap
end SkewGluing
