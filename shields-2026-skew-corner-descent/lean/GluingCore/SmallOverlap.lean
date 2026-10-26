/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap.lean`. -/
import GluingCore.SmallOverlap.SmallFinal

/-!
# Small overlaps: the gcd fold of a root of width zero or one

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`, `eq:gluing-singleton`).

A *proper root* of period `p` of a diagram `F` is a `Chart` `χ` with `χ.IsProperLegal`,
`χ.IsChartOf F` and `χ.period = p` (`Chart.IsProperRoot`).

* `Chart.IsProperRoot.singleton_table` (`eq:gluing-singleton`): the boundary coding of a root of
  width one at its own period, `SingletonTable`; `Chart.IsProperRoot.singleton_ends`: the end bits.
* `Chart.IsProperRoot.exists_emptyRoot_gcd`: a root of width zero and period `p`, and another
  proper root of period `Q` (neither period dividing the other), `g = gcd p Q > 1`, give a proper
  root of period `g` and width zero; its inner is the first `g` diagonals and its outer is read from
  the block starts (`exists_emptyRoot_of_blockData`); a mixed partner is impossible
  (`Chart.IsProperRoot.empty_mixed_false`).
* `Chart.IsProperRoot.exists_singletonRoot_gcd`: the same for width one: the period-`g` coding
  (`singleton_gperiodic`, `singleton_gperiodic_dd` with the drift argument of `drift_class_const`),
  the impossibility of mixed partners of an ordinary singleton (`SmallWords`), and the construction
  of the legal singleton mark and of the outer (`exists_singletonRoot_a`, `_b`, `_d`; case (c) by
  rotation).
* `Chart.IsProperRoot.exists_small_root_gcd`: the first assertion of `lem:gluing-small` in full:
  for roots of the same small width and `g = gcd p Q > 1` there is a proper root of period `g` and
  that width, including the equal and dividing periods and the equal small widths.
* `empty_singleton_coprime`: an empty root and a singleton root have coprime periods.
* `exists_least_small_root_dvd`: the least small-root period divides every proper root period, when
  the diagram has no two proper roots of coprime periods (`NoCoprimeRoots`).

**Not formalized here.**  The clause "every fork at this diagram glues" and the containment "all
fibers lie in the `p₀`-fiber" rest on `prop:gluing-divisible` and `lem:gluing-equal`;
`exists_least_small_root_dvd` is the constructive part that the assembly combines with
`Chart.IsProperLegal.equal_periods_same_fiber`.  `NoCoprimeRoots` is the consequence for a
line-inner-free diagram of `lem:gluing-lines` (coprime periods force line inners); it is supplied
by that lemma at the assembly.

Sorry-free.
-/

namespace GluingCore

open MarkedInner

/-- The period `p` is the period of a proper root of width `w` of `F`. -/
def SmallRootPeriod (F : Diagram) (w p : ℕ) : Prop :=
  ∃ χ : Chart, χ.IsProperRoot F p ∧ χ.ω.width = w

/-- No two proper roots of `F` have coprime periods.  By `lem:gluing-lines` this holds for a
diagram without proper line inners. -/
def NoCoprimeRoots (F : Diagram) : Prop :=
  ∀ (χ χ' : Chart) (p q : ℕ), χ.IsProperRoot F p → χ'.IsProperRoot F q → 1 < Nat.gcd p q

namespace SmallOverlap

/-- **`lem:gluing-small`, the first assertion.**  A diagram with a proper root of width `w ≤ 1` and
period `p` and another proper root of period `Q`, with `g = gcd p Q > 1`, has a proper root of
period `g` and the same width `w`. -/
theorem _root_.GluingCore.Chart.IsProperRoot.exists_small_root_gcd {χ₁ χ₂ : Chart} {F : Diagram}
    {p Q w : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q) (hw : w ≤ 1)
    (hw₁ : χ₁.ω.width = w) (hg : 1 < Nat.gcd p Q) :
    ∃ χ : Chart, χ.IsProperRoot F (Nat.gcd p Q) ∧ χ.ω.width = w := by
  by_cases hpQ : p ∣ Q
  · exact ⟨χ₁, by rw [Nat.gcd_eq_left hpQ]; exact h₁, hw₁⟩
  by_cases hQp : Q ∣ p
  · refine ⟨χ₂, by rw [Nat.gcd_eq_right hQp]; exact h₂, ?_⟩
    -- the width of the divisor root is the remainder `w` of the span
    obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
    obtain ⟨hm, hN2, hwQ, hQ2⟩ := h₂.arith
    obtain ⟨k, hk⟩ := hQp
    have hd : (Q : ℤ) ∣ (χ₂.ω.width : ℤ) - w := by
      have : (χ₂.ω.width : ℤ) - w = Q * (span χ₁.D * k - span χ₂.D) := by
        rw [hw₁] at hN1
        have : (p : ℤ) = Q * k := by exact_mod_cast hk
        rw [this] at hN1
        linarith
      rw [this]; exact dvd_mul_right _ _
    have hQ2' : (2 : ℤ) ≤ Q := by exact_mod_cast hQ2
    have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  have hQ0 : 0 < Q := by obtain ⟨-, -, -, h⟩ := h₂.arith; omega
  by_cases hW₁ : χ₁.ω.W = ∅
  · obtain ⟨χ, hχ, hW⟩ := h₁.exists_emptyRoot_gcd h₂ hW₁ hpQ hQp hg
    refine ⟨χ, hχ, ?_⟩
    have := width_eq_zero_of_eq_empty hW
    have h0 := width_eq_zero_of_eq_empty hW₁
    omega
  · have hw1 : χ₁.ω.width = 1 := by
      have hpos := h₁.1.2.2.2.width_pos_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hW₁)
      omega
    obtain ⟨χ, hχ, hχw⟩ := h₁.exists_singletonRoot_gcd h₂ hw1 hg hpQ hQp
    exact ⟨χ, hχ, by omega⟩

/-- An empty root and a singleton root have coprime periods: they divide `N` and `N - 1`. -/
theorem empty_singleton_coprime {χ₁ χ₂ : Chart} {F : Diagram} {p Q : ℕ}
    (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q) (hw₁ : χ₁.ω.width = 0)
    (hw₂ : χ₂.ω.width = 1) : Nat.gcd p Q = 1 := by
  obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
  obtain ⟨hm, hN2, -, hQ2⟩ := h₂.arith
  rw [hw₁] at hN1
  rw [hw₂] at hN2
  have hgp : (Nat.gcd p Q : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hgQ : (Nat.gcd p Q : ℤ) ∣ Q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)
  have hd : (Nat.gcd p Q : ℤ) ∣ 1 := by
    have : (1 : ℤ) = span χ₁.D * p - span χ₂.D * Q := by push_cast at hN1 hN2; linarith
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left hgp _) (Dvd.dvd.mul_left hgQ _)
  exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd

/-- Without proper roots of coprime periods, empty and singleton roots cannot both occur. -/
theorem not_empty_and_singleton {F : Diagram} (hF : NoCoprimeRoots F) {p q : ℕ} :
    ¬ (SmallRootPeriod F 0 p ∧ SmallRootPeriod F 1 q) := by
  rintro ⟨⟨χ₁, h₁, hw₁⟩, ⟨χ₂, h₂, hw₂⟩⟩
  have := hF χ₁ χ₂ p q h₁ h₂
  rw [empty_singleton_coprime h₁ h₂ hw₁ hw₂] at this
  omega

/-- **`lem:gluing-small`, the least small-root period.**  If no two proper roots of `F` have coprime
periods and `F` has a proper root of width `w ≤ 1`, the least period `p₀` of such a root exists and
divides the period of every proper root of `F`. -/
theorem exists_least_small_root_dvd {F : Diagram} (hF : NoCoprimeRoots F) {w : ℕ} (hw : w ≤ 1)
    (h : ∃ p, SmallRootPeriod F w p) :
    ∃ p₀, SmallRootPeriod F w p₀ ∧ (∀ p, SmallRootPeriod F w p → p₀ ≤ p) ∧
      ∀ (χ : Chart) (Q : ℕ), χ.IsProperRoot F Q → p₀ ∣ Q := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun p hp => Nat.find_min' h hp, ?_⟩
  intro χ Q hχ
  obtain ⟨χ₁, h₁, hw₁⟩ := Nat.find_spec h
  have hg := hF χ₁ χ _ Q h₁ hχ
  obtain ⟨χ', hχ', hw'⟩ := h₁.exists_small_root_gcd hχ hw hw₁ hg
  have hle := Nat.find_min' h (⟨χ', hχ', hw'⟩ : SmallRootPeriod F w (Nat.gcd (Nat.find h) Q))
  have hp0 : 0 < Nat.find h := by obtain ⟨-, -, -, h2⟩ := h₁.arith; omega
  have hge : Nat.gcd (Nat.find h) Q ≤ Nat.find h := Nat.le_of_dvd hp0 (Nat.gcd_dvd_left _ _)
  have heq : Nat.gcd (Nat.find h) Q = Nat.find h := le_antisymm hge hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

/-! ### Checked examples -/

section Examples

/-- The chart `(a) ∘ (row of b cells, empty mark)` of the row `(a b)`. -/
def emptyRowChart (a b : ℕ) : Chart := ⟨skewOf [a] [], emptyMarkH (skewOf [b] [])⟩

/-- The chart `(a) ∘ ω_{q,1}` of the row `(a q + 1)`, with the row mark of width one. -/
def singletonRowChart (a q : ℕ) (h : 2 ≤ q) : Chart :=
  ⟨skewOf [a] [], rowMark ⟨q, 1, h, by omega⟩⟩

/-- `(12) = (3) ∘ (4) = (2) ∘ (6)`: two empty roots, of periods `4` and `6`. -/
theorem emptyRowChart_4_root : (emptyRowChart 3 4).IsProperRoot (skewOf [12] []) 4 :=
  ⟨⟨by decide, by decide, by decide, isLegal_emptyMark (by decide)⟩, ⟨0, by decide +kernel⟩,
    by decide +kernel⟩

theorem emptyRowChart_6_root : (emptyRowChart 2 6).IsProperRoot (skewOf [12] []) 6 :=
  ⟨⟨by decide, by decide, by decide, isLegal_emptyMark (by decide)⟩, ⟨0, by decide +kernel⟩,
    by decide +kernel⟩

/-- The row `(12)` has a proper empty root of period `gcd 4 6 = 2`. -/
example : ∃ χ : Chart, χ.IsProperRoot (skewOf [12] []) 2 ∧ χ.ω.width = 0 := by
  have := emptyRowChart_4_root.exists_small_root_gcd emptyRowChart_6_root (w := 0) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  simpa using this

/-- `(13) = (3) ∘ ω_{4,1} = (2) ∘ ω_{6,1}`: two singleton roots, of periods `4` and `6`. -/
theorem singletonRowChart_4_root :
    (singletonRowChart 3 4 (by norm_num)).IsProperRoot (skewOf [13] []) 4 :=
  ⟨⟨by decide, by decide, by decide, rowMark_isLegal _⟩, ⟨0, by decide +kernel⟩,
    by decide +kernel⟩

theorem singletonRowChart_6_root :
    (singletonRowChart 2 6 (by norm_num)).IsProperRoot (skewOf [13] []) 6 :=
  ⟨⟨by decide, by decide, by decide, rowMark_isLegal _⟩, ⟨0, by decide +kernel⟩,
    by decide +kernel⟩

/-- The row `(13)` has a proper singleton root of period `gcd 4 6 = 2`. -/
example : ∃ χ : Chart, χ.IsProperRoot (skewOf [13] []) 2 ∧ χ.ω.width = 1 := by
  have := singletonRowChart_4_root.exists_small_root_gcd singletonRowChart_6_root (w := 1)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  simpa using this

/-- `eq:gluing-singleton` on the hook example: `(3) ∘ ω (2, 1)` has the singleton mark of case
(d) and period two; `A` has period two except at the residues `0, 1`, `B` has the full period, and
`B_1 = 1`, `B_0 = B_2 = 0`, with the end bits `A_1 = B_1 = 1`, `A_6 = B_6 = 0`. -/
example : PeriodWords.PeriodExcept 6 2 {0, 1} (wordA (compose (skewOf [3] []) hookInner)) ∧
    PeriodWords.PeriodExcept 6 2 ∅ (wordB (compose (skewOf [3] []) hookInner)) ∧
    wordB (compose (skewOf [3] []) hookInner) 1 = 1 ∧
    wordB (compose (skewOf [3] []) hookInner) 2 = 0 ∧
    wordA (compose (skewOf [3] []) hookInner) 1 = 1 ∧
    wordA (compose (skewOf [3] []) hookInner) 6 = 0 ∧
    wordB (compose (skewOf [3] []) hookInner) 6 = 0 := by
  decide +kernel

end Examples

end SmallOverlap
end GluingCore
