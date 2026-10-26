/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MinimalFibers/LeastPeriod.lean`. -/
import GluingCore.MinimalFibers.Domination

/-!
# The least root period

Formalizes `shields-2026-skew-factor-gluing.tex`, «Minimizing a chart» (`cor:least-root-period`).

* `properPeriods F`: the periods of the proper legal charts of `F`.
* `least_root_period`: if `F` is rooted and has no proper chart with a line inner, its least proper
  period `p₀` divides every proper period, and the proper charts of period `p₀` are exactly the
  source-minimal charts of `F`.
* `Chart.IsSourceMinimal.period_dvd`: the period of any source-minimal chart with a nonline inner
  divides every proper period at its source.
* `row_seven_least_period`: the line-inner qualification, `(7) = (3) ∘_{(1)} (3) = (2) ∘_{(1)} (4)`:
  the least proper period two does not divide the period three.

The arithmetic is that of `GluingCore.Score` (`least_period_dvd`, `dvd_of_isScoreMinimal`,
`isScoreMinimal_iff_eq_least`); the geometric inputs are the period-`gcd` root of
`Chart.IsProperLegal.exists_gcd_root` and the coprime-period line inner of `lem:gluing-lines`.  No
Olson-Harris input is used.

Sorry-free.
-/

namespace GluingCore

/-- The periods of the proper legal charts of `F`. -/
def properPeriods (F : Diagram) : Set ℕ := {p | ∃ χ : Chart, χ.IsProperRoot F p}

/-- A proper chart has period at least two: `N_E = q + w ≥ 2` with `0 ≤ w < q`. -/
theorem Chart.IsProperLegal.two_le_period {χ : Chart} (h : χ.IsProperLegal) :
    2 ≤ χ.period.toNat := by
  have hspan : (span χ.ω.E : ℤ) = χ.period + χ.ω.width := h.2.2.2.1.span_eq
  have hwq : (χ.ω.width : ℤ) < χ.period := h.2.2.2.2.2.1.2
  have hE := two_le_span_of_two_le_card h.2.2.2.1.1 h.2.2.1
  have hq : (χ.period.toNat : ℤ) = χ.period := h.period_toNat
  have hq0 : 0 < χ.period := h.2.2.2.period_pos
  have : (2 : ℤ) ≤ span χ.ω.E := by exact_mod_cast hE
  have hw0 : (0 : ℤ) ≤ χ.ω.width := by positivity
  omega

theorem two_le_of_mem_properPeriods {F : Diagram} {p : ℕ} (hp : p ∈ properPeriods F) : 2 ≤ p := by
  obtain ⟨χ, h, -, hper⟩ := hp
  have := h.two_le_period
  have hq := h.period_toNat
  have : (χ.period.toNat : ℤ) = p := by rw [hq]; exact hper
  omega

theorem Chart.IsProperLegal.mem_properPeriods {F : Diagram} {χ : Chart} (h : χ.IsProperLegal)
    (c : χ.IsChartOf F) : χ.period.toNat ∈ properPeriods F :=
  ⟨χ, h.isProperRoot c⟩

/-- Folding: the `gcd` of two nondividing proper periods with `gcd > 1` is a proper period. -/
theorem gcd_mem_properPeriods {F : Diagram} {p q : ℕ} (hp : p ∈ properPeriods F)
    (hq : q ∈ properPeriods F) (hn₁ : ¬ p ∣ q) (hn₂ : ¬ q ∣ p) (hg : 1 < Nat.gcd p q) :
    Nat.gcd p q ∈ properPeriods F := by
  obtain ⟨χ₁, h₁, c₁, e₁⟩ := hp
  obtain ⟨χ₂, h₂, c₂, e₂⟩ := hq
  have e₁' : χ₁.period.toNat = p := by omega
  have e₂' : χ₂.period.toNat = q := by omega
  subst e₁' e₂'
  obtain ⟨ψ, hψ, cψ, hper⟩ := Chart.IsProperLegal.exists_gcd_root h₁ h₂ c₁ c₂ hn₁ hn₂ hg
  exact ⟨ψ, hψ, cψ, hper⟩

/-- Two proper periods are not coprime when no proper chart of `F` has a line inner
(`lem:gluing-lines`). -/
theorem gcd_ne_one_of_not_line {F : Diagram} (hno : ¬ HasProperLineChart F) {p q : ℕ}
    (hp : p ∈ properPeriods F) (hq : q ∈ properPeriods F) : Nat.gcd p q ≠ 1 := by
  obtain ⟨χ₁, h₁, c₁, e₁⟩ := hp
  obtain ⟨χ₂, h₂, c₂, e₂⟩ := hq
  intro hcop
  have hcop' : Int.gcd χ₁.period χ₂.period = 1 := by
    have p₁ : 0 < χ₁.period := h₁.2.2.2.period_pos
    have p₂ : 0 < χ₂.period := h₂.2.2.2.period_pos
    have e₁' : χ₁.period.natAbs = p := by omega
    have e₂' : χ₂.period.natAbs = q := by omega
    change Nat.gcd χ₁.period.natAbs χ₂.period.natAbs = 1
    rw [e₁', e₂']
    exact hcop
  obtain ⟨-, -, hline⟩ := Chart.IsProperLegal.coprime_periods_line h₁ h₂ c₁ c₂ hcop'
  exact hno ⟨χ₁, h₁, c₁, hline.imp (fun x => x.1) (fun x => x.1)⟩

/-- **`cor:least-root-period`.**  Let `F` be rooted with no proper chart having a line inner.  Then
its least proper period `p₀` divides every proper period, and the proper charts of period `p₀` are
exactly its source-minimal charts. -/
theorem least_root_period {F : Diagram} (hF : HasProperChart F) (hno : ¬ HasProperLineChart F) :
    ∃ p₀ : ℕ, p₀ ∈ properPeriods F ∧ (∀ q ∈ properPeriods F, p₀ ≤ q) ∧
      (∀ q ∈ properPeriods F, p₀ ∣ q) ∧
      ∀ χ : Chart, (χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period.toNat = p₀) ↔
        χ.IsSourceMinimal F := by
  classical
  obtain ⟨χ₀, h₀, c₀⟩ := hF
  have hne : (properPeriods F).Nonempty := ⟨_, h₀.mem_properPeriods c₀⟩
  have hex : ∃ p, p ∈ properPeriods F := hne
  have hp₀ : Nat.find hex ∈ properPeriods F := Nat.find_spec hex
  have hleast : ∀ q ∈ properPeriods F, Nat.find hex ≤ q := fun q hq => Nat.find_min' hex hq
  have hdvd : ∀ q ∈ properPeriods F, Nat.find hex ∣ q :=
    least_period_dvd (fun q hq => two_le_of_mem_properPeriods hq) hp₀ hleast
      (fun p hp q hq hn₁ hn₂ hg => gcd_mem_properPeriods hp hq hn₁ hn₂ hg)
      (fun p hp q hq => gcd_ne_one_of_not_line hno hp hq)
  refine ⟨Nat.find hex, hp₀, hleast, hdvd, fun χ => ?_⟩
  constructor
  · rintro ⟨h, c, hper⟩
    refine ⟨h, c, fun χ' h' c' => ?_⟩
    have hmin := (isScoreMinimal_iff_eq_least (N := span F) hp₀ hleast hdvd
      (p := χ.period.toNat)).mpr hper
    rw [h.score_eq c, h'.score_eq c']
    exact hmin.2 _ (h'.mem_properPeriods c')
  · rintro ⟨h, c, hmin⟩
    refine ⟨h, c, ?_⟩
    refine (isScoreMinimal_iff_eq_least (N := span F) hp₀ hleast hdvd).mp
      ⟨h.mem_properPeriods c, ?_⟩
    intro q hq
    obtain ⟨χ', h', c', hq'⟩ := hq
    have hq'' : χ'.period.toNat = q := by omega
    have := hmin χ' h' c'
    rw [h.score_eq c, h'.score_eq c', hq''] at this
    exact this

/-- **`cor:least-root-period`, the general clause.**  The period of any source-minimal chart whose
inner is not a line divides every proper period at its source. -/
theorem Chart.IsSourceMinimal.period_dvd {F : Diagram} {χ : Chart} (hχ : χ.IsSourceMinimal F)
    (hnl : ¬ LineInner χ.ω) {χ' : Chart} (h' : χ'.IsProperLegal) (c' : χ'.IsChartOf F) :
    χ.period ∣ χ'.period := by
  obtain ⟨h, c, hmin⟩ := hχ
  have hS : ∀ q ∈ properPeriods F, 2 ≤ q := fun q hq => two_le_of_mem_properPeriods hq
  have hscore : IsScoreMinimal (span F) (properPeriods F) χ.period.toNat := by
    refine ⟨h.mem_properPeriods c, fun q hq => ?_⟩
    obtain ⟨χ'', h'', c'', hq''⟩ := hq
    have e : χ''.period.toNat = q := by omega
    have := hmin χ'' h'' c''
    rw [h.score_eq c, h''.score_eq c'', e] at this
    exact this
  have hdvd := dvd_of_isScoreMinimal hS hscore
    (fun q hq hn₁ hn₂ hg => gcd_mem_properPeriods (h.mem_properPeriods c) hq hn₁ hn₂ hg)
    (fun q hq hn hcop => by
      obtain ⟨χ'', h'', c'', hq''⟩ := hq
      have p₁ : 0 < χ.period := h.2.2.2.period_pos
      have p₂ : 0 < χ''.period := h''.2.2.2.period_pos
      have e : χ''.period.natAbs = q := by omega
      have hcop' : Int.gcd χ.period χ''.period = 1 := by
        have e₁ : χ.period.natAbs = χ.period.toNat := by omega
        change Nat.gcd χ.period.natAbs χ''.period.natAbs = 1
        rw [e₁, e]
        exact hcop
      obtain ⟨-, -, hline⟩ := Chart.IsProperLegal.coprime_periods_line h h'' c c'' hcop'
      exact hnl (hline.imp (fun x => x.1) (fun x => x.1)))
    _ (h'.mem_properPeriods c')
  rw [← h.period_toNat, ← h'.period_toNat]
  exact_mod_cast hdvd

/-! ### The line-inner qualification: `(7) = (3) ∘ (3) = (2) ∘ (4)` -/

/-- The row `(7)` has two proper roots with line inners, of periods two and three, so
`cor:least-root-period` fails without the line-inner hypothesis: its least proper period two
does not divide three. -/
theorem row_seven_least_period :
    (2 ∈ properPeriods (skewOf [7] []) ∧ 3 ∈ properPeriods (skewOf [7] [])) ∧
      (∀ p ∈ properPeriods (skewOf [7] []), 2 ≤ p) ∧ ¬ (2 ∣ 3) ∧
      HasProperLineChart (skewOf [7] []) := by
  have h₁ : Chart.IsProperLegal ⟨skewOf [3] [], rowInnerThree⟩ :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩
  have h₂ : Chart.IsProperLegal ⟨skewOf [2] [], rowInnerFour⟩ :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩
  have c₁ : Chart.IsChartOf ⟨skewOf [3] [], rowInnerThree⟩ (skewOf [7] []) :=
    ⟨0, by rw [translate_zero]; exact (by decide +kernel :
      MarkedInner.compose (skewOf [3] []) rowInnerThree = skewOf [7] []).symm⟩
  have c₂ : Chart.IsChartOf ⟨skewOf [2] [], rowInnerFour⟩ (skewOf [7] []) :=
    ⟨0, by rw [translate_zero]; exact (by decide +kernel :
      MarkedInner.compose (skewOf [2] []) rowInnerFour = skewOf [7] []).symm⟩
  refine ⟨⟨⟨_, h₁, c₁, by decide⟩, ⟨_, h₂, c₂, by decide⟩⟩,
    fun p hp => two_le_of_mem_properPeriods hp, by decide, ⟨_, h₁, c₁, Or.inl ?_⟩⟩
  exact ⟨0, by decide +kernel⟩

end GluingCore
