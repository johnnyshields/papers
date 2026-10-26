/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import GluingCore.MinimalFibers.LeastPeriod

/-!
# Independence of the source-minimal inner from the outer

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `lem:outer-independent`, `eq:score`).
The copied chart API describes the actual cell-set compositions and lexicographic scores.
A smaller divisor root of the inner lifts through every connected outer by aligned reassociation.

Sorry-free.
-/

namespace GluingCore

/-- An aligned proper root of an inner lifts to a proper chart of the parent. -/
theorem Chart.IsProperLegal.lift_inner_root {χ : Chart} (hχ : χ.IsProperLegal)
    {η : MarkedInner} (hη : η.IsLegal) (hηcard : 2 ≤ η.E.card)
    {V : Diagram} (hV : IsConnectedSkew V) (hVcard : 2 ≤ V.card)
    {t : ℤ × ℤ} (hE : χ.ω.E = translate t (η.compose V))
    (hdiv : η.period ∣ χ.period) :
    ∃ δ : Chart, δ.IsProperLegal ∧ δ.IsChartOf χ.parent ∧ δ.period = η.period := by
  let ζ := χ.ω.translate (-t)
  have hζ : ζ.IsLegal := MarkedInner.isLegal_translate (-t) hχ.2.2.2
  have hzE : ζ.E = η.compose V := by
    change translate (-t) χ.ω.E = η.compose V
    rw [hE, translate_translate, neg_add_cancel, translate_zero]
  obtain ⟨a, ha⟩ := hdiv
  have halign : content ζ.v = a * η.period := by
    change χ.period = a * η.period
    simpa only [mul_comm] using ha
  obtain ⟨μ, γ, hr⟩ := hη.aligned hV hζ hzE halign
  let δ : Chart := ⟨μ.compose (γ χ.D), η⟩
  refine ⟨δ, ⟨hr.legal.isConnectedSkew_compose (hr.connected_gamma hχ.1), ?_, hηcard, hη⟩,
    ⟨t, ?_⟩, rfl⟩
  · have hb := MarkedInner.card_le_compose (μ := μ) (hr.connected_gamma hχ.1).2.1
    rw [hr.inner] at hb
    exact hVcard.trans hb
  · change χ.parent = translate t (η.compose (μ.compose (γ χ.D)))
    rw [← hr.compose_eq χ.D hχ.1]
    change χ.parent = translate t ((χ.ω.translate (-t)).compose χ.D)
    rw [MarkedInner.compose_translate, translate_translate, add_neg_cancel, translate_zero]
    rfl

/-- A nonline chart and an incompatible period supply a smaller divisor root. -/
theorem Chart.IsProperLegal.smaller_divisor_root {F : Diagram} {χ ψ : Chart}
    (hχ : χ.IsProperLegal) (hψ : ψ.IsProperLegal) (cχ : χ.IsChartOf F)
    (cψ : ψ.IsChartOf F) (hnl : ¬ LineInner χ.ω) (hn : ¬ χ.period ∣ ψ.period) :
    ∃ δ : Chart, δ.IsProperLegal ∧ δ.IsChartOf F ∧
      δ.period < χ.period ∧ δ.period ∣ χ.period := by
  have hp : 0 < χ.period := hχ.2.2.2.period_pos
  have hq : 0 < ψ.period := hψ.2.2.2.period_pos
  have hp0 : 0 < χ.period.toNat := by omega
  have hq0 : 0 < ψ.period.toNat := by omega
  have hn' : ¬ χ.period.toNat ∣ ψ.period.toNat := by
    intro hd
    apply hn
    rw [← hχ.period_toNat, ← hψ.period_toNat]
    exact_mod_cast hd
  by_cases hd : ψ.period.toNat ∣ χ.period.toNat
  · have hlt : ψ.period.toNat < χ.period.toNat :=
      lt_of_le_of_ne (Nat.le_of_dvd hp0 hd) (fun he => hn' (he ▸ dvd_rfl))
    refine ⟨ψ, hψ, cψ, ?_, ?_⟩
    · omega
    · rw [← hχ.period_toNat, ← hψ.period_toNat]
      exact_mod_cast hd
  · have hg : 1 < Nat.gcd χ.period.toNat ψ.period.toNat := by
      have hg0 := Nat.gcd_pos_of_pos_left ψ.period.toNat hp0
      by_contra hh
      have he : Nat.gcd χ.period.toNat ψ.period.toNat = 1 := by omega
      have he' : Int.gcd χ.period ψ.period = 1 := by
        have hp' : χ.period.natAbs = χ.period.toNat := by omega
        have hq' : ψ.period.natAbs = ψ.period.toNat := by omega
        change Nat.gcd χ.period.natAbs ψ.period.natAbs = 1
        rw [hp', hq']
        exact he
      obtain ⟨_, _, hl⟩ := hχ.coprime_periods_line hψ cχ cψ he'
      exact hnl (hl.imp (fun hh => hh.1) (fun hh => hh.1))
    obtain ⟨δ, hδ, cδ, he⟩ := hχ.exists_gcd_root hψ cχ cψ hn' hd hg
    have hlt : Nat.gcd χ.period.toNat ψ.period.toNat < χ.period.toNat :=
      lt_of_le_of_ne (Nat.le_of_dvd hp0 (Nat.gcd_dvd_left _ _))
        (fun he => hn' (he ▸ Nat.gcd_dvd_right _ _))
    refine ⟨δ, hδ, cδ, ?_, ?_⟩
    · rw [he]
      omega
    · rw [he, ← hχ.period_toNat]
      exact_mod_cast Nat.gcd_dvd_left χ.period.toNat ψ.period.toNat

/-- The source-minimal nonline period divides every proper period under any new outer. -/
theorem Chart.IsSourceMinimal.outer_period_dvd {χ : Chart}
    (hχ : χ.IsSourceMinimal χ.parent) (hnl : ¬ LineInner χ.ω)
    {V : Diagram} (hV : IsConnectedSkew V) (hVcard : 2 ≤ V.card)
    {ψ : Chart} (hψ : ψ.IsProperLegal) (cψ : ψ.IsChartOf (χ.ω.compose V)) :
    χ.period ∣ ψ.period := by
  let ν : Chart := ⟨V, χ.ω⟩
  have hν : ν.IsProperLegal := ⟨hV, hVcard, hχ.1.2.2.1, hχ.1.2.2.2⟩
  have cν : ν.IsChartOf (χ.ω.compose V) := ⟨0, by simp [Chart.parent, ν, translate_zero]⟩
  by_contra hn
  obtain ⟨δ, hδ, cδ, hlt, hdiv⟩ := hν.smaller_divisor_root hψ cν cψ hnl hn
  obtain ⟨U, t, hU, hUcard, hE⟩ :=
    MarkedInner.exists_inner_factor_proof hδ hν cδ cν hlt hdiv
  obtain ⟨γ, hγ, cγ, hper⟩ :=
    hχ.1.lift_inner_root hδ.2.2.2 hδ.2.2.1 hU hUcard hE hdiv
  have hpd := hχ.period_dvd hnl hγ cγ
  rw [hper] at hpd
  have hδpos : 0 < δ.period := hδ.2.2.2.period_pos
  have hχpos : 0 < χ.period := hχ.1.2.2.2.period_pos
  have heν : ν.period = χ.period := rfl
  rw [heν] at hlt
  have hle := Int.le_of_dvd hδpos hpd
  omega

/-- Changing the connected proper outer preserves source-minimality of a nonline inner. -/
theorem Chart.IsSourceMinimal.outer_independent {χ : Chart}
    (hχ : χ.IsSourceMinimal χ.parent) (hnl : ¬ LineInner χ.ω)
    {V : Diagram} (hV : IsConnectedSkew V) (hVcard : 2 ≤ V.card) :
    (⟨V, χ.ω⟩ : Chart).IsSourceMinimal (χ.ω.compose V) := by
  let ν : Chart := ⟨V, χ.ω⟩
  have hν : ν.IsProperLegal := ⟨hV, hVcard, hχ.1.2.2.1, hχ.1.2.2.2⟩
  have cν : ν.IsChartOf (χ.ω.compose V) := ⟨0, by simp [Chart.parent, ν, translate_zero]⟩
  refine ⟨hν, cν, ?_⟩
  intro ψ hψ cψ
  have hd := hχ.outer_period_dvd hnl hV hVcard hψ cψ
  have hd' : ν.period.toNat ∣ ψ.period.toNat := by
    change ν.period ∣ ψ.period at hd
    rw [← hν.period_toNat, ← hψ.period_toNat] at hd
    exact_mod_cast hd
  rw [hν.score_eq cν, hψ.score_eq cψ]
  have hp : 0 < ψ.period := hψ.2.2.2.period_pos
  have hle := Nat.le_of_dvd (show 0 < ψ.period.toNat by omega) hd'
  rcases hle.eq_or_lt with he | he
  · rw [he]
  · exact (score_lt_of_dvd hd' he).le

end GluingCore
