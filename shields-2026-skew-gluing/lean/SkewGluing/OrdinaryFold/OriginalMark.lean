import SkewGluing.OrdinaryFold

/-!
# The heights of the original lower mark of an ordinary root

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`, `eq:gluing-original-ordinary-mark`).

For a proper legal ordinary chart of case (a) with a nonempty mark, the parent height on the first
band is the height of the lower mark plus one from the residue `s` on
(`Chart.IsProperLegal.heightWord_first_band`).  In the setting of two ordinary roots of
nondividing periods (`OrdinaryPair`, `GcdData`), with the generic bits `A⁰`, `B⁰` of
`lem:gluing-periods` (ii) and `H⁰_j = 1 + ∑_{i=1}^j C_i` (`heightWord A⁰ B⁰ j`), the case `ρ = 0`
of `eq:gluing-ordinary-slot` (`A⁰_τ = 0`) gives the exact heights of the lower mark `W₋` of the
first root:
`H_{W₋}(r) = H⁰_{r mod g} + 1_{t>0, r≥t} - 1_{r≥s}` for `0 ≤ r < w`
(`ordFold_original_mark_heights`).
The same case forces `t = τ < g` and `s = b g + σ`.

Sorry-free.
-/

namespace SkewGluing

open OrdinaryFold OrdinaryDrift

namespace Chart

/-- **The parent heights on the first band, exactly.**  For a proper legal chart of case (a) with
a nonempty mark and phases `s`, `t`, the height of the parent at the content `z < w` of the first
band is the height of the lower mark `W₋` plus one from the residue `s` on.  This is the exact
form of `IsProperLegal.markHeights`. -/
theorem IsProperLegal.heightWord_first_band {χ : Chart} {F : Diagram} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) (hca : χ.ω.case = .a) (hW : χ.ω.W.Nonempty) {s t : ℤ}
    (hph : χ.ω.IsPhases s t) (z : ℕ) (hz : z < χ.ω.width) :
    heightWord (ordFold_wA F) (ordFold_wB F) z =
      height χ.ω.W (minContent χ.ω.E + z) + (if s.toNat ≤ z then 1 else 0) := by
  obtain ⟨t0, rfl⟩ := hF
  have hl : χ.ω.IsLegalNonempty := ⟨h.2.2.2, hW⟩
  have hD := h.1
  have hP := h.2.2.2.isConnectedSkew_compose hD
  have hD2 := two_le_span_of_two_le_card h.1 h.2.1
  have hspan := hl.span_compose_nat hD
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hqn : (χ.ω.period.toNat : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
  have hwz : χ.ω.widthZ = (χ.ω.width : ℤ) := rfl
  have hzs : z < span (χ.ω.compose χ.D) := by
    have := Nat.mul_le_mul_right χ.ω.period.toNat hD2
    omega
  change heightWord (ordFold_wA (translate t0 (χ.ω.compose χ.D)))
      (ordFold_wB (translate t0 (χ.ω.compose χ.D))) z =
    height χ.ω.W (minContent χ.ω.E + z) + (if s.toNat ≤ z then 1 else 0)
  have hcongr : heightWord (ordFold_wA (translate t0 (χ.ω.compose χ.D)))
      (ordFold_wB (translate t0 (χ.ω.compose χ.D))) z =
      heightWord (ordFold_wA (χ.ω.compose χ.D)) (ordFold_wB (χ.ω.compose χ.D)) z :=
    heightWord_congr fun x hx1 hx2 => ⟨wordA_translate hP t0 (by omega) (by omega),
      wordB_translate hP t0 (by omega) (by omega)⟩
  rw [hcongr, ordFold_heightWord_wA_wB hP z hzs]
  obtain ⟨s1, s2, ht1, ht2, -, -⟩ := id hph
  have hmin := hl.minContent_compose' hD
  have hE := (hl.ordinary_endpoints_a hD hca hph (J := minContent χ.D) (z := (z : ℤ))
    (by omega)).2.2.1 (by omega) rfl
  have hends := MarkedInner.D_ends hD
  obtain ⟨hlo, hhi⟩ := hE
  unfold height
  rw [hmin]
  have e : minContent χ.ω.E + minContent χ.D * χ.ω.period + (z : ℤ) =
      minContent χ.ω.E + (minContent χ.D * χ.ω.period + (z : ℤ)) := by ring
  rw [e, hlo, hhi]
  by_cases hsz' : s ≤ (z : ℤ)
  · simp only [show s.toNat ≤ z by omega, show ¬ ((z : ℤ) < s) by omega, ite_true, ite_false]
    omega
  · simp only [show ¬ (s.toNat ≤ z) by omega, show (z : ℤ) < s by omega, ite_true, ite_false]
    omega

end Chart

/-- **`eq:gluing-original-ordinary-mark`, exactly.**  Two ordinary proper legal roots of
nondividing periods, in the setting `eq:gluing-gcd-data`, the first of case (a): there are phases
`s`, `t` of the first mark and generic bits `A⁰`, `B⁰` (`lem:gluing-periods` (ii)) such that, in
the case `ρ = 0` of `eq:gluing-ordinary-slot`, i.e. `A⁰_{t mod g} = 0`, one has `t < g`,
`b g ≤ s`, and the lower mark `W₋` of the first root has the heights
`H_{W₋}(r) = H⁰_{r mod g} + 1_{t>0, r≥t} - 1_{r≥s}` for `0 ≤ r < w`, where
`H⁰_j = 1 + ∑_{i=1}^j (A⁰_i - B⁰_i)` is `heightWord A⁰ B⁰ j`.  The height `H_{W₋}(r)` is
`height W (minContent E + r)`. -/
theorem ordFold_original_mark_heights {F : Diagram} {χ₁ χ₂ : Chart}
    (h : OrdinaryPair F χ₁ χ₂) (hca : χ₁.ω.case = .a) {g a b c d M wg : ℕ}
    (hd : GcdData F χ₁ χ₂ g a b c d M wg) :
    ∃ (s t s₂ t₂ : ℤ) (A0 B0 : ℕ → ℤ), χ₁.ω.IsPhases s t ∧ χ₂.ω.IsPhases s₂ t₂ ∧
      GcdPair (ordFold_wA F) (ordFold_wB F) A0 B0 (span F) g a b c d wg t.toNat s.toNat
        (ordHoleA χ₂.ω.case s₂ t₂).toNat (ordHoleB χ₂.ω.case s₂ t₂).toNat ∧
      (A0 (t.toNat % g) = 0 →
        t.toNat < g ∧ b * g ≤ s.toNat ∧
        ∀ r : ℕ, r < χ₁.ω.width →
          height χ₁.ω.W (minContent χ₁.ω.E + r) =
            heightWord A0 B0 (r % g) + (if 0 < t ∧ t ≤ (r : ℤ) then 1 else 0) -
              (if s ≤ (r : ℤ) then 1 else 0)) := by
  obtain ⟨s, t, s₂, t₂, A0, B0, hph, hph₂, hG⟩ := h.gcdPair hd
  have e1 : ordHoleA χ₁.ω.case s t = t := by simp [ordHoleA, hca]
  have e2 : ordHoleB χ₁.ω.case s t = s := by simp [ordHoleB, hca]
  rw [e1, e2] at hG
  refine ⟨s, t, s₂, t₂, A0, B0, hph, hph₂, hG, fun hρ => ?_⟩
  have hw := hd.width₁
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hwz : χ₁.ω.widthZ = (χ₁.ω.width : ℤ) := rfl
  have hha : t.toNat < b * g + wg := by omega
  have hhb1 : 1 ≤ s.toNat := by omega
  have hhb : s.toNat ≤ b * g + wg := by omega
  have sc := hG.slotScalars hha hhb1
  have hρB : B0 (s.toNat % g) = 0 := by rw [← sc.rho]; exact hρ
  have hg := hG.g_pos
  have hwg := hG.wg_lt
  obtain ⟨G1, G2, G3, G4⟩ := hG.cap_facts
  have hbg : b = 0 ∨ g ≤ b * g := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · left; exact h0
    · right; exact Nat.le_mul_of_pos_left g h0
  have hτ : t.toNat < g := by
    rcases hG.tau_struct hha with ⟨h1, -⟩ | ⟨h1, h2, h3, h4⟩
    · exact h1
    · have := G1 (by omega) (by omega)
      omega
  have hσ : b * g ≤ s.toNat := by
    by_contra hcon
    have hlt : s.toNat % g = s.toNat := by
      rcases hG.sigma_struct hhb with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · exact h2
      · omega
    have := G4 (by omega) (by omega)
    omega
  refine ⟨hτ, hσ, fun r hr => ?_⟩
  have hdr := hG.drift_full
  have hΔ := hdr.1
  have hr1 : r < a * g := by
    have := hG.root₁.hwq
    omega
  have hrN : r < span F := by
    have := hG.root₁.two_q_le
    have := hG.root₁.hwq
    omega
  have hpar := h.proper₁.heightWord_first_band h.chart₁ hca h.nonempty₁ hph r hr
  have hh1 := hG.height₁ (k := r) hr1 hrN
  have hshift : genSum (incr A0 B0 g) r = genSum (incr A0 B0 g) (r % g) := by
    have := genSum_shift A0 B0 hΔ (r / g) (r % g)
    rwa [Nat.div_add_mod'] at this
  have hlt : r % g < g := Nat.mod_lt _ hg
  have hgs := ordFold_genSum_incr_lt A0 B0 hlt
  have hHW : heightWord A0 B0 (r % g) = 1 + genSum (incr A0 B0 g) (r % g) := by
    rw [hgs]; rfl
  rw [hHW, ← hshift]
  rw [hh1, hρ, hρB] at hpar
  have hs0 : (s.toNat ≤ r) ↔ s ≤ (r : ℤ) := by omega
  have hs0' : (t.toNat ≤ r) ↔ t ≤ (r : ℤ) := by omega
  have hs1' : (1 ≤ t.toNat) ↔ 0 < t := by omega
  by_cases c1 : s ≤ (r : ℤ) <;> by_cases c2 : t ≤ (r : ℤ) <;> by_cases c3 : 0 < t <;>
    simp [hs0, hs0', hs1', c1, c2, c3] at hpar ⊢ <;> omega

/-! ### Checked example

The roots of the row `(20)` (periods `6` and `9`, `g = 3`, `w_g = 2`) satisfy the hypotheses. -/

example := ordFold_original_mark_heights ordFold_row20_ordinaryPair rfl ordFold_row20_gcdData

end SkewGluing
