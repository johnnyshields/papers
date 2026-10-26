import SkewGluing.Aligned.InnerFactor.Agree

/-!
# Repetition of the outer, case (d)

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`), via `eq:gluing-mixed-profile`.

For a legal case-(d) mark the private residue `w` of the class `J` reads the height `M_J` of the
diagonal `J` of the outer and a marked residue meeting neither middle tail reads the overlap
`S_J` (`sigmaD`), so repetition of the composite on `[c₀ + (m₀ + b) q + w,
c₀ + (m₀ + a) q - 1]` gives `M_j = M_{j+Δ}` for `m₀ + b ≤ j < m₀ + a` and `S_j = S_{j+Δ}` for
`m₀ + b < j < m₀ + a`, hence repetition of the diagonals of the outer under one row shift.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem MarkedInner.IsLegal.W_nonempty_of_case_d (hω : ω.IsLegal) (hc : ω.case = .d) :
    ω.W.Nonempty := by
  by_contra hn
  have hW : ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have := (IsLegalEmpty.case_a ⟨hω, hW⟩)
  rw [hc] at this
  exact absurd this (by decide)

namespace PerData

variable {a b Δ : ℤ} {τ : ℤ × ℤ}

/-- **Repetition of the outer, case (d).** -/
theorem factorData_d (h : PerData ω D a b Δ τ) (hc : ω.case = .d) :
    ∃ z₁, FactorData D a b Δ z₁ := by
  have hl : ω.IsLegalNonempty := ⟨h.legal, h.legal.W_nonempty_of_case_d hc⟩
  obtain ⟨s, t₀, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hc) hph
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hM := h.hM
  have hΔ := h.hΔ
  have hb := h.hb
  have ha := h.ha
  have hba := h.hba
  have hD := h.conn
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  obtain ⟨hs1, hs2, -, -, -, -⟩ := id hph
  have fa := d_E_facts hl hc hph (a := s - 1) (by omega) (by omega)
  have hdL : ω.dLo (s - 1) = 0 := by omega
  have hqp : 0 < ω.period := by omega
  have hexp : (minContent D + a - 1) * ω.period = (minContent D + a) * ω.period - ω.period := by
    ring
  -- the range of the diagonals read
  have hrange : ∀ J r : ℤ, minContent D + b ≤ J → J ≤ minContent D + a - 1 → 0 ≤ r →
      r < ω.period → (J = minContent D + b → ω.widthZ ≤ r) →
      minContent ω.E + (minContent D + b) * ω.period + ω.widthZ ≤
        minContent ω.E + (J * ω.period + r) ∧
      minContent ω.E + (J * ω.period + r) ≤ minContent ω.E + (minContent D + a) * ω.period - 1 ∧
      minContent ω.E + (J * ω.period + r) ∈ contents (ω.compose D) := by
    intro J r h0 h1 hr0 hr1 hr2
    have m1 := mul_le_mul_of_nonneg_right h0 hqp.le
    have m2 := mul_le_mul_of_nonneg_right h1 hqp.le
    have m3 := mul_le_mul_of_nonneg_right (show minContent D ≤ J by omega) hqp.le
    have m4 := mul_le_mul_of_nonneg_right (show J ≤ maxContent D by omega) hqp.le
    have hlow : (minContent D + b) * ω.period + ω.widthZ ≤ J * ω.period + r := by
      by_cases hJ : J = minContent D + b
      · subst hJ; have := hr2 rfl; omega
      · have m5 := mul_le_mul_of_nonneg_right (show minContent D + b + 1 ≤ J by omega) hqp.le
        have e : (minContent D + b + 1) * ω.period = (minContent D + b) * ω.period + ω.period := by
          ring
        omega
    refine ⟨by omega, by omega, ?_⟩
    rw [h.mem_contents_compose]
    unfold widthZ at *
    constructor <;> nlinarith
  -- the heights `M_J = M_{J + Δ}` and `τ₁ = Δ v₁`
  have key1 : ∀ J, minContent D + b ≤ J → J ≤ minContent D + a - 1 →
      (diagHi D (J + Δ) - diagLo D (J + Δ) = diagHi D J - diagLo D J) ∧
        τ.1 = Δ * ω.rowShift := by
    intro J h0 h1
    have hJ : minContent D ≤ J ∧ J ≤ maxContent D := by omega
    have hJ' : minContent D ≤ J + Δ ∧ J + Δ ≤ maxContent D := by omega
    have r1 := mix_rows_w hl hD hc hph hlt hJ
    have r2 := mix_rows_w hl hD hc hph hlt hJ'
    obtain ⟨g1, g2, g3⟩ := hrange J ω.widthZ h0 h1 (by omega) hq (fun _ => le_refl _)
    have ds := h.diag_shift g3 g1 g2
    have e : minContent ω.E + (J * ω.period + ω.widthZ) + Δ * ω.period =
        minContent ω.E + ((J + Δ) * ω.period + ω.widthZ) := by ring
    rw [e, r1.1, r2.1, r1.2, r2.2] at ds
    have ds2 := ds.2
    have hp : (J + Δ) * ω.rowShift = J * ω.rowShift + Δ * ω.rowShift := by ring
    constructor <;> omega
  -- the overlaps `S_J = S_{J + Δ}`
  have key2 : ∀ J, minContent D + b + 1 ≤ J → J ≤ minContent D + a - 1 →
      sigmaD D (J + Δ) = sigmaD D J := by
    intro J h0 h1
    have hJ : minContent D ≤ J ∧ J ≤ maxContent D + 1 := by omega
    have hJ' : minContent D ≤ J + Δ ∧ J + Δ ≤ maxContent D + 1 := by omega
    have r1 := mix_rows_a0 hl hD hc hph hlt (a := s - 1) (J := J) (by omega) (by omega) hdL hJ
    have r2 := mix_rows_a0 hl hD hc hph hlt (a := s - 1) (J := J + Δ) (by omega) (by omega) hdL
      hJ'
    obtain ⟨g1, g2, g3⟩ := hrange J (s - 1) (by omega) h1 (by omega) (by omega) (fun hh => by omega)
    have ds := h.diag_shift g3 g1 g2
    have e : minContent ω.E + (J * ω.period + (s - 1)) + Δ * ω.period =
        minContent ω.E + ((J + Δ) * ω.period + (s - 1)) := by ring
    rw [e, r1.1, r2.1] at ds
    have hτ1 := (key1 (minContent D + b) (le_refl _) (by omega)).2
    have hp : (J + Δ) * ω.rowShift = J * ω.rowShift + Δ * ω.rowShift := by ring
    have := ds.1
    omega
  -- the common shift
  set z := diagHi D (minContent D + b + Δ) - diagHi D (minContent D + b) with hz
  have key3 : ∀ n : ℕ, (n : ℤ) ≤ a - 1 - b →
      diagHi D (minContent D + b + n + Δ) - diagHi D (minContent D + b + n) = z ∧
      diagLo D (minContent D + b + n + Δ) - diagLo D (minContent D + b + n) = z := by
    intro n
    induction n with
    | zero =>
      intro _
      have k1 := (key1 (minContent D + b) (le_refl _) (by omega)).1
      simp only [Nat.cast_zero, add_zero]
      constructor <;> omega
    | succ n ih =>
      intro hn
      have ih := ih (by push_cast at hn; omega)
      push_cast at hn ⊢
      have k1 := (key1 (minContent D + b + (n + 1)) (by omega) (by omega)).1
      have k2 := key2 (minContent D + b + (n + 1)) (by omega) (by omega)
      unfold sigmaD at k2
      have c1 : minContent D + 1 ≤ minContent D + b + (n + 1) + Δ ∧
          minContent D + b + (n + 1) + Δ ≤ maxContent D := by omega
      have c2 : minContent D + 1 ≤ minContent D + b + (n + 1) ∧
          minContent D + b + (n + 1) ≤ maxContent D := by omega
      simp only [c1, c2, and_self, ite_true] at k2
      have e1 : minContent D + b + (n + 1) + Δ - 1 = minContent D + b + n + Δ := by ring
      have e2 : minContent D + b + (n + 1) - 1 = minContent D + b + n := by ring
      rw [e1, e2] at k2
      have e3 : minContent D + b + (n + 1) = minContent D + b + n + 1 := by ring
      rw [e3] at k1 k2 ⊢
      constructor <;> omega
  refine ⟨z, h.conn, h.ha, h.hb, h.hba, h.hΔ, h.hM, ?_⟩
  intro k h0 h1
  have := key3 (k - (minContent D + b)).toNat (by omega)
  have e : minContent D + b + ((k - (minContent D + b)).toNat : ℤ) = k := by omega
  rw [e] at this
  constructor <;> omega

end PerData

end SkewGluing
