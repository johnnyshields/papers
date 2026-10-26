/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.CaseDWeighted
import SkewMarkedFactor.CaseDRemainder
import SkewMarkedFactor.ModifiedMap
import SkewMarkedFactor.GeneratorSpan
import SkewMarkedFactor.MixedVanishing

/-!
# Mixed weighted covariance of the composition map

«Mixed weighted covariance» (`rt:mixed-covariance`) of `shields-2026-skew-marked-factor.tex`
for a legal mark in case (d): the weighted derivative of a row composite is a signed multiple of
the lower row composite, and covariance of `Ψ_η` is transported from the generators `h_j` to the
whole ring.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

variable {η : MarkedInner} {m : ℕ}

/-- The one-row outer of `j ≥ 1` cells is the row interval `[0, j)`. -/
theorem skewOf_row (j : ℕ) : skewOf [j] [] = rowCells 0 (j : ℤ) := by
  ext ⟨a, b⟩
  simp [skewOf, rowCells, Finset.mem_Ico]

theorem rowComposite_eq (j : ℕ) : rowComposite η j = η.compose (rowCells 0 (j : ℤ)) := by
  unfold rowComposite
  rw [skewOf_row]

/-- The northwest border segment of `k p` cells at content `(m - k) p + s` of the case-(d) row
power is removable on the left. -/
theorem rowPower_segment_mem_leftRibbons (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    Plan.segment (η.compose (rowCells 0 m))
        (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat) ∈
      leftRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpp : 0 < η.period := by omega
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hkmz : (k : ℤ) ≤ m := by exact_mod_cast hkm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hF := h.1.isConnectedSkew_compose hD
  obtain ⟨hmn, hmx⟩ := rowPower_content_range h hm
  have hkpos : 0 < k * η.period.toNat := Nat.mul_pos hk (by omega)
  have hcast : ((k * η.period.toNat : ℕ) : ℤ) = (k : ℤ) * η.period := by
    push_cast; rw [Int.toNat_of_nonneg hpp.le]
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  rw [mem_leftRibbons_iff_segment hF hkpos]
  refine ⟨_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [hmn]
    have : 0 ≤ ((m : ℤ) - k) * η.period := mul_nonneg (by omega) hpp.le
    omega
  · rw [hcast, hmx]
    have e : ((m : ℤ) - k) * η.period + s + k * η.period = m * η.period + s := by ring
    omega
  · right
    have hb := nwBit_rowPower_pos h hd hph hlt hm (J := (m : ℤ) - k) (a := s) (by omega)
      (by omega) (Or.inl ⟨by omega, by omega⟩)
    have hl := lo_pred_phase_sub h hd hph
    have : bitA (η.compose (rowCells 0 m)) (minContent η.E + (((m : ℤ) - k) * η.period + s)) =
        1 := by
      change nwBit _ _ = 1
      rw [hb, hl]
      have : ¬ (1 ≤ ((m : ℤ) - k) ∧ s = t) := by omega
      have h2 : ¬ ((m : ℤ) - k = m ∧ s = s) := by omega
      simp only [this, h2, ite_false]; omega
    exact this
  · rw [hcast]
    by_cases hsw : s = η.widthZ
    · left
      rw [hmx]
      have e : ((m : ℤ) - k) * η.period + s + k * η.period - 1 =
          m * η.period + η.widthZ - 1 := by rw [hsw]; ring
      omega
    · right
      have hb := nwBit_rowPower_pos h hd hph hlt hm (J := (m : ℤ)) (a := s) (by omega)
        (by omega) (Or.inr ⟨rfl, by omega⟩)
      have hl := lo_pred_phase_sub h hd hph
      have e : minContent η.E + (((m : ℤ) - k) * η.period + s) + k * η.period =
          minContent η.E + ((m : ℤ) * η.period + s) := by ring
      rw [e]
      change nwBit _ _ = 0
      rw [hb, hl]
      have : ¬ (1 ≤ (m : ℤ) ∧ s = t) := by omega
      simp only [this, ite_false]
      simp


/-- **Weighted derivative of a case-(d) row composite** (`rt:mixed-intertwining` on `h_m`):
for `1 ≤ k ≤ m`,
`V_{kp} b_m = ((m - k) p + s - t) (-1)^{k (-v₁)} (B C)^k b_{m-k}`, with `b_0 = A`. -/
theorem wDeriv_rowComposite (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    wDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 m))) =
      ((((m : ℤ) - k) * η.period + s - t : ℤ) : Lambda) * (-1 : Lambda) ^ (k * (-η.v.1).toNat) *
        (cellSchur (hatMarkFin η) ^ k * cellSchur (hatMiddleFin η) ^ k *
          cellSchur (η.compose (rowCells 0 ((m - k : ℕ) : ℤ)))) := by
  rw [wDeriv_rowPower h hd hph hlt hm hk hkm,
    if_pos (rowPower_segment_mem_leftRibbons h hd hph hlt hm hk hkm),
    rowPower_strip_signed h hd hph hlt hm hk hkm]
  ring

/-- Past the span, `V_{kp}` kills the row composite. -/
theorem wDeriv_rowComposite_of_lt (h : η.IsLegalNonempty) {k : ℕ} (hk : 1 ≤ k) (hmk : m < k)
    (hm : 1 ≤ m) :
    wDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 m))) = 0 := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hF := h.1.isConnectedSkew_compose hD
  apply wDeriv_cellSchur_of_span_le hF.1
  have hsp := Gluing.MarkedInner.span_compose hD h.1
  have hsr : (span (rowCells 0 (m : ℤ)) : ℤ) = m := by rw [span_rowCells]; omega
  rw [hsr] at hsp
  have hq := h.width_lt_period
  have hpp : 0 < η.period := h.1.period_pos
  have hkz : (m : ℤ) + 1 ≤ k := by exact_mod_cast hmk
  have hcast : ((k * η.period.toNat : ℕ) : ℤ) = (k : ℤ) * η.period := by
    push_cast; rw [Int.toNat_of_nonneg hpp.le]
  have : (span (η.compose (rowCells 0 m)) : ℤ) ≤ ((k * η.period.toNat : ℕ) : ℤ) := by
    rw [hsp, hcast]
    have : ((m : ℤ) + 1) * η.period ≤ k * η.period := mul_le_mul_of_nonneg_right hkz hpp.le
    have hw : (η.width : ℤ) < η.period := hq
    nlinarith
  exact_mod_cast this


/-- The factor `χ = (-1)^{-v₁} A B C` of `rt:mixed-covariance`. -/
def mixedChi (η : MarkedInner) : Lambda :=
  (-1 : Lambda) ^ (-η.v.1).toNat *
    (normalizerRow η * normalizerColumn η * normalizerDiagonal η)

theorem compositionMap_hPos (η : MarkedInner) {n : ℕ} (hn : 1 ≤ n) :
    compositionMap η (hPos n) =
      normalizerRow η ^ (n - 1) * cellSchur (η.compose (rowCells 0 (n : ℤ))) := by
  have h1 := hPos_pnat (⟨n, hn⟩ : ℕ+)
  have h2 := compositionMap_X η (⟨n, hn⟩ : ℕ+)
  simp only [PNat.mk_coe] at h1 h2
  rw [h1, h2]
  unfold modifiedGen
  rw [rowComposite_eq]
  rfl

theorem compositionMap_C (η : MarkedInner) (q : ℚ) : compositionMap η (C q) = C q := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

theorem compositionMap_C_mul (η : MarkedInner) (q : ℚ) (x : Lambda) :
    compositionMap η (C q * x) = C q * compositionMap η x := by
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]

theorem derivation_mul_killed (D : Derivation ℚ Lambda Lambda) {a : Lambda} (ha : D a = 0)
    (n : ℕ) (x : Lambda) : D (a ^ n * x) = a ^ n * D x := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, ha]
  simp

/-- **Generator intertwining** for a case-(d) mark: for every `j ≥ 1`,
`V_{kp} Ψ(h_j) = χ^k Ψ((p V_k + ρ δ_k) h_j)` with `ρ = s - t`. -/
theorem mixed_generator_intertwining (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) {k : ℕ} (hk : 1 ≤ k) (j : ℕ+) :
    wDeriv (k * η.period.toNat) (compositionMap η (X j)) =
      mixedChi η ^ k * compositionMap η
        (mixedOp (η.period : ℚ) ((s - t : ℤ) : ℚ) k (X j)) := by
  obtain ⟨hA, -, -⟩ := wDeriv_normalizers_eq_zero h.1 (by omega : 0 < k)
  obtain ⟨n, hn⟩ := j
  have hX : (X (⟨n, hn⟩ : ℕ+) : Lambda) = hPos n := (hPos_pnat ⟨n, hn⟩).symm
  rw [hX, compositionMap_hPos η hn, derivation_mul_killed _ hA, mixedOp_hPos _ _ (by omega)]
  have hsg : (-1 : Lambda) ^ (k * (-η.v.1).toNat) = ((-1 : Lambda) ^ (-η.v.1).toNat) ^ k := by
    rw [mul_comm, pow_mul]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, compositionMap_C_mul]
    have hsc : (C (η.period * (((n : ℚ)) - k) + ((s - t : ℤ) : ℚ)) : Lambda) =
        ((((n : ℤ) - k) * η.period + s - t : ℤ) : Lambda) := by
      simp only [map_add, map_mul, map_sub, map_natCast, map_intCast]
      push_cast
      ring
    rw [wDeriv_rowComposite h hd hph hlt hn hk hkn, ← hsc, mixedChi, mul_pow, mul_pow, hsg]
    rcases Nat.eq_or_lt_of_le hkn with hkk | hkn'
    · obtain rfl := hkk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.sub_self, Nat.cast_zero, compose_rowCells_zero, hPos_zero, map_one,
        Nat.add_sub_cancel]
      have hW : cellSchur η.W = normalizerRow η := rfl
      rw [hW]
      simp only [normalizerColumn, normalizerDiagonal]
      ring
    · obtain ⟨r, rfl⟩ : ∃ r, n = k + (r + 1) := ⟨n - k - 1, by omega⟩
      rw [compositionMap_hPos η (by omega : 1 ≤ k + (r + 1) - k)]
      have e1 : k + (r + 1) - k = r + 1 := by omega
      have e2 : k + (r + 1) - 1 = k + r := by omega
      rw [e1, e2, Nat.add_sub_cancel, pow_add]
      simp only [normalizerColumn, normalizerDiagonal]
      ring
  · rw [if_neg hkn, map_zero, mul_zero, wDeriv_rowComposite_of_lt h hk (by omega) hn, mul_zero]


/-- **Mixed weighted covariance** (`rt:mixed-covariance`, `eq:mixed-covariance`) for a case-(d)
mark, on the whole ring: `V_{kp} Ψ_η = χ^k Ψ_η (p V_k + ρ δ_k)` with `ρ = s - t`. -/
theorem mixed_covariance_d (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    wDeriv (k * η.period.toNat) (compositionMap η f) =
      mixedChi η ^ k * compositionMap η (mixedOp (η.period : ℚ) ((s - t : ℤ) : ℚ) k f) :=
  intertwine_of_generators (compositionMap η) (wDeriv (k * η.period.toNat))
    (mixedOp (η.period : ℚ) ((s - t : ℤ) : ℚ) k) (mixedChi η ^ k)
    (mixed_generator_intertwining h hd hph hlt hk) f

/-- The cell function of a single-cell composite is that of the inner. -/
theorem cellSchur_compose_single (η : MarkedInner) (z : ℤ × ℤ) :
    cellSchur (η.compose {z}) = cellSchur η.E := by
  have he : η.compose {z} = translate (η.origin {z} z) η.E := by
    ext x
    rw [Gluing.MarkedInner.mem_compose (Finset.singleton_nonempty z)]
    constructor
    · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hr, -⟩)
      · rw [Finset.mem_singleton] at hd
        subst hd
        exact hx
      · rw [Finset.mem_singleton] at hd
        subst hd
        have := congrArg Prod.fst (Finset.mem_singleton.mp hr.1)
        simp only at this
        omega
    · intro hx
      exact Or.inl ⟨z, Finset.mem_singleton_self z, hx⟩
  rw [he, cellSchur_translate]

theorem compositionMap_h_one (η : MarkedInner) :
    compositionMap η (hPos 1) = cellSchur η.E := by
  rw [compositionMap_hPos η le_rfl]
  have : rowCells 0 (((1 : ℕ)) : ℤ) = {((0 : ℤ), (0 : ℤ))} := by
    ext ⟨a, b⟩; simp [rowCells]; omega
  rw [this, cellSchur_compose_single]
  simp

/-- **`V_p s_E = ρ χ`** (`rt:mixed-intertwining`, second clause). -/
theorem wDeriv_period_inner (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) :
    wDeriv η.period.toNat (cellSchur η.E) =
      C (((s - t : ℤ) : ℚ)) * mixedChi η := by
  have h1 := mixed_covariance_d h hd hph hlt (k := 1) le_rfl (hPos 1)
  rw [compositionMap_h_one, mixedOp_hPos _ _ one_pos, if_pos le_rfl] at h1
  simp only [one_mul, pow_one, Nat.sub_self, hPos_zero, compositionMap_C_mul, compositionMap_C, map_one, mul_one,
    Nat.cast_one, sub_self, mul_zero, zero_add] at h1
  rw [h1]
  ring

/-- A mixed mark in case (d), obtained from a mixed legal mark by whole rotation. -/
def Gluing.MarkedInner.dForm (η : MarkedInner) : MarkedInner := if η.case = .c then η.rotate else η

theorem dForm_case_d (hm : η.case.IsMixed) : η.dForm.case = .d := by
  unfold Gluing.MarkedInner.dForm
  rcases hm with hc | hd
  · simp [hc, MarkedInner.rotate_case, AttachCase.rotate]
  · simp [hd]

theorem dForm_legal (h : η.IsLegal) : η.dForm.IsLegal := by
  unfold Gluing.MarkedInner.dForm
  split_ifs
  · exact Gluing.MarkedInner.isLegal_rotate h
  · exact h

theorem dForm_period (η : MarkedInner) : η.dForm.period = η.period := by
  unfold Gluing.MarkedInner.dForm
  split_ifs <;> rfl

theorem dForm_legalNonempty (h : η.IsLegal) (hm : η.case.IsMixed) : η.dForm.IsLegalNonempty := by
  have hl := dForm_legal h
  have hd := dForm_case_d hm
  refine ⟨hl, ?_⟩
  rcases hl.1.2 with h' | h'
  · have hc := h'.2.2
    rw [hd] at hc
    cases hc
  · exact h'.1


theorem cellSchur_rowComposite_rotate (η : MarkedInner) {j : ℕ} (hj : 1 ≤ j) :
    cellSchur (η.rotate.compose (rowCells 0 (j : ℤ))) =
      cellSchur (η.compose (rowCells 0 (j : ℤ))) := by
  have hjz : (0 : ℤ) < j := by exact_mod_cast hj
  have hne := rowCells_nonempty hjz
  have hrot : Gluing.rotate (rowCells 0 (j : ℤ)) =
      translate ((0 : ℤ), 1 - (j : ℤ)) (rowCells 0 (j : ℤ)) := by
    ext ⟨a, b⟩
    simp only [Gluing.mem_rotate, mem_translate, mem_rowCells, Prod.neg_mk, Prod.mk_sub_mk]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨by omega, by omega, by omega⟩
  have hne' : (Gluing.rotate (rowCells 0 (j : ℤ))).Nonempty := hne.image _
  have h1 := Gluing.MarkedInner.cellSchur_compose_rotate_outer hne' η
  have h2 := Gluing.MarkedInner.compose_translate_outer ((0 : ℤ), 1 - (j : ℤ)) hne η
  rw [Gluing.rotate_rotate] at h1
  rw [← h1, hrot, h2, cellSchur_translate]


theorem modifiedGen_rotate (η : MarkedInner) (j : ℕ+) :
    modifiedGen η.rotate j = modifiedGen η j := by
  unfold modifiedGen
  rw [rowComposite_eq, rowComposite_eq, cellSchur_rowComposite_rotate η j.pos]
  unfold normalizerRow
  rw [Gluing.Plan.MarkedInner.cellSchur_W_rotate]

/-- Whole rotation does not change the composition map. -/
theorem compositionMap_rotate (η : MarkedInner) : compositionMap η.rotate = compositionMap η := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [compositionMap_X, compositionMap_X, modifiedGen_rotate]

theorem mixedChi_rotate (h : η.IsLegal) : mixedChi η.rotate = mixedChi η := by
  unfold mixedChi normalizerRow normalizerColumn normalizerDiagonal
  rw [Gluing.Plan.MarkedInner.cellSchur_W_rotate, Gluing.Plan.MarkedInner.cellSchur_hatMarkFin_rotate h.1 h.2.2.1,
    Gluing.Plan.MarkedInner.cellSchur_hatMiddleFin_rotate]
  rfl

theorem compositionMap_dForm (η : MarkedInner) : compositionMap η.dForm = compositionMap η := by
  unfold Gluing.MarkedInner.dForm
  split_ifs
  · exact compositionMap_rotate η
  · rfl

theorem mixedChi_dForm (h : η.IsLegal) : mixedChi η.dForm = mixedChi η := by
  unfold Gluing.MarkedInner.dForm
  split_ifs
  · exact mixedChi_rotate h
  · rfl

/-- **Mixed weighted covariance** (`rt:mixed-covariance`) for an arbitrary legal mixed mark, in the
positive-phase convention: `s, t` are the phases of the case-(d) form obtained by whole rotation.
`V_{kp} Ψ_η = χ^k Ψ_η (p V_k + ρ δ_k)`, `ρ = s - t`. -/
theorem mixed_covariance (h : η.IsLegal) (hm : η.case.IsMixed) {s t : ℤ}
    (hph : η.dForm.IsPhases s t) {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    wDeriv (k * η.period.toNat) (compositionMap η f) =
      mixedChi η ^ k * compositionMap η (mixedOp (η.period : ℚ) ((s - t : ℤ) : ℚ) k f) := by
  have hn := dForm_legalNonempty h hm
  have hd := dForm_case_d hm
  have hlt := hn.phases_lt (Or.inr hd) hph
  have := mixed_covariance_d hn hd hph hlt hk f
  rwa [dForm_period, compositionMap_dForm, mixedChi_dForm h] at this

/-- **`V_p s_E = ρ χ`** for an arbitrary legal mixed mark. -/
theorem wDeriv_period_inner_mixed (h : η.IsLegal) (hm : η.case.IsMixed) {s t : ℤ}
    (hph : η.dForm.IsPhases s t) :
    wDeriv η.period.toNat (cellSchur η.E) = C (((s - t : ℤ) : ℚ)) * mixedChi η := by
  have hn := dForm_legalNonempty h hm
  have hd := dForm_case_d hm
  have hlt := hn.phases_lt (Or.inr hd) hph
  have := wDeriv_period_inner hn hd hph hlt
  rw [dForm_period, mixedChi_dForm h] at this
  unfold Gluing.MarkedInner.dForm at this
  split_ifs at this
  · have e : cellSchur η.rotate.E = cellSchur η.E := Gluing.cellSchur_rotate _
    rw [e] at this
    exact this
  · exact this

end SkewMarkedFactor
