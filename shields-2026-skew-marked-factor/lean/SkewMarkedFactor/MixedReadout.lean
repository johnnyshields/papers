/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MixedChain
import SkewMarkedFactor.AllTypeNormalization
import SkewMarkedFactor.RibbonNonvanishing
import SkewMarkedFactor.ReducedNumerator
import SkewMarkedFactor.FactorRecovery
import SkewMarkedFactor.PowerCoordinates

/-!
# Recovering mixed ribbon factors

«Recovering mixed ribbon factors» (`rt:mixed-readout`, `lem:terminal-readout`,
`eq:mixed-terminal-ratio`, `rt:outer-triangle`, `eq:mixed-readout`) of
`shields-2026-skew-marked-factor.tex`, for a legal mark in case (d) and a ribbon outer; case (c)
is reduced to it by whole rotation.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

variable {η : MarkedInner}

theorem vKilled_normalizers (h : η.IsLegal) :
    VKilled η.period.toNat (normalizerRow η) ∧ VKilled η.period.toNat (normalizerColumn η) ∧
      VKilled η.period.toNat (normalizerDiagonal η) :=
  ⟨fun a ha => (wDeriv_normalizers_eq_zero h ha).1, fun a ha => (wDeriv_normalizers_eq_zero h ha).2.1,
    fun a ha => (wDeriv_normalizers_eq_zero h ha).2.2⟩

theorem vKilled_mixedChi (h : η.IsLegal) : VKilled η.period.toNat (mixedChi η) := by
  obtain ⟨hA, hB, hC⟩ := vKilled_normalizers h
  exact (VKilled.neg_one_pow _ _).mul ((hA.mul hB).mul hC)

theorem vKilled_fullNormalizer (h : η.IsLegal) (D : Diagram) :
    VKilled η.period.toNat (fullNormalizer η D) := by
  obtain ⟨hA, hB, hC⟩ := vKilled_normalizers h
  exact (VKilled.neg_one_pow _ _).mul (((hA.pow _).mul (hB.pow _)).mul (hC.pow _))

theorem mixedChi_ne_zero (h : η.IsLegal) : mixedChi η ≠ 0 := by
  obtain ⟨hA, hB, hC⟩ := normalizers_ne_zero h.readoutLegal
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero (mul_ne_zero hA hB) hC)

theorem fullNormalizer_ne_zero (h : η.IsLegal) (D : Diagram) : fullNormalizer η D ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (normalization_ne_zero h.readoutLegal D)

/-- **Weighted chain of a mixed parent** (`eq:mixed-terminal-ratio`, `rt:outer-triangle`),
case (d), ribbon outer `D` of `m` cells, `ρ = s - t`: the terminal order of `V_p` on the parent
is `m`, and the penultimate and terminal derivatives satisfy
`V_p^{m-1} P · (V_p s_E) = V_p^m P · s_E`, `V_p s_E = ρ χ`; and every word `V_{pν}`, `ν ⊢ m`,
is the scalar `B_ν s_D / B_1^m s_D` times the terminal derivative. -/
theorem mixed_chain (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) {D : Diagram} (hD : IsRibbon D) :
    ∃ κ : ℚ, κ ≠ 0 ∧
      mixedWord (η.period : ℚ) ((s - t : ℤ) : ℚ) (List.replicate D.card 1) (cellSchur D) = C κ ∧
      (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) ≠ 0 ∧
      (∀ j, D.card < j → (wDeriv η.period.toNat)^[j] (cellSchur (η.compose D)) = 0) ∧
      (wDeriv η.period.toNat)^[D.card - 1] (cellSchur (η.compose D)) *
          wDeriv η.period.toNat (cellSchur η.E) =
        (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) * cellSchur η.E ∧
      ∀ ν : List ℕ, (∀ a ∈ ν, 0 < a) → ν.sum = D.card → ∃ c : ℚ,
        mixedWord (η.period : ℚ) ((s - t : ℤ) : ℚ) ν (cellSchur D) = C c ∧
        C κ * wWord η.period.toNat ν (cellSchur (η.compose D)) =
          C c * (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) := by
  have hl := h.1
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hpp : 0 < η.period := hl.period_pos
  have hρpos : (0 : ℚ) < ((s - t : ℤ) : ℚ) := by exact_mod_cast (by omega : 0 < s - t)
  have hpposq : (0 : ℚ) < (η.period : ℚ) := by exact_mod_cast hpp
  have hρlt : ((s - t : ℤ) : ℚ) < (η.period : ℚ) := by exact_mod_cast (by omega : s - t < η.period)
  have hx0 : 0 < ((s - t : ℤ) : ℚ) / (η.period : ℚ) := div_pos hρpos hpposq
  have hx1 : ((s - t : ℤ) : ℚ) / (η.period : ℚ) < 1 := (div_lt_one hpposq).mpr hρlt
  have hκ := ribbon_powerSumSpecialize_ne_zero hD hx0 hx1
  have hm : 1 ≤ D.card := hD.1.2.1.card_pos
  have key := weighted_chain η.period.toNat (η.period : ℚ) ((s - t : ℤ) : ℚ) hpposq.ne' hρpos.ne'
    (compositionMap η) (mixedChi η) (fullNormalizer η D) (vKilled_mixedChi hl)
    (vKilled_fullNormalizer hl D) (fullNormalizer_ne_zero hl D) (mixedChi_ne_zero hl)
    (fun k hk f => mixed_covariance_d h hd hph hlt hk f) (cellSchur (η.compose D)) (cellSchur D)
    hm (isWeightedHomogeneous_cellSchur hD.1.1) hκ
    (compositionMap_cellSchur hl hD.1).symm
  obtain ⟨κ, hκ0, hκe, hV, hV0, hratio, hν⟩ := key
  refine ⟨κ, hκ0, hκe, hV, hV0, ?_, hν⟩
  rw [wDeriv_period_inner h hd hph hlt, ← compositionMap_h_one η]
  exact hratio


theorem wIterate_penultimate_ne_zero {q m : ℕ} {P : Lambda} (hm : 1 ≤ m)
    (h : (wDeriv q)^[m] P ≠ 0) : (wDeriv q)^[m - 1] P ≠ 0 := by
  intro h0
  apply h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  simp only [Nat.add_sub_cancel] at h0
  rw [h0, Derivation.map_zero]

/-- The inner factor is coprime to the derivative `V_p s_E = ρ χ`. -/
theorem mixed_inner_coprime (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) :
    IsRelPrime (cellSchur η.E) (wDeriv η.period.toNat (cellSchur η.E)) := by
  have hl := h.1
  have hconn : IsConnectedSkew η.E := hl.1.1
  have hirr : Irreducible (cellSchur η.E) := by
    rw [cellSchur_of_isConnectedSkew hconn]
    exact irreducible_schur _ _
  apply relPrime_of_irreducible_not_dvd hirr
  have hpp : 0 < η.period.toNat := by have := hl.period_pos; omega
  have hE : 1 ≤ η.E.card := hconn.2.1.card_pos
  have hhom := (wDeriv_homogeneous (k := η.period.toNat)
    (isWeightedHomogeneous_cellSchur hconn.1)).1
  have hne : wDeriv η.period.toNat (cellSchur η.E) ≠ 0 := by
    rw [wDeriv_period_inner h hd hph hlt]
    refine mul_ne_zero ?_ (mixedChi_ne_zero hl)
    intro h0
    have := MvPolynomial.C_injective _ _ (h0.trans (map_zero C).symm)
    have : (0 : ℚ) < ((s - t : ℤ) : ℚ) := by
      have hs := hph; obtain ⟨-, -, -, -, -, -⟩ := hs; exact_mod_cast (by omega : 0 < s - t)
    linarith
  exact not_dvd_of_weightedDegree_lt
    (show IsWeightedHomogeneous lambdaWeight (wDeriv η.period.toNat (cellSchur η.E))
      (η.E.card - η.period.toNat) from hhom)
    (show IsWeightedHomogeneous lambdaWeight (cellSchur η.E) η.E.card from
      isWeightedHomogeneous_cellSchur hconn.1) (by omega) hne

/-- **Inner readout** (`eq:mixed-terminal-ratio`): the primitive gcd-reduced numerator of the
penultimate over the terminal derivative is the inner Schur function. -/
theorem mixed_inner_readout (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) {D : Diagram} (hD : IsRibbon D) :
    primitive (reducedNumerator
      ((wDeriv η.period.toNat)^[D.card - 1] (cellSchur (η.compose D)))
      ((wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)))) = cellSchur η.E := by
  obtain ⟨κ, -, -, hV, -, hratio, -⟩ := mixed_chain h hd hph hlt hD
  have hm : 1 ≤ D.card := hD.1.2.1.card_pos
  exact primitive_reducedNumerator_of_ratio h.1.1.1.1 (wIterate_penultimate_ne_zero hm hV)
    (mixed_inner_coprime h hd hph hlt) hratio


/-! ### Recovery of the phase difference from the content of `V_p s_E` -/

theorem least_scaled {X : Lambda} {m : MonomialIndex} (hX : coefficientOneMinimum X m) {c : ℚ}
    (hc : c ≠ 0) : leastMonomial (c • X).support = m ∧ (c • X).coeff m = c := by
  have hcoef : (c • X).coeff m = c := by rw [coeff_smul, smul_eq_mul, hX.1, mul_one]
  refine ⟨least_monomial_eq (by rw [hcoef]; exact hc) (fun n hn hne => ?_), hcoef⟩
  refine hX.2 n ?_ hne
  intro h0
  apply hn
  rw [coeff_smul, smul_eq_mul, h0, mul_zero]

theorem coefficient_one_minimum_normalizers (h : η.IsLegal) :
    ∃ m, coefficientOneMinimum (normalizerRow η * normalizerColumn η * normalizerDiagonal η) m :=
  ⟨_, coefficient_one_minimum_mul
    (coefficient_one_minimum_mul (coefficient_one_minimum_cell_schur h.isSkew_W)
      (coefficient_one_minimum_cell_schur h.isSkew_hatMarkFin))
    (coefficient_one_minimum_cell_schur h.isSkew_hatMiddleFin)⟩

/-- `V_p s_E` is `ρ` times a function with a unit extreme coefficient. -/
theorem wDeriv_period_inner_least (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) :
    ∃ (m : MonomialIndex) (ε : ℚ), (ε = 1 ∨ ε = -1) ∧
      leastMonomial (wDeriv η.period.toNat (cellSchur η.E)).support = m ∧
      (wDeriv η.period.toNat (cellSchur η.E)).coeff m = ((s - t : ℤ) : ℚ) * ε := by
  obtain ⟨m, hm⟩ := coefficient_one_minimum_normalizers h.1
  have hρ : ((s - t : ℤ) : ℚ) ≠ 0 := by
    obtain ⟨-, -, -, -, -, -⟩ := id hph
    exact_mod_cast (by omega : s - t ≠ 0)
  have e : wDeriv η.period.toNat (cellSchur η.E) =
      (((s - t : ℤ) : ℚ) * ((-1 : ℚ) ^ (-η.v.1).toNat)) •
        (normalizerRow η * normalizerColumn η * normalizerDiagonal η) := by
    rw [wDeriv_period_inner h hd hph hlt, mixedChi, MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [map_pow, map_neg, map_one]
    ring
  have hsign : ((-1 : ℚ) ^ (-η.v.1).toNat = 1 ∨ (-1 : ℚ) ^ (-η.v.1).toNat = -1) :=
    neg_one_pow_eq_or ℚ _
  have hne : ((s - t : ℤ) : ℚ) * ((-1 : ℚ) ^ (-η.v.1).toNat) ≠ 0 :=
    mul_ne_zero hρ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  obtain ⟨hl, hc⟩ := least_scaled hm hne
  refine ⟨m, (-1 : ℚ) ^ (-η.v.1).toNat, hsign, ?_, ?_⟩
  · rw [e]; exact hl
  · rw [e]; exact hc

theorem phase_unique {η η' : MarkedInner} (h : η.IsLegalNonempty) (h' : η'.IsLegalNonempty)
    (hd : η.case = .d) (hd' : η'.case = .d) {s t s' t' : ℤ} (hph : η.IsPhases s t)
    (hph' : η'.IsPhases s' t') (hlt : t < s) (hlt' : t' < s')
    (hp : η.period = η'.period) (hE : cellSchur η.E = cellSchur η'.E) : s - t = s' - t' := by
  obtain ⟨m, ε, hε, hl, hc⟩ := wDeriv_period_inner_least h hd hph hlt
  obtain ⟨m', ε', hε', hl', hc'⟩ := wDeriv_period_inner_least h' hd' hph' hlt'
  have hpt : η.period.toNat = η'.period.toNat := by rw [hp]
  rw [hpt, hE] at hl hc
  have hmm : m = m' := hl.symm.trans hl'
  subst hmm
  have := hc.symm.trans hc'
  have hρ : (0 : ℚ) < ((s - t : ℤ) : ℚ) := by
    obtain ⟨-, -, -, -, -, -⟩ := id hph
    exact_mod_cast (by omega : 0 < s - t)
  have hρ' : (0 : ℚ) < ((s' - t' : ℤ) : ℚ) := by
    obtain ⟨-, -, -, -, -, -⟩ := id hph'
    exact_mod_cast (by omega : 0 < s' - t')
  have habs := congrArg abs this
  rw [abs_mul, abs_mul, abs_of_pos hρ, abs_of_pos hρ'] at habs
  have h1 : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  have h2 : |ε'| = 1 := by rcases hε' with rfl | rfl <;> simp
  rw [h1, h2] at habs
  have h3 : ((s - t : ℤ) : ℚ) = ((s' - t' : ℤ) : ℚ) := by simpa using habs
  exact_mod_cast h3


/-! ### Whole rotation to case (d) -/

theorem dForm_E_schur (η : MarkedInner) : cellSchur η.dForm.E = cellSchur η.E := by
  unfold Gluing.MarkedInner.dForm
  split_ifs
  · exact Gluing.cellSchur_rotate _
  · rfl

theorem mixed_dForm_outer (η : MarkedInner) (D : Diagram) (hD : IsRibbon D) :
    ∃ D0, IsRibbon D0 ∧ D0.card = D.card ∧ cellSchur D0 = cellSchur D ∧
      cellSchur (η.dForm.compose D0) = cellSchur (η.compose D) := by
  unfold Gluing.MarkedInner.dForm
  split_ifs with hc
  · refine ⟨Gluing.rotate D, Gluing.Plan.MN.isRibbon_rotate.mpr hD, Gluing.Plan.MN.card_rotate D,
      Gluing.cellSchur_rotate D, ?_⟩
    exact (Gluing.MarkedInner.cellSchur_compose_rotate_outer hD.1.2.1 η).symm
  · exact ⟨D, hD, rfl, rfl, rfl⟩

theorem eq_of_scaled_cellSchur {D D' : Diagram} (hD : IsSkew D) (hD' : IsSkew D') {a b : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : a • cellSchur D = b • cellSchur D') :
    cellSchur D = cellSchur D' := by
  have h1 := primitive_cellSchur_scalar hD a ha
  have h2 := primitive_cellSchur_scalar hD' b hb
  rw [← h1, ← h2, h]

theorem const_mul_cancel {a b : ℚ} {V : Lambda} (hV : V ≠ 0)
    (h : (C a : Lambda) * V = C b * V) : a = b := by
  have := mul_right_cancel₀ hV h
  exact MvPolynomial.C_injective _ _ this

/-- **Outer readout from the word quotients** (`rt:outer-triangle`): two homogeneous functions of
weight `m` whose `B_ν` values are proportional to the same word derivatives of `P`, with the same
`ρ > 0`, are proportional. -/
theorem outer_proportional (q : ℕ) (p ρ : ℚ) (hρ : 0 < ρ) {P V : Lambda} (hV : V ≠ 0) {m : ℕ}
    {u u' : Lambda} (hu : IsWeightedHomogeneous degWeight u m)
    (hu' : IsWeightedHomogeneous degWeight u' m) {κ κ' : ℚ}
    (hν : ∀ ν : List ℕ, (∀ a ∈ ν, 0 < a) → ν.sum = m → ∃ c : ℚ,
      mixedWord p ρ ν u = C c ∧ C κ * wWord q ν P = C c * V)
    (hν' : ∀ ν : List ℕ, (∀ a ∈ ν, 0 < a) → ν.sum = m → ∃ c : ℚ,
      mixedWord p ρ ν u' = C c ∧ C κ' * wWord q ν P = C c * V) :
    κ' • u = κ • u' := by
  have hg : κ' • u - κ • u' = 0 := by
    refine readout_injective p ρ hρ (((by rw [MvPolynomial.smul_eq_C_mul]; exact hu.C_mul κ' :
      IsWeightedHomogeneous degWeight (κ' • u) m).sub
      (by rw [MvPolynomial.smul_eq_C_mul]; exact hu'.C_mul κ :
      IsWeightedHomogeneous degWeight (κ • u') m))) ?_
    intro ν hpos hsum hdec
    obtain ⟨c, hc, hcw⟩ := hν ν hpos hsum
    obtain ⟨c', hc', hcw'⟩ := hν' ν hpos hsum
    have hmul : C κ' * (C κ * wWord q ν P) = C κ * (C κ' * wWord q ν P) := by ring
    rw [hcw, hcw', ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul] at hmul
    have e : κ' * c = κ * c' := const_mul_cancel hV hmul
    rw [map_sub, map_smul, map_smul, hc, hc']
    simp only [MvPolynomial.smul_eq_C_mul, ← map_mul]
    rw [e, sub_self]
  exact sub_eq_zero.mp hg

/-- **Recovery of the factors of a mixed ribbon chart** (`rt:mixed-readout`): two legal mixed
charts with ribbon outers, the same period, and the same parent function have the same inner
function and the same outer function. -/
theorem mixed_factor_recovery {η η' : MarkedInner} (h : η.IsLegal) (h' : η'.IsLegal)
    (hm : η.case.IsMixed) (hm' : η'.case.IsMixed) {D D' : Diagram} (hD : IsRibbon D)
    (hD' : IsRibbon D') (hp : η.period = η'.period)
    (hP : cellSchur (η.compose D) = cellSchur (η'.compose D')) :
    cellSchur η.E = cellSchur η'.E ∧ cellSchur D = cellSchur D' := by
  obtain ⟨D0, hD0, hc0, hs0, hP0⟩ := mixed_dForm_outer η D hD
  obtain ⟨D1, hD1, hc1, hs1, hP1⟩ := mixed_dForm_outer η' D' hD'
  have hn := dForm_legalNonempty h hm
  have hn' := dForm_legalNonempty h' hm'
  have hd := dForm_case_d hm
  have hd' := dForm_case_d hm'
  obtain ⟨s, t, hph⟩ := hn.exists_phases
  obtain ⟨s', t', hph'⟩ := hn'.exists_phases
  have hlt := hn.phases_lt (Or.inr hd) hph
  have hlt' := hn'.phases_lt (Or.inr hd') hph'
  have hpd : η.dForm.period = η'.dForm.period := by rw [dForm_period, dForm_period, hp]
  have hPeq : cellSchur (η.dForm.compose D0) = cellSchur (η'.dForm.compose D1) := by
    rw [hP0, hP1, hP]
  obtain ⟨κ, hκ0, hκe, hV, hVz, hrat, hν⟩ := mixed_chain hn hd hph hlt hD0
  obtain ⟨κ', hκ0', hκe', hV', hVz', hrat', hν'⟩ := mixed_chain hn' hd' hph' hlt' hD1
  have hpt : η'.dForm.period.toNat = η.dForm.period.toNat := by rw [hpd]
  rw [← hPeq, hpt] at hV' hVz' hrat' hν'
  have hcard : D0.card = D1.card := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt2 | hlt2
    · exact hV' (hVz _ hlt2)
    · exact hV (hVz' _ hlt2)
  have hE : cellSchur η.dForm.E = cellSchur η'.dForm.E := by
    have e1 := mixed_inner_readout hn hd hph hlt hD0
    have e2 := mixed_inner_readout hn' hd' hph' hlt' hD1
    rw [← hPeq, hpt, ← hcard] at e2
    exact e1.symm.trans e2
  have hρ : s - t = s' - t' := phase_unique hn hn' hd hd' hph hph' hlt hlt' hpd hE
  refine ⟨by rw [← dForm_E_schur η, ← dForm_E_schur η', hE], ?_⟩
  have hρpos : (0 : ℚ) < ((s - t : ℤ) : ℚ) := by
    obtain ⟨-, -, -, -, -, -⟩ := id hph
    exact_mod_cast (by omega : 0 < s - t)
  have hpq : ((η'.dForm.period : ℤ) : ℚ) = ((η.dForm.period : ℤ) : ℚ) := by rw [hpd]
  have hρq : ((s' - t' : ℤ) : ℚ) = ((s - t : ℤ) : ℚ) := by rw [hρ]
  rw [hpq, hρq, ← hcard] at hν'
  have hprop := outer_proportional η.dForm.period.toNat (η.dForm.period : ℚ) ((s - t : ℤ) : ℚ)
    hρpos hV (isWeightedHomogeneous_cellSchur hD0.1.1)
    (by rw [hcard]; exact isWeightedHomogeneous_cellSchur hD1.1.1) hν hν'
  have := eq_of_scaled_cellSchur hD0.1.1 hD1.1.1 hκ0' hκ0 hprop
  rw [← hs0, ← hs1, this]


/-! ### The displays for an arbitrary legal mixed mark -/

/-- The positive phase difference `ρ = s - t` of a mixed mark, from its case-(d) form. -/
theorem mixed_rho_exists (h : η.IsLegal) (hm : η.case.IsMixed) :
    ∃ s t : ℤ, η.dForm.IsPhases s t ∧ t < s := by
  have hn := dForm_legalNonempty h hm
  obtain ⟨s, t, hph⟩ := hn.exists_phases
  exact ⟨s, t, hph, hn.phases_lt (Or.inr (dForm_case_d hm)) hph⟩

/-- **Terminal data of a mixed ribbon chart** (`eq:mixed-terminal-ratio`, `eq:mixed-readout`,
`rt:outer-triangle`): for a legal mixed mark and ribbon outer `D` of `M` cells with parent
`P = s_{D ∘_η E}`, in the positive-phase convention with `ρ = s - t`:
the terminal order of `V_p` on `P` is `M`; `V_p^{M-1} P · V_p s_E = V_p^M P · s_E`, where
`V_p s_E = ρ χ` is nonzero; and every word quotient `V_{pν} P / V_p^M P` is the quotient
`B_ν s_D / B_1^M s_D`. -/
theorem mixed_terminal_data (h : η.IsLegal) (hm : η.case.IsMixed) {s t : ℤ}
    (hph : η.dForm.IsPhases s t) (hlt : t < s) {D : Diagram} (hD : IsRibbon D) :
    ∃ κ : ℚ, κ ≠ 0 ∧
      mixedWord (η.period : ℚ) ((s - t : ℤ) : ℚ) (List.replicate D.card 1) (cellSchur D) = C κ ∧
      (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) ≠ 0 ∧
      (∀ j, D.card < j → (wDeriv η.period.toNat)^[j] (cellSchur (η.compose D)) = 0) ∧
      wDeriv η.period.toNat (cellSchur η.E) = C ((s - t : ℤ) : ℚ) * mixedChi η ∧
      wDeriv η.period.toNat (cellSchur η.E) ≠ 0 ∧
      (wDeriv η.period.toNat)^[D.card - 1] (cellSchur (η.compose D)) *
          wDeriv η.period.toNat (cellSchur η.E) =
        (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) * cellSchur η.E ∧
      ∀ ν : List ℕ, (∀ a ∈ ν, 0 < a) → ν.sum = D.card → ∃ c : ℚ,
        mixedWord (η.period : ℚ) ((s - t : ℤ) : ℚ) ν (cellSchur D) = C c ∧
        C κ * wWord η.period.toNat ν (cellSchur (η.compose D)) =
          C c * (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) := by
  obtain ⟨D0, hD0, hc0, hs0, hP0⟩ := mixed_dForm_outer η D hD
  have hn := dForm_legalNonempty h hm
  have hd := dForm_case_d hm
  obtain ⟨κ, hκ0, hκe, hV, hVz, hrat, hν⟩ := mixed_chain hn hd hph hlt hD0
  have hpt : η.dForm.period.toNat = η.period.toNat := by rw [dForm_period]
  have hpq : ((η.dForm.period : ℤ) : ℚ) = ((η.period : ℤ) : ℚ) := by rw [dForm_period]
  have hEs := dForm_E_schur η
  have hinner := wDeriv_period_inner hn hd hph hlt
  rw [mixedChi_dForm h, hpt, hEs] at hinner
  simp only [hpt, hpq, hc0, hs0, hP0, hEs] at hV hVz hrat hν hκe
  have hne : wDeriv η.period.toNat (cellSchur η.E) ≠ 0 := by
    rw [hinner]
    refine mul_ne_zero ?_ (mixedChi_ne_zero h)
    intro h0
    have h1 := MvPolynomial.C_injective _ _ (h0.trans (map_zero C).symm)
    obtain ⟨-, -, -, -, -, -⟩ := id hph
    have : (0 : ℚ) < ((s - t : ℤ) : ℚ) := by exact_mod_cast (by omega : 0 < s - t)
    linarith
  exact ⟨κ, hκ0, hκe, hV, hVz, hinner, hne, by rw [hinner]; rw [hinner] at hrat; exact hrat, hν⟩


/-- A cross-multiplied identity gives equality of the genuine fraction-field quotients. -/
theorem actualRatio_eq_of_cross {a b c d : Lambda} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = b * c) :
    actualRatio a b = actualRatio c d := by
  have hb' : algebraMap Lambda ReadoutField b ≠ 0 :=
    fun h0 => hb ((IsFractionRing.injective Lambda ReadoutField) (by simpa using h0))
  have hd' : algebraMap Lambda ReadoutField d ≠ 0 :=
    fun h0 => hd ((IsFractionRing.injective Lambda ReadoutField) (by simpa using h0))
  unfold actualRatio
  rw [div_eq_div_iff hb' hd', ← map_mul, ← map_mul, h, mul_comm]

/-- **Terminal readout, mixed clause** (`lem:terminal-readout`, `eq:mixed-readout`): for a legal
mixed mark and a ribbon outer of `M` cells, both denominators are nonzero and the ratio of
the last two weighted derivatives of the parent is `s_E / (ρ χ)` in the fraction field. -/
theorem mixed_terminal_readout (h : η.IsLegal) (hm : η.case.IsMixed) {s t : ℤ}
    (hph : η.dForm.IsPhases s t) (hlt : t < s) {D : Diagram} (hD : IsRibbon D) :
    (wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)) ≠ 0 ∧
      C ((s - t : ℤ) : ℚ) * mixedChi η ≠ 0 ∧
      actualRatio ((wDeriv η.period.toNat)^[D.card - 1] (cellSchur (η.compose D)))
          ((wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D))) =
        actualRatio (cellSchur η.E) (C ((s - t : ℤ) : ℚ) * mixedChi η) := by
  obtain ⟨κ, hκ0, hκe, hV, hVz, hinner, hne, hrat, hν⟩ := mixed_terminal_data h hm hph hlt hD
  rw [hinner] at hne hrat
  exact ⟨hV, hne, actualRatio_eq_of_cross hV hne hrat⟩

/-- **Terminal evaluation at a fractional alphabet** (`eq:mixed-terminal-evaluation`): for a
ribbon `D` with `m` cells, a nonzero period `p`, and `0 < ρ / p < 1`,
`B_1^m s_D = m! p^m s_D(1^{ρ/p}) ≠ 0`. -/
theorem mixed_terminal_evaluation {p ρ : ℚ} (hp : p ≠ 0) {D : Diagram} (hD : IsRibbon D)
    (hx0 : 0 < ρ / p) (hx1 : ρ / p < 1) :
    (mixedOp p ρ 1)^[D.card] (cellSchur D) =
        C ((D.card.factorial : ℚ) * p ^ D.card * powerSumSpecialize (ρ / p) (cellSchur D)) ∧
      (D.card.factorial : ℚ) * p ^ D.card * powerSumSpecialize (ρ / p) (cellSchur D) ≠ 0 := by
  refine ⟨mixedOp_iterate_terminal hp (isWeightedHomogeneous_cellSchur hD.1.1), ?_⟩
  have := ribbon_powerSumSpecialize_ne_zero hD hx0 hx1
  have hf : (D.card.factorial : ℚ) ≠ 0 := by exact_mod_cast D.card.factorial_ne_zero
  exact mul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hp)) this


/-- **Inner readout for an arbitrary legal mixed mark** (`eq:mixed-terminal-ratio`,
`rt:mixed-readout`): the primitive gcd-reduced numerator of `V_p^{M-1} P` over `V_p^M P` is `s_E`. -/
theorem mixed_inner_readout_general (h : η.IsLegal) (hm : η.case.IsMixed) {D : Diagram}
    (hD : IsRibbon D) :
    primitive (reducedNumerator
      ((wDeriv η.period.toNat)^[D.card - 1] (cellSchur (η.compose D)))
      ((wDeriv η.period.toNat)^[D.card] (cellSchur (η.compose D)))) = cellSchur η.E := by
  obtain ⟨s, t, hph, hlt⟩ := mixed_rho_exists h hm
  obtain ⟨κ, hκ0, hκe, hV, hVz, hinner, hne, hrat, hν⟩ := mixed_terminal_data h hm hph hlt hD
  have hmc : 1 ≤ D.card := hD.1.2.1.card_pos
  have hconn : IsConnectedSkew η.E := h.1.1
  have hirr : Irreducible (cellSchur η.E) := by
    rw [cellSchur_of_isConnectedSkew hconn]
    exact irreducible_schur _ _
  have hpp : 0 < η.period.toNat := by have := h.period_pos; omega
  have hE : 1 ≤ η.E.card := hconn.2.1.card_pos
  have hhom := (wDeriv_homogeneous (k := η.period.toNat)
    (isWeightedHomogeneous_cellSchur hconn.1)).1
  have hcop : IsRelPrime (cellSchur η.E) (wDeriv η.period.toNat (cellSchur η.E)) :=
    relPrime_of_irreducible_not_dvd hirr (not_dvd_of_weightedDegree_lt
      (show IsWeightedHomogeneous lambdaWeight (wDeriv η.period.toNat (cellSchur η.E))
        (η.E.card - η.period.toNat) from hhom)
      (show IsWeightedHomogeneous lambdaWeight (cellSchur η.E) η.E.card from
        isWeightedHomogeneous_cellSchur hconn.1) (by omega) hne)
  exact primitive_reducedNumerator_of_ratio hconn.1 (wIterate_penultimate_ne_zero hmc hV) hcop hrat

end SkewMarkedFactor
