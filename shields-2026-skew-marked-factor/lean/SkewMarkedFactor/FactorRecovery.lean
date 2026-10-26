/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.CanonicalReadout
import SkewMarkedFactor.RibbonWordEvaluation
import SkewMarkedFactor.MarkAtlas
import SkewMarkedFactor.Gluing.Irreducibility

/-!
# Factor recovery at a supplied period

«Recovering the factors» (`sec:extraction`, `thm:extraction`, `eq:terminal`,
`eq:penultimate`, `eq:last`, `eq:ratio`, `eq:inner-recovery`,
`eq:outer-recovery`) of `shields-2026-skew-marked-factor.tex`.
The recovery functions take only the parent polynomial and the supplied period.
The geometry supplies all normalization, nonvanishing, and coprimeness proofs.
Both ordinary attachment types include their empty-edge readings.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial
open scoped BigOperators

/-- The outer function in the convention selected by the ordinary attachment. -/
noncomputable def adjustedOuter (χ : Chart) : Lambda :=
  if χ.ω.case = .b then schurInvolution (cellSchur χ.D) else cellSchur χ.D

/-- Readout legality supplies a positive period even for the vertical empty edge. -/
theorem readout_period_pos {η : MarkedInner} (hη : η.IsReadoutLegal) :
    0 < η.period.toNat := by
  have hp : 0 < η.period := by
    rcases hη with h | ⟨hE, he⟩
    · exact h.period_pos
    · have h := (emptyMarkH_isLegal hE).period_pos
      have hp := MarkAtlas.empty_period_eq η.E
      rw [← hp] at h
      simpa only [← he] using h
  omega

private theorem word_mul_of_killed {ν : List ℕ} {a : Lambda}
    (ha : ∀ n ∈ ν, pDeriv n a = 0) (b : Lambda) :
    pDerivWord ν (a * b) = a * pDerivWord ν b := by
  induction ν generalizing b with
  | nil => rfl
  | cons n ν ih =>
    have hn := ha n (List.mem_cons_self)
    have ht : ∀ k ∈ ν, pDeriv k a = 0 := fun k hk => ha k (List.mem_cons_of_mem n hk)
    simp only [pDerivWord, LinearMap.comp_apply, Derivation.coeFn_coe]
    rw [Derivation.leibniz, hn]
    simp only [smul_eq_mul, mul_zero, add_zero]
    exact ih ht _

/-- The killed normalization can be moved past every actual period-scaled word. -/
theorem normalized_parent_word {χ : Chart} (hχ : χ.IsProperOrdinary)
    {ν : List ℕ} (hν : ∀ m ∈ ν, 0 < m) :
    normalizationFactor χ.ω χ.D *
      pDerivWord (ν.map (fun m => m * χ.period.toNat)) (cellSchur χ.parent) =
      (if χ.ω.case = .b then (-1 : Lambda) ^ (ν.sum - ν.length) else 1) *
        xi χ.ω ^ ν.sum * modifiedMap χ.ω (removalWord ν (shape χ.D)) := by
  have hn := modified_normalization_nonempty hχ.1.2.2.2 hχ.2 hχ.1.1.1 hχ.1.1.2.1
  have hk : ∀ n ∈ ν.map (fun m => m * χ.period.toNat),
      pDeriv n (normalizationFactor χ.ω χ.D) = 0 := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    exact normalization_killed hχ.1.2.2.2 χ.D (hν m hm)
  have hw := ordinary_diagram_word_action hχ.1.2.2.2 hχ.2 hχ.1.1.1 hν
  rw [hn] at hw
  change pDerivWord (ν.map (fun m => m * χ.period.toNat))
    (normalizationFactor χ.ω χ.D * cellSchur χ.parent) = _ at hw
  rw [word_mul_of_killed hk] at hw
  exact hw

/-- Repeated singletons carry no vertical outer sign. -/
theorem normalized_singleton_word {χ : Chart} (hχ : χ.IsProperOrdinary) (n : ℕ) :
    normalizationFactor χ.ω χ.D * deltaAt χ.period.toNat n (cellSchur χ.parent) =
      xi χ.ω ^ n * modifiedMap χ.ω (removalWord (List.replicate n 1) (shape χ.D)) := by
  have h := normalized_parent_word hχ (ν := List.replicate n 1) (by
    intro m hm
    have he : m = 1 := List.eq_of_mem_replicate hm
    omega)
  simpa [deltaAt, List.map_replicate] using h

/-- The terminal derivative has its actual tableau-count normalization. -/
theorem normalized_terminal {χ : Chart} (hχ : χ.IsProperOrdinary) :
    normalizationFactor χ.ω χ.D * deltaAt χ.period.toNat χ.D.card (cellSchur χ.parent) =
      xi χ.ω ^ χ.D.card * C (standardTableauCount χ.D : ℚ) := by
  rw [normalized_singleton_word hχ, modified_terminal_word]

/-- The penultimate derivative retains precisely the actual inner function. -/
theorem normalized_penultimate {χ : Chart} (hχ : χ.IsProperOrdinary) :
    normalizationFactor χ.ω χ.D * deltaAt χ.period.toNat (χ.D.card - 1)
      (cellSchur χ.parent) =
      xi χ.ω ^ (χ.D.card - 1) * C (standardTableauCount χ.D : ℚ) * cellSchur χ.ω.E := by
  rw [normalized_singleton_word hχ,
    modified_penultimate_word hχ.2 χ.D hχ.1.1.2.1, smul_eq_C_mul]
  ring

/-- Positivity of the genuine finite tableau set makes its rational count nonzero. -/
theorem tableau_scalar_ne_zero (D : Diagram) : (standardTableauCount D : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (standardTableauCount_pos D))

/-- The last derivative is nonzero, with no formal nonvanishing certificate. -/
theorem ordinary_terminal_ne_zero {χ : Chart} (hχ : χ.IsProperOrdinary) :
    deltaAt χ.period.toNat χ.D.card (cellSchur χ.parent) ≠ 0 := by
  have hn : xi χ.ω ^ χ.D.card * C (standardTableauCount χ.D : ℚ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (xi_ne_zero hχ.1.2.2.2 hχ.2))
      (by simpa using tableau_scalar_ne_zero χ.D)
  intro hz
  rw [← normalized_terminal hχ, hz, mul_zero] at hn
  exact hn rfl

/-- The next order vanishes before cancellation of the nonzero normalization. -/
theorem ordinary_next_eq_zero {χ : Chart} (hχ : χ.IsProperOrdinary) :
    deltaAt χ.period.toNat (χ.D.card + 1) (cellSchur χ.parent) = 0 := by
  apply (mul_eq_zero.mp ?_).resolve_left (normalization_ne_zero hχ.1.2.2.2 χ.D)
  rw [normalized_singleton_word hχ, modified_next_word, mul_zero]

/-- The supplied-period terminal order is exactly the outer area. -/
theorem factor_recovery_order {χ : Chart} (hχ : χ.IsProperOrdinary) :
    terminalOrder (cellSchur χ.parent) χ.period.toNat = χ.D.card :=
  terminalOrder_eq_of_next (ordinary_terminal_ne_zero hχ) (ordinary_next_eq_zero hχ)

/-- A proper ordinary parent always survives its first supplied-period derivative. -/
theorem ordinary_parent_first_derivative_ne_zero {χ : Chart} (hχ : χ.IsProperOrdinary) :
    pDeriv χ.period.toNat (cellSchur χ.parent) ≠ 0 :=
  first_derivative_ne_zero (by have := hχ.1.2.1; omega) (ordinary_terminal_ne_zero hχ)

/-- The canonical last polynomial has a nonzero selected coefficient. -/
theorem terminalDerivative_ne_zero {χ : Chart} (hχ : χ.IsProperOrdinary) :
    terminalDerivative (cellSchur χ.parent) χ.period.toNat ≠ 0 := by
  simpa only [terminalDerivative, factor_recovery_order hχ] using ordinary_terminal_ne_zero hχ

/-- The canonical penultimate polynomial is nonzero. -/
theorem penultimateDerivative_ne_zero {χ : Chart} (hχ : χ.IsProperOrdinary) :
    penultimateDerivative (cellSchur χ.parent) χ.period.toNat ≠ 0 := by
  have hn := normalized_penultimate hχ
  have he := MarkFacts.cellSchur_ne_zero (MarkAtlas.inner_connected hχ.1.2.2.2).1
  have hz : xi χ.ω ^ (χ.D.card - 1) * C (standardTableauCount χ.D : ℚ) *
      cellSchur χ.ω.E ≠ 0 := mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (xi_ne_zero hχ.1.2.2.2 hχ.2))
      (show C (standardTableauCount χ.D : ℚ) ≠ (0 : Lambda) by
        simpa using tableau_scalar_ne_zero χ.D)) he
  intro h
  rw [penultimateDerivative, factor_recovery_order hχ] at h
  rw [h, mul_zero] at hn
  exact hz hn.symm

/-- The ratio is proved by cross multiplication without knowing any normalizer exponents. -/
theorem ordinary_cross_ratio {χ : Chart} (hχ : χ.IsProperOrdinary) :
    penultimateDerivative (cellSchur χ.parent) χ.period.toNat * xi χ.ω =
      terminalDerivative (cellSchur χ.parent) χ.period.toNat * cellSchur χ.ω.E := by
  apply mul_left_cancel₀ (normalization_ne_zero hχ.1.2.2.2 χ.D)
  simp only [penultimateDerivative, terminalDerivative, factor_recovery_order hχ]
  rw [← mul_assoc, normalized_penultimate hχ, ← mul_assoc, normalized_terminal hχ]
  have he : χ.D.card = (χ.D.card - 1) + 1 := by have := hχ.1.2.1; omega
  conv_rhs => rw [he, pow_succ]
  ring

/-- The actual connected inner is irreducible through its canonical cell profile. -/
theorem ordinary_inner_irreducible {χ : Chart} (hχ : χ.IsProperOrdinary) :
    Irreducible (cellSchur χ.ω.E) := by
  rw [cellSchur_of_isConnectedSkew (MarkAtlas.inner_connected hχ.1.2.2.2)]
  exact irreducible_schur _ _

/-- The strictly lower weighted degree of the actual multiplier proves coprimeness. -/
theorem ordinary_inner_coprime {χ : Chart} (hχ : χ.IsProperOrdinary) :
    IsRelPrime (cellSchur χ.ω.E) (xi χ.ω) := by
  apply relPrime_of_irreducible_not_dvd (ordinary_inner_irreducible hχ)
  apply not_dvd_of_weightedDegree_lt
    (show IsWeightedHomogeneous lambdaWeight (xi χ.ω) (χ.ω.E.card - χ.period.toNat) from
      xi_homogeneous hχ.1.2.2.2)
    (show IsWeightedHomogeneous lambdaWeight (cellSchur χ.ω.E) χ.ω.E.card from
      isWeightedHomogeneous_cellSchur (MarkAtlas.inner_connected hχ.1.2.2.2).1)
  · change χ.ω.E.card - χ.ω.period.toNat < χ.ω.E.card
    have hp : 0 < χ.ω.period.toNat := readout_period_pos hχ.1.2.2.2
    have hE : 2 ≤ χ.ω.E.card := hχ.1.2.2.1
    omega
  · exact xi_ne_zero hχ.1.2.2.2 hχ.2

/-- Primitive gcd reduction recovers the actual inner from the parent and supplied period. -/
theorem factor_recovery_inner {χ : Chart} (hχ : χ.IsProperOrdinary) :
    innerReadout (cellSchur χ.parent) χ.period.toNat = cellSchur χ.ω.E := by
  exact primitive_reducedNumerator_of_ratio
    (MarkAtlas.inner_connected hχ.1.2.2.2).1
    (penultimateDerivative_ne_zero hχ) (ordinary_inner_coprime hχ) (ordinary_cross_ratio hχ)

private theorem involution_C (q : ℚ) : schurInvolution (C q) = C q := by
  rw [← MvPolynomial.algebraMap_eq]
  exact AlgHom.commutes _ q

/-- Moving the involution across a positive word gives its genuine character sign. -/
theorem pDerivWord_involution {ν : List ℕ} (hν : ∀ n ∈ ν, 0 < n) (f : Lambda) :
    pDerivWord ν (schurInvolution f) =
      (-1 : Lambda) ^ (ν.sum - ν.length) * schurInvolution (pDerivWord ν f) := by
  induction ν generalizing f with
  | nil => simp [pDerivWord]
  | cons n ν ih =>
    have hn := hν n (List.mem_cons_self)
    have ht : ∀ k ∈ ν, 0 < k := fun k hk => hν k (List.mem_cons_of_mem n hk)
    have hlen := word_length_le_sum ht
    simp only [pDerivWord, LinearMap.comp_apply, Derivation.coeFn_coe]
    rw [pDeriv_schurInvolution hn,
      word_mul_of_killed (fun k _ => pDeriv_neg_one_pow k (n - 1)), ih ht]
    have he : n - 1 + (ν.sum - ν.length) = (n + ν.sum) - (ν.length + 1) := by omega
    simp only [List.sum_cons, List.length_cons]
    rw [← he, pow_add]
    ring

/-- The adjusted outer is an actual Schur function, including the vertical convention. -/
theorem adjustedOuter_cellSchur (χ : Chart) :
    adjustedOuter χ = cellSchur (if χ.ω.case = .b then antitranspose χ.D else χ.D) := by
  unfold adjustedOuter
  split_ifs <;> simp only [cellSchur_antitranspose]

/-- The convention change preserves the actual outer degree. -/
theorem adjustedOuter_homogeneous {χ : Chart} (hχ : χ.IsProperOrdinary) :
    IsWeightedHomogeneous degWeight (adjustedOuter χ) χ.D.card := by
  rw [adjustedOuter_cellSchur]
  split_ifs
  · simpa only [card_antitranspose] using
      isWeightedHomogeneous_cellSchur (isConnectedSkew_antitranspose hχ.1.1).1
  · exact isWeightedHomogeneous_cellSchur hχ.1.1.1

/-- The signed ordinary character is derived from the copied involution identity. -/
theorem adjustedOuter_character {χ : Chart} (hχ : χ.IsProperOrdinary)
    {d : powerExponent} (hd : Finsupp.weight degWeight d = χ.D.card) :
    C (characterCoefficient (adjustedOuter χ) d) =
      (if χ.ω.case = .b then (-1 : Lambda) ^ (χ.D.card - (exponentWord d).length) else 1) *
        C (characterCoefficient (cellSchur χ.D) d) := by
  rw [← deltaWord_exponentWord_coeff (adjustedOuter_homogeneous hχ) hd]
  unfold adjustedOuter
  split_ifs with hb
  · rw [pDerivWord_involution (exponentWord_positive d),
      deltaWord_exponentWord_coeff (isWeightedHomogeneous_cellSchur hχ.1.1.1) hd,
      involution_C, exponentWord_sum, hd]
  · rw [deltaWord_exponentWord_coeff (isWeightedHomogeneous_cellSchur hχ.1.1.1) hd,
      one_mul]

/-- Every complete period word has the same normalization power as the terminal word. -/
theorem normalized_character_word {χ : Chart} (hχ : χ.IsProperOrdinary)
    {d : powerExponent} (hd : Finsupp.weight degWeight d = χ.D.card) :
    normalizationFactor χ.ω χ.D * characterDerivative (cellSchur χ.parent) χ.period.toNat d =
      xi χ.ω ^ χ.D.card * C (characterCoefficient (adjustedOuter χ) d) := by
  rw [characterDerivative, periodWord, normalized_parent_word hχ (exponentWord_positive d),
    modified_map_total_word χ.ω hχ.1.1.1 _ (exponentWord_positive d)
      ((exponentWord_sum d).trans hd),
    deltaWord_exponentWord_coeff (isWeightedHomogeneous_cellSchur hχ.1.1.1) hd,
    exponentWord_sum, hd, adjustedOuter_character hχ hd]
  ring

/-- The actual character derivative is a rational multiple of the actual terminal polynomial. -/
theorem character_derivative_eq_scalar {χ : Chart} (hχ : χ.IsProperOrdinary)
    {d : powerExponent} (hd : d ∈ partitionExponents
      (terminalOrder (cellSchur χ.parent) χ.period.toNat)) :
    characterDerivative (cellSchur χ.parent) χ.period.toNat d =
      C (characterCoefficient (adjustedOuter χ) d / (standardTableauCount χ.D : ℚ)) *
        terminalDerivative (cellSchur χ.parent) χ.period.toNat := by
  have hd' : Finsupp.weight degWeight d = χ.D.card := by
    rw [factor_recovery_order hχ] at hd
    exact (mem_partitionExponents _ _).mp hd
  apply mul_left_cancel₀ (normalization_ne_zero hχ.1.2.2.2 χ.D)
  rw [normalized_character_word hχ hd']
  rw [mul_left_comm (normalizationFactor χ.ω χ.D),
    terminalDerivative, factor_recovery_order hχ, normalized_terminal hχ]
  have he : characterCoefficient (adjustedOuter χ) d /
      (standardTableauCount χ.D : ℚ) * (standardTableauCount χ.D : ℚ) =
      characterCoefficient (adjustedOuter χ) d :=
    div_mul_cancel₀ _ (tableau_scalar_ne_zero χ.D)
  calc
    xi χ.ω ^ χ.D.card * C (characterCoefficient (adjustedOuter χ) d) =
        xi χ.ω ^ χ.D.card * C (characterCoefficient (adjustedOuter χ) d /
          (standardTableauCount χ.D : ℚ) * (standardTableauCount χ.D : ℚ)) := by rw [he]
    _ = C (characterCoefficient (adjustedOuter χ) d /
        (standardTableauCount χ.D : ℚ)) *
        (xi χ.ω ^ χ.D.card * C (standardTableauCount χ.D : ℚ)) := by
      rw [map_mul]
      ring

/-- Complete-word quotients in the true fraction field are rational,
with exact character values. -/
theorem character_ratios_rational {χ : Chart} (hχ : χ.IsProperOrdinary)
    {d : powerExponent} (hd : d ∈ partitionExponents
      (terminalOrder (cellSchur χ.parent) χ.period.toNat)) :
    actualRatio (characterDerivative (cellSchur χ.parent) χ.period.toNat d)
      (terminalDerivative (cellSchur χ.parent) χ.period.toNat) =
      algebraMap ℚ ReadoutField
        (characterCoefficient (adjustedOuter χ) d / (standardTableauCount χ.D : ℚ)) :=
  actualRatio_eq_scalar (terminalDerivative_ne_zero hχ) (character_derivative_eq_scalar hχ hd)

/-- The canonical character readout recovers the adjusted outer
divided by its tableau count. -/
theorem factor_recovery_outer {χ : Chart} (hχ : χ.IsProperOrdinary) :
    outerReadout (cellSchur χ.parent) χ.period.toNat =
      (standardTableauCount χ.D : ℚ)⁻¹ • adjustedOuter χ := by
  classical
  rw [outerReadout, factor_recovery_order hχ,
    character_expansion (adjustedOuter_homogeneous hχ), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d ∈ partitionExponents (terminalOrder (cellSchur χ.parent) χ.period.toNat) := by
    simpa only [factor_recovery_order hχ] using hd
  rw [scalarReading_eq (terminalDerivative_ne_zero hχ)
    (character_derivative_eq_scalar hχ hd'), smul_eq_C_mul]
  simp only [div_eq_mul_inv, map_mul]
  ring

/-- Primitive normalization removes the positive tableau count in either outer convention. -/
theorem factor_recovery_outer_primitive {χ : Chart} (hχ : χ.IsProperOrdinary) :
    primitive (outerReadout (cellSchur χ.parent) χ.period.toNat) = adjustedOuter χ := by
  rw [factor_recovery_outer hχ, adjustedOuter_cellSchur]
  apply primitive_cellSchur_scalar
  · split_ifs
    · exact (isConnectedSkew_antitranspose hχ.1.1).1
    · exact hχ.1.1.1
  · exact inv_ne_zero (tableau_scalar_ne_zero χ.D)

/-- Each occupied geometric dimension lies between one and the outer area. -/
theorem outer_dimension_bounds {χ : Chart} (hχ : χ.IsProperOrdinary) :
    (0 < numRows χ.D ∧ numRows χ.D ≤ χ.D.card) ∧
      (0 < numCols χ.D ∧ numCols χ.D ≤ χ.D.card) ∧
      (0 < span χ.D ∧ span χ.D ≤ χ.D.card) := by
  have hn := hχ.1.1.2.1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact Finset.card_pos.mpr (hn.image Prod.fst)
  · exact Finset.card_image_le
  · rw [numCols_eq_card_image_snd]
    exact Finset.card_pos.mpr (hn.image Prod.snd)
  · rw [numCols_eq_card_image_snd]
    exact Finset.card_image_le
  · exact Finset.card_pos.mpr (hn.image content)
  · exact Finset.card_image_le

private theorem power_area_split (A : Lambda) {a r : ℕ} (hr : r ≤ a) :
    A ^ a = A ^ (a - r) * A ^ r := by
  rw [← pow_add, Nat.sub_add_cancel hr]

private theorem power_penultimate_split (A : Lambda) {a r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ a) :
    A ^ (a - 1) = A ^ (a - r) * A ^ (r - 1) := by
  rw [← pow_add]
  congr 1
  omega

/-- The displayed last derivative, with actual row, column, and span exponents. -/
theorem ordinary_last_display {χ : Chart} (hχ : χ.IsProperOrdinary) :
    terminalDerivative (cellSchur χ.parent) χ.period.toNat =
      (edgeSign χ.ω 1 : Lambda) ^ χ.D.card * C (standardTableauCount χ.D : ℚ) *
        normalizerRow χ.ω ^ numRows χ.D * normalizerColumn χ.ω ^ numCols χ.D *
        normalizerDiagonal χ.ω ^ span χ.D := by
  obtain ⟨hr, hc, hM⟩ := outer_dimension_bounds hχ
  apply mul_left_cancel₀ (normalization_ne_zero hχ.1.2.2.2 χ.D)
  rw [terminalDerivative, factor_recovery_order hχ, normalized_terminal hχ,
    xi_factor_normalizers hχ.1.2.2.2 hχ.2]
  simp only [mul_pow]
  rw [power_area_split (normalizerRow χ.ω) hr.2,
    power_area_split (normalizerColumn χ.ω) hc.2,
    power_area_split (normalizerDiagonal χ.ω) hM.2]
  unfold normalizationFactor
  ring

/-- The displayed penultimate derivative holds in both ordinary attachment conventions. -/
theorem ordinary_penultimate_display {χ : Chart} (hχ : χ.IsProperOrdinary) :
    penultimateDerivative (cellSchur χ.parent) χ.period.toNat =
      (edgeSign χ.ω 1 : Lambda) ^ (χ.D.card - 1) * C (standardTableauCount χ.D : ℚ) *
        normalizerRow χ.ω ^ (numRows χ.D - 1) *
        normalizerColumn χ.ω ^ (numCols χ.D - 1) *
        normalizerDiagonal χ.ω ^ (span χ.D - 1) * cellSchur χ.ω.E := by
  obtain ⟨hr, hc, hM⟩ := outer_dimension_bounds hχ
  apply mul_left_cancel₀ (normalization_ne_zero hχ.1.2.2.2 χ.D)
  rw [penultimateDerivative, factor_recovery_order hχ, normalized_penultimate hχ,
    xi_factor_normalizers hχ.1.2.2.2 hχ.2]
  simp only [mul_pow]
  rw [power_penultimate_split (normalizerRow χ.ω) hr.1 hr.2,
    power_penultimate_split (normalizerColumn χ.ω) hc.1 hc.2,
    power_penultimate_split (normalizerDiagonal χ.ω) hM.1 hM.2]
  unfold normalizationFactor
  ring

/-- The displayed quotient is an equality in the genuine fraction field. -/
theorem ordinary_ratio_display {χ : Chart} (hχ : χ.IsProperOrdinary) :
    actualRatio (penultimateDerivative (cellSchur χ.parent) χ.period.toNat)
      (terminalDerivative (cellSchur χ.parent) χ.period.toNat) =
        actualRatio (cellSchur χ.ω.E) (xi χ.ω) := by
  have hT : algebraMap Lambda ReadoutField
      (terminalDerivative (cellSchur χ.parent) χ.period.toNat) ≠ 0 := by
    intro h
    exact terminalDerivative_ne_zero hχ
      (IsFractionRing.injective Lambda ReadoutField (by simpa using h))
  have hx : algebraMap Lambda ReadoutField (xi χ.ω) ≠ 0 := by
    intro h
    exact xi_ne_zero hχ.1.2.2.2 hχ.2
      (IsFractionRing.injective Lambda ReadoutField (by simpa using h))
  change algebraMap Lambda ReadoutField
      (penultimateDerivative (cellSchur χ.parent) χ.period.toNat) /
        algebraMap Lambda ReadoutField
          (terminalDerivative (cellSchur χ.parent) χ.period.toNat) =
      algebraMap Lambda ReadoutField (cellSchur χ.ω.E) /
        algebraMap Lambda ReadoutField (xi χ.ω)
  apply (div_eq_div_iff hT hx).mpr
  have h := congrArg (algebraMap Lambda ReadoutField) (ordinary_cross_ratio hχ)
  simpa only [map_mul, mul_comm] using h

/-- All clauses of factor extraction depend only on the actual proper ordinary geometry. -/
theorem factor_recovery {χ : Chart} (hχ : χ.IsProperOrdinary) :
    terminalOrder (cellSchur χ.parent) χ.period.toNat = χ.D.card ∧
      innerReadout (cellSchur χ.parent) χ.period.toNat = cellSchur χ.ω.E ∧
      outerReadout (cellSchur χ.parent) χ.period.toNat =
        (standardTableauCount χ.D : ℚ)⁻¹ • adjustedOuter χ ∧
      primitive (outerReadout (cellSchur χ.parent) χ.period.toNat) = adjustedOuter χ ∧
      ∀ d ∈ partitionExponents (terminalOrder (cellSchur χ.parent) χ.period.toNat),
        actualRatio (characterDerivative (cellSchur χ.parent) χ.period.toNat d)
          (terminalDerivative (cellSchur χ.parent) χ.period.toNat) =
            algebraMap ℚ ReadoutField
              (characterCoefficient (adjustedOuter χ) d / (standardTableauCount χ.D : ℚ)) :=
  ⟨factor_recovery_order hχ, factor_recovery_inner hχ, factor_recovery_outer hχ,
    factor_recovery_outer_primitive hχ, fun _ hd => character_ratios_rational hχ hd⟩

/-- The horizontal empty edge satisfies the same proper-ordinary recovery hypotheses. -/
theorem empty_horizontal_proper {D E : Diagram} (hD : IsConnectedSkew D)
    (hE : IsConnectedSkew E) (hDc : 2 ≤ D.card) (hEc : 2 ≤ E.card) :
    (⟨D, emptyMarkH E⟩ : Chart).IsProperOrdinary := by
  refine ⟨⟨hD, hDc, hEc, MarkedInner.emptyMarkH_readoutLegal hE⟩, ?_⟩
  simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]

/-- The vertical empty edge is explicitly admitted, rather than inferred from old legality. -/
theorem empty_vertical_proper {D E : Diagram} (hD : IsConnectedSkew D)
    (hE : IsConnectedSkew E) (hDc : 2 ≤ D.card) (hEc : 2 ≤ E.card) :
    (⟨D, emptyMarkV E⟩ : Chart).IsProperOrdinary := by
  refine ⟨⟨hD, hDc, hEc, MarkedInner.emptyMarkV_readoutLegal hE⟩, ?_⟩
  simp [MarkedInner.IsOrdinary, emptyMarkV, AttachCase.IsMixed]

/-- Explicit vertical-empty recovery retains the involuted outer and the uninvoluted inner. -/
theorem factor_recovery_empty_vertical {D E : Diagram} (hD : IsConnectedSkew D)
    (hE : IsConnectedSkew E) (hDc : 2 ≤ D.card) (hEc : 2 ≤ E.card) :
    innerReadout (cellSchur ((emptyMarkV E).compose D)) (emptyMarkV E).period.toNat =
        cellSchur E ∧
      outerReadout (cellSchur ((emptyMarkV E).compose D)) (emptyMarkV E).period.toNat =
        (standardTableauCount D : ℚ)⁻¹ • schurInvolution (cellSchur D) := by
  have hχ : (⟨D, emptyMarkV E⟩ : Chart).IsProperOrdinary :=
    empty_vertical_proper hD hE hDc hEc
  constructor
  · simpa only [Chart.parent, Chart.period, emptyMarkV] using
      (factor_recovery_inner (χ := ⟨D, emptyMarkV E⟩) hχ)
  · simpa only [Chart.parent, Chart.period, adjustedOuter, emptyMarkV, ↓reduceIte] using
      (factor_recovery_outer (χ := ⟨D, emptyMarkV E⟩) hχ)

end SkewMarkedFactor
