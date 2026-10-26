/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/DetectorBudget.lean
import SkewRibbonCoarsenings.LocalAlternative
import SkewRibbonCoarsenings.PeriodRatios
import SkewRibbonCoarsenings.Selection
import SkewRibbonCoarsenings.NestedIdentity

/-!
# The detector budget

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:realization`
(`prop:local-alternative`, `eq:coarse-local-budget`, `prop:budget`).

A strict chain `eq:chain` of `L` mask increases, from `e` up to `P ∣ d`, has successive ratios
forming a list of the kind bounded by `lem:arithmetic-optimization`; hence `L ≤ T_e(d/e)` and the
`L + 4` blocks of the detector fit in the arithmetic budget `B(n)`.  Also `L ≤ Ω(d/e)` and
`4 + Ω(d/e) ≤ Ω(n) + 2`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

section Budget

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

/-- The successive ratios `p_{i+1} / p_i`, `i < m`, of a chain. -/
def chainRatios (p : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map fun i => p (i + 1) / p i

lemma chain_pos (hc : MaskChain n S d e L p) (he0 : 0 < e) : ∀ j ≤ L, 0 < p j := by
  intro j
  induction j with
  | zero => intro _; rw [hc.p_zero]; exact he0
  | succ j ih => intro hj; have := hc.lt j (by omega); have := ih (by omega); omega

lemma chainRatios_prod (hc : MaskChain n S d e L p) :
    ∀ m ≤ L, (chainRatios p m).prod * e = p m := by
  intro m
  induction m with
  | zero => intro _; simp [chainRatios, hc.p_zero]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hc.dvd m (by omega)
    unfold chainRatios at *
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    calc (List.map (fun i => p (i + 1) / p i) (List.range m)).prod * (p (m + 1) / p m) * e
        = (List.map (fun i => p (i + 1) / p i) (List.range m)).prod * e * (p (m + 1) / p m) := by
          ring
      _ = p m * (p (m + 1) / p m) := by rw [h1]
      _ = p (m + 1) := Nat.mul_div_cancel' h2

lemma chainRatios_two_le (hc : MaskChain n S d e L p) (he0 : 0 < e) :
    ∀ x ∈ chainRatios p L, 2 ≤ x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi := List.mem_range.1 hi
  have hl := hc.lt i hi
  have hp := chain_pos hc he0 i (by omega)
  obtain ⟨k, hk⟩ := hc.dvd i hi
  rw [hk, Nat.mul_div_cancel_left _ hp]
  have : 1 < k := by
    by_contra hk1
    have : k ≤ 1 := by omega
    interval_cases k <;> omega
  omega

/-- `eq:chain` with least periods: `𝓑_{p_i}` has least period `p_{i+1}`. -/
def LeastChain (n : ℕ) (S : Finset ℕ) (L : ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1))

/-- `prop:local-alternative`: the successive ratios of a chain of least periods form a list of the
kind bounded in `lem:arithmetic-optimization` (`lem:ratios`: no two adjacent ratios equal two, and
the first is not two when `e = 4`). -/
theorem chainRatios_isRatioList (h : NormalizedSetting n S S' d e) [NeZero n]
    (hc : MaskChain n S d e L p) (hl : LeastChain n S L p) :
    IsRatioList e (d / e) (chainRatios p L) := by
  have he0 := h.e_pos
  refine ⟨chainRatios_two_le hc he0, ?_, ?_, ?_⟩
  · have h1 := chainRatios_prod hc L le_rfl
    have h2 : (chainRatios p L).prod * e ∣ d := h1 ▸ hc.dvd_d
    exact Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at h2)
  · rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i + 1 < L := by simpa [chainRatios] using hi
    have hi2 : i + 2 ≤ L := by omega
    have hc2 := ratios_doubling_chain h hc hi2 (hl (i + 1) (by omega))
    have hpos0 := chain_pos hc he0 i (by omega)
    have hpos1 := chain_pos hc he0 (i + 1) (by omega)
    obtain ⟨k, hk⟩ := hc.dvd i (by omega)
    obtain ⟨k', hk'⟩ := hc.dvd (i + 1) (by omega)
    simp only [chainRatios, List.getElem_map, List.getElem_range]
    rintro ⟨h1, h2⟩
    apply hc2
    rw [hk, Nat.mul_div_cancel_left _ hpos0] at h1
    rw [hk', Nat.mul_div_cancel_left _ hpos1] at h2
    subst h1
    constructor
    · rw [hk]; ring
    · rw [hk', h2, hk]; ring
  · intro he4 hhead
    have hL := hc.one_le
    have h0 : chainRatios p L = (p 1 / p 0) :: (chainRatios p L).tail := by
      obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
      simp [chainRatios, List.range_succ_eq_map]
    have hpos0 := chain_pos hc he0 0 (by omega)
    obtain ⟨k, hk⟩ := hc.dvd 0 (by omega)
    rw [h0] at hhead
    simp only [List.head?_cons, ne_eq, Option.some.injEq] at hhead
    rw [hk, Nat.mul_div_cancel_left _ hpos0] at hhead
    have hcl := hl 0 (by omega)
    rw [hc.p_zero] at hcl
    have hp1 : p 1 = 8 := by rw [hk, hc.p_zero, he4, hhead]
    rw [hp1] at hcl
    subst he4
    exact ratios_four h hcl

/-- `2 ^ Ω(D) ≤ D`. -/
lemma two_pow_cardFactors_le {D : ℕ} (hD : D ≠ 0) : 2 ^ ArithmeticFunction.cardFactors D ≤ D := by
  have h1 : 2 ^ (Nat.primeFactorsList D).length ≤ (Nat.primeFactorsList D).prod := by
    have := List.pow_length_le_prod (Nat.primeFactorsList D) 2
      (fun x hx => (Nat.prime_of_mem_primeFactorsList hx).two_le)
    simpa using this
  rw [Nat.prod_primeFactorsList hD, ← ArithmeticFunction.cardFactors_apply] at h1
  exact h1

/-- The weight of a normalized setting: `n ≥ 9`. -/
lemma setting_nine_le (h : NormalizedSetting n S S' d e) : 9 ≤ n := by
  have h3 := h.three_le_e
  have hn := h.three_le_ratio
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0] at hn; simp at hn
    · exact h0
  have hd : e ≤ d := Nat.le_of_dvd hd0 h.e_dvd_d
  have : d * (n / d) = n := Nat.mul_div_cancel' h.d_dvd_n
  nlinarith

/-- `eq:coarse-local-budget`, second inequality: for `3 ≤ e`, `e ∣ d ∣ n` and `3 ≤ n / d`,
`4 + Ω(d/e) ≤ Ω(n) + 2`. -/
theorem omega_budget_le {n e d : ℕ} (hn : n ≠ 0) (hed : e ∣ d) (hdn : d ∣ n) (he : 3 ≤ e)
    (h3 : 3 ≤ n / d) :
    4 + ArithmeticFunction.cardFactors (d / e) ≤ ArithmeticFunction.cardFactors n + 2 := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hdn
  have he0 : e ≠ 0 := by omega
  have hde : d / e ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed)
    (by omega)).ne'
  have hnd : n / d ≠ 0 := by omega
  have hfac : n = (n / d) * (e * (d / e)) := by
    rw [Nat.mul_div_cancel' hed, Nat.div_mul_cancel hdn]
  have h1 : ArithmeticFunction.cardFactors n =
      ArithmeticFunction.cardFactors (n / d) +
        (ArithmeticFunction.cardFactors e + ArithmeticFunction.cardFactors (d / e)) := by
    conv_lhs => rw [hfac]
    rw [ArithmeticFunction.cardFactors_mul hnd (mul_ne_zero he0 hde),
      ArithmeticFunction.cardFactors_mul he0 hde]
  have h2 : 0 < ArithmeticFunction.cardFactors (n / d) :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
  have h3' : 0 < ArithmeticFunction.cardFactors e :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
  omega

lemma cardFactors_le_of_dvd {x y : ℕ} (hy : y ≠ 0) (h : x ∣ y) :
    ArithmeticFunction.cardFactors x ≤ ArithmeticFunction.cardFactors y := by
  obtain ⟨k, rfl⟩ := h
  have hx : x ≠ 0 := left_ne_zero_of_mul hy
  have hk : k ≠ 0 := right_ne_zero_of_mul hy
  rw [ArithmeticFunction.cardFactors_mul hx hk]; omega

lemma length_le_cardFactors_prod : ∀ l : List ℕ, (∀ x ∈ l, 2 ≤ x) →
    l.length ≤ ArithmeticFunction.cardFactors l.prod
  | [], _ => by simp
  | x :: l, h => by
    have hx : 2 ≤ x := h x (by simp)
    have ih := length_le_cardFactors_prod l (fun y hy => h y (by simp [hy]))
    have hl0 : l.prod ≠ 0 := by
      rw [Ne, List.prod_eq_zero_iff]
      intro h0; have := h 0 (by simp [h0]); omega
    rw [List.prod_cons, ArithmeticFunction.cardFactors_mul (by omega) hl0]
    have : 0 < ArithmeticFunction.cardFactors x :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    simp only [List.length_cons]; omega

/-- `prop:local-alternative`, `eq:coarse-local-budget`: a strict increase consumes at least one
prime factor of `d / e`, so the number `L` of strict mask increases satisfies `L ≤ Ω(d / e)`. -/
theorem chain_length_le_omega (h : NormalizedSetting n S S' d e)
    (hc : MaskChain n S d e L p) :
    L ≤ ArithmeticFunction.cardFactors (d / e) := by
  have hd0 : d ≠ 0 := by have := h.three_le_ratio; rintro rfl; simp at this
  have hde : d / e ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h.e_dvd_d)
    h.e_pos).ne'
  have hr := chainRatios_two_le hc h.e_pos
  have hprod : (chainRatios p L).prod ∣ d / e := by
    have h1 := chainRatios_prod hc L le_rfl
    have h2 : (chainRatios p L).prod * e ∣ d := h1 ▸ hc.dvd_d
    exact Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at h2)
  have := length_le_cardFactors_prod _ hr
  have h2 := cardFactors_le_of_dvd hde hprod
  simpa [chainRatios] using this.trans h2

/-- `eq:coarse-local-budget`: `L + 4 ≤ Ω(n) + 2` for a chain of `L` strict increases in a
normalized setting. -/
theorem chain_blocks_le_omega (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p) :
    L + 4 ≤ ArithmeticFunction.cardFactors n + 2 := by
  have hn : n ≠ 0 := h.n_pos.ne'
  have h1 := chain_length_le_omega h hc
  have h2 := omega_budget_le hn h.e_dvd_d h.d_dvd_n h.three_le_e h.three_le_ratio
  omega

lemma add_two_le_two_pow : ∀ m : ℕ, 2 ≤ m → m + 2 ≤ 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

/-- `eq:arithmetic-bound`: for `4 ≤ e`, `e ∣ d ∣ n`, `3 ≤ n / d`, the candidate
`4 + T_e(d/e)` is at most `n`, hence at most `B(n)`. -/
theorem candidate_le_arithBound {n e d : ℕ} (hn : 5 ≤ n) (hed : e ∣ d) (hdn : d ∣ n)
    (he : 4 ≤ e) (h3 : 3 ≤ n / d) : 4 + arithT e (d / e) ≤ arithBound n := by
  refine le_arithBound_of_cand hn hed hdn he h3 ?_
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (by omega) hdn
  have hde : d / e ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed)
    (by omega)).ne'
  have h1 := arithT_le_Omega (e := e) hde
  have h2 := omega_budget_le (by omega : n ≠ 0) hed hdn (by omega) h3
  have hfac : n = (n / d) * (e * (d / e)) := by
    rw [Nat.mul_div_cancel' hed, Nat.div_mul_cancel hdn]
  have hnd : n / d ≠ 0 := by omega
  have he0 : e ≠ 0 := by omega
  have hO : 2 ≤ ArithmeticFunction.cardFactors n := by
    have e1 : ArithmeticFunction.cardFactors n =
        ArithmeticFunction.cardFactors (n / d) +
          (ArithmeticFunction.cardFactors e + ArithmeticFunction.cardFactors (d / e)) := by
      conv_lhs => rw [hfac]
      rw [ArithmeticFunction.cardFactors_mul hnd (mul_ne_zero he0 hde),
        ArithmeticFunction.cardFactors_mul he0 hde]
    have a1 : 0 < ArithmeticFunction.cardFactors (n / d) :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    have a2 : 0 < ArithmeticFunction.cardFactors e :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    omega
  have h4 := two_pow_cardFactors_le (by omega : n ≠ 0)
  have h5 := add_two_le_two_pow _ hO
  omega

/-- `prop:local-alternative`, `prop:budget`: the `L + 4` blocks of a detector after `L ≥ 1`
strict increases (and the four blocks of the starting mask) fit in the arithmetic budget, when
`e ≥ 4`. -/
theorem chain_blocks_le_arithBound (h : NormalizedSetting n S S' d e) [NeZero n]
    (hc : MaskChain n S d e L p) (hl : LeastChain n S L p) (he4 : 4 ≤ e) :
    L + 4 ≤ arithBound n := by
  have hn := setting_nine_le h
  have h1 := ratioList_length_le (e := e) (D := d / e)
    (by
      have hd0 : d ≠ 0 := by have := h.three_le_ratio; rintro rfl; simp at this
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h.e_dvd_d) h.e_pos).ne')
    (chainRatios_isRatioList h hc hl)
  have h2 := candidate_le_arithBound (by omega) h.e_dvd_d h.d_dvd_n he4 h.three_le_ratio
  simp only [chainRatios, List.length_map, List.length_range] at h1
  omega

/-- The initial tests: three blocks fit in the arithmetic budget for `n ≥ 5`. -/
theorem three_blocks_le_arithBound {n : ℕ} (hn : 5 ≤ n) : 3 ≤ arithBound n :=
  three_le_arithBound hn

/-- The four blocks of the starting mask fit in `B(n)` in a normalized setting with `e ≥ 4`. -/
theorem four_blocks_le_arithBound (h : NormalizedSetting n S S' d e) (he4 : 4 ≤ e) :
    4 ≤ arithBound n := by
  have hn := setting_nine_le h
  have := candidate_le_arithBound (by omega) h.e_dvd_d h.d_dvd_n he4 h.three_le_ratio
  omega

end Budget

end SkewRibbonCoarsenings
