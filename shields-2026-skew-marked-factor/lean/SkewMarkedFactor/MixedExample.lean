/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MixedTerminal
import SkewMarkedFactor.MarkedCharts
import SkewMarkedFactor.OrdinaryAction

/-!
# The literal legal mixed example

«Explicit formulas and examples» (`sec:examples`, `eq:mixed-example`) of
`shields-2026-skew-marked-factor.tex`.
The mixed mark on the hook `(2,1)` with singleton end copies is an actual legal marked
inner of case (d); its composition with a two-cell row is the skew diagram
`(3,2,1)/(1)`, whose Jacobi–Trudi determinant is evaluated and differentiated by the
weighted operator.
-/

set_option maxRecDepth 4096

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The hook `(2,1)` as a cell diagram. -/
def mixedExampleInner : Diagram := skewOf [2, 1] []

/-- The mixed mark: lower singleton `(1,0)`, displacement `(-1,1)`, case (d). -/
def mixedExampleMark : MarkedInner where
  E := mixedExampleInner
  W := {(1, 0)}
  v := (-1, 1)
  case := .d

/-- The two-cell row outer. -/
def mixedExampleOuter : Diagram := skewOf [2] []

/-- The composite parent. -/
def mixedExampleParent : Diagram := mixedExampleMark.compose mixedExampleOuter

theorem mixedExampleMark_legal : mixedExampleMark.IsLegal := by decide +kernel

theorem mixedExampleMark_mixed : mixedExampleMark.case.IsMixed := by
  right; rfl

theorem mixedExampleMark_period : mixedExampleMark.period = 2 := rfl


/-- The composite is a translate of the skew diagram `(3,2,1)/(1)`, with no supplemental
copy. -/
theorem mixedExampleParent_eq :
    ∃ t : ℤ × ℤ, mixedExampleParent = translate t (skewOf [3, 2, 1] [1]) :=
  ⟨(-1, 0), by decide +kernel⟩

/-- The row profile of `(3,2,1)/(1)`: rows of two, two and one cells, each pair of
neighboring rows overlapping in one column. -/
def mixedExampleProfile : Profile 2 where
  r := ![2, 2, 1]
  g := ![0, 0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

theorem mixedExample_cells :
    ∃ t : ℤ × ℤ, skewOf [3, 2, 1] [1] = translate t mixedExampleProfile.cells := by
  refine ⟨(0, -2), ?_⟩
  decide +kernel

/-- The genuine Jacobi–Trudi determinant of the composite parent
(`h₁h₂² - h₂h₃ - h₁h₄ + h₅`). -/
theorem mixedExampleParent_schur :
    cellSchur mixedExampleParent =
      X 1 * X 2 ^ 2 - X 2 * X 3 - X 1 * X 4 + X 5 := by
  obtain ⟨t, ht⟩ := mixedExampleParent_eq
  obtain ⟨u, hu⟩ := mixedExample_cells
  rw [ht, cellSchur_translate, hu, cellSchur_translate, cellSchur_cells, Profile.schur,
    Matrix.det_fin_three]
  norm_num [Profile.xi, Profile.zeta, mixedExampleProfile, Fin.sum_univ_succ, hh, hPos]
  ring

theorem mixedExampleMark_hatMark : hatMarkFin mixedExampleMark = ∅ := by decide +kernel

theorem mixedExampleMark_hatMiddle : hatMiddleFin mixedExampleMark = ∅ := by decide +kernel

/-- The normalizers: `A = h₁` and `B = C = 1`. -/
theorem mixedExampleMark_normalizers :
    normalizerRow mixedExampleMark = X 1 ∧ normalizerColumn mixedExampleMark = 1 ∧
      normalizerDiagonal mixedExampleMark = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have hW : mixedExampleMark.W = {(1, 0)} := rfl
    rw [normalizerRow, hW, cellSchur_singleton]
  · rw [normalizerColumn, mixedExampleMark_hatMark, cellSchur_empty]
  · rw [normalizerDiagonal, mixedExampleMark_hatMiddle, cellSchur_empty]

/-- The sign carried by the lower vertical end is `-1`, so `χ = -h₁`. -/
theorem mixedExampleMark_edgeSign : edgeSign mixedExampleMark 1 = -1 := by decide

/-- The inner hook has the Jacobi–Trudi function `h₁h₂ - h₃`. -/
theorem mixedExampleInner_schur : cellSchur mixedExampleInner = X 1 * X 2 - X 3 :=
  cellSchur_hook

private theorem wDeriv_X_ne (k : ℕ) (m : ℕ+) (h : (m : ℕ) < k) : wDeriv k (X m) = 0 := by
  rw [wDeriv_X, hh_of_neg (by omega), mul_zero]

/-- The weighted tail of the parent (`eq:mixed-example`). -/
theorem mixedExample_weighted_tail :
    wDeriv 2 (cellSchur mixedExampleParent) = -(3 : Lambda) * (X 1 * X 2 - X 3) ∧
    wDeriv 2 (wDeriv 2 (cellSchur mixedExampleParent)) = 3 * X 1 ∧
    wDeriv 2 (wDeriv 2 (wDeriv 2 (cellSchur mixedExampleParent))) = 0 ∧
    wDeriv 4 (cellSchur mixedExampleParent) = X 1 := by
  have hw : ∀ (k n : ℕ) (hn : 0 < n), wDeriv k (X ⟨n, hn⟩ : Lambda) =
      if k < n then ((n : Lambda) - k) * hPos (n - k) else 0 := fun k n hn => by
    rw [← hPos_pnat ⟨n, hn⟩]; exact wDeriv_hPos k hn
  have e1 : hPos 1 = (X 1 : Lambda) := hPos_pnat 1
  have e2 : hPos 2 = (X 2 : Lambda) := hPos_pnat 2
  have e3 : hPos 3 = (X 3 : Lambda) := hPos_pnat 3
  have h12 : wDeriv 2 (X 1 : Lambda) = 0 := by simpa using hw 2 1 one_pos
  have h22 : wDeriv 2 (X 2 : Lambda) = 0 := by simpa using hw 2 2 two_pos
  have h32 : wDeriv 2 (X 3 : Lambda) = X 1 := by
    have := hw 2 3 (by norm_num)
    norm_num [e1] at this
    exact this
  have h42 : wDeriv 2 (X 4 : Lambda) = 2 * X 2 := by
    have := hw 2 4 (by norm_num)
    norm_num [e2] at this
    rw [this]
  have h52 : wDeriv 2 (X 5 : Lambda) = 3 * X 3 := by
    have := hw 2 5 (by norm_num)
    norm_num [e3] at this
    rw [this]
  have h14 : wDeriv 4 (X 1 : Lambda) = 0 := by simpa using hw 4 1 one_pos
  have h24 : wDeriv 4 (X 2 : Lambda) = 0 := by simpa using hw 4 2 two_pos
  have h34 : wDeriv 4 (X 3 : Lambda) = 0 := by simpa using hw 4 3 (by norm_num)
  have h44 : wDeriv 4 (X 4 : Lambda) = 0 := by
    have := hw 4 4 (by norm_num); simpa using this
  have h54 : wDeriv 4 (X 5 : Lambda) = X 1 := by
    have := hw 4 5 (by norm_num)
    norm_num [e1] at this
    exact this
  rw [mixedExampleParent_schur]
  have e1' : wDeriv 2 (X 1 * X 2 ^ 2 - X 2 * X 3 - X 1 * X 4 + X 5 : Lambda) =
      -(3 : Lambda) * (X 1 * X 2 - X 3) := by
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, h12, h22, h32, h42,
      h52, smul_eq_mul]
    norm_num
    ring
  have e2' : wDeriv 2 (-(3 : Lambda) * (X 1 * X 2 - X 3)) = 3 * X 1 := by
    have h3 : wDeriv 2 (3 : Lambda) = 0 := by
      have : (3 : Lambda) = C 3 := by rw [map_ofNat]
      rw [this, ← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    simp only [Derivation.leibniz, map_sub, h12, h22, h32, smul_eq_mul, map_neg, h3]
    ring
  refine ⟨e1', ?_, ?_, ?_⟩
  · rw [e1', e2']
  · rw [e1', e2']
    have : wDeriv 2 (3 * X 1 : Lambda) = 0 := by
      have h3 : wDeriv 2 (3 : Lambda) = 0 := by
        have : (3 : Lambda) = C 3 := by rw [map_ofNat]
        rw [this, ← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
      simp only [Derivation.leibniz, h12, h3, smul_eq_mul]; ring
    exact this
  · simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, h14, h24, h34, h44,
      h54, smul_eq_mul]
    try norm_num
    try ring

/-- The ratio of `V₄P` to `V₂²P` is `1/3`. -/
theorem mixedExample_ratio : 3 * wDeriv 4 (cellSchur mixedExampleParent) =
    wDeriv 2 (wDeriv 2 (cellSchur mixedExampleParent)) := by
  obtain ⟨_, h2, _, h4⟩ := mixedExample_weighted_tail
  rw [h2, h4]

/-- The readout operators on the outer `h₂` for `p = 2`, `ρ = 1`: `B₁²h₂ = 3` and `B₂h₂ = 1`. -/
theorem mixedExample_outer_operators :
    mixedOp 2 1 1 (mixedOp 2 1 1 (hPos 2)) = 3 ∧ mixedOp 2 1 2 (hPos 2) = 1 := by
  have hh1 : mixedOp 2 1 1 (hPos 2) = C 3 * hPos 1 := by
    rw [mixedOp_hPos 2 1 one_pos, ite_eq_left (by norm_num)]
    congr 2
    norm_num
  have hh2 : mixedOp 2 1 1 (hPos 1) = 1 := by
    rw [mixedOp_hPos 2 1 one_pos]; simp [hPos]
  constructor
  · rw [hh1, Derivation.leibniz, hh2]
    have h0 : mixedOp 2 1 1 (C 3 : Lambda) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    simp only [smul_eq_mul, h0, mul_zero, add_zero, mul_one]
    rw [map_ofNat]
  · rw [mixedOp_hPos 2 1 two_pos]; simp [hPos]

/-- `V₂ s_E = -h₁`, so the integer content of `V₂ s_E` is `ρ = 1` and `χ = -h₁`. -/
theorem mixedExample_wDeriv_inner : wDeriv 2 (cellSchur mixedExampleInner) = -(X 1 : Lambda) := by
  rw [mixedExampleInner_schur]
  have hw : ∀ (k n : ℕ) (hn : 0 < n), wDeriv k (X ⟨n, hn⟩ : Lambda) =
      if k < n then ((n : Lambda) - k) * hPos (n - k) else 0 := fun k n hn => by
    rw [← hPos_pnat ⟨n, hn⟩]; exact wDeriv_hPos k hn
  have e1 : hPos 1 = (X 1 : Lambda) := hPos_pnat 1
  have h12 : wDeriv 2 (X 1 : Lambda) = 0 := by simpa using hw 2 1 one_pos
  have h22 : wDeriv 2 (X 2 : Lambda) = 0 := by simpa using hw 2 2 two_pos
  have h32 : wDeriv 2 (X 3 : Lambda) = X 1 := by
    have := hw 2 3 (by norm_num)
    norm_num [e1] at this
    exact this
  simp only [map_sub, Derivation.leibniz, h12, h22, h32, smul_eq_mul]
  ring

/-- The terminal quotient is `-s_E / h₁`: `h₁ · V₂P = -s_E · V₂²P`. -/
theorem mixedExample_terminal_quotient :
    (X 1 : Lambda) * wDeriv 2 (cellSchur mixedExampleParent) =
      -cellSchur mixedExampleInner * wDeriv 2 (wDeriv 2 (cellSchur mixedExampleParent)) := by
  obtain ⟨h1, h2, _, _⟩ := mixedExample_weighted_tail
  rw [h2, h1, mixedExampleInner_schur]
  ring

/-- The readout of a weight-two function `a h₁² + b h₂` by `(B₁², B₂)` is `(2a + 3b, b)`
for `p = 2`, `ρ = 1`; hence the readout `(3, 1)` returns `h₂`. -/
theorem mixedExample_readout_h2 (a b : ℚ) :
    mixedOp 2 1 1 (mixedOp 2 1 1 (C a * hPos 1 ^ 2 + C b * hPos 2)) = C (2 * a + 3 * b) ∧
      mixedOp 2 1 2 (C a * hPos 1 ^ 2 + C b * hPos 2) = C b := by
  obtain ⟨h3, h1⟩ := mixedExample_outer_operators
  have c0 : ∀ c : ℚ, mixedOp 2 1 1 (C c : Lambda) = 0 := fun c => by
    rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
  have c2 : ∀ c : ℚ, mixedOp 2 1 2 (C c : Lambda) = 0 := fun c => by
    rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
  have hB1 : mixedOp 2 1 1 (hPos 1) = 1 := by
    rw [mixedOp_hPos 2 1 one_pos]; simp [hPos]
  have hB2 : mixedOp 2 1 2 (hPos 1) = 0 := by
    rw [mixedOp_hPos 2 1 two_pos]; simp
  have hh2 : mixedOp 2 1 1 (hPos 2) = C 3 * hPos 1 := by
    rw [mixedOp_hPos 2 1 one_pos, ite_eq_left (by norm_num)]
    congr 2
    norm_num
  have hf1 : mixedOp 2 1 1 (C a * hPos 1 ^ 2 + C b * hPos 2) = C (2 * a + 3 * b) * hPos 1 := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hB1, hh2, c0, c0]
    simp only [smul_eq_mul, mul_zero, add_zero]
    have : (C (2 * a + 3 * b) : Lambda) = C 2 * C a + C 3 * C b := by
      rw [map_add, map_mul, map_mul]
    rw [this]
    try simp only [pow_one]
    have : (C 2 : Lambda) = 2 := by rw [map_ofNat]
    rw [this]
    ring
  constructor
  · rw [hf1, Derivation.leibniz, hB1, c0]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  · rw [map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hB2, h1, c2, c2]
    simp

end SkewMarkedFactor
