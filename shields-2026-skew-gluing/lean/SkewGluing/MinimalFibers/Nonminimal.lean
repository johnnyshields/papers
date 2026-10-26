import SkewGluing.MinimalFibers.Key

/-!
# A nonminimal fiber

Formalizes `shields-2026-skew-gluing.tex`, «A nonminimal fiber» (`eq:nonminimal-fiber`).

With `H = (2, 1)`, `V = (4, 1)` and their singleton case-(d) marks `ω` (period two) and `μ`
(period four), the diagrams of `eq:nonminimal-fiber` are
`D = H ∘_μ V`, `B = V ∘_ω H`, `Y = D ∘_ω H`, `X = (H ∘_{μ*} V*) ∘_ω H`.  The cell computations
are checked by the kernel:

* `D_profile`, `B_profile`: `D = (4,5,4,1; 0,1,0)` and `B = (2,2,2,3,2,1; 0,0,0,1,0)`;
* `eta_legal`, `Y_eq_eta_compose`: the lower mark `{(4,0),(4,1),(5,0)}` with displacement
  `(-4, 4)` on the normalized `B` is a legal case-(d) mark `η` of period eight and width three, and
  `Y = H ∘_η B`;
* `Y_rows`, `Z_rows`, `X_rows`: the row-length sequences of `Y`, `Z = H* ∘_η B` and `X`; both
  parents have 32 cells and span 27 (`parents_card_span`) and are not rotations of one another
  (`X_not_translate_rotate_Y`);
* `coarse_fiber_iff`: the coarse fiber `𝓕(η, s_H)` consists precisely of the translates of the four
  diagrams `Y`, `Z` and their rotations (the outer is `H` or `H*` and the inner `η` or `η*`);
* `X_not_mem_coarse_fiber`: `X` is outside the coarse fiber;
* `nonminimal_fiber`: `X` and `Y` share the fine fiber `𝓕(ω, s_D)` and have a common final factor
  (taking `hOH`, the Olson-Harris composition theorem, for `s_X = s_Y`; `SkewGluing.MainTheorems`
  discharges it by `olsonHarrisComposition`), although `X` is outside the coarse fiber;
* `fine_isSourceMinimal`, `coarse_score_lt_fine`: the fine chart has score `(1, 3)`, the coarse
  chart `(3, 11)`; the fine chart is source-minimal (a score below `(1, 3)` would need width zero,
  at span 27 the periods three or nine, coprime to two, contradicting `lem:gluing-lines`).

Sorry-free.
-/

namespace SkewGluing

namespace NonminimalFiber

/-- The northernmost occupied row of a diagram (`0` for the empty diagram). -/
def rowTop (D : Diagram) : ℤ :=
  if h : (rowSet D).Nonempty then (rowSet D).min' h else 0

/-- The row lengths of `D`, top to bottom. -/
def rowLengths (D : Diagram) : List ℕ :=
  (List.range (numRows D)).map fun i => rowLength D (rowTop D + i)

/-- The overlaps minus one of consecutive rows of `D`, top to bottom. -/
def rowOverlapsMinusOne (D : Diagram) : List ℕ :=
  (List.range (numRows D - 1)).map fun i => rowOverlap D (rowTop D + i) - 1

/-- The hook `H = (2, 1)`. -/
def H : Diagram := skewOf [2, 1] []

/-- The rotated hook `H* = (2, 2) / (1)`. -/
def Hstar : Diagram := skewOf [2, 2] [1]

/-- The diagram `V = (4, 1)`. -/
def V : Diagram := skewOf [4, 1] []

/-- The singleton case-(d) mark `ω` on `H` (period two). -/
def ω : MarkedInner := hookInner

/-- The singleton case-(d) mark `μ` on `V` (period four). -/
def μ : MarkedInner where
  E := V
  W := {(1, 0)}
  v := (-1, 3)
  case := .d

/-- `D = H ∘_μ V`. -/
def D : Diagram := μ.compose H

/-- `B = V ∘_ω H`. -/
def B : Diagram := ω.compose V

/-- `Y = D ∘_ω H`. -/
def Y : Diagram := ω.compose D

/-- `X = (H ∘_{μ*} V*) ∘_ω H`. -/
def X : Diagram := ω.compose (μ.rotate.compose H)

/-- The coarse mark `η` on `B`, normalized with bottom row `{(5, 0)}`: lower copy
`{(4,0), (4,1), (5,0)}`, displacement `(-4, 4)`, case (d). -/
def η : MarkedInner where
  E := translate (3, 1) B
  W := {(4, 0), (4, 1), (5, 0)}
  v := (-4, 4)
  case := .d

/-- `Z = H* ∘_η B`. -/
def Z : Diagram := η.compose Hstar

theorem ω_legal : ω.IsLegal := by decide +kernel

theorem μ_legal : μ.IsLegal := by decide +kernel

set_option maxRecDepth 100000 in
/-- The mark `η` is a legal case-(d) mark. -/
theorem η_legal : η.IsLegal := by decide +kernel

theorem marks_data :
    ω.case = .d ∧ ω.period = 2 ∧ ω.W.card = 1 ∧ μ.case = .d ∧ μ.period = 4 ∧ μ.W.card = 1 ∧
      η.case = .d ∧ η.period = 8 ∧ η.width = 3 := by
  decide +kernel

/-- `D = (4, 5, 4, 1; 0, 1, 0)`. -/
theorem D_profile : rowLengths D = [4, 5, 4, 1] ∧ rowOverlapsMinusOne D = [0, 1, 0] := by
  decide +kernel

/-- `B = (2, 2, 2, 3, 2, 1; 0, 0, 0, 1, 0)`. -/
theorem B_profile : rowLengths B = [2, 2, 2, 3, 2, 1] ∧
    rowOverlapsMinusOne B = [0, 0, 0, 1, 0] := by
  decide +kernel

/-- The bottom row of the normalized `B` is the single cell `(5, 0)`. -/
theorem η_bottom_row : (5, 0) ∈ η.E ∧ rowLength η.E 5 = 1 ∧ η.E.card = 12 := by
  decide +kernel

/-- `Y = H ∘_η B`, up to translation. -/
theorem Y_eq_eta_compose : Y = translate (-3, -1) (η.compose H) := by decide +kernel

theorem Y_rows : rowLengths Y = [2, 2, 2, 3, 2, 2, 2, 4, 3, 2, 2, 3, 2, 1] := by decide +kernel

theorem Z_rows : rowLengths Z = [2, 2, 2, 4, 3, 2, 2, 3, 2, 2, 2, 3, 2, 1] := by decide +kernel

theorem X_rows : rowLengths X = [3, 2, 2, 2, 3, 2, 2, 4, 3, 2, 2, 2, 2, 1] := by decide +kernel

/-- Both parents have 32 cells and span 27. -/
theorem parents_card_span : Y.card = 32 ∧ X.card = 32 ∧ span Y = 27 ∧ span X = 27 := by
  decide +kernel

/-- `X` and `Y` are not translates of one another, nor of each other's rotation. -/
theorem X_not_translate_rotate_Y :
    normalize X ≠ normalize Y ∧ normalize X ≠ normalize (rotate Y) := by
  decide +kernel

/-! ### The fine and the coarse chart -/

/-- The fine chart `(D, ω)` of `Y`: period two, width one. -/
def fineChart : Chart := ⟨D, ω⟩

/-- The coarse chart `(H, η)` of `Y`: period eight, width three. -/
def coarseChart : Chart := ⟨H, η⟩

theorem fineChart_proper : fineChart.IsProperLegal :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, ω_legal⟩

theorem fineChart_chartOf : fineChart.IsChartOf Y := ⟨0, translate_zero.symm⟩

theorem coarseChart_proper : coarseChart.IsProperLegal :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, η_legal⟩

theorem coarseChart_chartOf : coarseChart.IsChartOf Y := ⟨(-3, -1), Y_eq_eta_compose⟩

/-- The fine score is `(1, 3)` and the coarse score is `(3, 11)`. -/
theorem fine_coarse_score :
    fineChart.score = toLex (1, 3) ∧ coarseChart.score = toLex (3, 11) := by
  decide +kernel

/-- The coarse score exceeds the fine score, so the coarse chart is not source-minimal. -/
theorem coarse_score_lt_fine : fineChart.score < coarseChart.score := by
  rw [fine_coarse_score.1, fine_coarse_score.2]
  decide

/-- **The fine chart is source-minimal.**  A score below `(1, 3)` would need width zero; at span 27
the only possible proper empty-overlap periods are three and nine, both coprime to the period two
of the supplied mixed chart, contradicting `lem:gluing-lines`. -/
theorem fine_isSourceMinimal : fineChart.IsSourceMinimal Y := by
  refine ⟨fineChart_proper, fineChart_chartOf, fun χ' h' c' => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hs := h'.score_eq c'
  have hspan : span Y = 27 := parents_card_span.2.2.1
  have hf : fineChart.score = score 27 2 := by rw [fine_coarse_score.1]; rfl
  rw [hs, hspan, hf] at hlt
  have hp2 := h'.two_le_period
  have hp13 := h'.two_mul_period_le c'
  rw [hspan] at hp13
  have hmem : χ'.period.toNat ∈ Set.Icc 2 (27 / 2) := ⟨hp2, by omega⟩
  have h39 := (span_27_score_below_fine _ hmem).mp hlt
  have hcop : Int.gcd fineChart.period χ'.period = 1 := by
    have e : (χ'.period.toNat : ℤ) = χ'.period := h'.period_toNat
    have p0 : 0 < χ'.period := h'.2.2.2.period_pos
    have e' : χ'.period.natAbs = χ'.period.toNat := by omega
    change Int.gcd 2 χ'.period = 1
    unfold Int.gcd
    rw [e']
    rcases h39 with h | h <;> rw [h] <;> decide
  obtain ⟨hnm, -, -⟩ := Chart.IsProperLegal.coprime_periods_line fineChart_proper h'
    fineChart_chartOf c' hcop
  exact hnm (by decide)

/-- The coarse chart is not source-minimal. -/
theorem coarse_not_isSourceMinimal : ¬ coarseChart.IsSourceMinimal Y := fun h =>
  absurd (h.2.2 fineChart fineChart_proper fineChart_chartOf) (not_le.mpr coarse_score_lt_fine)

/-! ### The coarse fiber -/

/-- The southwest-normalized outers of the class `[H] = {H, H*}`. -/
def A₀ : Diagram := translate (-1, 0) H

def A₁ : Diagram := translate (-1, 0) Hstar

theorem H_conn : IsConnectedSkew H := by decide +kernel

theorem Hstar_conn : IsConnectedSkew Hstar := by decide +kernel

theorem cellSchur_Hstar : cellSchur Hstar = cellSchur H := by
  unfold H Hstar
  rw [cellSchur_hookRotated, cellSchur_hook]

theorem A₀_conn : IsConnectedSkew A₀ := isConnectedSkew_translate _ H_conn

theorem A₁_conn : IsConnectedSkew A₁ := isConnectedSkew_translate _ Hstar_conn

theorem cellSchur_A₀ : cellSchur A₀ = cellSchur H := cellSchur_translate _ _

theorem cellSchur_A₁ : cellSchur A₁ = cellSchur H :=
  (cellSchur_translate _ _).trans cellSchur_Hstar

theorem A_card : 2 ≤ A₀.card ∧ 2 ≤ A₁.card := by decide +kernel

/-- The four members of the coarse fiber, in terms of `Y`, `Z` and their rotations. -/
theorem coarse_members :
    η.compose A₀ = translate (-1, 5) Y ∧ η.compose A₁ = translate (-4, 4) Z ∧
    η.rotate.compose A₀ = translate (-4, 4) (rotate Z) ∧
    η.rotate.compose A₁ = translate (-7, 3) (rotate Y) := by
  decide +kernel

theorem eq_translate_neg {C Y' : Diagram} {u : ℤ × ℤ} (h : C = translate u Y') :
    Y' = translate (-u) C := by
  rw [h, translate_translate, neg_add_cancel, translate_zero]

/-- A member `A` of `[H]` with `sw A = 0` is `A₀` or `A₁`. -/
theorem eq_A_of_class {A : Diagram} (hA : IsConnectedSkew A) (hs : cellSchur A = cellSchur H)
    (hsw : sw A = 0) : A = A₀ ∨ A = A₁ := by
  have hH : sw H = (1, 0) := by decide +kernel
  have hHs : sw Hstar = (1, 0) := by decide +kernel
  have hne : H.Nonempty := H_conn.2.1
  have hne' : Hstar.Nonempty := Hstar_conn.2.1
  rcases (cellSchur_eq_hook_iff hA.1).mp (hs.trans cellSchur_hook) with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · left
    change sw (translate v H) = 0 at hsw
    change translate v H = A₀
    rw [sw_translate hne, hH] at hsw
    have : v = (-1, 0) := by
      ext
      · have := congrArg Prod.fst hsw; simp at this ⊢; omega
      · have := congrArg Prod.snd hsw; simp at this ⊢; omega
    rw [this]; rfl
  · right
    change sw (translate v Hstar) = 0 at hsw
    change translate v Hstar = A₁
    rw [sw_translate hne', hHs] at hsw
    have : v = (-1, 0) := by
      ext
      · have := congrArg Prod.fst hsw; simp at this ⊢; omega
      · have := congrArg Prod.snd hsw; simp at this ⊢; omega
    rw [this]; rfl

/-- **The coarse fiber consists precisely of four diagrams.**  `𝓕(η, s_H)`, read up to translation,
consists of the translates of `Y = H ∘_η B`, `Z = H* ∘_η B` and their reversals (the rotations),
that is, the diagrams with outer `H` or `H*` and marked inner `η` or `η*`. -/
theorem coarse_fiber_iff {F : Diagram} :
    F ∈ fiberClass cellSchur η (cellSchur H) ↔
      ∃ t, F = translate t Y ∨ F = translate t Z ∨ F = translate t (rotate Y) ∨
        F = translate t (rotate Z) := by
  obtain ⟨m₀, m₁, m₂, m₃⟩ := coarse_members
  rw [fiberClass_cellSchur_eq_normalized]
  constructor
  · rintro ⟨A, hA, -, hs, hsw, ⟨t, ht⟩ | ⟨t, ht⟩⟩
    · rcases eq_A_of_class hA hs hsw with rfl | rfl
      · exact ⟨t + (-1, 5), Or.inl (by rw [ht, m₀, translate_translate])⟩
      · exact ⟨t + (-4, 4), Or.inr (Or.inl (by rw [ht, m₁, translate_translate]))⟩
    · rcases eq_A_of_class hA hs hsw with rfl | rfl
      · exact ⟨t + (-4, 4), Or.inr (Or.inr (Or.inr (by rw [ht, m₂, translate_translate])))⟩
      · exact ⟨t + (-7, 3), Or.inr (Or.inr (Or.inl (by rw [ht, m₃, translate_translate])))⟩
  · rintro ⟨t, h | h | h | h⟩
    · refine ⟨A₀, A₀_conn, A_card.1, cellSchur_A₀, by decide +kernel, Or.inl ⟨t + (1, -5), ?_⟩⟩
      rw [h, eq_translate_neg m₀, translate_translate]
      simp
    · refine ⟨A₁, A₁_conn, A_card.2, cellSchur_A₁, by decide +kernel, Or.inl ⟨t + (4, -4), ?_⟩⟩
      rw [h, eq_translate_neg m₁, translate_translate]
      simp
    · refine ⟨A₁, A₁_conn, A_card.2, cellSchur_A₁, by decide +kernel, Or.inr ⟨t + (7, -3), ?_⟩⟩
      rw [h, eq_translate_neg m₃, translate_translate]
      simp
    · refine ⟨A₀, A₀_conn, A_card.1, cellSchur_A₀, by decide +kernel, Or.inr ⟨t + (4, -4), ?_⟩⟩
      rw [h, eq_translate_neg m₂, translate_translate]
      simp

/-- **`X` is outside the coarse fiber**: its first row has three cells, whereas the four diagrams of
the coarse fiber start with one or two. -/
theorem X_not_mem_coarse_fiber : X ∉ fiberClass cellSchur η (cellSchur H) := by
  rw [coarse_fiber_iff]
  rintro ⟨t, h | h | h | h⟩ <;>
  · have hn := congrArg normalize h
    rw [normalize_translate (by decide +kernel)] at hn
    revert hn
    decide +kernel

/-- **The nonminimal fiber** (`eq:nonminimal-fiber`).  `X` and `Y` lie in the fine fiber
`𝓕(ω, s_D)`: the outer of `X` is `H ∘_{μ*} V*`, of the same function as `D = H ∘_μ V` by the
Olson-Harris reversal theorem (`hOH`).  They have the same Schur function and a common final
factor, but `X` is outside the coarse fiber `𝓕(η, s_H)`, which contains `Y`. -/
theorem nonminimal_fiber (hOH : OlsonHarrisComposition) :
    X ∈ fiber cellSchur ω (cellSchur D) ∧ Y ∈ fiber cellSchur ω (cellSchur D) ∧
      cellSchur X = cellSchur Y ∧ HasCommonFinalFactor cellSchur X Y ∧
      X ∉ fiberClass cellSchur η (cellSchur H) ∧ Y ∈ fiberClass cellSchur η (cellSchur H) := by
  have hμ := μ_legal
  have hD : IsConnectedSkew D := hμ.isConnectedSkew_compose H_conn
  have hAX : IsConnectedSkew (μ.rotate.compose H) :=
    (MarkedInner.isLegal_rotate hμ).isConnectedSkew_compose H_conn
  have hDc : 2 ≤ D.card := by decide +kernel
  have hAXc : 2 ≤ (μ.rotate.compose H).card := by decide +kernel
  have hsX : cellSchur (μ.rotate.compose H) = cellSchur D :=
    (hOH.compose_eq_rotate_compose hμ H_conn H_conn rfl).symm
  have hXm : X ∈ fiber cellSchur ω (cellSchur D) := ⟨_, hAX, hAXc, hsX, Or.inl rfl⟩
  have hYm : Y ∈ fiber cellSchur ω (cellSchur D) := ⟨D, hD, hDc, rfl, Or.inl rfl⟩
  refine ⟨hXm, hYm, hOH.fiber_eq ω_legal hXm hYm, ?_, X_not_mem_coarse_fiber,
    coarse_fiber_iff.mpr ⟨0, Or.inl translate_zero.symm⟩⟩
  refine fiber_hasCommonFinalFactor ω_legal (by decide +kernel) hXm hYm ?_
  rintro ⟨t, ht⟩
  have hn := congrArg normalize ht
  rw [normalize_translate (by decide +kernel)] at hn
  exact X_not_translate_rotate_Y.1 hn.symm

end NonminimalFiber

end SkewGluing
