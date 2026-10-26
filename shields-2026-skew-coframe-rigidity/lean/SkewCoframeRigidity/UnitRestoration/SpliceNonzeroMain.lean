/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.SpliceNonzeroMain.CoreCommute

/-!
# The first cell-splice grade

Formalizes `sc:splice-nonzero` in `shields-2026-skew-coframe-rigidity.tex`.  For a connected
normalized diagram `V` with `V ≠ V*`, the difference `J₂ = s_{V ◁ CELL} - s_{CELL ◁ V}` is
nonzero (`splice_nonzero`), and its first nonzero grade in the positive letters is the number
`k` of core rows when the zero-free core is not its own half-turn, and `k + 1` when it is.

* `s_{V ◁ CELL} = s_{CELL ◁ V*}` (`schur_splice_cell`), so `J₂ = s_{CELL ◁ V*} - s_{CELL ◁ V}`.
* `grade_core`, `grade_cellTop`: the grades `k` and `k + 1` of `s_X` and `s_{CELL ◁ X}` through
  the whole-unit series, in terms of the core, the sorting sign and the unit positions.
* Core not self-rotating: grade `k` is `σ (s_{CELL ◁ B*} - s_{CELL ◁ B})`, and its vanishing
  contradicts fixed-cap rigidity for the cell cap.
* Core self-rotating: grade `k` cancels, and grade `k + 1` is `σ · ṡ_{CELL ◁ B}` with weights
  `ρ = 1_{U*} - 1_U` on the unit values; `s_V = s_{V*}` gives `ṡ_B = 0` for the same weights, so
  `linearized_cap` forces `ρ = 0`, hence `V = V*`.

The one-cell cap is the only cap used.  Conditional on `CapVanishing cellCap` (fixed-cap
rigidity) and on `linearized_cap`.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap

local notation "CR" => SkewCofactorIndependence.CompleteRing

theorem SameLists.connected {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) (hD : D.Connected) : E.Connected := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [← BetaDiagram.eq_of_rows_cols (show D.row = E.row from funext hr)
    (show D.col = E.col from funext hc)]
  exact hD

theorem SameLists.cellTop {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) : SameLists (cellTop D) (cellTop E) := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [BetaDiagram.eq_of_rows_cols (show D.row = E.row from funext hr)
    (show D.col = E.col from funext hc)]
  exact SameLists.refl _

/-- The same lists on an index type presented as a successor. -/
def castDiagram {m m' : ℕ} (D : BetaDiagram m) (h : m = m') : BetaDiagram m' where
  row i := D.row (Fin.cast h.symm i)
  col i := D.col (Fin.cast h.symm i)
  row_strictAnti := D.row_strictAnti.comp_strictMono (Fin.castOrderIso h.symm).strictMono
  col_strictAnti := D.col_strictAnti.comp_strictMono (Fin.castOrderIso h.symm).strictMono
  row_nonempty _ := D.row_nonempty _

theorem sameLists_castDiagram {m m' : ℕ} (D : BetaDiagram m) (h : m = m') :
    SameLists D (castDiagram D h) :=
  ⟨h, fun i => by simp [castDiagram], fun i => by simp [castDiagram]⟩

/-- The grades of `s_X` in terms of any copy `C` of its core. -/
theorem grade_core {m c : ℕ} (X : BetaDiagram m) (C : BetaDiagram c)
    (hC : SameLists (coreDiagram X) C) :
    (∀ g < coreCount X, MvPolynomial.homogeneousComponent g X.schur = 0) ∧
    MvPolynomial.homogeneousComponent (coreCount X) X.schur =
      (((sortingSign X : ℤˣ) : ℤ) : CR) * C.schur ∧
    MvPolynomial.homogeneousComponent (coreCount X + 1) X.schur =
      (((sortingSign X : ℤˣ) : ℤ) : CR) * ∑ b ∈ unitVals X, dotS C b := by
  obtain ⟨h1, h2, h3⟩ := grade_expansion X
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, hC.schur_eq]
  · rw [h3]; simp_rw [hC.dotS_eq]

/-- The grades of `s_{CELL ◁ X}` in terms of any copy `C` of the core of `X`. -/
theorem grade_cellTop {m c : ℕ} (X : BetaDiagram m) (C : BetaDiagram c)
    (hC : SameLists (coreDiagram X) C) :
    (∀ g < coreCount X, MvPolynomial.homogeneousComponent g (cellTop X).schur = 0) ∧
    MvPolynomial.homogeneousComponent (coreCount X) (cellTop X).schur =
      (((sortingSign X : ℤˣ) : ℤ) : CR) * (cellTop C).schur ∧
    MvPolynomial.homogeneousComponent (coreCount X + 1) (cellTop X).schur =
      (((sortingSign X : ℤˣ) : ℤ) : CR) * ∑ b ∈ unitVals X, dotS (cellTop C) b := by
  have hC' : SameLists (coreDiagram (cellTop X)) (cellTop C) :=
    (sameLists_coreDiagram_cellTop X).trans hC.cellTop
  obtain ⟨h1, h2, h3⟩ := grade_core (cellTop X) (cellTop C) hC'
  rw [coreCount_cellTop, sortingSign_cellTop, unitVals_cellTop] at *
  exact ⟨h1, h2, h3⟩

theorem SameLists.zeroFree {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) (hD : ZeroFree D) : ZeroFree E := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [← BetaDiagram.eq_of_rows_cols (show D.row = E.row from funext hr)
    (show D.col = E.col from funext hc)]
  exact hD

theorem zeroFree_coreDiagram {m : ℕ} (D : BetaDiagram m) : ZeroFree (coreDiagram D) := by
  intro k l h
  rw [coreDiagram_row, coreDiagram_col] at h
  exact coreRowEmb_mem D k ⟨coreColEmb D l, h⟩

/-- A diagram is its own half-turn exactly when the half-turn is the identity on a normalized
copy. -/
theorem symmetric_iff_rotation {m b : ℕ} {D : BetaDiagram m} {B : BetaDiagram (b + 1)}
    (h : SameLists D B) (hB : IsNorm B) : D.Symmetric ↔ B.rotation = B := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [← BetaDiagram.eq_of_rows_cols (show D.row = B.row from funext hr)
    (show D.col = B.col from funext hc)] at hB ⊢
  clear hr hc
  have hlast : D.col (Fin.last b) = 0 := hB
  constructor
  · rintro ⟨c, h1, h2⟩
    have hc : c = D.row 0 := by
      have := h2 (Fin.last b)
      simp only [Fin.rev_last] at this
      omega
    have hL : D.largestLabel = c := by simp [BetaDiagram.largestLabel, hlast, hc]
    refine BetaDiagram.eq_of_rows_cols (funext fun i => ?_) (funext fun i => ?_)
    · rw [BetaDiagram.rotation_row, hL, h1 i]
    · rw [BetaDiagram.rotation_col, hL, h2 i]
  · intro h
    refine ⟨D.largestLabel, fun i => ?_, fun i => ?_⟩
    · have := congrArg (fun E => E.row i) h
      simpa using this.symm
    · have := congrArg (fun E => E.col i) h
      simpa using this.symm

theorem isVacancy_of_unitVal {n b : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (B : BetaDiagram (b + 1)) (hB : SameLists (coreDiagram D) B) {x : ℤ}
    (hx : x ∈ unitVals D) : IsVacancy B x := by
  have hL := largestLabel_of_sameLists_core D B hB
  obtain ⟨h0, h1⟩ := unitVals_pos_lt hD hx
  obtain ⟨hcc, hr, hc⟩ := hB
  refine ⟨h0, hL ▸ h1, fun i h => ?_, fun j h => ?_⟩
  · have e : Fin.cast hcc (Fin.cast hcc.symm i) = i := Fin.ext rfl
    have := hr (Fin.cast hcc.symm i)
    rw [e] at this
    exact (unitVals_ne_core hx (Fin.cast hcc.symm i)).1 (this.trans h)
  · have e : Fin.cast hcc (Fin.cast hcc.symm j) = j := Fin.ext rfl
    have := hc (Fin.cast hcc.symm j)
    rw [e] at this
    exact (unitVals_ne_core hx (Fin.cast hcc.symm j)).2 (this.trans h)

/-- The difference of the two literal cell splices, `J₂ = s_{V ◁ CELL} - s_{CELL ◁ V}`. -/
noncomputable def cellSpliceDiff {n : ℕ} (V : BetaDiagram (n + 1)) (hV : IsNorm V) :
    SkewCofactorIndependence.CompleteRing :=
  (splice V cellCap hV cellCap_isNorm).schur - (splice cellCap V cellCap_isNorm hV).schur

open MvPolynomial in
/-- **The first cell-splice grade** (`sc:splice-nonzero`).  For a connected normalized diagram
`V` that is not its own half-turn, with zero-free core of `k` rows, the difference `J₂` of the two
literal cell splices is nonzero.  Its components of positive-letter degree below `λ` vanish and
the component of degree `λ` does not, where `λ = k` if the core is not its own half-turn and
`λ = k + 1` if it is.  Conditional on fixed-cap rigidity for the one-cell cap, `hcap`. -/
theorem splice_nonzero (hcap : CapVanishing cellCap) {n : ℕ} (V : BetaDiagram (n + 1))
    (hV : IsNorm V) (hVc : V.Connected) (hne : V.rotation ≠ V) :
    cellSpliceDiff V hV ≠ 0 ∧
    (¬ (coreDiagram V).Symmetric →
      (∀ g < coreCount V, homogeneousComponent g (cellSpliceDiff V hV) = 0) ∧
        homogeneousComponent (coreCount V) (cellSpliceDiff V hV) ≠ 0) ∧
    ((coreDiagram V).Symmetric →
      (∀ g < coreCount V + 1, homogeneousComponent g (cellSpliceDiff V hV) = 0) ∧
        homogeneousComponent (coreCount V + 1) (cellSpliceDiff V hV) ≠ 0) := by
  have hJ : cellSpliceDiff V hV = (cellTop V.rotation).schur - (cellTop V).schur := by
    unfold cellSpliceDiff
    rw [schur_splice_cell V hV, (sameLists_splice_cell V hV).schur_eq]
  have hcJ : ∀ g, homogeneousComponent g (cellSpliceDiff V hV) =
      homogeneousComponent g (cellTop V.rotation).schur -
        homogeneousComponent g (cellTop V).schur := by
    intro g; rw [hJ, map_sub]
  obtain ⟨b, hb⟩ : ∃ b, coreCount V = b + 1 :=
    ⟨coreCount V - 1, by have := coreCount_pos_of_pos V (Nat.succ_pos n); omega⟩
  set B := castDiagram (coreDiagram V) hb with hBdef
  have hBV : SameLists (coreDiagram V) B := sameLists_castDiagram _ hb
  have hBV' : SameLists (coreDiagram V.rotation) B.rotation :=
    sameLists_coreDiagram_rotation V B hBV
  have hBn : IsNorm B := by
    obtain ⟨hcc, hr, hc⟩ := hBV
    have e : Fin.cast hcc (Fin.cast hcc.symm (Fin.last b)) = Fin.last b := Fin.ext rfl
    have h1 := hc (Fin.cast hcc.symm (Fin.last b))
    rw [e, coreDiagram_col] at h1
    have h2 : coreColEmb V (Fin.cast hcc.symm (Fin.last b)) = Fin.last n := by
      have := (coreColEmb_last_iff V (Fin.cast hcc.symm (Fin.last b))).mpr (by simp [hcc])
      exact Fin.ext (by simp; omega)
    rw [h2] at h1
    exact h1.symm.trans hV
  have hVn' : IsNorm V.rotation := BetaDiagram.rotation_col_last V hV
  have hBc : B.Connected := hBV.connected (coreDiagram_connected hVc)
  have hBrn : IsNorm B.rotation := BetaDiagram.rotation_col_last B hBn
  have hBz : ZeroFree B := hBV.zeroFree (zeroFree_coreDiagram V)
  have hrot : V.rotation.schur = V.schur := BetaDiagram.schur_rotation V
  have hk' : coreCount V.rotation = coreCount V := coreCount_rotation V
  have hsym_iff : (coreDiagram V).Symmetric ↔ B.rotation = B := symmetric_iff_rotation hBV hBn
  obtain ⟨gV1, gV2, gV3⟩ := grade_core V B hBV
  obtain ⟨gW1, gW2, gW3⟩ := grade_core V.rotation B.rotation hBV'
  rw [hk'] at gW1 gW2 gW3
  rw [hrot] at gW1 gW2 gW3
  have hBrs : B.rotation.schur = B.schur := BetaDiagram.schur_rotation B
  have hσ : ((sortingSign V.rotation : ℤˣ) : ℤ) = ((sortingSign V : ℤˣ) : ℤ) := by
    have h := gW2.symm.trans gV2
    rw [hBrs] at h
    have := (mul_right_cancel₀ (BetaDiagram.schur_ne_zero B) h)
    exact_mod_cast this
  have hσne : ((((sortingSign V : ℤˣ) : ℤ)) : CR) ≠ 0 := by
    exact_mod_cast (Units.ne_zero (sortingSign V))
  obtain ⟨cV1, cV2, cV3⟩ := grade_cellTop V B hBV
  obtain ⟨cW1, cW2, cW3⟩ := grade_cellTop V.rotation B.rotation hBV'
  rw [hk'] at cW1 cW2 cW3
  rw [hσ] at cW2 cW3
  have hlow : ∀ g < coreCount V, homogeneousComponent g (cellSpliceDiff V hV) = 0 := by
    intro g hg; rw [hcJ, cW1 g hg, cV1 g hg, sub_zero]
  have hnz : ∀ g, homogeneousComponent g (cellSpliceDiff V hV) ≠ 0 → cellSpliceDiff V hV ≠ 0 := by
    intro g hg h; apply hg; rw [h, map_zero]
  have h2 : ¬ (coreDiagram V).Symmetric →
      (∀ g < coreCount V, homogeneousComponent g (cellSpliceDiff V hV) = 0) ∧
        homogeneousComponent (coreCount V) (cellSpliceDiff V hV) ≠ 0 := by
    intro hsym
    have hBrne : B.rotation ≠ B := fun h => hsym (hsym_iff.mpr h)
    refine ⟨hlow, ?_⟩
    intro h0
    rw [hcJ, cW2, cV2] at h0
    have h1 : (cellTop B.rotation).schur = (cellTop B).schur := by
      have : (((sortingSign V : ℤˣ) : ℤ) : CR) *
          ((cellTop B.rotation).schur - (cellTop B).schur) = 0 := by linear_combination h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hσne)
    apply hBrne
    refine cell_splice_ne_of_not_symmetric hcap B hBn hBc hBrn ?_
    rw [(sameLists_splice_cell B hBn).schur_eq, (sameLists_splice_cell B.rotation hBrn).schur_eq]
    exact h1.symm
  have h3 : (coreDiagram V).Symmetric →
      (∀ g < coreCount V + 1, homogeneousComponent g (cellSpliceDiff V hV) = 0) ∧
        homogeneousComponent (coreCount V + 1) (cellSpliceDiff V hV) ≠ 0 := by
    intro hsym
    have hBsym : B.rotation = B := hsym_iff.mp hsym
    have hBV'' : SameLists (coreDiagram V.rotation) B := by
      have := hBV'; rwa [hBsym] at this
    have hlow' : ∀ g < coreCount V + 1, homogeneousComponent g (cellSpliceDiff V hV) = 0 := by
      intro g hg
      by_cases hgk : g < coreCount V
      · exact hlow g hgk
      · have : g = coreCount V := by omega
        subst this
        rw [hcJ, cW2, cV2, hBsym]; ring
    refine ⟨hlow', ?_⟩
    intro h0
    rw [hcJ, cW3, cV3, hBsym] at h0
    rw [hBsym] at gW3
    have hS : ∑ b ∈ unitVals V.rotation, dotS (cellTop B) b =
        ∑ b ∈ unitVals V, dotS (cellTop B) b := by
      have : (((sortingSign V : ℤˣ) : ℤ) : CR) * (∑ b ∈ unitVals V.rotation, dotS (cellTop B) b -
          ∑ b ∈ unitVals V, dotS (cellTop B) b) = 0 := by linear_combination h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hσne)
    have hS0 : ∑ b ∈ unitVals V.rotation, dotS B b = ∑ b ∈ unitVals V, dotS B b := by
      rw [hσ] at gW3
      exact mul_left_cancel₀ hσne (gW3.symm.trans gV3)
    set ρ' : ℤ →₀ ℚ := indWeight (unitVals V.rotation) - indWeight (unitVals V) with hρ'
    have h2 : dotW (splice cellCap B cellCap_isNorm hBn) ρ' = 0 := by
      rw [(sameLists_splice_cell B hBn).dotW_eq, hρ', dotW_sub, dotW_indWeight, dotW_indWeight,
        hS, sub_self]
    have h1 : dotW B ρ' = 0 := by
      rw [hρ', dotW_sub, dotW_indWeight, dotW_indWeight, hS0, sub_self]
    have hvac : ∀ x ∈ ρ'.support, IsVacancy B x := by
      intro x hx
      rw [Finsupp.mem_support_iff] at hx
      simp only [hρ', Finsupp.sub_apply, indWeight_apply] at hx
      by_cases hx1 : x ∈ unitVals V.rotation
      · exact isVacancy_of_unitVal V.rotation hVn' B hBV'' hx1
      · by_cases hx2 : x ∈ unitVals V
        · exact isVacancy_of_unitVal V hV B hBV hx2
        · exfalso; apply hx; simp [hx1, hx2]
    have hρ0 := linearized_cap cellCap B cellCap_isNorm hBn cellCap_connected hBc cellCap_zeroFree
      hBz ρ' hvac h1 h2
    have hU : unitVals V.rotation = unitVals V := by
      ext x
      have := congrArg (fun f => f x) hρ0
      simp only [hρ', Finsupp.sub_apply, indWeight_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      by_cases hx1 : x ∈ unitVals V.rotation <;> by_cases hx2 : x ∈ unitVals V <;>
        simp [hx1, hx2] at this ⊢
    exact absurd (eq_of_core_unit (hBV''.trans hBV.symm) hU) hne
  refine ⟨?_, h2, h3⟩
  by_cases hsym : (coreDiagram V).Symmetric
  · exact hnz _ (h3 hsym).2
  · exact hnz _ (h2 hsym).2

end SkewCoframeRigidity.UnitRestoration
