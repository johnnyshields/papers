/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/MixedEta.lean`. -/
import GluingCore.Aligned.MixedEta.Base
import GluingCore.Aligned.MixedEta.Package
import GluingCore.Aligned.MixedEta.Extract
import GluingCore.Aligned.MixedEta.Upper
import GluingCore.Aligned.MixedEta.SignB

set_option linter.unusedSectionVars false

/-!
# `lem:gluing-aligned`: ordinary `ω` and a mixed upper mark `η`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-nested-count`).

`aligned_ordinary_mixed_eta_proof` is the case of `lem:gluing-aligned` in which the inner mark
`ω` is ordinary (case (a) or (b)) and the mark `η` on `U = V ∘_ω E` is mixed.  For `η` of case
(d) the lower mark is `μ = (V, V ∩ (V - z), z)`, where `L_ω(z) = v_η`, of case (d) when `ω` is of
case (a) and of case (c) when `ω` is of case (b); its legality is read off the diagonal package
of `V` (of `V` itself for `ω` of case (a), of its rotation for case (b)), which is extracted from
the private sampling of `η` at the singleton diagonal `w` of `E`.  The identity
`W_η = W_μ ∘_ω E` (the nested count of `eq:gluing-nested-count`) and the lattice map then give
`eq:gluing-reassociation`.  Case (c) of `η` follows by rotation.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

namespace MixedEta

variable {ω η : MarkedInner} {V : Diagram} {a : ℤ}

/-- The lower mark of case (c) on `V` is the rotation of the lower mark of case (d) on the rotation
of `V`. -/
theorem lowerMark_c_eq_rotate (V : Diagram) (z : ℤ × ℤ) :
    lowerMark V z .c = (lowerMark (GluingCore.rotate V) z .d).rotate := by
  have hW : V.filter (fun y => y + z ∈ V) =
      GluingCore.rotate ((lowerMark (GluingCore.rotate V) z .d).upper) := by
    ext y
    rw [mem_rotate]
    unfold upper
    rw [mem_translate]
    change _ ↔ -y - z ∈ (GluingCore.rotate V).filter (fun y => y + z ∈ GluingCore.rotate V)
    rw [Finset.mem_filter, Finset.mem_filter, mem_rotate, mem_rotate]
    have e1 : -(-y - z) = y + z := by abel
    have e2 : -(-y - z + z) = y := by abel
    rw [e1, e2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  unfold lowerMark MarkedInner.rotate
  rw [MarkedInner.mk.injEq]
  refine ⟨GluingCore.rotate_rotate.symm, hW, rfl, rfl⟩

theorem case_a_of_sign (hord : ¬ ω.case.IsMixed) (hs : ω.ordSign = 1) : ω.case = .a := by
  unfold AttachCase.IsMixed at hord
  unfold ordSign at hs
  cases hh : ω.case <;> simp_all

theorem case_b_of_sign (hord : ¬ ω.case.IsMixed) (hs : ω.ordSign = -1) : ω.case = .b := by
  unfold AttachCase.IsMixed at hord
  unfold ordSign at hs
  cases hh : ω.case <;> simp_all

/-- The lower copy of a legal mark of period `a` on `V` has `N_V - a` diagonals. -/
theorem contents_of_legal {μ : MarkedInner} (hμ : μ.IsLegal) (hne : μ.W.Nonempty)
    {V : Diagram} (hμE : μ.E = V) {a : ℤ} (hμv : content μ.v = a) :
    contents μ.W = Finset.Icc (minContent V) (minContent V + ((span V : ℤ) - a) - 1) := by
  have h : μ.IsLegalNonempty := ⟨hμ, hne⟩
  have hn := h.nonemptyMark
  have hWs := hn.2.1
  have hWd := isConnectedSkew_iff_diagonal.mp hWs
  have hspan := span_eq_of_isConnectedSkew hWs
  have hmin := h.minContent_W
  have hsp := h.span_eq
  have hper : μ.period = a := hμv
  have hw : (span μ.W : ℤ) = μ.widthZ := rfl
  rw [hμE] at hsp hmin
  rw [hWd.contents_eq]
  rw [hmin]
  congr 1
  omega

namespace Setup

variable (S : Setup ω η V a)
include S

theorem z_eq {z : ℤ × ℤ} (hzc : content z = a) : z = (z.1, z.1 + a) := by
  ext
  · rfl
  · simp only [content] at hzc; omega

/-- The lower mark `(V, V ∩ (V - z), z)` is legal (`lem:gluing-aligned`, ordinary `ω`, `η` of
case (d)).  **Differs from the paper's route.**  For `ω` of case (b) the paper repeats the
calculation with `L(e) = -e`; here the lower mark of case (c) is the rotation of the case-(d)
mark on the rotation of `V`, so the diagonal package is proved once. -/
theorem legal_lowerMark {z : ℤ × ℤ} (hz : ω.lat z = η.v) (hzc : content z = a) :
    (lowerMark V z (lowerCase ω)).IsLegal := by
  have hz' := S.z_eq hzc
  have hp := eta_rowShift_eq (ω := ω) (η := η) (a := a) (θ := z.1) (by rw [← hz']; exact hz)
  rcases ordSign_cases ω with hs | hs
  · have hcase : ω.case = .a := case_a_of_sign S.hord hs
    have hk : lowerCase ω = .d := by simp only [lowerCase, hs, ite_true]
    rw [hk]
    have hpk := S.package_a hcase
    rw [hs] at hp
    have e : z = DPackage.zOf a (η.v.1 - a * ω.rowShift) := by
      rw [hz']; unfold DPackage.zOf; ext <;> simp <;> omega
    rw [e]
    exact hpk.legal
  · have hcase : ω.case = .b := case_b_of_sign S.hord hs
    have hne1 : ¬ (ω.ordSign = 1) := by rw [hs]; decide
    have hk : lowerCase ω = .c := by simp only [lowerCase, hne1, ite_false]
    rw [hk, lowerMark_c_eq_rotate]
    have hpk := S.package_b hcase
    rw [hs] at hp
    have e : z = DPackage.zOf a (a * ω.rowShift - η.v.1) := by
      rw [hz']; unfold DPackage.zOf; ext <;> simp <;> omega
    rw [e]
    exact isLegal_rotate hpk.legal

/-- A mixed `η` forces `b > 0`. -/
theorem b_pos_of_sign : 1 ≤ (span V : ℤ) - a := by
  rcases ordSign_cases ω with hs | hs
  · exact S.b_pos_a (case_a_of_sign S.hord hs)
  · exact S.b_pos_b (case_b_of_sign S.hord hs)

theorem nonemptyMark_lowerMark {z : ℤ × ℤ} (hz : ω.lat z = η.v) (hzc : content z = a) :
    (lowerMark V z (lowerCase ω)).IsNonemptyMark := by
  have hleg := S.legal_lowerMark hz hzc
  rcases hleg.1.2 with hemp | hnon
  · exfalso
    have := hemp.2.2
    change lowerCase ω = .a at this
    unfold lowerCase at this
    split_ifs at this
  · exact hnon

/-- `W_η + v_η = (W_μ + v_μ) ∘_ω E`. -/
theorem upper_eq {z : ℤ × ℤ} (hz : ω.lat z = η.v) (hzc : content z = a) :
    η.upper = ω.compose (lowerMark V z (lowerCase ω)).upper := by
  have hleg := S.legal_lowerMark hz hzc
  have hnon := S.nonemptyMark_lowerMark hz hzc
  have hb := S.b_pos_of_sign
  obtain ⟨θ, hθ⟩ : ∃ θ, z = (θ, θ + a) := ⟨z.1, S.z_eq hzc⟩
  subst hθ
  set μ := lowerMark V (θ, θ + a) (lowerCase ω) with hμ
  have hμE : μ.E = V := rfl
  have hZ : μ.W = V.filter fun y => y + (θ, θ + a) ∈ V := rfl
  have hZc : IsConnectedSkew μ.W := hnon.2.1
  have hZcont := contents_of_legal hleg hnon.1 hμE (a := a) hzc
  have hW := S.W_eq_compose hb hz hZ hZc hZcont
  have hZne := hZc.2.1
  ext x
  have e1 : x ∈ η.upper ↔ x - η.v ∈ η.W := by
    unfold upper; rw [mem_translate]
  have e2 : x ∈ ω.compose μ.upper ↔ x - ω.lat (θ, θ + a) ∈ ω.compose μ.W := by
    unfold upper
    exact mem_compose_translate S.hord hZne (θ, θ + a)
  rw [e1, e2, hz, hW]

/-- `lem:gluing-aligned` for an ordinary `ω` and an upper mark `η` of case (d). -/
theorem reassoc_of_mixedEta_d :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ := by
  have hω := S.hω
  have hord := S.hord
  have hV := S.hV
  have hη := S.hη
  have hηd := S.hηd
  have hU := S.hU
  obtain ⟨z, hz, hzc⟩ := exists_lat_preimage (ω := ω) (η := η) S.ha
  have hleg := S.legal_lowerMark hz hzc
  have hup := S.upper_eq hz hzc
  set μ := lowerMark V z (lowerCase ω) with hμ
  have hμE : μ.E = V := rfl
  have hμv : μ.v = z := rfl
  have hsign := ordSign_cases ω
  have hμc : μ.case = lowerCase ω := rfl
  have hnon : μ.IsNonemptyMark := S.nonemptyMark_lowerMark hz hzc
  have hWne : μ.W.Nonempty := hnon.1
  have hupne : μ.upper.Nonempty := hWne.image _
  have hηnon : η.IsNonemptyMark := by
    rcases hη.1.2 with hemp | hnon
    · exfalso
      have := hemp.2.2
      rw [hηd] at this
      exact absurd this (by decide)
    · exact hnon
  have hWE : η.W ⊆ η.E := hηnon.2.2.1
  have hupE : η.upper ⊆ η.E := hηnon.2.2.2.1
  refine ⟨μ, id, ⟨hleg, hμE, Or.inl rfl, ?_⟩⟩
  intro C hC
  have hvv : η.v = ω.lat μ.v := by rw [hμv, hz]
  rcases hsign with hs | hs
  · have hc : η.case = μ.case := by
      rw [hηd, hμc]; simp only [lowerCase, hs, ite_true]
    exact compose_reassoc_mixed_sign_one hord hs hV.2.1 hμE hU hvv hc hupne hup hC.2.1
  · have hne1 : ¬ (ω.ordSign = 1) := by rw [hs]; decide
    have hcμ : μ.case = .c := by
      rw [hμc]; simp only [lowerCase, hne1, ite_false]
    exact compose_reassoc_mixed_sign_neg hord hs hV.2.1 hμE hU hvv hηd hcμ hupne hup hupE hWE hC

end Setup

end MixedEta

/-! ### Case (c) of `η` by rotation, and the lemma -/

theorem rotate_antitranspose_rotate (C : Diagram) :
    GluingCore.rotate (antitranspose (GluingCore.rotate C)) = antitranspose C := by
  ext y
  simp only [mem_rotate, mem_antitranspose]
  simp

theorem IsReassociation.of_rotate_mixedEta {ω η : MarkedInner} {V : Diagram} {μ : MarkedInner}
    {γ : Diagram → Diagram} (hV : V.Nonempty)
    (h : IsReassociation ω.rotate η.rotate (GluingCore.rotate V) μ γ) :
    IsReassociation ω η V μ.rotate γ := by
  refine ⟨isLegal_rotate h.legal, ?_, ?_, ?_⟩
  · change GluingCore.rotate μ.E = V
    rw [h.inner, GluingCore.rotate_rotate]
  · rcases h.gamma with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      change GluingCore.rotate μ.upper = ∅
      simp [upper, h2, GluingCore.translate, GluingCore.rotate]
  · intro C hC
    have hrC : IsConnectedSkew (GluingCore.rotate C) := isConnectedSkew_rotate hC
    have h1 := h.compose_eq _ hrC
    have hCne := hC.2.1
    have hγne : ∀ X : Diagram, X.Nonempty → (γ X).Nonempty := by
      intro X hX
      rcases h.gamma with h3 | ⟨h3, -⟩
      · rw [h3]; exact hX
      · rw [h3]; exact hX.image _
    have hY : (γ (GluingCore.rotate C)).Nonempty := hγne _ (hCne.image _)
    have hμne : μ.E.Nonempty := by
      rw [h.inner]; exact hV.image _
    have hX : (μ.compose (γ (GluingCore.rotate C))).Nonempty := by
      obtain ⟨d, hd⟩ := hY
      obtain ⟨y, hy⟩ := hμne
      refine ⟨y + μ.origin (γ (GluingCore.rotate C)) d, ?_⟩
      rw [mem_compose ⟨d, hd⟩]
      exact Or.inl ⟨d, hd, by rw [mem_translate]; simpa using hy⟩
    have e1 : η.compose C =
        GluingCore.rotate (η.rotate.compose (GluingCore.rotate C)) := by
      have := rotate_compose (D := GluingCore.rotate C) (hCne.image _) η.rotate
      rw [rotate_rotate, GluingCore.rotate_rotate] at this
      exact this
    have e2 : GluingCore.rotate (ω.rotate.compose (μ.compose (γ (GluingCore.rotate C)))) =
        ω.compose (GluingCore.rotate (μ.compose (γ (GluingCore.rotate C)))) := by
      have := rotate_compose (D := μ.compose (γ (GluingCore.rotate C))) hX ω.rotate
      rw [rotate_rotate] at this
      exact this.symm
    have e3 : GluingCore.rotate (μ.compose (γ (GluingCore.rotate C))) =
        μ.rotate.compose (γ C) := by
      have := rotate_compose (D := γ (GluingCore.rotate C)) hY μ
      have e4 : GluingCore.rotate (γ (GluingCore.rotate C)) = γ C := by
        rcases h.gamma with h3 | ⟨h3, -⟩
        · rw [h3]; exact GluingCore.rotate_rotate
        · rw [h3]; exact rotate_antitranspose_rotate C
      rw [e4] at this
      exact this.symm
    rw [e1, h1, e2, e3]

variable {ω η : MarkedInner} {V : Diagram}

/-- **`lem:gluing-aligned`, ordinary `ω` and mixed `η`.**  Same statement as
`aligned_ordinary_mixed_eta`; case (c) of `η` is reduced to case (d) by rotation. -/
theorem aligned_ordinary_mixed_eta_proof (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) (hη : η.IsLegal) (hηmix : η.case.IsMixed)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ := by
  have hVne := hV.2.1
  unfold AttachCase.IsMixed at hηmix
  rcases hηmix with hc | hd
  · have hd : η.rotate.case = .d := by simp [rotate, hc, AttachCase.rotate]
    have hU' : η.rotate.E = ω.rotate.compose (GluingCore.rotate V) := by
      rw [rotate_compose hVne]
      change GluingCore.rotate η.E = _
      rw [hU]
    have ha' : content η.rotate.v = a * ω.rotate.period := ha
    have hord' : ¬ ω.rotate.case.IsMixed := by
      unfold AttachCase.IsMixed at hord ⊢
      change ¬ (ω.case.rotate = .c ∨ ω.case.rotate = .d)
      cases hcc : ω.case <;> simp_all [AttachCase.rotate]
    obtain ⟨μ, γ, h⟩ := (MixedEta.Setup.reassoc_of_mixedEta_d
      ⟨isLegal_rotate hω, hord', isConnectedSkew_rotate hV, isLegal_rotate hη, hd, hU', ha'⟩)
    exact ⟨μ.rotate, γ, h.of_rotate_mixedEta hVne⟩
  · exact MixedEta.Setup.reassoc_of_mixedEta_d ⟨hω, hord, hV, hη, hd, hU, ha⟩

end MarkedInner

end GluingCore
