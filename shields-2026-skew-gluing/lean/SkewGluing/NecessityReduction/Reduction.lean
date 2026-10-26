import SkewGluing.NecessityReduction.Connectivity

/-!
# The reduction of composition necessity

Formalizes `shields-2026-skew-gluing.tex`, «Reduction of composition necessity»
(`thm:necessity-reduction`).

The three global assertions about connected diagrams:

1. `CommonPresentations`: every Schur-equal pair admits a common legal left-associated
   composition presentation with connected factors, whose corresponding factors and marks agree
   up to transported rotation;
2. `TerminalRigidityAndKeyInvariance`: (TR) and (RI) hold in every connected Schur class;
3. `TowersExhaustClasses`: every prescribed complete source-minimal tower has reversal family
   equal to the full connected Schur class of its source.

`necessity_reduction` proves that they are equivalent, from the composition theorem
`OlsonHarrisComposition` (forward composition and reversal), `thm:gluing` (`GluingStatement`),
`thm:source-minimal-domination` (`SourceMinimalDomination`) and `prop:component-key`
(`ComponentKeyClassifies`).  The implications are `commonPresentations_to_terminalRigidity`
(first to second), `terminalRigidity_to_towersExhaust` (second to third) and
`towersExhaust_to_commonPresentations` (third to first).

The four hypotheses are discharged in `SkewGluing.MainTheorems` (`olsonHarrisComposition`,
`gluing`, `source_minimal_domination`, `component_key`).

Sorry-free.
-/

namespace SkewGluing

/-! ### Fibers lie in one Schur class -/

namespace OlsonHarrisComposition

variable (hOH : OlsonHarrisComposition)

include hOH

/-- The fiber `𝓕(ω, s_D)` of a proper legal chart `(D, ω)`, read up to translation, consists of
connected diagrams with the function of the parent `D ∘_ω E`: `𝓕_χ ⊆ [F]`. -/
theorem fiberClass_subset_connectedClass {χ : Chart} (hχ : χ.IsProperLegal) :
    ∀ G ∈ fiberClass cellSchur χ.ω (cellSchur χ.D), connectedClass (cellSchur χ.parent) G := by
  obtain ⟨hD, hc, -, hω⟩ := hχ
  rintro G ⟨F', hF', t, rfl⟩
  have hmem : χ.parent ∈ fiber cellSchur χ.ω (cellSchur χ.D) :=
    ⟨χ.D, hD, hc, rfl, Or.inl rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA, -, -, rfl | rfl⟩ := hF'
    · exact isConnectedSkew_translate t (hω.isConnectedSkew_compose hA)
    · exact isConnectedSkew_translate t
        ((MarkedInner.isLegal_rotate hω).isConnectedSkew_compose hA)
  · rw [cellSchur_translate]
    exact hOH.fiber_eq hω hF' hmem

end OlsonHarrisComposition

/-! ### The three assertions -/

/-- The first assertion of `thm:necessity-reduction`: every Schur-equal pair of connected
diagrams admits a common legal left-associated composition presentation with connected factors,
whose corresponding factors and marks agree up to transported rotation (the diagrams being read
up to translation).  This is the composition-and-reversal necessity part of the conjecture of
McNamara–van Willigenburg, without its class-cardinality clause. -/
def CommonPresentations : Prop :=
  ∀ F G : Diagram, IsConnectedSkew F → IsConnectedSkew G → cellSchur F = cellSchur G →
    ∃ π π' : Presentation, π.IsLegal ∧ π'.IsLegal ∧ π.Corresponds π' ∧
      (∃ t : ℤ × ℤ, F = translate t π.value) ∧ ∃ t : ℤ × ℤ, G = translate t π'.value

/-- The second assertion of `thm:necessity-reduction`: (TR) and (RI) hold in every connected
Schur class. -/
def TerminalRigidityAndKeyInvariance : Prop :=
  ∀ P : Lambda, TerminalRigidity P ∧ RootedKeyInvariance P

/-- The third assertion of `thm:necessity-reduction`: every prescribed complete source-minimal
tower has reversal family equal to the full connected Schur class of its source. -/
def TowersExhaustClasses : Prop :=
  ∀ π : Presentation, π.IsCompleteTower →
    π.reversalFamily = {G | connectedClass (cellSchur π.value) G}

/-! ### First implies second -/

/-- **`thm:necessity-reduction`, the first assertion implies the second.**  A common presentation
of a nonrotation pair has a proper final stage whose two outer prefixes are Schur-equal by
forward composition and reversal, so the pair has a common final factor
(`Presentation.Corresponds.rotationMates_or_hasCommonFinalFactor`); then
`thm:connectivity-reduction` gives (TR) and (RI). -/
theorem commonPresentations_to_terminalRigidity (hOH : OlsonHarrisComposition)
    (hgluing : GluingStatement) (hkey : ComponentKeyClassifies) (h1 : CommonPresentations) :
    TerminalRigidityAndKeyInvariance := by
  intro P
  by_cases hP : ∃ F, connectedClass P F
  · refine ((connectivity_reduction hgluing hkey P hP).out 3 4).mp ?_
    intro F G hF hG hnm
    obtain ⟨π, π', hl, -, hc, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      h1 F G hF.1 hG.1 (hF.2.trans hG.2.symm)
    rcases hc.rotationMates_or_hasCommonFinalFactor hOH hl with h | h
    · exact absurd (RotationMates.of_translates h ha hb) hnm
    · rw [ha, hb]
      exact (h.translate_left a).translate_right b
  · push Not at hP
    exact ⟨fun F _ hF => absurd hF (hP F), fun F _ hF => absurd hF (hP F)⟩

/-! ### Second implies third -/

/-- Under (TR), (RI), `thm:gluing`, `prop:component-key` and `thm:source-minimal-domination`, the
connected Schur class of a diagram `F` is the fiber of any source-minimal chart of `F`:
`[F] = 𝓕(ω, s_D)` (`thm:necessity-reduction`, second to third). -/
theorem connectedClass_subset_fiberClass (hgluing : GluingStatement)
    (hkey : ComponentKeyClassifies) (hdom : SourceMinimalDomination) {P : Lambda}
    (hP : TerminalRigidity P ∧ RootedKeyInvariance P) {F : Diagram} (hF : connectedClass P F)
    {χ : Chart} (hχ : χ.IsSourceMinimal F) {G : Diagram} (hG : connectedClass P G) :
    G ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  have hconn := ((connectivity_reduction hgluing hkey P ⟨F, hF⟩).out 4 1).mp hP
  have hr := hconn.preconnected (classOf ⟨F, hF⟩) (classOf ⟨G, hG⟩)
  exact (((hdom P ⟨F, hF⟩ χ hχ).2 ⟨G, hG⟩).2).mp hr

/-- **`thm:necessity-reduction`, the second assertion implies the third.**  The induction on the
prescribed tower: at a chartless first factor (TR) identifies the class with its one-factor
reversal family; at a stage `F = D ∘_ω E`, `[F] = 𝓕(ω, s_D)` by `thm:connectivity-reduction` and
`thm:source-minimal-domination`, the class of `D` is the reversal family of the prefix tower, and
appending `(E, ω)` or `(E*, ω*)` to every member gives the fiber; forward composition and
reversal gives the reverse inclusion. -/
theorem terminalRigidity_to_towersExhaust (hOH : OlsonHarrisComposition)
    (hgluing : GluingStatement) (hkey : ComponentKeyClassifies) (hdom : SourceMinimalDomination)
    (h2 : TerminalRigidityAndKeyInvariance) : TowersExhaustClasses := by
  intro π hπ
  induction hπ with
  | @first F₀ hF₀ hnr =>
    ext G
    constructor
    · rintro ⟨π', hcor, t, rfl⟩
      cases π' with
      | first F' =>
        have hF' : IsConnectedSkew F' := Presentation.Corresponds.isLegal hcor hF₀
        exact ⟨isConnectedSkew_translate t hF', by
          rw [cellSchur_translate]; exact hcor.cellSchur_eq⟩
      | step _ _ => exact hcor.elim
    · intro hG
      exact ⟨.first G, (h2 _).1 F₀ G ⟨hF₀, rfl⟩ hG hnr, 0, (translate_zero).symm⟩
  | @step π ω hπ hsm ih =>
    have hl : π.IsLegal := hπ.isLegal
    obtain ⟨hD, hc, hE, hω⟩ := hsm.1
    have hFc : IsConnectedSkew (ω.compose π.value) := hω.isConnectedSkew_compose hD
    ext G
    constructor
    · rintro ⟨π', hcor, t, rfl⟩
      cases π' with
      | first _ => exact hcor.elim
      | step π'' ω' =>
        obtain ⟨hπ'', hω'⟩ := hcor
        have hA : π''.value ∈ π.reversalFamily := ⟨π'', hπ'', 0, (translate_zero).symm⟩
        rw [ih] at hA
        have hcard : π''.value.card = π.value.card :=
          card_eq_of_cellSchur_eq hD hA.1.1 hA.2
        have hc2 : 2 ≤ π''.value.card := by
          have : 2 ≤ π.value.card := hc
          omega
        change connectedClass (cellSchur (ω.compose π.value)) (translate t (ω'.compose π''.value))
        rcases hω' with ⟨s, rfl⟩ | ⟨s, rfl⟩
        · have hmem : translate t ((ω.translateBy s).compose π''.value) ∈
              fiberClass cellSchur ω (cellSchur π.value) :=
            ⟨ω.compose π''.value, ⟨π''.value, hA.1, hc2, hA.2, Or.inl rfl⟩, t + s, by
              change translate t ((ω.translate s).compose π''.value) = _
              rw [MarkedInner.compose_translate, translate_translate]⟩
          exact hOH.fiberClass_subset_connectedClass hsm.1 _ hmem
        · have hmem : translate t ((ω.rotate.translateBy s).compose π''.value) ∈
              fiberClass cellSchur ω (cellSchur π.value) :=
            ⟨ω.rotate.compose π''.value, ⟨π''.value, hA.1, hc2, hA.2, Or.inr rfl⟩, t + s, by
              change translate t ((ω.rotate.translate s).compose π''.value) = _
              rw [MarkedInner.compose_translate, translate_translate]⟩
          exact hOH.fiberClass_subset_connectedClass hsm.1 _ hmem
    · intro hG
      have hclass := (h2 (cellSchur (ω.compose π.value)))
      have hmem := connectedClass_subset_fiberClass hgluing hkey hdom hclass
        (F := ω.compose π.value) ⟨hFc, rfl⟩ hsm hG
      obtain ⟨F', ⟨A, hA, -, hAs, hF'⟩, t, rfl⟩ := hmem
      have hAm : A ∈ π.reversalFamily := by
        rw [ih]; exact ⟨hA, hAs⟩
      obtain ⟨π'', hπ'', u, rfl⟩ := hAm
      have hl'' : π''.IsLegal := hπ''.isLegal hl
      have hne : π''.value.Nonempty := (Presentation.isConnectedSkew_value hl'').2.1
      rcases hF' with rfl | rfl
      · refine ⟨.step π'' ω, ⟨hπ'', Or.inl (MarkedInner.EquivTranslate.refl ω)⟩,
          t + ω.outerShift u, ?_⟩
        change translate t (ω.compose (translate u π''.value)) =
          translate (t + ω.outerShift u) (ω.compose π''.value)
        rw [MarkedInner.compose_translate_outer u hne, translate_translate]
      · refine ⟨.step π'' ω.rotate, ⟨hπ'', Or.inr (MarkedInner.EquivTranslate.refl _)⟩,
          t + ω.rotate.outerShift u, ?_⟩
        change translate t (ω.rotate.compose (translate u π''.value)) =
          translate (t + ω.rotate.outerShift u) (ω.rotate.compose π''.value)
        rw [MarkedInner.compose_translate_outer u hne, translate_translate]

/-! ### Third implies first -/

/-- **`thm:necessity-reduction`, the third assertion implies the first.**  Every connected
diagram is the value of a complete source-minimal tower (`Presentation.exists_isCompleteTower`);
the reversal family of a tower of `F` is the whole Schur class of `F`, so a Schur-equal `G` is
a presentation corresponding to the tower of `F`. -/
theorem towersExhaust_to_commonPresentations (h3 : TowersExhaustClasses) :
    CommonPresentations := by
  intro F G hF hG hFG
  obtain ⟨π, hπ, hval⟩ := Presentation.exists_isCompleteTower _ F rfl hF
  have hfam := h3 π hπ
  have hGm : G ∈ π.reversalFamily := by
    rw [hfam, hval]; exact ⟨hG, hFG.symm⟩
  obtain ⟨π', hcor, t, hGt⟩ := hGm
  exact ⟨π, π', hπ.isLegal, hcor.isLegal hπ.isLegal, hcor, ⟨0, by
    rw [hval, translate_zero]⟩, ⟨t, hGt⟩⟩

/-! ### The reduction -/

/-- **`thm:necessity-reduction` (Reduction of necessity).**  The following global assertions
about connected diagrams are equivalent:

1. every Schur-equal pair admits a common legal left-associated composition presentation with
   connected factors, whose corresponding factors and marks agree up to transported rotation
   (`CommonPresentations`);
2. assertions (TR) and (RI) hold in every connected Schur class
   (`TerminalRigidityAndKeyInvariance`);
3. every prescribed complete source-minimal tower has reversal family equal to its source's full
   connected Schur class (`TowersExhaustClasses`).

The inputs are `hOH`, forward composition and reversal (Olson-Harris, Thms. 5.3.9–5.3.10, the
proposition `OlsonHarrisComposition`), `hgluing` (`thm:gluing`), `hdom`
(`thm:source-minimal-domination`) and `hkey` (`prop:component-key`).  The first assertion is the
composition-and-reversal necessity part of the conjecture of McNamara–van Willigenburg, without
its class-cardinality clause. -/
theorem necessity_reduction (hOH : OlsonHarrisComposition) (hgluing : GluingStatement)
    (hdom : SourceMinimalDomination) (hkey : ComponentKeyClassifies) :
    List.TFAE [CommonPresentations, TerminalRigidityAndKeyInvariance, TowersExhaustClasses] := by
  tfae_have 1 → 2 := commonPresentations_to_terminalRigidity hOH hgluing hkey
  tfae_have 2 → 3 := terminalRigidity_to_towersExhaust hOH hgluing hkey hdom
  tfae_have 3 → 1 := towersExhaust_to_commonPresentations
  tfae_finish

end SkewGluing
