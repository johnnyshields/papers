import SkewGluing.MinimalFibers.Score
import SkewGluing.Score

/-!
# Source-minimal domination

Formalizes `shields-2026-skew-gluing.tex`, «Minimizing a chart»
(`thm:source-minimal-domination`) and `lem:rotation-components`.

* `Chart.IsSourceMinimal.fiber_subset`: for a source-minimal chart `χ` of `F` and any proper
  legal chart
  `χ'` of `F`, the fiber of `χ'` lies in `𝓕_χ = 𝓕(χ.ω, s_{χ.D})`.  The proof is the comparison table
  of the paper: equal and dividing periods (`lem:gluing-equal`, `prop:gluing-divisible`), a
  period `q ∣ p` excluded by the score, nondividing periods with `gcd > 1` excluded by the score
  of the period-`gcd` root, and coprime periods giving a line inner and `𝓕_χ = [F]`
  (`lem:gluing-lines`).
* `Chart.IsSourceMinimal.fiberClass_subset`: every fiber `𝓕(ω, Q)` through `F` is contained in
  `𝓕_χ`.
* `source_minimal_domination`: the components of `F` in `Γ(s_F)` and in `Γ⁺(s_F)` are exactly
  the translation classes of the members of `𝓕_χ`.

The Olson-Harris composition theorem is the hypothesis `hOH`, discharged by
`olsonHarrisComposition` in `SkewGluing.MainTheorems`.

Sorry-free.
-/

namespace SkewGluing

/-! ### Elementary facts about fibers -/

theorem fiberClass_translate_mem {s : Diagram → Lambda} {ω : MarkedInner} {Q : Lambda}
    {F : Diagram} (h : F ∈ fiberClass s ω Q) (u : ℤ × ℤ) : translate u F ∈ fiberClass s ω Q := by
  obtain ⟨F', hF', t, rfl⟩ := h
  exact ⟨F', hF', u + t, by rw [translate_translate]⟩

/-- `𝓕(ω*, Q) = 𝓕(ω, Q)`: the fiber contains the compositions through both orientations. -/
theorem fiber_rotate_inner {R : Type*} (s : Diagram → R) (ω : MarkedInner) (Q : R) :
    fiber s ω.rotate Q = fiber s ω Q := by
  ext F
  simp only [fiber, MarkedInner.rotate_rotate, Set.mem_ofPred_eq]
  exact exists_congr fun A => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => or_comm

theorem fiberClass_rotate_inner {R : Type*} (s : Diagram → R) (ω : MarkedInner) (Q : R) :
    fiberClass s ω.rotate Q = fiberClass s ω Q := by
  unfold fiberClass
  rw [fiber_rotate_inner]

/-- Every member of a fiber of a legal marked inner is a connected skew diagram. -/
theorem isConnectedSkew_of_mem_fiberClass {ω : MarkedInner} (hω : ω.IsLegal) {Q : Lambda}
    {F : Diagram} (hF : F ∈ fiberClass cellSchur ω Q) : IsConnectedSkew F := by
  obtain ⟨F', ⟨A, hA, -, -, hF'⟩, t, rfl⟩ := hF
  refine (isConnectedSkew_translate_iff t).mpr ?_
  rcases hF' with rfl | rfl
  · exact hω.isConnectedSkew_compose hA
  · exact (MarkedInner.isLegal_rotate hω).isConnectedSkew_compose hA

/-- **Every member of a fiber has the same Schur function** (Olson-Harris, via `hOH`). -/
theorem cellSchur_eq_of_mem_fiberClass (hOH : OlsonHarrisComposition) {ω : MarkedInner}
    (hω : ω.IsLegal) {Q : Lambda} {F F' : Diagram} (hF : F ∈ fiberClass cellSchur ω Q)
    (hF' : F' ∈ fiberClass cellSchur ω Q) : cellSchur F = cellSchur F' := by
  obtain ⟨G, hG, t, rfl⟩ := hF
  obtain ⟨G', hG', t', rfl⟩ := hF'
  rw [cellSchur_translate, cellSchur_translate]
  exact hOH.fiber_eq hω hG hG'

/-! ### The comparison table of `thm:source-minimal-domination` -/

/-- If `χ` has a line inner, every diagram with a fiber through `F` (a diagram of the Schur class
of `F`) lies in `𝓕_χ`: `𝓕_χ = [F]`. -/
theorem fiberClass_subset_of_line (hOH : OlsonHarrisComposition) {F : Diagram} {χ χ' : Chart}
    (h : χ.IsProperLegal) (c : χ.IsChartOf F) (hline : LineInner χ.ω) (h' : χ'.IsProperLegal)
    (c' : χ'.IsChartOf F) :
    fiberClass cellSchur χ'.ω (cellSchur χ'.D) ⊆ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  intro H hH
  have hFmem := h'.mem_fiberClass_parent c'
  have hHF : cellSchur H = cellSchur F := cellSchur_eq_of_mem_fiberClass hOH h'.2.2.2 hH hFmem
  have hHconn := isConnectedSkew_of_mem_fiberClass h'.2.2.2 hH
  obtain ⟨t, rfl⟩ := c
  have hpar : cellSchur H = cellSchur χ.parent := by
    rw [hHF, cellSchur_translate]
  obtain ⟨χ'', h'', hω'', hs'', c''⟩ := h.exists_chart_of_line hline hHconn.1 hpar
  have := h''.mem_fiberClass_parent c''
  rwa [hω'', hs''] at this

/-- **`thm:source-minimal-domination`, containment.**  For a source-minimal chart `χ` of `F`,
every proper-chart fiber through `F` is contained in `𝓕_χ`: for every proper legal chart `χ'` of
`F`, `𝓕(χ'.ω, s_{χ'.D}) ⊆ 𝓕(χ.ω, s_{χ.D})`.  The Olson-Harris composition theorem is
`hOH`. -/
theorem Chart.IsSourceMinimal.fiber_subset (hOH : OlsonHarrisComposition) {F : Diagram}
    {χ : Chart} (hχ : χ.IsSourceMinimal F) {χ' : Chart} (h' : χ'.IsProperLegal)
    (c' : χ'.IsChartOf F) :
    fiberClass cellSchur χ'.ω (cellSchur χ'.D) ⊆ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  obtain ⟨h, c, hmin⟩ := hχ
  have hp : 0 < χ.period := h.2.2.2.period_pos
  have hp' : 0 < χ'.period := h'.2.2.2.period_pos
  -- `p ∣ q`: equal or divisible periods
  by_cases hd : χ.period ∣ χ'.period
  · exact h.fiber_subset_of_dvd hOH h' c c' hd
  have hn : ¬ χ.period.toNat ∣ χ'.period.toNat := fun hh => hd (by
    rw [← h.period_toNat, ← h'.period_toNat]; exact_mod_cast hh)
  have hp0 : 0 < χ.period.toNat := by omega
  have hq0 : 0 < χ'.period.toNat := by omega
  by_cases hd' : χ'.period.toNat ∣ χ.period.toNat
  · -- `q ∣ p`, `q < p`: a smaller score
    have hlt : χ'.period.toNat < χ.period.toNat :=
      lt_of_le_of_ne (Nat.le_of_dvd hp0 hd') (fun e => hn (e ▸ dvd_rfl))
    have hs := score_lt_of_dvd (N := span F) hd' hlt
    rw [← h.score_eq c, ← h'.score_eq c'] at hs
    exact absurd (hmin χ' h' c') (not_le.mpr hs)
  by_cases hg : 1 < Nat.gcd χ.period.toNat χ'.period.toNat
  · -- a proper root of period `g`, of smaller score
    obtain ⟨ψ, hψ, cψ, hper⟩ := Chart.IsProperLegal.exists_gcd_root h h' c c' hn hd' hg
    have hs := score_gcd_lt_left (N := span F) hp0 hn
    have hψs := hψ.score_eq cψ
    have hper' : ψ.period.toNat = Nat.gcd χ.period.toNat χ'.period.toNat := by omega
    rw [hper'] at hψs
    rw [← hψs, ← h.score_eq c] at hs
    exact absurd (hmin ψ hψ cψ) (not_le.mpr hs)
  · -- coprime periods: a line inner
    have hcop : Nat.gcd χ.period.toNat χ'.period.toNat = 1 := by
      have := Nat.gcd_pos_of_pos_left χ'.period.toNat hp0
      omega
    have hcop' : Int.gcd χ.period χ'.period = 1 := by
      have e₁ : χ.period.natAbs = χ.period.toNat := by omega
      have e₂ : χ'.period.natAbs = χ'.period.toNat := by omega
      change Nat.gcd χ.period.natAbs χ'.period.natAbs = 1
      rw [e₁, e₂]
      exact hcop
    obtain ⟨-, -, hline⟩ := Chart.IsProperLegal.coprime_periods_line h h' c c' hcop'
    exact fiberClass_subset_of_line hOH h c (hline.imp (fun x => x.1) (fun x => x.1)) h' c'

/-- **`thm:source-minimal-domination`, for fibers `𝓕(ω, Q)`.**  Every fiber `𝓕(ω, Q)` of a legal
marked inner with `|E| ≥ 2` that contains `F` is contained in `𝓕_χ`. -/
theorem Chart.IsSourceMinimal.fiberClass_subset (hOH : OlsonHarrisComposition) {F : Diagram}
    {χ : Chart} (hχ : χ.IsSourceMinimal F) {ω : MarkedInner} (hω : ω.IsLegal)
    (hE : 2 ≤ ω.E.card) {Q : Lambda} (hF : F ∈ fiberClass cellSchur ω Q) :
    fiberClass cellSchur ω Q ⊆ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  obtain ⟨χ', hχ', cχ', hω', hQ⟩ := exists_chart_of_mem_fiberClass hω hE hF
  have e : fiberClass cellSchur χ'.ω (cellSchur χ'.D) = fiberClass cellSchur ω Q := by
    rw [hQ]
    rcases hω' with h | h
    · rw [h]
    · rw [h, fiberClass_rotate_inner]
  rw [← e]
  exact hχ.fiber_subset hOH hχ' cχ'

/-! ### The component of `F` -/

/-- The vertices of `Γ(P)` (translation classes of connected skew diagrams with function `P`)
represented by a diagram of `S`. -/
def classVertices (P : Lambda) (S : Set Diagram) : Set (TranslationClass (connectedClass P)) :=
  {c | ∃ x : {F : Diagram // connectedClass P F}, classOf x = c ∧ x.1 ∈ S}

/-- Every member of `𝓕_χ` is a vertex of `Γ(s_F)`: a connected skew diagram of the Schur class of
`F` (Olson-Harris, via `hOH`). -/
theorem Chart.IsSourceMinimal.fiberClass_subset_connectedClass (hOH : OlsonHarrisComposition)
    {F : Diagram} {χ : Chart} (hχ : χ.IsSourceMinimal F) {H : Diagram}
    (hH : H ∈ fiberClass cellSchur χ.ω (cellSchur χ.D)) : connectedClass (cellSchur F) H :=
  ⟨isConnectedSkew_of_mem_fiberClass hχ.1.2.2.2 hH,
    cellSchur_eq_of_mem_fiberClass hOH hχ.1.2.2.2 hH (hχ.1.mem_fiberClass_parent hχ.2.1)⟩

/-- **`thm:source-minimal-domination`, the components.**  For a source-minimal chart `χ` of `F`
and `P = s_F`, the component of the class of `F` in `Γ(P)` and in `Γ⁺(P)` is exactly the set of
translation classes of the members of `𝓕_χ`.

Every other vertex in the component of `F` is adjacent to `F` by `thm:gluing`, and that edge
is witnessed by a proper-chart fiber through `F`, which is contained in `𝓕_χ` by
`Chart.IsSourceMinimal.fiber_subset`.  Conversely `𝓕_χ` is a fiber, hence a clique containing
`F`. -/
theorem Chart.IsSourceMinimal.component_eq (hOH : OlsonHarrisComposition) {P : Lambda}
    {F : Diagram} {χ : Chart} (hχ : χ.IsSourceMinimal F) (hF : connectedClass P F) :
    ((classGraph (connectedClass P)).connectedComponentMk (classOf ⟨F, hF⟩)).supp =
        classVertices P (fiberClass cellSchur χ.ω (cellSchur χ.D)) ∧
    ((connectedRotationData P).augmented.connectedComponentMk (classOf ⟨F, hF⟩)).supp =
        classVertices P (fiberClass cellSchur χ.ω (cellSchur χ.D)) := by
  have hFmem := hχ.1.mem_fiberClass_parent hχ.2.1
  have hcl := gluing_connectedClass_componentsAreCliques hOH P
  have key : ((classGraph (connectedClass P)).connectedComponentMk (classOf ⟨F, hF⟩)).supp =
        classVertices P (fiberClass cellSchur χ.ω (cellSchur χ.D)) := by
    ext c
    obtain ⟨y, rfl⟩ := exists_classOf c
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    constructor
    · intro hr
      refine ⟨y, rfl, ?_⟩
      by_cases hyF : classOf y = classOf (⟨F, hF⟩ : {F : Diagram // connectedClass P F})
      · obtain ⟨t, ht⟩ := classOf_eq_iff.mp hyF
        have e : y.1 = SkewGluing.translate (-t) F := by
          have : F = SkewGluing.translate t y.1 := ht
          rw [this, SkewGluing.translate_translate, neg_add_cancel, SkewGluing.translate_zero]
        rw [e]
        exact fiberClass_translate_mem hFmem _
      · have hadj := hcl.adj_of_reachable hr hyF
        rw [classGraph_adj_iff] at hadj
        obtain ⟨χ'', h'', c'', hy⟩ := hadj.exists_chart_fiber
        exact hχ.fiber_subset hOH h'' c'' hy
    · rintro ⟨x, hx, hxmem⟩
      rw [← hx]
      by_cases hxF : classOf x = classOf (⟨F, hF⟩ : {F : Diagram // connectedClass P F})
      · rw [hxF]
      · refine SimpleGraph.Adj.reachable ?_
        rw [classGraph_adj_iff]
        refine fiberClass_hasCommonFinalFactor hχ.1.2.2.2 hχ.1.2.2.1 hxmem hFmem ?_
        rintro ⟨t, ht⟩
        exact hxF (classOf_eq_iff.mpr ⟨t, ht⟩)
  exact ⟨key, by
    rw [← key]
    exact (connectedRotationData P).augmented_connectedComponent_supp_eq_of_rooted
      ((classOf_mem_classRooted_iff).mpr ⟨χ, hχ.1, hχ.2.1⟩)⟩

end SkewGluing
