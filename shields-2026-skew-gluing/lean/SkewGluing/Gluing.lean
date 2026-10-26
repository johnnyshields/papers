import SkewGluing.Gluing.Edges
import SkewGluing.Gluing.Roots
import SkewGluing.Gluing.Fibers
import SkewGluing.NecessityReduction.Statements

/-!
# Local common-factor gluing

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`thm:gluing`) and
«Completion of the gluing proof».

* `Chart.IsProperLegal.exists_covering_chart`: the case analysis of the proof.  Two proper charts
  `χ₁`, `χ₂` of one diagram `Y` with no proper line inner at `Y` have a proper chart `ψ` at `Y`
  whose fiber contains both of their fibers: equal and dividing periods are
  `lem:gluing-equal` and `prop:gluing-divisible` (`fiber_subset_of_dvd`); coprime periods force
  line inners (`lem:gluing-lines`); nondividing periods with `g = gcd > 1` have a proper
  period-`g` root (`exists_gcd_root`: `lem:gluing-small`, `prop:gluing-ordinary-fold`,
  `lem:gluing-incompatible`, `prop:gluing-mixed-fold`), whose fiber contains both by
  `prop:gluing-divisible`.
* `gluing_fork` (`thm:gluing`, fork form): if `X, Y` and `Y, Z` each have a common final factor
  and `X, Z` are not translates of one another, then `X, Z` have a common final factor.  With a
  proper line inner at `Y` this is `lem:gluing-lines`; otherwise two fibers are placed in one
  fiber by `exists_covering_chart`, and fibers are cliques (`fiberClass_hasCommonFinalFactor`).
  Vertices without a proper chart are isolated, so the fork cannot occur there: an edge produces a
  proper chart (`HasCommonFinalFactor.exists_chart_fiber`).
* `gluing_componentsAreCliques` (`thm:gluing`): every connected component of the common-factor
  graph `classGraph (skewClass P)` of every Schur function `P` is a clique.  The closing
  shortest-path argument is `componentsAreCliques_iff_incident_edges`.
* `gluingStatement`: `thm:gluing` as the proposition `GluingStatement`.
* `rotation_components_unconditional` (`lem:rotation-components`): the hypothesis `hgluing` of
  `rotation_components` is discharged.

The Olson-Harris composition theorem, which the paper cites, is the hypothesis
`hOH : OlsonHarrisComposition` (Olson-Harris, Thms. 5.3.9–5.3.10); it is used only by
`prop:gluing-divisible`, and `SkewGluing.MainTheorems` discharges it by `olsonHarrisComposition`.

Sorry-free.
-/

namespace SkewGluing

/-- A proper legal chart of `F` whose inner is a row or a column: a *proper line inner at `F`*. -/
def HasProperLineChart (F : Diagram) : Prop :=
  ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ LineInner χ.ω

namespace Chart

/-- **The case analysis of the proof of `thm:gluing`.**  Let `χ₁`, `χ₂` be proper legal charts of
one diagram `F` with no proper line inner at `F`.  Then some proper legal chart `ψ` of `F` has a
fiber containing both fibers `𝓕(χ₁.ω, s_{χ₁.D})` and `𝓕(χ₂.ω, s_{χ₂.D})`. -/
theorem IsProperLegal.exists_covering_chart (hOH : OlsonHarrisComposition) {F : Diagram}
    (hno : ¬ HasProperLineChart F) {χ₁ χ₂ : Chart} (h₁ : χ₁.IsProperLegal)
    (h₂ : χ₂.IsProperLegal) (c₁ : χ₁.IsChartOf F) (c₂ : χ₂.IsChartOf F) :
    ∃ ψ : Chart, ψ.IsProperLegal ∧ ψ.IsChartOf F ∧
      fiberClass cellSchur χ₁.ω (cellSchur χ₁.D) ⊆ fiberClass cellSchur ψ.ω (cellSchur ψ.D) ∧
      fiberClass cellSchur χ₂.ω (cellSchur χ₂.D) ⊆ fiberClass cellSchur ψ.ω (cellSchur ψ.D) := by
  by_cases hd₁ : χ₁.period ∣ χ₂.period
  · exact ⟨χ₁, h₁, c₁, subset_rfl, h₁.fiber_subset_of_dvd hOH h₂ c₁ c₂ hd₁⟩
  by_cases hd₂ : χ₂.period ∣ χ₁.period
  · exact ⟨χ₂, h₂, c₂, h₂.fiber_subset_of_dvd hOH h₁ c₂ c₁ hd₂, subset_rfl⟩
  have hn₁ : ¬ χ₁.period.toNat ∣ χ₂.period.toNat := fun h => hd₁ (by
    rw [← h₁.period_toNat, ← h₂.period_toNat]; exact_mod_cast h)
  have hn₂ : ¬ χ₂.period.toNat ∣ χ₁.period.toNat := fun h => hd₂ (by
    rw [← h₁.period_toNat, ← h₂.period_toNat]; exact_mod_cast h)
  have hp₁ : 0 < χ₁.period.toNat := by
    have e := h₁.period_toNat
    have hpos : 0 < χ₁.period := h₁.2.2.2.period_pos
    omega
  have hg : 1 < Nat.gcd χ₁.period.toNat χ₂.period.toNat := by
    have hg0 : 0 < Nat.gcd χ₁.period.toNat χ₂.period.toNat := Nat.gcd_pos_of_pos_left _ hp₁
    by_contra hle
    have hcop : Nat.gcd χ₁.period.toNat χ₂.period.toNat = 1 := by omega
    have hcop' : Int.gcd χ₁.period χ₂.period = 1 := by
      have p₁ : 0 < χ₁.period := h₁.2.2.2.period_pos
      have p₂ : 0 < χ₂.period := h₂.2.2.2.period_pos
      have e₁ : χ₁.period.natAbs = χ₁.period.toNat := by omega
      have e₂ : χ₂.period.natAbs = χ₂.period.toNat := by omega
      change Nat.gcd χ₁.period.natAbs χ₂.period.natAbs = 1
      rw [e₁, e₂]
      exact hcop
    obtain ⟨-, -, hline⟩ := IsProperLegal.coprime_periods_line h₁ h₂ c₁ c₂ hcop'
    exact hno ⟨χ₁, h₁, c₁, hline.imp (fun h => h.1) (fun h => h.1)⟩
  obtain ⟨ψ, hψ, cψ, hper⟩ := IsProperLegal.exists_gcd_root h₁ h₂ c₁ c₂ hn₁ hn₂ hg
  refine ⟨ψ, hψ, cψ, hψ.fiber_subset_of_dvd hOH h₁ cψ c₁ ?_,
    hψ.fiber_subset_of_dvd hOH h₂ cψ c₂ ?_⟩
  · rw [hper, ← h₁.period_toNat]
    exact_mod_cast Nat.gcd_dvd_left _ _
  · rw [hper, ← h₂.period_toNat]
    exact_mod_cast Nat.gcd_dvd_right _ _

end Chart

/-- **`thm:gluing`, fork form.**  Let `X`, `Y`, `Z` be skew diagrams of one Schur function such that
`X, Y` and `Y, Z` each have a common final factor, and `X`, `Z` are not translates of one another.
Then `X, Z` have a common final factor.

The Olson-Harris composition theorem is the hypothesis `hOH`. -/
theorem gluing_fork (hOH : OlsonHarrisComposition) {X Y Z : Diagram} (hX : IsSkew X)
    (hZ : IsSkew Z) (hXY : cellSchur X = cellSchur Y) (hZY : cellSchur Z = cellSchur Y)
    (hxy : HasCommonFinalFactor cellSchur X Y) (hyz : HasCommonFinalFactor cellSchur Y Z)
    (hne : ¬ ∃ t, Z = translate t X) : HasCommonFinalFactor cellSchur X Z := by
  by_cases hline : HasProperLineChart Y
  · obtain ⟨χ, hχ, hY, hl⟩ := hline
    exact HasCommonFinalFactor.of_line_inner hχ hl hY hX hZ hXY hZY hne
  obtain ⟨χ₁, h₁, c₁, hXf⟩ := hxy.exists_chart_fiber
  obtain ⟨χ₂, h₂, c₂, hZf⟩ := hyz.symm.exists_chart_fiber
  obtain ⟨ψ, hψ, -, hs₁, hs₂⟩ :=
    Chart.IsProperLegal.exists_covering_chart hOH hline h₁ h₂ c₁ c₂
  exact fiberClass_hasCommonFinalFactor hψ.2.2.2 hψ.2.2.1 (hs₁ hXf) (hs₂ hZf) hne

/-- **`thm:gluing`.**  Every connected component of every common-factor graph is a clique: for
every Schur function `P`, the components of the graph of `def:gluing-graph`, whose vertices are the
translation classes of skew diagrams `F` with `s_F = P`, are cliques.  Equivalently
(`componentsAreCliques_iff_incident_edges`), two incident edges force the third.

The Olson-Harris composition theorem is the hypothesis `hOH`. -/
theorem gluing_componentsAreCliques (hOH : OlsonHarrisComposition) (P : Lambda) :
    ComponentsAreCliques (classGraph (skewClass P)) := by
  rw [componentsAreCliques_iff_incident_edges]
  intro a b c hac hab hbc
  obtain ⟨x, rfl⟩ := exists_classOf a
  obtain ⟨y, rfl⟩ := exists_classOf b
  obtain ⟨z, rfl⟩ := exists_classOf c
  rw [classGraph_adj_iff] at hab hbc ⊢
  refine gluing_fork hOH x.2.1 z.2.1 (x.2.2.trans y.2.2.symm) (z.2.2.trans y.2.2.symm) hab hbc ?_
  rintro ⟨t, ht⟩
  exact hac (classOf_eq_iff.mpr ⟨t, ht⟩)

/-- **`thm:gluing`** as the proposition `GluingStatement`: every connected component of the
common-factor graph of every Schur class is a clique.  The Olson-Harris composition theorem
(`hOH`) is genuinely needed, by `prop:gluing-divisible`. -/
theorem gluingStatement (hOH : OlsonHarrisComposition) : GluingStatement :=
  gluing_componentsAreCliques hOH

/-- **`thm:gluing`, in the graph form used downstream.**  The hypothesis `hgluing` of
`rotation_components` and `connectedClass_componentsAreCliques`, for every Schur function. -/
theorem gluing_forall (hOH : OlsonHarrisComposition) :
    ∀ P : Lambda, ComponentsAreCliques (classGraph (skewClass P)) :=
  gluing_componentsAreCliques hOH

/-- **`lem:rotation-components`, with `thm:gluing` discharged.**  On the connected class of `P`,
every component of `Γ⁺(P)` and of `Γ̄(P)` is a clique, and rotation augmentation changes no rooted
component. -/
theorem rotation_components_unconditional (hOH : OlsonHarrisComposition) (P : Lambda) :
    ComponentsAreCliques (connectedRotationData P).augmented ∧
    ComponentsAreCliques (connectedRotationData P).quotientGraph ∧
    ∀ a ∈ (connectedRotationData P).rooted,
      ((connectedRotationData P).augmented.connectedComponentMk a).supp =
        ((connectedRotationData P).graph.connectedComponentMk a).supp :=
  rotation_components (gluing_forall hOH) P

/-- **`thm:gluing`, on the connected class.**  The components of `Γ(P)` are cliques. -/
theorem gluing_connectedClass_componentsAreCliques (hOH : OlsonHarrisComposition) (P : Lambda) :
    ComponentsAreCliques (classGraph (connectedClass P)) :=
  connectedClass_componentsAreCliques (gluing_forall hOH) P

end SkewGluing
