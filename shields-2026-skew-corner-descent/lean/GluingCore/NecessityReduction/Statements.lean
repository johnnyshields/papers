/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/NecessityReduction/Statements.lean`. -/
import GluingCore.CommonFactorGraph
import GluingCore.OlsonHarris.Deductions
import GluingCore.Score
import GluingCore.Local

/-!
# Statements consumed by the reduction of composition necessity

Formalizes `shields-2026-skew-factor-gluing.tex`, «Source-minimal fibers» (`eq:chart-score`,
`thm:source-minimal-domination`, `eq:component-key`, `prop:component-key`) and «Reduction of
composition necessity» (`sec:necessity-reduction`).

This file fixes, on the concrete tree, the objects the reduction speaks about:

* `GluingStatement`: `thm:gluing`, that every component of the common-factor graph of every
  Schur class is a clique.
* `Chart.score`, `Chart.IsSourceMinimal`, `Chart.IsProperLegal.score_eq`: the score
  `(w, N_E)` of `eq:chart-score`, equal to `(N_F mod p, p + N_F mod p)`, and source-minimal
  charts (`exists_isSourceMinimal`: a rooted diagram has one).
* `KeyStep`, `Key`, `Chart.key`: the key `[(ω, s_D)]` of `eq:component-key`, with its
  identifications by translation, transported rotation and the legal ordinary gauge with `ι`.
* `SourceMinimalDomination`: `thm:source-minimal-domination`, on the concrete graph.
* `ComponentKeyClassifies`: `prop:component-key`, on the concrete graph.
* `RotationMates`, `TerminalRigidity`, `RootedKeyInvariance`: (TR) and (RI) on a connected
  Schur class.

`GluingStatement`, `SourceMinimalDomination` and `ComponentKeyClassifies` are statements proved
in the sections named above (`gluing`, `source_minimal_domination`, `component_key` of
`GluingCore.MainTheorems`); here they are `Prop`s, taken as hypotheses by the theorems of the rest
of the reduction.

Sorry-free.
-/

namespace GluingCore

/-! ### `thm:gluing` -/

/-- `thm:gluing`: every connected component of the common-factor graph of every Schur class
(`def:gluing-graph`) is a clique. -/
def GluingStatement : Prop :=
  ∀ P : Lambda, ComponentsAreCliques (classGraph (skewClass P))

/-! ### The chart score -/

namespace Chart

/-- `eq:chart-score`: the score `(w, N_E)` of a chart, the width of its mark and the span of its
inner, in the lexicographic order. -/
def score (χ : Chart) : ℕ ×ₗ ℕ := toLex (χ.ω.width, span χ.ω.E)

/-- A chart `χ` of `F` is *source-minimal* if it is a proper legal chart of `F` whose score is
lexicographically least among the proper legal charts of `F`.  This is the minimum of the
minimal-factorization convention, taken at the diagram `F`; it does not assert that the inner is
chartless. -/
def IsSourceMinimal (χ : Chart) (F : Diagram) : Prop :=
  χ.IsProperLegal ∧ χ.IsChartOf F ∧
    ∀ χ' : Chart, χ'.IsProperLegal → χ'.IsChartOf F → χ.score ≤ χ'.score

theorem isChartOf_translate_iff (χ : Chart) (F : Diagram) (t : ℤ × ℤ) :
    χ.IsChartOf (translate t F) ↔ χ.IsChartOf F := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨-t + s, ?_⟩
    rw [← translate_translate, ← hs, translate_translate, neg_add_cancel, translate_zero]
  · rintro ⟨s, hs⟩
    exact ⟨t + s, by rw [hs, translate_translate]⟩

/-- Being a source-minimal chart is invariant under translating the diagram. -/
theorem isSourceMinimal_translate_iff (χ : Chart) (F : Diagram) (t : ℤ × ℤ) :
    χ.IsSourceMinimal (translate t F) ↔ χ.IsSourceMinimal F := by
  simp only [IsSourceMinimal, isChartOf_translate_iff]

/-- **`eq:chart-score`.**  The score of a proper legal chart of `F`, of period `p` and width
`w`, is `(w, N_E) = (N_F mod p, p + N_F mod p)`; it depends on the period alone. -/
theorem IsProperLegal.score_eq {χ : Chart} (h : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) :
    χ.score = GluingCore.score (span F) χ.period.toNat := by
  obtain ⟨hD, -, -, hω⟩ := h
  obtain ⟨t, rfl⟩ := hF
  have hspan := MarkedInner.span_compose hD hω
  have hE := hω.1.span_eq
  have hwq := hω.2.2.1.2
  have hq := hω.period_pos
  have hp : ((χ.period.toNat : ℕ) : ℤ) = χ.ω.period := by
    have e : χ.period = χ.ω.period := rfl
    rw [e, Int.toNat_of_nonneg hq.le]
  have hN : span (translate t χ.parent) = span χ.D * χ.period.toNat + χ.ω.width := by
    rw [span_translate]
    have : (span χ.parent : ℤ) = span χ.D * χ.period.toNat + χ.ω.width := by
      rw [hp]; exact hspan
    exact_mod_cast this
  have hlt : χ.ω.width < χ.period.toNat := by
    have : (χ.ω.width : ℤ) < χ.period.toNat := by rw [hp]; exact hwq
    exact_mod_cast this
  have hw := (width_eq_mod_of_span hlt hN).1
  have hEq : span χ.ω.E = χ.period.toNat + χ.ω.width := by
    have : (span χ.ω.E : ℤ) = χ.period.toNat + χ.ω.width := by rw [hp]; exact hE
    exact_mod_cast this
  unfold score GluingCore.score
  rw [← hw, ← hEq]

/-- Every proper legal chart of `F` has a score; a source-minimal chart exists as soon as one
proper legal chart does. -/
theorem exists_isSourceMinimal {F : Diagram}
    (h : ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F) :
    ∃ χ : Chart, χ.IsSourceMinimal F := by
  obtain ⟨χ₀, h₀⟩ := h
  obtain ⟨χ, ⟨hχ1, hχ2⟩, hmin⟩ := (InvImage.wf (fun χ : Chart => χ.score)
    wellFounded_lt).has_min {χ : Chart | χ.IsProperLegal ∧ χ.IsChartOf F} ⟨χ₀, h₀⟩
  exact ⟨χ, hχ1, hχ2, fun χ' h1 h2 => not_lt.mp fun hlt => hmin χ' ⟨h1, h2⟩ hlt⟩

end Chart

/-! ### The component key -/

/-- The generating identifications of `eq:component-key` on pairs `(ω, Q)`, a marked inner and an
outer function: translation of `ω`; the transported rotation `(ω, Q) ∼ (ω*, Q)`; and the legal
ordinary gauge `(ω_a, Q) ∼ (ω_b, ι(Q))` of `eq:gluing-gauge`, for legal marks `ω_a`, `ω_b` on the
same diagram `E`, of cases (a) and (b), with `v_a = v_b + e`.

The empty vertical reading of the paper is not a separate mark in this development: every empty
mark is the horizontal one (`MarkedInner.IsEmptyMark`), so the conversion of vertical empty
readings to the horizontal convention is already built into the charts. -/
inductive KeyStep : MarkedInner × Lambda → MarkedInner × Lambda → Prop
  | translate (t : ℤ × ℤ) (ω : MarkedInner) (Q : Lambda) :
      KeyStep (ω, Q) (ω.translateBy t, Q)
  | rotate (ω : MarkedInner) (Q : Lambda) : KeyStep (ω, Q) (ω.rotate, Q)
  | gauge {ωa ωb : MarkedInner} (Q : Lambda) (hE : ωa.E = ωb.E) (ha : ωa.case = .a)
      (hb : ωb.case = .b) (hv : ωa.v = ωb.v + eCell) (hla : ωa.IsLegal) (hlb : ωb.IsLegal) :
      KeyStep (ωa, Q) (ωb, schurInvolution Q)

/-- The keys: pairs `(ω, Q)` modulo the equivalence relation generated by `KeyStep`. -/
def Key : Type := Quot KeyStep

/-- The key `[(ω, s_D)]` of a chart `(D, ω)`, `eq:component-key`. -/
noncomputable def Chart.key (χ : Chart) : Key := Quot.mk KeyStep (χ.ω, cellSchur χ.D)

/-! ### `thm:source-minimal-domination` and `prop:component-key` -/

/-- `thm:source-minimal-domination`, on the concrete graph.  For every prescribed source-minimal
chart `χ` of a connected diagram `F` with function `P`:

* every proper-chart fiber through `F` is contained in `𝓕_χ = 𝓕(ω, s_D)`: for every proper
  legal chart `χ'` of `F`, `𝓕(ω', s_{D'}) ⊆ 𝓕_χ`, all fibers read up to translation
  (`fiberClass`);
* the component of `F` in `Γ(P)` and in `Γ⁺(P)` is `𝓕_χ`: a connected diagram `G` with function
  `P` lies in the component exactly when it lies in `𝓕_χ` (the inclusion `𝓕_χ ⊆ [F]` is
  `OlsonHarrisComposition.fiberClass_subset_connectedClass`).

The vertices of `Γ(P)` are translation classes. -/
def SourceMinimalDomination : Prop :=
  ∀ (P : Lambda) (F : {F : Diagram // connectedClass P F}) (χ : Chart),
    χ.IsSourceMinimal F.1 →
    (∀ χ' : Chart, χ'.IsProperLegal → χ'.IsChartOf F.1 →
      fiberClass cellSchur χ'.ω (cellSchur χ'.D) ⊆ fiberClass cellSchur χ.ω (cellSchur χ.D)) ∧
    ∀ G : {F : Diagram // connectedClass P F},
      ((classGraph (connectedClass P)).Reachable (classOf F) (classOf G) ↔
        G.1 ∈ fiberClass cellSchur χ.ω (cellSchur χ.D)) ∧
      ((connectedRotationData P).augmented.Reachable (classOf F) (classOf G) ↔
        G.1 ∈ fiberClass cellSchur χ.ω (cellSchur χ.D))

/-- `prop:component-key`, on the concrete graph.  The key is independent of the source-minimal
chart chosen at a connected diagram; and for rooted diagrams `F`, `H` in one connected Schur
class, `K(F) = K(H)` exactly when `F` and `H` lie in the same component of `Γ(P)`.  (A rooted
diagram has a source-minimal chart, `Chart.exists_isSourceMinimal`, so `K` is defined on it.) -/
def ComponentKeyClassifies : Prop :=
  (∀ F : Diagram, IsConnectedSkew F → ∀ χ χ' : Chart,
      χ.IsSourceMinimal F → χ'.IsSourceMinimal F → χ.key = χ'.key) ∧
  ∀ (P : Lambda) (F H : {F : Diagram // connectedClass P F}),
    HasProperChart F.1 → HasProperChart H.1 →
      ((∃ χ χ' : Chart, χ.IsSourceMinimal F.1 ∧ χ'.IsSourceMinimal H.1 ∧ χ.key = χ'.key) ↔
        (classGraph (connectedClass P)).Reachable (classOf F) (classOf H))

/-! ### (TR) and (RI) -/

/-- Two diagrams are rotation mates: they are equal up to translation, or one is a translate of
the rotation of the other. -/
def RotationMates (F G : Diagram) : Prop :=
  (∃ t, G = translate t F) ∨ ∃ t, G = translate t (rotate F)

/-- **Terminal rigidity (TR)** on the connected Schur class of `P`: if a member `F` is chartless,
then the class is `{F, F*}`. -/
def TerminalRigidity (P : Lambda) : Prop :=
  ∀ F G : Diagram, connectedClass P F → connectedClass P G → ¬ HasProperChart F →
    RotationMates F G

/-- **Rooted-key invariance (RI)** on the connected Schur class of `P`: any two rooted members
have equal keys, whatever their source-minimal charts. -/
def RootedKeyInvariance (P : Lambda) : Prop :=
  ∀ F H : Diagram, connectedClass P F → connectedClass P H → HasProperChart F →
    HasProperChart H → ∀ χ χ' : Chart, χ.IsSourceMinimal F → χ'.IsSourceMinimal H →
      χ.key = χ'.key

end GluingCore
