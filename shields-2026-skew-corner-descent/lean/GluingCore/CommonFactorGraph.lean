/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/CommonFactorGraph.lean`. -/
import GluingCore.EqualPeriods
import GluingCore.GraphTheory
import GluingCore.Invariance
import GluingCore.CellSchur

/-!
# The concrete common-factor graph

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`def:gluing-graph`) and «Source-minimal fibers» (`sec:minimal-fibers`,
`lem:rotation-components`).

* `HasCommonFinalFactor.symm`, `HasCommonFinalFactor.translate_left`,
  `HasCommonFinalFactor.translate_right`: the common-final-factor relation is symmetric and
  invariant under translating either diagram.
* `TranslationClass S`: translation classes of the diagrams satisfying `S`; `classGraph S`: the
  graph with an edge between two distinct classes exactly when their representatives have a
  common final factor (`classGraph_adj_mk_iff`).  `skewClass P` and `connectedClass P` give the
  graph of `def:gluing-graph` (all skew diagrams with function `P`) and the graph `Γ(P)` on the
  connected class of `sec:minimal-fibers`.
* `HasProperChart`, `classRooted`: rooted vertices; `classRotate`: the rotation involution on
  classes.
* `classRotationData`: the `RotationData` of `GraphTheory`, with `adj_rot_of_rooted` and
  `isolated_of_not_rooted` discharged (`HasProperChart.rotate`, `Chart.rotate`).
  `RotationData.augmented` is `Γ⁺` and `RotationData.quotientGraph` is `Γ̄`.
* `Chart.IsProperLegal.four_le_span_parent`: a proper chart has span at least four.
* `hook_class_graph`, `hook_quotient_subsingleton`: the hook example at the head of
  `sec:minimal-fibers` (two isolated vertices, one vertex after the rotation quotient).
* `connectedClass_componentsAreCliques`, `rotation_components`: `lem:rotation-components`
  for the concrete graph, taking `thm:gluing` as the hypothesis `hgluing`.

Sorry-free.
-/

namespace GluingCore

/-! ### The common final factor is symmetric and translation invariant -/

namespace MarkedInner

theorem EquivTranslate.symm {a b : MarkedInner} (h : a.EquivTranslate b) : b.EquivTranslate a := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨-t, (MarkedInner.translate_neg_translate t a).symm⟩

theorem EquivTranslate.rotate_symm {a b : MarkedInner} (h : a.rotate.EquivTranslate b) :
    b.rotate.EquivTranslate a := by
  obtain ⟨t, rfl⟩ := h
  have : (a.rotate.translate t).rotate.translate t = a := by
    rw [MarkedInner.rotate_translate, MarkedInner.rotate_rotate, MarkedInner.translate_translate,
      add_neg_cancel, MarkedInner.translate_zero]
  exact ⟨t, this.symm⟩

end MarkedInner

namespace HasCommonFinalFactor

variable {R : Type*} {s : Diagram → R} {F₁ F₂ : Diagram}

/-- The common final factor relation is symmetric. -/
theorem symm (h : HasCommonFinalFactor s F₁ F₂) : HasCommonFinalFactor s F₂ F₁ := by
  obtain ⟨hne, χ₁, χ₂, p₁, p₂, c₁, c₂, hω, hs⟩ := h
  refine ⟨fun ⟨t, ht⟩ => hne ⟨-t, ?_⟩, χ₂, χ₁, p₂, p₁, c₂, c₁, ?_, hs.symm⟩
  · rw [ht, translate_translate, neg_add_cancel, translate_zero]
  · rcases hω with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.rotate_symm

/-- The common final factor relation is invariant under translating the first diagram. -/
theorem translate_left (u : ℤ × ℤ) (h : HasCommonFinalFactor s F₁ F₂) :
    HasCommonFinalFactor s (translate u F₁) F₂ := by
  obtain ⟨hne, χ₁, χ₂, p₁, p₂, ⟨t, ht⟩, c₂, hω, hs⟩ := h
  refine ⟨fun ⟨t', ht'⟩ => hne ⟨t' + u, ?_⟩, χ₁, χ₂, p₁, p₂, ⟨u + t, ?_⟩, c₂, hω, hs⟩
  · rw [ht', translate_translate]
  · rw [ht, translate_translate]

/-- The common final factor relation is invariant under translating the second diagram. -/
theorem translate_right (u : ℤ × ℤ) (h : HasCommonFinalFactor s F₁ F₂) :
    HasCommonFinalFactor s F₁ (translate u F₂) :=
  (translate_left u h.symm).symm

/-- A diagram with a common final factor with another has a proper chart. -/
theorem exists_chart_left (h : HasCommonFinalFactor s F₁ F₂) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F₁ := by
  obtain ⟨-, χ₁, -, p₁, -, c₁, -⟩ := h
  exact ⟨χ₁, p₁, c₁⟩

end HasCommonFinalFactor

/-! ### Charts, rotation, and the span of a proper chart -/

namespace Chart

/-- The rotated chart `(D*, ω*)`. -/
def rotate (χ : Chart) : Chart := ⟨GluingCore.rotate χ.D, χ.ω.rotate⟩

theorem card_rotate (D : Diagram) : (GluingCore.rotate D).card = D.card := by
  rw [GluingCore.rotate, Finset.card_image_of_injective _ neg_injective]

theorem IsProperLegal.rotate {χ : Chart} (h : χ.IsProperLegal) : χ.rotate.IsProperLegal := by
  obtain ⟨hD, hc, hE, hω⟩ := h
  refine ⟨isConnectedSkew_rotate hD, ?_, ?_, MarkedInner.isLegal_rotate hω⟩
  · change 2 ≤ (GluingCore.rotate χ.D).card
    rw [card_rotate]; exact hc
  · change 2 ≤ (GluingCore.rotate χ.ω.E).card
    rw [card_rotate]; exact hE

/-- Rotating a chart rotates its parent. -/
theorem parent_rotate {χ : Chart} (h : χ.IsProperLegal) :
    χ.rotate.parent = GluingCore.rotate χ.parent :=
  MarkedInner.rotate_compose h.1.2.1 χ.ω

end Chart

/-- A connected skew diagram with at least two cells has span at least two. -/
theorem two_le_span_of_two_le_card {D : Diagram} (hD : IsConnectedSkew D) (hc : 2 ≤ D.card) :
    2 ≤ span D := by
  by_contra hlt
  have hne : D.Nonempty := hD.2.1
  have hsp : (contents D).card ≤ 1 := by unfold span at hlt; omega
  rw [Finset.card_le_one] at hsp
  have hmin := MarkedInner.diagLo_eq_diagHi_minContent hD
  have hmem := minContent_mem hne
  have hcard : D.card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, j⟩ ha ⟨i', j'⟩ hb
    have hka : content (i, j) = minContent D :=
      hsp _ (content_mem_contents ha) _ hmem
    have hkb : content (i', j') = minContent D :=
      hsp _ (content_mem_contents hb) _ hmem
    have h1 := diagLo_le (k := minContent D) ha hka
    have h2 := le_diagHi (k := minContent D) ha hka
    have h3 := diagLo_le (k := minContent D) hb hkb
    have h4 := le_diagHi (k := minContent D) hb hkb
    simp only [content] at hka hkb
    have : i = i' := by omega
    subst this
    have : j = j' := by omega
    rw [this]
  omega

/-- **A proper chart has span at least four** (`sec:minimal-fibers`: a proper chart has span
`r q + w ≥ 4`): `N_F = N_D q + w` with `N_D ≥ 2` and `q ≥ 2`. -/
theorem Chart.IsProperLegal.four_le_span_parent {χ : Chart} (h : χ.IsProperLegal) :
    4 ≤ span χ.parent := by
  obtain ⟨hD, hc, hE, hω⟩ := h
  have hspan := MarkedInner.span_compose hD hω
  have hE2 := two_le_span_of_two_le_card hω.1.1 hE
  have hD2 := two_le_span_of_two_le_card hD hc
  have hEq := hω.1.span_eq
  have hwq := hω.2.2.1.2
  have hq := hω.period_pos
  change 4 ≤ span (χ.ω.compose χ.D)
  have hq2 : 2 ≤ χ.ω.period := by omega
  have : (4 : ℤ) ≤ span (χ.ω.compose χ.D) := by
    rw [hspan]
    have h1 : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hD2
    nlinarith [(by positivity : (0 : ℤ) ≤ χ.ω.width)]
  exact_mod_cast this

/-! ### Translation classes and the graph -/

/-- The diagrams satisfying `S`, with two of them related when one is a translate of the other. -/
def translationSetoid (S : Diagram → Prop) : Setoid {F : Diagram // S F} where
  r F G := ∃ t, G.1 = translate t F.1
  iseqv :=
    { refl := fun F => ⟨0, translate_zero.symm⟩
      symm := by
        rintro F G ⟨t, h⟩
        exact ⟨-t, by rw [h, translate_translate, neg_add_cancel, translate_zero]⟩
      trans := by
        rintro F G H ⟨t, h⟩ ⟨u, h'⟩
        exact ⟨u + t, by rw [h', h, translate_translate]⟩ }

/-- The translation classes of the diagrams satisfying `S`: the vertices of the common-factor
graph. -/
abbrev TranslationClass (S : Diagram → Prop) : Type := Quotient (translationSetoid S)

/-- The translation class of a diagram satisfying `S`. -/
def classOf {S : Diagram → Prop} (F : {F : Diagram // S F}) : TranslationClass S :=
  Quotient.mk (translationSetoid S) F

theorem classOf_eq_iff {S : Diagram → Prop} {F G : {F : Diagram // S F}} :
    classOf F = classOf G ↔ ∃ t, G.1 = translate t F.1 :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **The common-factor graph of `def:gluing-graph`** on the translation classes of the diagrams
satisfying `S`: two distinct classes are adjacent exactly when some representatives have a common
final factor (`HasCommonFinalFactor cellSchur`).  `skewClass P` gives the graph of
`def:gluing-graph`; `connectedClass P` gives `Γ(P)` of `sec:minimal-fibers`. -/
def classGraph (S : Diagram → Prop) : SimpleGraph (TranslationClass S) where
  Adj a b := a ≠ b ∧ ∃ x y : {F : Diagram // S F}, classOf x = a ∧ classOf y = b ∧
    HasCommonFinalFactor cellSchur x.1 y.1
  symm := ⟨by
    rintro a b ⟨hab, x, y, hx, hy, h⟩
    exact ⟨hab.symm, y, x, hy, hx, h.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Adjacency in the common-factor graph is the common final factor of any representatives:
the relation is invariant under translation. -/
theorem classGraph_adj_iff {S : Diagram → Prop} {x y : {F : Diagram // S F}} :
    (classGraph S).Adj (classOf x) (classOf y) ↔ HasCommonFinalFactor cellSchur x.1 y.1 := by
  constructor
  · rintro ⟨-, x', y', hx, hy, h⟩
    obtain ⟨t, ht⟩ := classOf_eq_iff.mp hx
    obtain ⟨u, hu⟩ := classOf_eq_iff.mp hy
    rw [ht, hu]
    exact (h.translate_left t).translate_right u
  · intro h
    refine ⟨fun e => h.1 (classOf_eq_iff.mp e), x, y, rfl, rfl, h⟩

/-- Every vertex of the common-factor graph is a class of a diagram. -/
theorem exists_classOf {S : Diagram → Prop} (a : TranslationClass S) :
    ∃ x : {F : Diagram // S F}, classOf x = a :=
  Quotient.exists_rep a

/-- The skew diagrams with function `P`: the vertex set of the graph of `def:gluing-graph`. -/
def skewClass (P : Lambda) (F : Diagram) : Prop := IsSkew F ∧ cellSchur F = P

/-- The connected skew diagrams with function `P`: the vertex set of `Γ(P)` in
`sec:minimal-fibers`. -/
def connectedClass (P : Lambda) (F : Diagram) : Prop := IsConnectedSkew F ∧ cellSchur F = P

theorem skewClass_rotate {P : Lambda} {F : Diagram} (h : skewClass P F) :
    skewClass P (rotate F) :=
  ⟨isSkew_rotate h.1, (cellSchur_rotate F).trans h.2⟩

theorem connectedClass_rotate {P : Lambda} {F : Diagram} (h : connectedClass P F) :
    connectedClass P (rotate F) :=
  ⟨isConnectedSkew_rotate h.1, (cellSchur_rotate F).trans h.2⟩

/-! ### Rooted and chartless vertices, rotation -/

/-- A diagram is *rooted* if it has a proper chart (up to translation), *chartless* otherwise. -/
def HasProperChart (F : Diagram) : Prop := ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F

theorem hasProperChart_translate (u : ℤ × ℤ) {F : Diagram} (h : HasProperChart F) :
    HasProperChart (translate u F) := by
  obtain ⟨χ, p, t, ht⟩ := h
  exact ⟨χ, p, u + t, by rw [ht, translate_translate]⟩

theorem hasProperChart_translate_iff (u : ℤ × ℤ) {F : Diagram} :
    HasProperChart (translate u F) ↔ HasProperChart F := by
  refine ⟨fun h => ?_, hasProperChart_translate u⟩
  have := hasProperChart_translate (-u) h
  rwa [translate_translate, neg_add_cancel, translate_zero] at this

/-- A rooted diagram has a rooted rotation. -/
theorem HasProperChart.rotate {F : Diagram} (h : HasProperChart F) :
    HasProperChart (GluingCore.rotate F) := by
  obtain ⟨χ, p, t, ht⟩ := h
  refine ⟨χ.rotate, p.rotate, -t, ?_⟩
  rw [ht, rotate_translate_eq, Chart.parent_rotate p]

/-- The rooted vertices of the common-factor graph: the classes of diagrams with a proper
chart. -/
def classRooted (S : Diagram → Prop) : Set (TranslationClass S) :=
  {c | ∃ x : {F : Diagram // S F}, classOf x = c ∧ HasProperChart x.1}

theorem classOf_mem_classRooted_iff {S : Diagram → Prop} {x : {F : Diagram // S F}} :
    classOf x ∈ classRooted S ↔ HasProperChart x.1 := by
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨t, ht⟩ := classOf_eq_iff.mp hy
    rw [ht]
    exact hasProperChart_translate t h
  · exact fun h => ⟨x, rfl, h⟩

/-- The rotation `D ↦ D*` on translation classes, for a class closed under rotation. -/
def classRotate {S : Diagram → Prop} (hS : ∀ F, S F → S (rotate F)) :
    TranslationClass S → TranslationClass S :=
  Quotient.map (fun F => ⟨rotate F.1, hS _ F.2⟩) (by
    rintro F G ⟨t, h⟩
    exact ⟨-t, by simp only [h, rotate_translate_eq]⟩)

theorem classRotate_classOf {S : Diagram → Prop} (hS : ∀ F, S F → S (rotate F))
    (x : {F : Diagram // S F}) : classRotate hS (classOf x) = classOf ⟨rotate x.1, hS _ x.2⟩ :=
  rfl

/-- **`rot_rot`, `adj_rot_of_rooted` and `isolated_of_not_rooted` for the concrete graph.**  The
rotation data of the common-factor graph on a class closed under rotation: a rooted class is
adjacent to its rotation when they differ (`F = D ∘_ω E` gives `F* = D* ∘_{ω*} E*`, with
`s_{D*} = s_D`), and a class with no proper chart has no edge. -/
def classRotationData (S : Diagram → Prop) (hS : ∀ F, S F → S (rotate F)) :
    RotationData (TranslationClass S) where
  graph := classGraph S
  rot := classRotate hS
  rot_rot := by
    intro a
    obtain ⟨x, rfl⟩ := exists_classOf a
    rw [classRotate_classOf, classRotate_classOf]
    exact classOf_eq_iff.mpr ⟨0, by simp [rotate_rotate, translate_zero]⟩
  rooted := classRooted S
  adj_rot_of_rooted := by
    intro a ha hne
    obtain ⟨x, rfl⟩ := exists_classOf a
    rw [classRotate_classOf] at hne ⊢
    rw [classOf_mem_classRooted_iff] at ha
    obtain ⟨χ, p, t, ht⟩ := ha
    refine classGraph_adj_iff.mpr ⟨fun ⟨u, hu⟩ => hne (classOf_eq_iff.mpr ⟨u, hu⟩).symm,
      χ, χ.rotate, p, p.rotate, ⟨t, ht⟩, ⟨-t, ?_⟩, Or.inr ⟨0, ?_⟩, ?_⟩
    · change rotate x.1 = translate (-t) χ.rotate.parent
      rw [ht, rotate_translate_eq, Chart.parent_rotate p]
    · exact (MarkedInner.translate_zero χ.ω.rotate).symm
    · exact (cellSchur_rotate _).symm
  isolated_of_not_rooted := by
    intro a ha b hab
    obtain ⟨x, rfl⟩ := exists_classOf a
    obtain ⟨y, rfl⟩ := exists_classOf b
    exact ha (classOf_mem_classRooted_iff.mpr (classGraph_adj_iff.mp hab).exists_chart_left)

/-! ### The concrete rotation data -/

/-- The rotation data of the graph of `def:gluing-graph` for the class of skew diagrams with
function `P`. -/
def skewRotationData (P : Lambda) : RotationData (TranslationClass (skewClass P)) :=
  classRotationData (skewClass P) fun _ h => skewClass_rotate h

/-- The rotation data of `Γ(P)` on the connected class of `P`, from which `Γ⁺(P)` is
`(connectedRotationData P).augmented` and `Γ̄(P)` is `(connectedRotationData P).quotientGraph`. -/
def connectedRotationData (P : Lambda) : RotationData (TranslationClass (connectedClass P)) :=
  classRotationData (connectedClass P) fun _ h => connectedClass_rotate h

/-! ### The hook example of `sec:minimal-fibers` -/

section Hook

open MvPolynomial

/-- The function `h₁ h₂ - h₃` of the two hooks. -/
noncomputable def hookSchur : Lambda := X 1 * X 2 - X 3

theorem isConnectedSkew_hook : IsConnectedSkew (skewOf [2, 1] []) := by decide +kernel

theorem isConnectedSkew_hookRotated : IsConnectedSkew (skewOf [2, 2] [1]) := by decide +kernel

theorem span_hook : span (skewOf [2, 1] []) = 3 := by decide +kernel

theorem span_hookRotated : span (skewOf [2, 2] [1]) = 3 := by decide +kernel

/-- Every diagram in the class of `h₁ h₂ - h₃` has span three. -/
theorem span_eq_three_of_connectedClass_hook {F : Diagram} (h : connectedClass hookSchur F) :
    span F = 3 := by
  rcases (cellSchur_eq_hook_iff h.1.1).mp h.2 with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [span_translate, span_hook]
  · rw [span_translate, span_hookRotated]

/-- No diagram of the class of the hook has a proper chart: a proper chart has span at least
four, the hooks have span three. -/
theorem not_hasProperChart_of_connectedClass_hook {F : Diagram}
    (h : connectedClass hookSchur F) : ¬ HasProperChart F := by
  rintro ⟨χ, p, t, ht⟩
  have h4 := p.four_le_span_parent
  have h3 := span_eq_three_of_connectedClass_hook h
  rw [ht, span_translate] at h3
  omega

/-- The two hooks are not translates of one another. -/
theorem hook_not_translate_hookRotated (t : ℤ × ℤ) :
    skewOf [2, 2] [1] ≠ translate t (skewOf [2, 1] []) := by
  intro h
  have h1 := normalize_translate (D := skewOf [2, 1] []) (by decide +kernel) t
  rw [← h] at h1
  have h2 : normalize (skewOf [2, 2] [1]) ≠ normalize (skewOf [2, 1] []) := by decide +kernel
  exact h2 h1

theorem connectedClass_hook_hook : connectedClass hookSchur (skewOf [2, 1] []) :=
  ⟨isConnectedSkew_hook, cellSchur_hook⟩

theorem connectedClass_hook_hookRotated : connectedClass hookSchur (skewOf [2, 2] [1]) :=
  ⟨isConnectedSkew_hookRotated, cellSchur_hookRotated⟩

theorem hookRotated_eq_rotate_hook :
    skewOf [2, 2] [1] = translate (1, 1) (rotate (skewOf [2, 1] [])) := by
  decide +kernel

/-- **The hook example of `sec:minimal-fibers`.**  The common-factor graph `Γ(s_H)` has exactly
two vertices, the classes of `H = (2, 1)` and `H* = (2, 2)/(1)`; both are isolated; and they are
rotations of one another. -/
theorem hook_class_graph :
    ∃ a b : TranslationClass (connectedClass hookSchur), a ≠ b ∧ (∀ c, c = a ∨ c = b) ∧
      (∀ c d, ¬ (classGraph (connectedClass hookSchur)).Adj c d) ∧
      (connectedRotationData hookSchur).rot a = b := by
  refine ⟨classOf ⟨_, connectedClass_hook_hook⟩, classOf ⟨_, connectedClass_hook_hookRotated⟩,
    ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨t, ht⟩ := classOf_eq_iff.mp h
    exact hook_not_translate_hookRotated t ht
  · intro c
    obtain ⟨x, rfl⟩ := exists_classOf c
    rcases (cellSchur_eq_hook_iff x.2.1.1).mp x.2.2 with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact Or.inl (classOf_eq_iff.mpr ⟨v, hv⟩).symm
    · exact Or.inr (classOf_eq_iff.mpr ⟨v, hv⟩).symm
  · intro c d hcd
    obtain ⟨x, rfl⟩ := exists_classOf c
    obtain ⟨y, rfl⟩ := exists_classOf d
    exact not_hasProperChart_of_connectedClass_hook x.2
      (classGraph_adj_iff.mp hcd).exists_chart_left
  · exact classOf_eq_iff.mpr ⟨(1, 1), hookRotated_eq_rotate_hook⟩

/-- **The hook example of `sec:minimal-fibers`, the rotation quotient.**  `Γ̄(s_H)` has one
vertex. -/
theorem hook_quotient_subsingleton : Subsingleton (connectedRotationData hookSchur).Orbit := by
  obtain ⟨a, b, -, hall, -, hrot⟩ := hook_class_graph
  refine ⟨fun o₁ o₂ => ?_⟩
  have key : ∀ o : (connectedRotationData hookSchur).Orbit,
      o = (connectedRotationData hookSchur).orbit a := by
    intro o
    obtain ⟨c, rfl⟩ := Quotient.exists_rep o
    rcases hall c with rfl | rfl
    · rfl
    · exact ((RotationData.orbit_eq_iff _).mpr (Or.inr hrot.symm)).symm
  rw [key o₁, key o₂]

/-- `Γ̄(s_H)` is connected (a single vertex). -/
theorem hook_quotientGraph_connected :
    (connectedRotationData hookSchur).quotientGraph.Connected := by
  have := hook_quotient_subsingleton
  obtain ⟨a, -⟩ := hook_class_graph
  have : Nonempty (connectedRotationData hookSchur).Orbit :=
    ⟨(connectedRotationData hookSchur).orbit a⟩
  exact ⟨fun x y => by rw [Subsingleton.elim x y]⟩

end Hook

/-! ### A checked common final factor -/

/-- A non-vacuity witness for `HasCommonFinalFactor`: the two hooks, composed with the singleton
mark on the row `(3)`, give two diagrams with a common final factor (outers `H`, `H*`, with equal
function `h₁ h₂ - h₃`). -/
example : HasCommonFinalFactor cellSchur (rowInnerThree.compose (skewOf [2, 1] []))
    (rowInnerThree.compose (skewOf [2, 2] [1])) := by
  have hmem : ∀ A : Diagram, connectedClass hookSchur A →
      rowInnerThree.compose A ∈ fiberClass cellSchur rowInnerThree hookSchur := by
    intro A hA
    refine subset_fiberClass _ ⟨A, hA.1, ?_, hA.2, Or.inl rfl⟩
    rcases (cellSchur_eq_hook_iff hA.1.1).mp hA.2 with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [translate, Finset.card_image_of_injective _ (add_left_injective v)]
      decide +kernel
    · rw [translate, Finset.card_image_of_injective _ (add_left_injective v)]
      decide +kernel
  refine fiberClass_hasCommonFinalFactor (by decide +kernel) (by decide +kernel)
    (hmem _ connectedClass_hook_hook) (hmem _ connectedClass_hook_hookRotated) ?_
  rintro ⟨t, ht⟩
  have h1 := normalize_translate
    (D := rowInnerThree.compose (skewOf [2, 1] [])) (by decide +kernel) t
  rw [← ht] at h1
  have h2 : normalize (rowInnerThree.compose (skewOf [2, 2] [1])) ≠
      normalize (rowInnerThree.compose (skewOf [2, 1] [])) := by decide +kernel
  exact h2 h1

/-! ### `lem:rotation-components` for the concrete graph -/

/-- The graph `Γ(P)` of `sec:minimal-fibers` is the part of the graph of `def:gluing-graph`
on the connected diagrams, so its components are cliques as soon as those of the latter are. -/
theorem connectedClass_componentsAreCliques
    (hgluing : ∀ P : Lambda, ComponentsAreCliques (classGraph (skewClass P))) (P : Lambda) :
    ComponentsAreCliques (classGraph (connectedClass P)) := by
  rw [componentsAreCliques_iff_incident_edges]
  intro a b c hac hab hbc
  obtain ⟨x, rfl⟩ := exists_classOf a
  obtain ⟨y, rfl⟩ := exists_classOf b
  obtain ⟨z, rfl⟩ := exists_classOf c
  have hxy := classGraph_adj_iff.mp hab
  have hyz := classGraph_adj_iff.mp hbc
  let lift : {F : Diagram // connectedClass P F} → {F : Diagram // skewClass P F} :=
    fun x => ⟨x.1, x.2.1.1, x.2.2⟩
  have hne : classOf (lift x) ≠ classOf (lift z) := fun e =>
    hac ((classOf_eq_iff (S := connectedClass P)).mpr
      ((classOf_eq_iff (S := skewClass P)).mp e))
  have hadj := ((componentsAreCliques_iff_incident_edges _).mp (hgluing P)) _ (classOf (lift y))
    _ hne (classGraph_adj_iff.mpr hxy) (classGraph_adj_iff.mpr hyz)
  exact classGraph_adj_iff.mpr
    ((classGraph_adj_iff (S := skewClass P) (x := lift x) (y := lift z)).mp hadj)

/-- **`lem:rotation-components`, concrete.**  Take `thm:gluing` as the hypothesis `hgluing`: the
components of the common-factor graph of every Schur class are cliques.  Then, on the connected
class of `P`, every component of `Γ⁺(P)` and of `Γ̄(P)` is a clique, and rotation augmentation
changes no rooted component. -/
theorem rotation_components
    (hgluing : ∀ P : Lambda, ComponentsAreCliques (classGraph (skewClass P))) (P : Lambda) :
    ComponentsAreCliques (connectedRotationData P).augmented ∧
    ComponentsAreCliques (connectedRotationData P).quotientGraph ∧
    ∀ a ∈ (connectedRotationData P).rooted,
      ((connectedRotationData P).augmented.connectedComponentMk a).supp =
        ((connectedRotationData P).graph.connectedComponentMk a).supp := by
  have h := connectedClass_componentsAreCliques hgluing P
  exact ⟨(connectedRotationData P).componentsAreCliques_augmented h,
    (connectedRotationData P).componentsAreCliques_quotient h,
    fun a ha => (connectedRotationData P).augmented_connectedComponent_supp_eq_of_rooted ha⟩

end GluingCore
