import SkewGluing.NecessityReduction.Presentation

/-!
# Connectivity reduction on a connected Schur class

Formalizes `shields-2026-skew-gluing.tex`, «Reduction of composition necessity»
(`thm:connectivity-reduction`, and the remark after it) and «Source-minimal fibers»
(`lem:rotation-components`).

* `connectedKeyedData`: the concrete `KeyedRotationData` of the connected class of `P`: the
  rotation data of `Γ(P)` together with the component key `K` of `eq:component-key`
  (`ComponentKeyClassifies` supplies its field `key_eq_iff`).
* `connectivity_reduction`: the four equivalent statements of `thm:connectivity-reduction` for
  the connected Schur class of `P`, given `thm:gluing` (`GluingStatement`) and
  `prop:component-key` (`ComponentKeyClassifies`): `Γ⁺` connected; `Γ̄` connected; every
  nonrotation pair has a common final factor; (TR) and (RI).
* `disjoint_cliques_remark`: the abstract example after `thm:connectivity-reduction`.

Sorry-free.
-/

namespace SkewGluing

instance : Nonempty Chart := ⟨⟨∅, ⟨∅, ∅, 0, .a⟩⟩⟩

/-- The key `K(F)` of a diagram, read at a chosen source-minimal chart.  (It is meaningful, and
independent of the choice by `ComponentKeyClassifies`, on diagrams with a proper chart.) -/
noncomputable def keyOf (F : Diagram) : Key :=
  (Classical.epsilon fun χ : Chart => χ.IsSourceMinimal F).key

theorem keyOf_translate (t : ℤ × ℤ) (F : Diagram) : keyOf (translate t F) = keyOf F := by
  simp only [keyOf, Chart.isSourceMinimal_translate_iff]

theorem isSourceMinimal_epsilon {F : Diagram} (h : HasProperChart F) :
    (Classical.epsilon fun χ : Chart => χ.IsSourceMinimal F).IsSourceMinimal F :=
  Classical.epsilon_spec (p := fun χ : Chart => χ.IsSourceMinimal F)
    (Chart.exists_isSourceMinimal h)

/-- The key on the translation classes of the connected class of `P`. -/
noncomputable def classKey (P : Lambda) : TranslationClass (connectedClass P) → Key :=
  Quotient.lift (fun F => keyOf F.1) (by
    rintro F G ⟨t, ht⟩
    rw [ht, keyOf_translate])

/-- The keyed rotation data of the connected class of `P`: the rotation data of `Γ(P)` with the
component key.  Its field `key_eq_iff` is `prop:component-key`. -/
noncomputable def connectedKeyedData (hkey : ComponentKeyClassifies) (P : Lambda) :
    KeyedRotationData (TranslationClass (connectedClass P)) Key where
  toRotationData := connectedRotationData P
  key := classKey P
  key_eq_iff := by
    intro x hx y hy
    obtain ⟨F, rfl⟩ := exists_classOf x
    obtain ⟨H, rfl⟩ := exists_classOf y
    have hF : HasProperChart F.1 := classOf_mem_classRooted_iff.mp hx
    have hH : HasProperChart H.1 := classOf_mem_classRooted_iff.mp hy
    have eF := isSourceMinimal_epsilon hF
    have eH := isSourceMinimal_epsilon hH
    refine Iff.trans ?_ (hkey.2 P F H hF hH)
    change keyOf F.1 = keyOf H.1 ↔ _
    constructor
    · intro h
      exact ⟨_, _, eF, eH, h⟩
    · rintro ⟨χ, χ', h1, h2, hk⟩
      have a1 := hkey.1 F.1 F.2.1 _ _ eF h1
      have a2 := hkey.1 H.1 H.2.1 _ _ eH h2
      unfold keyOf
      rw [a1, a2, hk]

/-! ### Translating the abstract statements -/

private theorem eq_translate_symm {a b : Diagram} {t : ℤ × ℤ} (h : a = translate t b) :
    b = translate (-t) a := by
  rw [h, translate_translate, neg_add_cancel, translate_zero]

private theorem rotationMates_of_class {P : Lambda} (hS : ∀ F, connectedClass P F →
    connectedClass P (rotate F)) {F G : {F : Diagram // connectedClass P F}}
    (h : classOf G = classOf F ∨
      classOf G = classRotate (S := connectedClass P) (fun _ h => hS _ h) (classOf F)) :
    RotationMates F.1 G.1 := by
  rcases h with h | h
  · obtain ⟨t, ht⟩ := classOf_eq_iff.mp h
    exact Or.inl ⟨-t, eq_translate_symm ht⟩
  · rw [classRotate_classOf] at h
    obtain ⟨t, ht⟩ := classOf_eq_iff.mp h
    exact Or.inr ⟨-t, eq_translate_symm ht⟩

private theorem class_of_rotationMates {P : Lambda} (hS : ∀ F, connectedClass P F →
    connectedClass P (rotate F)) {F G : {F : Diagram // connectedClass P F}}
    (h : RotationMates F.1 G.1) :
    classOf G = classOf F ∨
      classOf G = classRotate (S := connectedClass P) (fun _ h => hS _ h) (classOf F) := by
  rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact Or.inl (classOf_eq_iff.mpr ⟨t, ht⟩).symm
  · rw [classRotate_classOf]
    exact Or.inr (classOf_eq_iff.mpr ⟨t, ht⟩).symm

/-- **`thm:connectivity-reduction`, concretely.**  For the connected Schur class of `P`
(nonempty), given `thm:gluing` and `prop:component-key`, the following are equivalent:

1. the rotation-augmented common-factor graph `Γ⁺(P)` is connected;
2. the rotation-quotiented common-factor graph `Γ̄(P)` is connected;
3. every nonrotation pair in the class has a common final factor;
4. (TR) and (RI) hold on the class.

The proof is `KeyedRotationData.connectivity_reduction` applied to `connectedKeyedData`. -/
theorem connectivity_reduction (hgluing : GluingStatement) (hkey : ComponentKeyClassifies)
    (P : Lambda) (hP : ∃ F, connectedClass P F) :
    List.TFAE
      [ (connectedRotationData P).augmented.Connected,
        (connectedRotationData P).quotientGraph.Connected,
        ∀ F G : Diagram, connectedClass P F → connectedClass P G → ¬ RotationMates F G →
          HasCommonFinalFactor cellSchur F G,
        TerminalRigidity P ∧ RootedKeyInvariance P ] := by
  set K := connectedKeyedData hkey P with hK
  obtain ⟨F₀, hF₀⟩ := hP
  have : Nonempty (TranslationClass (connectedClass P)) := ⟨classOf ⟨F₀, hF₀⟩⟩
  have hcl : ComponentsAreCliques K.graph := connectedClass_componentsAreCliques hgluing P
  have h := K.connectivity_reduction hcl
  have hS : ∀ F, connectedClass P F → connectedClass P (rotate F) := fun _ h =>
    connectedClass_rotate h
  have e3 : (∀ F G : Diagram, connectedClass P F → connectedClass P G → ¬ RotationMates F G →
      HasCommonFinalFactor cellSchur F G) ↔ K.NonrotationPairsAdjacent := by
    constructor
    · intro h3 x y hyx hyr
      obtain ⟨F, rfl⟩ := exists_classOf x
      obtain ⟨G, rfl⟩ := exists_classOf y
      refine classGraph_adj_iff.mpr (h3 F.1 G.1 F.2 G.2 fun hm => ?_)
      rcases class_of_rotationMates hS hm with e | e
      · exact hyx e
      · exact hyr e
    · intro h3 F G hF hG hnm
      have := h3 (classOf ⟨F, hF⟩) (classOf ⟨G, hG⟩) (fun e => hnm (rotationMates_of_class hS
        (Or.inl e))) (fun e => hnm (rotationMates_of_class hS (Or.inr e)))
      exact classGraph_adj_iff.mp this
  have e4 : (TerminalRigidity P ∧ RootedKeyInvariance P) ↔
      (K.TerminalRigidity ∧ K.RootedKeyInvariance) := by
    constructor
    · rintro ⟨hTR, hRI⟩
      refine ⟨?_, ?_⟩
      · intro x hx y
        obtain ⟨F, rfl⟩ := exists_classOf x
        obtain ⟨G, rfl⟩ := exists_classOf y
        have hF : ¬ HasProperChart F.1 := fun h => hx (classOf_mem_classRooted_iff.mpr h)
        exact class_of_rotationMates hS (hTR F.1 G.1 F.2 G.2 hF) |>.imp id id
      · intro x hx y hy
        obtain ⟨F, rfl⟩ := exists_classOf x
        obtain ⟨H, rfl⟩ := exists_classOf y
        have hF : HasProperChart F.1 := classOf_mem_classRooted_iff.mp hx
        have hH : HasProperChart H.1 := classOf_mem_classRooted_iff.mp hy
        exact hRI F.1 H.1 F.2 H.2 hF hH _ _ (isSourceMinimal_epsilon hF)
          (isSourceMinimal_epsilon hH)
    · rintro ⟨hTR, hRI⟩
      refine ⟨?_, ?_⟩
      · intro F G hF hG hnF
        exact rotationMates_of_class hS (hTR (classOf ⟨F, hF⟩) (fun hx =>
          hnF (classOf_mem_classRooted_iff.mp hx)) (classOf ⟨G, hG⟩))
      · intro F H hF hH rF rH χ χ' h1 h2
        have k := hRI (classOf ⟨F, hF⟩) (classOf_mem_classRooted_iff.mpr rF)
          (classOf ⟨H, hH⟩) (classOf_mem_classRooted_iff.mpr rH)
        change keyOf F = keyOf H at k
        have a1 := hkey.1 F hF.1 _ _ (isSourceMinimal_epsilon rF) h1
        have a2 := hkey.1 H hH.1 _ _ (isSourceMinimal_epsilon rH) h2
        unfold keyOf at k
        rw [← a1, ← a2]
        exact k
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 1 ↔ 3 := (h.out 1 3).trans e3.symm
  tfae_have 1 ↔ 4 := (h.out 1 4).trans e4.symm
  tfae_finish

/-- **The remark after `thm:connectivity-reduction`.**  Absence of isolated vertices does not
imply connectivity: there is an abstract graph (two disjoint four-vertex cliques, rotation
pairing vertices inside each clique, every vertex rooted) whose components are cliques, which has
no isolated vertex and in which every vertex is adjacent to its rotation (the fibers dominate),
yet which is not connected even after rotation augmentation.  This is an abstract graph
example, not a Schur class. -/
theorem disjoint_cliques_remark :
    ∃ G : RotationData (Fin 8), ComponentsAreCliques G.graph ∧
      (∀ x : Fin 8, x ∈ G.rooted ∧ ∃ y, G.graph.Adj x y) ∧ ¬ G.augmented.Connected :=
  ⟨twoQuadruples, twoQuadruples_componentsAreCliques,
    fun x => ⟨Set.mem_univ x, twoQuadruples_no_isolated_vertex x⟩, twoQuadruples_not_connected⟩

end SkewGluing
