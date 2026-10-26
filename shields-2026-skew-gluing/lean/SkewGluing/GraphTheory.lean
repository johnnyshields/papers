import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Notation
import SkewGluing.Tactics

/-!
# Graph theory of the common-factor graph

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`thm:gluing`) and
«Source-minimal fibers» (`lem:rotation-components`), «Reduction of composition necessity»
(`thm:connectivity-reduction`).

Everything here is stated for an abstract simple graph, so that the modules on diagrams
instantiate it with the concrete common-factor graph `Γ(P)` of a connected Schur class.

* `componentsAreCliques_iff_incident_edges`: the shortest-path argument that closes the proof of
  `thm:gluing`: all components are cliques iff two incident edges force the third.
* `RotationData`: the abstract data of `lem:rotation-components` (graph, rotation, rooted
  vertices), with the rotation-augmented graph `Γ⁺` and the rotation quotient `Γ̄`.  The lemma is
  proved as `RotationData.componentsAreCliques_augmented`,
  `RotationData.augmented_connectedComponent_eq_of_rooted` and
  `RotationData.componentsAreCliques_quotient`.
* `KeyedRotationData.connectivity_reduction`: the four equivalent statements of
  `thm:connectivity-reduction`, with an abstract key satisfying the conclusion of
  `prop:component-key`.
* `twoQuadruples`: the abstract example in the remark after `thm:connectivity-reduction`.
* `CompositionModel.reversalFamily_eq_class` and `CompositionModel.exists_common_tower`: the
  induction of `thm:necessity-reduction` from the second to the third assertion, over an abstract
  composition layer.  The converse implications need forward composition and reversal, and are
  proved on concrete diagrams in `SkewGluing.NecessityReduction.Reduction`.

Sorry-free.
-/

namespace SkewGluing

open SimpleGraph

variable {V : Type*}

/-! ### Clique components and the shortest-path argument -/

/-- Every connected component of `G` is a clique. -/
def ComponentsAreCliques (G : SimpleGraph V) : Prop :=
  ∀ C : G.ConnectedComponent, G.IsClique C.supp

/-- Two incident edges force the third: if `x ≠ z` both have a neighbor `y` in common, then
`x ~ z`. -/
def IncidentEdgesForceThird (G : SimpleGraph V) : Prop :=
  ∀ x y z : V, x ≠ z → G.Adj x y → G.Adj y z → G.Adj x z

/-- In a graph whose components are cliques, two distinct vertices in one component are
adjacent. -/
theorem ComponentsAreCliques.adj_of_reachable {G : SimpleGraph V} (h : ComponentsAreCliques G)
    {x y : V} (hr : G.Reachable x y) (hne : x ≠ y) : G.Adj x y := by
  apply h (G.connectedComponentMk x)
  · exact ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl
  · exact ConnectedComponent.mem_supp_iff _ _ |>.mpr (ConnectedComponent.eq.mpr hr.symm)
  · exact hne

/-- The shortest-path argument: if two incident edges force the third, then distinct vertices
joined by a chain of edges are adjacent. -/
theorem adj_of_reflTransGen {G : SimpleGraph V} (h : IncidentEdgesForceThird G) {x y : V}
    (hr : Relation.ReflTransGen G.Adj x y) : x ≠ y → G.Adj x y := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => absurd rfl h
  | @head a c hstep _ ih =>
    intro hay
    by_cases hcy : c = y
    · exact hcy ▸ hstep
    · exact h _ _ _ hay hstep (ih hcy)

/-- **Equivalence clause of `thm:gluing` and its closing argument.**  In any simple graph, every
connected component is a clique exactly when two incident edges force the third.  The forward
direction is the clique property; the converse is the shortest-path argument. -/
theorem componentsAreCliques_iff_incident_edges (G : SimpleGraph V) :
    ComponentsAreCliques G ↔ IncidentEdgesForceThird G := by
  constructor
  · intro h x y z hxz hxy hyz
    exact h.adj_of_reachable (hxy.reachable.trans hyz.reachable) hxz
  · intro h C x hx y hy hxy
    obtain rfl := (ConnectedComponent.mem_supp_iff _ _).mp hx
    have hr : G.Reachable x y := ConnectedComponent.eq.mp
      ((ConnectedComponent.mem_supp_iff _ _).mp hy).symm
    exact adj_of_reflTransGen h (reachable_iff_reflTransGen _ _ |>.mp hr) hxy

/-- An isolated vertex forms a singleton component, which is trivially a clique. -/
theorem connectedComponent_supp_eq_singleton_of_isolated {G : SimpleGraph V} {x : V}
    (hx : ∀ y, ¬ G.Adj x y) : (G.connectedComponentMk x).supp = {x} := by
  ext y
  rw [ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hr : G.Reachable x y := ConnectedComponent.eq.mp h.symm
    rw [reachable_iff_reflTransGen] at hr
    rcases Relation.ReflTransGen.cases_head hr with h1 | ⟨b, hb, _⟩
    · exact h1.symm
    · exact absurd hb (hx b)
  · rintro rfl; rfl

/-! ### Rotation augmentation and quotient (`lem:rotation-components`) -/

/-- The abstract data of `lem:rotation-components`: the common-factor graph `Γ(P)` on a Schur
class `V`, the rotation `D ↦ D*` as an involution, and the rooted diagrams.

The hypotheses are the three facts the paper uses about the concrete graph, discharged for the
common-factor graph by `SkewGluing.CommonFactorGraph`:

* `rot_rot`: rotation through `180` degrees is an involution;
* `adj_rot_of_rooted`: "a rooted diagram already shares a fiber with its rotation", so a rooted
  vertex is adjacent to its rotation when they are distinct;
* `isolated_of_not_rooted`: a chartless diagram has no proper chart, so it has no edge in `Γ`
  (`def:gluing-graph`).

That `Γ` is invariant under rotation is not needed for `lem:rotation-components`.  The
hypothesis that the components of `Γ` are cliques is `thm:gluing`; it is an explicit hypothesis
of the theorems below. -/
structure RotationData (V : Type*) where
  /-- The common-factor graph `Γ(P)`. -/
  graph : SimpleGraph V
  /-- Rotation `D ↦ D*`. -/
  rot : V → V
  rot_rot : Function.Involutive rot
  /-- The rooted vertices: those with a proper chart. -/
  rooted : Set V
  adj_rot_of_rooted : ∀ x ∈ rooted, rot x ≠ x → graph.Adj x (rot x)
  isolated_of_not_rooted : ∀ x ∉ rooted, ∀ y, ¬ graph.Adj x y

namespace RotationData

variable (P : RotationData V)

/-- The edges `x ~ x*` between distinct rotation mates. -/
def rotationEdges : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => y = P.rot x

/-- The rotation-augmented graph `Γ⁺(P) = Γ(P) ⊔ {x ~ x*}`. -/
def augmented : SimpleGraph V := P.graph ⊔ P.rotationEdges

/-- Two vertices are rotation mates when they are equal or rotations of one another. -/
def rotationSetoid : Setoid V where
  r x y := y = x ∨ y = P.rot x
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro x y (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (P.rot_rot x).symm
      trans := by
        rintro x y z (rfl | rfl) (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl (P.rot_rot x) }

/-- The vertices of the rotation quotient: rotation orbits. -/
abbrev Orbit : Type _ := Quotient P.rotationSetoid

/-- The rotation orbit of a vertex. -/
def orbit (x : V) : P.Orbit := Quotient.mk P.rotationSetoid x

/-- The rotation quotient `Γ̄(P)`: two distinct orbits are adjacent when some representatives
are adjacent in `Γ(P)`. -/
def quotientGraph : SimpleGraph P.Orbit where
  Adj a b := a ≠ b ∧ ∃ x y, P.orbit x = a ∧ P.orbit y = b ∧ P.graph.Adj x y
  symm := ⟨by
    rintro a b ⟨hab, x, y, hx, hy, hxy⟩
    exact ⟨hab.symm, y, x, hy, hx, hxy.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

theorem orbit_eq_iff {x y : V} : P.orbit x = P.orbit y ↔ y = x ∨ y = P.rot x := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

theorem augmented_adj_iff {a b : V} :
    P.augmented.Adj a b ↔ P.graph.Adj a b ∨ (a ≠ b ∧ b = P.rot a) := by
  have key : a ≠ b ∧ (b = P.rot a ∨ a = P.rot b) ↔ a ≠ b ∧ b = P.rot a := by
    refine and_congr_right fun _ => ⟨?_, Or.inl⟩
    rintro (h | h)
    · exact h
    · rw [h, P.rot_rot]
  simp [augmented, rotationEdges, key]

/-- Rotation mates are joined in `Γ⁺`. -/
theorem augmented_reachable_of_orbit_eq {x y : V} (h : P.orbit x = P.orbit y) :
    P.augmented.Reachable x y := by
  rcases (P.orbit_eq_iff).mp h with rfl | rfl
  · exact Reachable.refl _
  · by_cases hne : x = P.rot x
    · rw [← hne]
    · exact Adj.reachable ((P.augmented_adj_iff).mpr (Or.inr ⟨hne, rfl⟩))

/-- A vertex with a neighbor in `Γ` is rooted. -/
theorem mem_rooted_of_adj {a b : V} (h : P.graph.Adj a b) : a ∈ P.rooted := by
  by_contra ha
  exact P.isolated_of_not_rooted a ha b h

/-- From a rooted vertex, `Γ⁺` has no edges beyond those of `Γ`. -/
theorem graph_adj_of_augmented_adj {a b : V} (ha : a ∈ P.rooted)
    (h : P.augmented.Adj a b) : P.graph.Adj a b := by
  rcases (P.augmented_adj_iff).mp h with h | ⟨hne, rfl⟩
  · exact h
  · exact P.adj_rot_of_rooted a ha (Ne.symm hne)

/-- **`lem:rotation-components`, rotation augmentation changes no rooted component** (as a
statement about reachability). -/
theorem augmented_reachable_iff_of_rooted {a b : V} (ha : a ∈ P.rooted) :
    P.augmented.Reachable a b ↔ P.graph.Reachable a b := by
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    suffices H : Relation.ReflTransGen P.graph.Adj a b ∧ b ∈ P.rooted from
      reachable_iff_reflTransGen _ _ |>.mpr H.1
    induction h with
    | refl => exact ⟨.refl, ha⟩
    | tail _ hstep ih =>
      have hg := P.graph_adj_of_augmented_adj ih.2 hstep
      exact ⟨ih.1.tail hg, P.mem_rooted_of_adj hg.symm⟩
  · exact fun h => h.mono le_sup_left

/-- **`lem:rotation-components`, rotation augmentation changes no rooted component** (as a
statement about components: the component of a rooted vertex has the same support in `Γ⁺`). -/
theorem augmented_connectedComponent_supp_eq_of_rooted {a : V} (ha : a ∈ P.rooted) :
    (P.augmented.connectedComponentMk a).supp = (P.graph.connectedComponentMk a).supp := by
  ext b
  rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.mem_supp_iff,
    ConnectedComponent.eq, ConnectedComponent.eq]
  constructor
  · intro h; exact (P.augmented_reachable_iff_of_rooted ha).mp h.symm |>.symm
  · intro h; exact (P.augmented_reachable_iff_of_rooted ha).mpr h.symm |>.symm

/-- **`lem:rotation-components`, `Γ⁺`.**  If the components of `Γ` are cliques (`thm:gluing`),
then so are those of `Γ⁺`. -/
theorem componentsAreCliques_augmented (h : ComponentsAreCliques P.graph) :
    ComponentsAreCliques P.augmented := by
  rw [componentsAreCliques_iff_incident_edges]
  intro x y z hxz hxy hyz
  by_cases hy : y ∈ P.rooted
  · have h1 := P.graph_adj_of_augmented_adj hy hxy.symm
    have h2 := P.graph_adj_of_augmented_adj hy hyz
    have hle : P.graph ≤ P.augmented := le_sup_left
    exact hle (h.adj_of_reachable (h1.symm.reachable.trans h2.reachable) hxz)
  · -- `y` is isolated in `Γ`, so its only `Γ⁺`-neighbor is `y*`
    have nb : ∀ b, P.augmented.Adj y b → b = P.rot y := by
      intro b hb
      rcases (P.augmented_adj_iff).mp hb with hb | ⟨_, hb⟩
      · exact absurd hb (P.isolated_of_not_rooted y hy b)
      · exact hb
    exact absurd ((nb x hxy.symm).trans (nb z hyz).symm) hxz

/-- The quotient graph reaches exactly as the augmented graph. -/
theorem quotientGraph_reachable_iff {x y : V} :
    P.quotientGraph.Reachable (P.orbit x) (P.orbit y) ↔ P.augmented.Reachable x y := by
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    suffices H : ∀ b, Relation.ReflTransGen P.quotientGraph.Adj (P.orbit x) b →
        ∃ y, b = P.orbit y ∧ P.augmented.Reachable x y by
      obtain ⟨y', hy', hr⟩ := H _ h
      exact hr.trans (P.augmented_reachable_of_orbit_eq hy'.symm)
    intro b hb
    induction hb with
    | refl => exact ⟨x, rfl, Reachable.refl _⟩
    | tail _ hstep ih =>
      obtain ⟨y1, rfl, hr⟩ := ih
      obtain ⟨_, x', y', hx', hy', hadj⟩ := hstep
      have hle : P.graph ≤ P.augmented := le_sup_left
      refine ⟨y', hy'.symm, hr.trans ?_⟩
      exact (P.augmented_reachable_of_orbit_eq hx').symm.trans (hle hadj).reachable
  · intro h
    rw [reachable_iff_reflTransGen] at h
    rw [reachable_iff_reflTransGen]
    induction h with
    | refl => exact .refl
    | @tail b c _ hstep ih =>
      by_cases hbc : P.orbit b = P.orbit c
      · rw [← hbc]; exact ih
      · refine ih.tail ⟨hbc, b, c, rfl, rfl, ?_⟩
        rcases (P.augmented_adj_iff).mp hstep with h | ⟨_, h⟩
        · exact h
        · exact absurd (P.orbit_eq_iff.mpr (Or.inr h)) hbc

/-- **`lem:rotation-components`, `Γ̄`.**  If the components of `Γ` are cliques (`thm:gluing`),
then so are those of the rotation quotient `Γ̄`.  The proof also shows (by
`quotientGraph_reachable_iff`) that quotienting does not merge distinct components of `Γ⁺`.

**Differs from the paper's route.**  Cliqueness of the quotient is deduced from that of `Γ⁺`
through reachability, so no rotation-stability of the components is used. -/
theorem componentsAreCliques_quotient (h : ComponentsAreCliques P.graph) :
    ComponentsAreCliques P.quotientGraph := by
  have haug := P.componentsAreCliques_augmented h
  rw [componentsAreCliques_iff_incident_edges]
  intro a b c hac hab hbc
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨z, rfl⟩ := Quotient.exists_rep c
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  have hr : P.augmented.Reachable x z :=
    (P.quotientGraph_reachable_iff).mp (hab.reachable.trans hbc.reachable)
  have hne : x ≠ z := fun e => hac (by rw [e])
  have hadj := haug.adj_of_reachable hr hne
  refine ⟨hac, x, z, rfl, rfl, ?_⟩
  rcases (P.augmented_adj_iff).mp hadj with h | ⟨_, h⟩
  · exact h
  · exact absurd (P.orbit_eq_iff.mpr (Or.inr h)) hac

end RotationData

/-! ### Connectivity reduction (`thm:connectivity-reduction`) -/

/-- `RotationData` together with an abstract key `K` on rooted vertices.

The field `key_eq_iff` is the conclusion of `prop:component-key`: for rooted `F, H` in one class,
`K(F) = K(H)` exactly when `F, H` lie in the same common-factor component.  It is a hypothesis
here, supplied for the concrete graph by `ComponentKeyClassifies` (`prop:component-key`),
proved as `component_key` in `SkewGluing.MainTheorems`. -/
structure KeyedRotationData (V κ : Type*) extends RotationData V where
  /-- The component key `K`, only meaningful on rooted vertices. -/
  key : V → κ
  key_eq_iff : ∀ x ∈ rooted, ∀ y ∈ rooted, key x = key y ↔ graph.Reachable x y

namespace KeyedRotationData

variable {κ : Type*} (P : KeyedRotationData V κ)

/-- Terminal rigidity (TR): every chartless `F` has class `{F, F*}`. -/
def TerminalRigidity : Prop :=
  ∀ F ∉ P.rooted, ∀ G : V, G = F ∨ G = P.rot F

/-- Rooted-key invariance (RI): any two rooted members of the class have equal keys. -/
def RootedKeyInvariance : Prop :=
  ∀ F ∈ P.rooted, ∀ H ∈ P.rooted, P.key F = P.key H

/-- Every nonrotation pair has a common final factor, i.e. is an edge of `Γ`. -/
def NonrotationPairsAdjacent : Prop :=
  ∀ x y : V, y ≠ x → y ≠ P.rot x → P.graph.Adj x y

/-- **`thm:connectivity-reduction`.**  For a nonempty class whose common-factor components are
cliques (`thm:gluing`), the following are equivalent: (1) `Γ⁺` is connected; (2) `Γ̄` is
connected; (3) every nonrotation pair is adjacent in `Γ`; (4) (TR) and (RI).

**Differs from the paper's route.**  The proof shows (3) ⇔ (4) directly and avoids the case
analysis on chartless orbits used for (1) ⇒ (4). -/
theorem connectivity_reduction [Nonempty V] (hcl : ComponentsAreCliques P.graph) :
    List.TFAE
      [ P.augmented.Connected,
        P.quotientGraph.Connected,
        P.NonrotationPairsAdjacent,
        P.TerminalRigidity ∧ P.RootedKeyInvariance ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      have : Nonempty P.Orbit := ⟨P.orbit (Classical.arbitrary V)⟩
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      exact (P.quotientGraph_reachable_iff).mpr (h.preconnected x y)
    · intro h
      refine ⟨fun x y => ?_⟩
      exact (P.quotientGraph_reachable_iff).mp (h.preconnected (P.orbit x) (P.orbit y))
  tfae_have 1 → 3 := by
    intro h x y hyx hyr
    have hadj := (P.componentsAreCliques_augmented hcl).adj_of_reachable
      (h.preconnected x y) (Ne.symm hyx)
    rcases (P.augmented_adj_iff).mp hadj with h | ⟨_, h⟩
    · exact h
    · exact absurd h hyr
  tfae_have 3 → 1 := by
    intro h
    refine ⟨fun x y => ?_⟩
    by_cases hxy : y = x
    · rw [hxy]
    by_cases hr : y = P.rot x
    · exact Adj.reachable ((P.augmented_adj_iff).mpr (Or.inr ⟨Ne.symm hxy, hr⟩))
    · exact (h x y hxy hr).reachable.mono le_sup_left
  tfae_have 3 → 4 := by
    intro h
    refine ⟨?_, ?_⟩
    · intro F hF G
      by_contra hG
      rw [not_or] at hG
      exact P.isolated_of_not_rooted F hF G (h F G hG.1 hG.2)
    · intro F hF H hH
      rw [P.key_eq_iff F hF H hH]
      by_cases hFH : H = F
      · rw [hFH]
      by_cases hr : H = P.rot F
      · exact (hr ▸ P.adj_rot_of_rooted F hF (fun e => hFH (hr.trans e))).reachable
      · exact (h F H hFH hr).reachable
  tfae_have 4 → 3 := by
    rintro ⟨hTR, hRI⟩ x y hyx hyr
    have hx : x ∈ P.rooted := by
      by_contra hx
      rcases hTR x hx y with h | h
      · exact hyx h
      · exact hyr h
    have hy : y ∈ P.rooted := by
      by_contra hy
      rcases hTR y hy x with h | h
      · exact hyx h.symm
      · exact hyr (by rw [h, P.rot_rot])
    have hreach := (P.key_eq_iff x hx y hy).mp (hRI x hx y hy)
    exact hcl.adj_of_reachable hreach (Ne.symm hyx)
  tfae_finish

end KeyedRotationData

/-! ### The remark after `thm:connectivity-reduction` -/

/-- Adjacency of the two-quadruples graph: distinct vertices in the same block of four. -/
def twoQuadruplesAdj (i j : Fin 8) : Prop := i ≠ j ∧ i.val / 4 = j.val / 4

instance : DecidableRel twoQuadruplesAdj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ i.val / 4 = j.val / 4))

/-- The rotation `0↔1, 2↔3, 4↔5, 6↔7` of the two-quadruples graph. -/
def twoQuadruplesRot : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- The remark after `thm:connectivity-reduction`: two disjoint four-vertex cliques on `Fin 8`
(`{0,1,2,3}` and `{4,5,6,7}`), with rotation `0↔1, 2↔3, 4↔5, 6↔7` pairing vertices inside each
clique.  Every vertex is rooted. -/
def twoQuadruples : RotationData (Fin 8) where
  graph :=
    { Adj := twoQuadruplesAdj
      symm := ⟨fun i j h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
  rot := twoQuadruplesRot
  rot_rot := by
    intro x
    revert x
    decide
  rooted := Set.univ
  adj_rot_of_rooted := by
    intro x _ h
    change twoQuadruplesAdj x (twoQuadruplesRot x)
    revert x
    decide
  isolated_of_not_rooted := by simp

/-- Every vertex of the two-quadruples graph has a neighbor: there is no isolated vertex, and
indeed each fiber dominates (every vertex is adjacent to its rotation). -/
theorem twoQuadruples_no_isolated_vertex :
    ∀ x : Fin 8, ∃ y, twoQuadruples.graph.Adj x y := by
  change ∀ x : Fin 8, ∃ y, twoQuadruplesAdj x y
  decide

/-- The components of the two-quadruples graph are cliques. -/
theorem twoQuadruples_componentsAreCliques : ComponentsAreCliques twoQuadruples.graph := by
  rw [componentsAreCliques_iff_incident_edges]
  intro x y z hxz hxy hyz
  exact (⟨hxz, hxy.2.trans hyz.2⟩ : twoQuadruplesAdj x z)

/-- Adjacent vertices of the augmented two-quadruples graph lie in the same clique. -/
theorem twoQuadruples_augmented_adj_div {a b : Fin 8} (h : twoQuadruples.augmented.Adj a b) :
    a.val / 4 = b.val / 4 := by
  have key : ∀ a b : Fin 8,
      (twoQuadruplesAdj a b ∨ (a ≠ b ∧ b = twoQuadruplesRot a)) → a.val / 4 = b.val / 4 := by
    decide
  exact key a b ((RotationData.augmented_adj_iff _).mp h)

/-- The two-quadruples graph is not connected, although it has no isolated vertex, even after
rotation augmentation.  This is why "no isolated vertex" alone does not give connectivity in
`thm:connectivity-reduction`. -/
theorem twoQuadruples_not_connected : ¬ twoQuadruples.augmented.Connected := by
  intro h
  have hr := h.preconnected 0 4
  rw [reachable_iff_reflTransGen] at hr
  have : ∀ b, Relation.ReflTransGen twoQuadruples.augmented.Adj 0 b → b.val / 4 = 0 := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail _ hstep ih => rw [← twoQuadruples_augmented_adj_div hstep]; exact ih
  have := this 4 hr
  omega

/-- The two-quadruples graph itself is not connected either. -/
theorem twoQuadruples_graph_not_connected : ¬ twoQuadruples.graph.Connected := by
  intro h
  apply twoQuadruples_not_connected
  exact h.mono le_sup_left

/-! ### The tower skeleton of `thm:necessity-reduction`

The induction in the proof that the second assertion of `thm:necessity-reduction` implies the
third uses only graph-theoretic facts about the common-factor graph and the shape of a tower.  We
model the composition layer abstractly: diagrams `D`, marked inners `M`, a composition
`comp A ω = A ∘_ω E` (the inner diagram `E` is part of the marked inner `ω`), rotation of
diagrams and of marked inners, the Schur function, and the common-factor graph.  The facts that
only the diagram layer can supply enter as explicit hypotheses of the theorems below, named in
each docstring with the paper label that proves them.

Only the implication from the second to the third assertion (with the consequence that every
Schur-equal pair has a common tower) is formalized here.  The converse implications use forward
composition and reversal from Olson-Harris, which the abstract layer does not provide; they are
proved on concrete diagrams in `SkewGluing.NecessityReduction.Reduction`. -/

/-- The abstract composition layer: diagrams `D` with Schur functions in `S`, marked inners `M`,
and the common-factor graph.  The graph satisfies the same abstract facts as in `RotationData`,
and edges join diagrams with equal Schur functions. -/
structure CompositionModel (D M S κ : Type*) where
  /-- The skew Schur function `s_F` of a diagram. -/
  schur : D → S
  /-- The number of cells; Schur-equal diagrams have equally many (homogeneity). -/
  cells : D → ℕ
  cells_eq : ∀ F G, schur F = schur G → cells F = cells G
  /-- Rotation `D ↦ D*`. -/
  rot : D → D
  rot_rot : Function.Involutive rot
  schur_rot : ∀ F, schur (rot F) = schur F
  /-- Rotation of a marked inner `ω ↦ ω*`. -/
  markRot : M → M
  markRot_markRot : Function.Involutive markRot
  /-- The composition `A ∘_ω E`. -/
  comp : D → M → D
  /-- The common-factor graph on all diagrams; its edges lie within Schur classes. -/
  graph : SimpleGraph D
  adj_schur : ∀ F G, graph.Adj F G → schur F = schur G
  rooted : Set D
  adj_rot_of_rooted : ∀ x ∈ rooted, rot x ≠ x → graph.Adj x (rot x)
  isolated_of_not_rooted : ∀ x ∉ rooted, ∀ y, ¬ graph.Adj x y
  /-- The component key `K`. -/
  key : D → κ

namespace CompositionModel

variable {D M S κ : Type*} (C : CompositionModel D M S κ)

/-- The rotation data of the common-factor graph on all diagrams. -/
def toRotationData : RotationData D where
  graph := C.graph
  rot := C.rot
  rot_rot := C.rot_rot
  rooted := C.rooted
  adj_rot_of_rooted := C.adj_rot_of_rooted
  isolated_of_not_rooted := C.isolated_of_not_rooted

/-- The fiber `𝓕(ω, Q) = {A ∘_ω E, A ∘_{ω*} E* : A connected, |A| ≥ 2, s_A = Q}`.  All
diagrams of the model are connected. -/
def fiber (ω : M) (Q : S) : Set D :=
  {G | ∃ A, 2 ≤ C.cells A ∧ C.schur A = Q ∧ (G = C.comp A ω ∨ G = C.comp A (C.markRot ω))}

/-- Terminal rigidity (TR) in every Schur class. -/
def TerminalRigidity : Prop :=
  ∀ F ∉ C.rooted, ∀ G, C.schur G = C.schur F → G = F ∨ G = C.rot F

/-- Rooted-key invariance (RI) in every Schur class. -/
def RootedKeyInvariance : Prop :=
  ∀ F ∈ C.rooted, ∀ H ∈ C.rooted, C.schur F = C.schur H → C.key F = C.key H

/-- The conclusion of `prop:component-key`: within a Schur class, rooted diagrams have equal keys
exactly when they lie in one common-factor component. -/
def KeyClassifiesComponents : Prop :=
  ∀ F ∈ C.rooted, ∀ H ∈ C.rooted, C.schur F = C.schur H →
    (C.key F = C.key H ↔ C.graph.Reachable F H)

/-- A Schur class as a keyed rotation datum on the subtype of its members. -/
def classData (hkey : C.KeyClassifiesComponents) (P : S) :
    KeyedRotationData {G // C.schur G = P} κ where
  graph := C.graph.comap Subtype.val
  rot := fun G => ⟨C.rot G.1, by rw [C.schur_rot]; exact G.2⟩
  rot_rot := fun G => Subtype.ext (C.rot_rot G.1)
  rooted := {G | G.1 ∈ C.rooted}
  adj_rot_of_rooted := fun G hG h =>
    C.adj_rot_of_rooted G.1 hG (fun e => h (Subtype.ext e))
  isolated_of_not_rooted := fun G hG H => C.isolated_of_not_rooted G.1 hG H.1
  key := fun G => C.key G.1
  key_eq_iff := by
    intro F hF H hH
    rw [hkey F.1 hF H.1 hH (F.2.trans H.2.symm)]
    constructor
    · intro h
      rw [reachable_iff_reflTransGen] at h
      suffices H' : ∀ b, Relation.ReflTransGen C.graph.Adj F.1 b →
          ∃ hb : C.schur b = P, Relation.ReflTransGen (C.graph.comap Subtype.val).Adj F ⟨b, hb⟩ by
        obtain ⟨hb, hr⟩ := H' H.1 h
        exact (reachable_iff_reflTransGen _ _).mpr hr
      intro b hb
      induction hb with
      | refl => exact ⟨F.2, .refl⟩
      | @tail b c _ hstep ih =>
        obtain ⟨hb, hr⟩ := ih
        have hc : C.schur c = P := by rw [← C.adj_schur b c hstep]; exact hb
        exact ⟨hc, hr.tail hstep⟩
    · intro h
      let f : (C.graph.comap (Subtype.val : {G // C.schur G = P} → D)) →g C.graph :=
        ⟨Subtype.val, fun h => h⟩
      exact h.map f

/-- Reachability in the rotation-augmented graph stays in one Schur class. -/
theorem schur_eq_of_augmented_reachable {F G : D}
    (h : C.toRotationData.augmented.Reachable F G) : C.schur G = C.schur F := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail b c _ hstep ih =>
    rcases (C.toRotationData.augmented_adj_iff).mp hstep with h | ⟨_, h⟩
    · exact (C.adj_schur b c h).symm.trans ih
    · rw [h]; exact (C.schur_rot b).trans ih

/-- A Schur class is connected in `Γ⁺` as soon as (TR) and (RI) hold: the implication from the
fourth to the first statement of `thm:connectivity-reduction`, applied to the class.  The
hypotheses `hcl` and `hkey` are `thm:gluing` and `prop:component-key`. -/
theorem augmented_reachable_of_schur_eq (hcl : ComponentsAreCliques C.graph)
    (hkey : C.KeyClassifiesComponents) (hTR : C.TerminalRigidity)
    (hRI : C.RootedKeyInvariance) {F G : D} (h : C.schur G = C.schur F) :
    C.toRotationData.augmented.Reachable F G := by
  set Q := C.classData hkey (C.schur F) with hQ
  have : Nonempty {G // C.schur G = C.schur F} := ⟨⟨F, rfl⟩⟩
  have hcl' : ComponentsAreCliques Q.graph := by
    rw [componentsAreCliques_iff_incident_edges] at hcl ⊢
    exact fun x y z hxz hxy hyz => hcl x.1 y.1 z.1 (fun e => hxz (Subtype.ext e)) hxy hyz
  have h4 : Q.TerminalRigidity ∧ Q.RootedKeyInvariance :=
    ⟨fun F' hF' G' => (hTR F'.1 hF' G'.1 (G'.2.trans F'.2.symm)).imp
        (fun e => Subtype.ext e) (fun e => Subtype.ext e),
      fun F' hF' H' hH' => hRI F'.1 hF' H'.1 hH' (F'.2.trans H'.2.symm)⟩
  have hconn := ((Q.connectivity_reduction hcl').out 4 1).mp h4
  have hr := hconn.preconnected ⟨F, rfl⟩ ⟨G, h⟩
  let f : Q.augmented →g C.toRotationData.augmented :=
    ⟨Subtype.val, fun {a b} hab => by
      rcases (Q.augmented_adj_iff).mp hab with h1 | ⟨h1, h2⟩
      · exact (C.toRotationData.augmented_adj_iff).mpr (Or.inl h1)
      · exact (C.toRotationData.augmented_adj_iff).mpr
          (Or.inr ⟨fun e => h1 (Subtype.ext e), congrArg Subtype.val h2⟩)⟩
  exact hr.map f

/-- A prescribed tower: a chartless-or-arbitrary first factor and a list of marked inners, read
as the left-associated composition `(((F₀ ∘_{ω₁} E₁) ∘_{ω₂} E₂) ⋯)`. -/
inductive Tower (D M : Type*) where
  /-- The first factor `F₀`. -/
  | terminal (F₀ : D) : Tower D M
  /-- Compose the tower so far with one more marked inner. -/
  | step (T : Tower D M) (ω : M) : Tower D M

/-- The diagram the tower composes to. -/
def top : Tower D M → D
  | .terminal F₀ => F₀
  | .step T ω => C.comp (top T) ω

/-- The reversal family: independently retain or rotate each factor, transporting the whole
mark with a rotated inner. -/
def reversalFamily : Tower D M → Set D
  | .terminal F₀ => {G | G = F₀ ∨ G = C.rot F₀}
  | .step T ω =>
    {G | ∃ A ∈ reversalFamily T, G = C.comp A ω ∨ G = C.comp A (C.markRot ω)}

/-- A complete source-minimal tower.  The predicate `smc A ω` says that `(A, ω)` is a proper
legal chart of `A ∘_ω E` that is source-minimal at that diagram.  The terminal factor is
chartless, and every stage is a source-minimal chart of the diagram built so far. -/
inductive IsCompleteTower (smc : D → M → Prop) : Tower D M → Prop where
  | terminal (F₀ : D) : F₀ ∉ C.rooted → IsCompleteTower smc (.terminal F₀)
  | step {T : Tower D M} {ω : M} :
      IsCompleteTower smc T → smc (C.top T) ω → IsCompleteTower smc (.step T ω)

/-- **`thm:necessity-reduction`, the second assertion implies the third.**  If (TR) and (RI) hold
in every Schur class, every prescribed complete source-minimal tower has reversal family equal
to the full Schur class of its source.

The proof is the induction of the paper.  The inputs from the other layers are:
`hcl` is `thm:gluing`; `hkey` is `prop:component-key`; `hdom` is `thm:source-minimal-domination`
(the component of `F` in `Γ⁺` is the fiber of any source-minimal chart); `hsmc_outer` says a
proper chart has an outer with at least two cells.  The reverse inclusion for the fiber, that
the fiber lies in one Schur class, is not needed here: `hdom` already identifies the fiber with
a component of `Γ⁺`, which lies in one class (`schur_eq_of_augmented_reachable`). -/
theorem reversalFamily_eq_class (smc : D → M → Prop)
    (hsmc_outer : ∀ A ω, smc A ω → 2 ≤ C.cells A)
    (hdom : ∀ A ω, smc A ω → ∀ G,
      C.toRotationData.augmented.Reachable (C.comp A ω) G ↔ G ∈ C.fiber ω (C.schur A))
    (hcl : ComponentsAreCliques C.graph) (hkey : C.KeyClassifiesComponents)
    (hTR : C.TerminalRigidity) (hRI : C.RootedKeyInvariance) :
    ∀ T : Tower D M, IsCompleteTower C smc T →
      C.reversalFamily T = {G | C.schur G = C.schur (C.top T)} := by
  intro T hT
  induction hT with
  | terminal F₀ hF₀ =>
    ext G
    simp only [reversalFamily, top, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | rfl)
      · rfl
      · exact C.schur_rot _
    · exact fun h => hTR F₀ hF₀ G h
  | @step T ω hT hsmc ih =>
    ext G
    have hcells : 2 ≤ C.cells (C.top T) := hsmc_outer _ _ hsmc
    have hclass : C.schur G = C.schur (C.comp (C.top T) ω) ↔ G ∈ C.fiber ω (C.schur (C.top T)) := by
      rw [← hdom _ _ hsmc]
      exact ⟨fun h => C.augmented_reachable_of_schur_eq hcl hkey hTR hRI h,
        C.schur_eq_of_augmented_reachable⟩
    simp only [top, Set.mem_ofPred_eq]
    rw [hclass]
    simp only [reversalFamily, fiber, ih, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨A, hA, hG⟩
      exact ⟨A, (C.cells_eq _ _ hA).symm ▸ hcells, hA, hG⟩
    · rintro ⟨A, -, hA, hG⟩
      exact ⟨A, hA, hG⟩

/-- **`thm:necessity-reduction`, the third assertion gives a common presentation.**  Under the
hypotheses of `reversalFamily_eq_class`, and given that every diagram has a complete
source-minimal tower (`htower`: the choice of a source-minimal chart, repeated on the actual
outer, terminates by the span law `N_F = p N_D + w > N_D`), every Schur-equal pair lies in the
reversal family of one complete source-minimal tower, namely a tower of either of them. -/
theorem exists_common_tower (smc : D → M → Prop)
    (hsmc_outer : ∀ A ω, smc A ω → 2 ≤ C.cells A)
    (hdom : ∀ A ω, smc A ω → ∀ G,
      C.toRotationData.augmented.Reachable (C.comp A ω) G ↔ G ∈ C.fiber ω (C.schur A))
    (hcl : ComponentsAreCliques C.graph) (hkey : C.KeyClassifiesComponents)
    (hTR : C.TerminalRigidity) (hRI : C.RootedKeyInvariance)
    (htower : ∀ F : D, ∃ T : Tower D M, IsCompleteTower C smc T ∧ C.top T = F)
    {F G : D} (h : C.schur F = C.schur G) :
    ∃ T : Tower D M, IsCompleteTower C smc T ∧
      F ∈ C.reversalFamily T ∧ G ∈ C.reversalFamily T := by
  obtain ⟨T, hT, rfl⟩ := htower F
  have := C.reversalFamily_eq_class smc hsmc_outer hdom hcl hkey hTR hRI T hT
  refine ⟨T, hT, ?_, ?_⟩
  · rw [this]; rfl
  · rw [this]; exact h.symm

end CompositionModel

end SkewGluing
