import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import SkewGluing.CellProfile
import SkewGluing.Irreducibility
import SkewGluing.RowInvariants
import SkewGluing.SchurBridge

/-!
# The skew Schur function of a cell diagram

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the paragraph on profiles: the function of a skew diagram is the product of the nonconstant
functions of its connected components, so every diagram with the same function as a connected
diagram is connected, and Schur-equal connected diagrams have the same span; and
«Source-minimal fibers» (`sec:minimal-fibers`), the class of the hook.

* `edgeComponents D`, `connectedSchur`, `cellSchur D`: the edge-connected components of a cell
  diagram and the function `s_D`, the product over the components of the Jacobi--Trudi function of
  their profiles (empty diagram `↦ 1`).
* `cellSchur_translate`, `cellSchur_rotate`, `cellSchur_transpose`, `cellSchur_antitranspose`:
  `s` is translation invariant, `s_{D*} = s_D`, `s_{Dᵗ} = s_{AT(D)} = ι(s_D)`.
* `isWeightedHomogeneous_cellSchur`: `s_D` is homogeneous of degree the number of cells.
* `isConnectedSkew_of_cellSchur_eq`: a skew diagram with the function of a connected diagram is
  connected (`barekatIrreducibility`).
* `span_eq_of_cellSchur_eq`: Schur-equal connected diagrams have equal span
  (`reinerRowInvariants`, and `ι` for the columns).
* `cellSchur_eq_hook_iff`: the diagrams with function `h₁ h₂ - h₃` are the translates of the hook
  `(2, 1)` and its rotation.
* `aeval_cellSchur_skewDiagram`: for a connected skew diagram `λ / μ`, `s_D` specializes to the
  tableau skew Schur polynomial.  For a skew diagram that is not connected, `cellSchur` is the
  product of the component functions by definition; agreement with the tableau definition for
  every skew shape is `aeval_cellSchur_skewDiagram_all` in `SkewGluing.CellSchurTableau`.

Sorry-free.
-/

namespace SkewGluing

attribute [local instance 10] Classical.propDecidable

/-! ### Edge-connected edgeComponents -/

/-- The edge-connected edgeComponents of a diagram: the classes of cells joined by chains of cells
of the diagram sharing edges. -/
noncomputable def edgeComponents (D : Diagram) : Finset Diagram :=
  D.image fun x => D.filter fun y => DiagReach D x y

section Components

variable {D : Diagram}

theorem mem_edgeComponents {C : Diagram} :
    C ∈ edgeComponents D ↔ ∃ x ∈ D, C = D.filter fun y => DiagReach D x y := by
  simp only [edgeComponents, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem DiagReach.mono {D' : Diagram} (hD : D ⊆ D') {x y : ℤ × ℤ} (h : DiagReach D x y) :
    DiagReach D' x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨hD hab.1, hD hab.2.1, hab.2.2⟩) x y h

theorem component_subset {C : Diagram} (hC : C ∈ edgeComponents D) : C ⊆ D := by
  obtain ⟨x, hx, rfl⟩ := mem_edgeComponents.mp hC
  exact Finset.filter_subset _ _

theorem component_reach {x y : ℤ × ℤ} (h : DiagReach D x y) :
    DiagReach (D.filter fun z => DiagReach D x z) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hbc ih =>
    refine Relation.ReflTransGen.tail ih ⟨?_, ?_, hbc.2.2⟩
    · exact Finset.mem_filter.mpr ⟨hbc.1, hxb⟩
    · exact Finset.mem_filter.mpr ⟨hbc.2.1, hxb.tail hbc⟩

theorem isEdgeConnected_component {C : Diagram} (hC : C ∈ edgeComponents D) :
    IsEdgeConnected C := by
  obtain ⟨x, hx, rfl⟩ := mem_edgeComponents.mp hC
  have hxm : x ∈ D.filter fun z => DiagReach D x z :=
    Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
  refine isEdgeConnected_of_reach hxm fun y hy => ?_
  exact component_reach (Finset.mem_filter.mp hy).2

theorem component_nonempty {C : Diagram} (hC : C ∈ edgeComponents D) : C.Nonempty :=
  (isEdgeConnected_component hC).1

theorem component_eq_of_mem {C : Diagram} (hC : C ∈ edgeComponents D) {z : ℤ × ℤ} (hz : z ∈ C) :
    C = D.filter fun y => DiagReach D z y := by
  obtain ⟨x, hx, rfl⟩ := mem_edgeComponents.mp hC
  obtain ⟨hzD, hxz⟩ := Finset.mem_filter.mp hz
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hxy⟩
    exact ⟨hy, hxz.symm.trans hxy⟩
  · rintro ⟨hy, hzy⟩
    exact ⟨hy, hxz.trans hzy⟩

theorem edgeComponents_disjoint {C C' : Diagram} (hC : C ∈ edgeComponents D)
    (hC' : C' ∈ edgeComponents D)
    (hne : C ≠ C') : Disjoint C C' := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hne ((component_eq_of_mem hC hz).trans (component_eq_of_mem hC' hz').symm)

/-- The components of a diagram partition it. -/
theorem biUnion_edgeComponents : (edgeComponents D).biUnion id = D := by
  ext z
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨C, hC, hz⟩
    exact component_subset hC hz
  · intro hz
    refine ⟨D.filter fun y => DiagReach D z y, mem_edgeComponents.mpr ⟨z, hz, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hz, Relation.ReflTransGen.refl⟩

/-- The number of cells is the sum of the numbers of cells of the components. -/
theorem card_eq_sum_edgeComponents : D.card = ∑ C ∈ edgeComponents D, C.card := by
  conv_lhs => rw [← biUnion_edgeComponents (D := D)]
  rw [Finset.card_biUnion]
  · rfl
  · intro C hC C' hC' hne
    exact edgeComponents_disjoint hC hC' hne

end Components

section SkewComponents

variable {D : Diagram}

/-- Cells in one column of a skew diagram are joined by a chain inside the column. -/
theorem IsSkew.reach_col (hs : IsSkew D) {a b c : ℤ} (ha : (a, c) ∈ D) (hb : (b, c) ∈ D) :
    DiagReach D (a, c) (b, c) := by
  have key : ∀ a b : ℤ, a ≤ b → (a, c) ∈ D → (b, c) ∈ D → DiagReach D (a, c) (b, c) := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => intro _ _; exact Relation.ReflTransGen.refl
    | succ b hab ih =>
      intro ha hb
      have hb' : (b, c) ∈ D := hs.mem ha hb (by omega) (le_refl c) (by omega) (by omega)
        (le_refl c) (le_refl c)
      refine Relation.ReflTransGen.tail (ih ha hb') ⟨hb', hb, ?_⟩
      rw [cellAdj_iff]; simp
  rcases le_total a b with h | h
  · exact key a b h ha hb
  · exact (key b a h hb ha).symm

/-- In a skew diagram, two cells related by `≤` in both coordinates are joined by a chain inside
the rectangle they span. -/
theorem IsSkew.reach_rect (hs : IsSkew D) {x y : ℤ × ℤ} (hx : x ∈ D) (hy : y ∈ D)
    (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) {i j : ℤ} (hi1 : x.1 ≤ i) (hi2 : i ≤ y.1)
    (hj1 : x.2 ≤ j) (hj2 : j ≤ y.2) : DiagReach D x (i, j) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at *
  have hz : (a, j) ∈ D := hs.mem hx hy h1 h2 (le_refl a) h1 (by omega) (by omega)
  have hw : (i, j) ∈ D := hs.mem hx hy h1 h2 (by omega) (by omega) (by omega) (by omega)
  exact (hs.reach_row hx hz).trans (hs.reach_col hz hw)

/-- Every component of a skew diagram is skew. -/
theorem isSkew_component (hs : IsSkew D) {C : Diagram} (hC : C ∈ edgeComponents D) : IsSkew C := by
  obtain ⟨x0, hx0, rfl⟩ := mem_edgeComponents.mp hC
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxD, hx0x⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyD, -⟩ := Finset.mem_filter.mp hy
  simp only [Finset.mem_Icc] at hi hj
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact hs.mem (a := x.1) (b := x.2) (c := y.1) (d := y.2) hxD hyD h1 h2 hi.1 hi.2 hj.1 hj.2
  · exact hx0x.trans (hs.reach_rect hxD hyD h1 h2 hi.1 hi.2 hj.1 hj.2)

/-- Every component of a skew diagram is a connected skew diagram. -/
theorem isConnectedSkew_component (hs : IsSkew D) {C : Diagram} (hC : C ∈ edgeComponents D) :
    IsConnectedSkew C :=
  ⟨isSkew_component hs hC, isEdgeConnected_component hC⟩

/-- A connected diagram is its own unique component. -/
theorem edgeComponents_eq_singleton (hD : IsEdgeConnected D) : edgeComponents D = {D} := by
  ext C
  rw [Finset.mem_singleton, mem_edgeComponents]
  constructor
  · rintro ⟨x, hx, rfl⟩
    ext y
    rw [Finset.mem_filter]
    exact ⟨fun h => h.1, fun hy => ⟨hy, hD.2 x hx y hy⟩⟩
  · rintro rfl
    obtain ⟨x, hx⟩ := hD.1
    refine ⟨x, hx, ?_⟩
    ext y
    rw [Finset.mem_filter]
    exact ⟨fun hy => ⟨hy, hD.2 x hx y hy⟩, fun h => h.1⟩

/-- The empty diagram has no components. -/
theorem edgeComponents_empty : edgeComponents (∅ : Diagram) = ∅ := by
  simp [edgeComponents]

end SkewComponents

/-! ### The function of a cell diagram -/

/-- The skew Schur function of a connected skew diagram: the Jacobi--Trudi determinant of its
profile.  The value `1` is a placeholder off connected skew diagrams. -/
noncomputable def connectedSchur (D : Diagram) : Lambda :=
  if IsConnectedSkew D then (cellProfile D).2.schur else 1

/-- **The skew Schur function `s_D` of a cell diagram**: the product, over its edge-connected
edgeComponents, of the Jacobi--Trudi function of the component's profile; the empty diagram has
function `1`.  This is the skew Schur function of a skew diagram (connected or not) of the
paper. -/
noncomputable def cellSchur (D : Diagram) : Lambda := ∏ C ∈ edgeComponents D, connectedSchur C

/-- On a connected skew diagram, `connectedSchur` is the Jacobi--Trudi function of the profile. -/
theorem connectedSchur_of_isConnectedSkew {D : Diagram} (hD : IsConnectedSkew D) :
    connectedSchur D = (cellProfile D).2.schur := by
  simp [connectedSchur, hD]

/-- On a connected skew diagram, `s_D` is the Jacobi--Trudi function of its profile. -/
theorem cellSchur_of_isConnectedSkew {D : Diagram} (hD : IsConnectedSkew D) :
    cellSchur D = (cellProfile D).2.schur := by
  rw [cellSchur, edgeComponents_eq_singleton hD.2, Finset.prod_singleton,
    connectedSchur_of_isConnectedSkew hD]

/-- The empty diagram has function `1`. -/
@[simp]
theorem cellSchur_empty : cellSchur ∅ = 1 := by
  simp [cellSchur, edgeComponents_empty]

/-- The function of the cell diagram of a profile is its Jacobi--Trudi function. -/
theorem cellSchur_cells {n : ℕ} (P : Profile n) : cellSchur P.cells = P.schur := by
  rw [cellSchur_of_isConnectedSkew P.isConnectedSkew_cells, cellProfile_cells]

/-- The product formula: `s_D` is the product of the Jacobi--Trudi functions of the profiles of
the components. -/
theorem cellSchur_eq_prod {D : Diagram} (hD : IsSkew D) :
    cellSchur D = ∏ C ∈ edgeComponents D, (cellProfile C).2.schur :=
  Finset.prod_congr rfl fun _ hC =>
    connectedSchur_of_isConnectedSkew (isConnectedSkew_component hD hC)

/-! ### Adjacency-preserving bijections and edgeComponents -/

section Maps

variable (g : (ℤ × ℤ) ≃ (ℤ × ℤ)) (hg : ∀ a b, CellAdj (g a) (g b) ↔ CellAdj a b)
include hg

theorem diagReach_image_of {D : Diagram} {x y : ℤ × ℤ} (h : DiagReach D x y) :
    DiagReach (D.image g) (g x) (g y) := by
  refine Relation.ReflTransGen.lift g (p := fun a b => a ∈ D.image g ∧ b ∈ D.image g ∧ CellAdj a b)
    ?_ x y h
  intro a b hab
  exact ⟨Finset.mem_image_of_mem _ hab.1, Finset.mem_image_of_mem _ hab.2.1, (hg a b).mpr hab.2.2⟩

theorem diagReach_image_iff {D : Diagram} {x y : ℤ × ℤ} :
    DiagReach (D.image g) (g x) (g y) ↔ DiagReach D x y := by
  refine ⟨fun h => ?_, diagReach_image_of g hg⟩
  have hg' : ∀ a b, CellAdj (g.symm a) (g.symm b) ↔ CellAdj a b := fun a b => by
    rw [← hg (g.symm a) (g.symm b)]; simp
  have := diagReach_image_of g.symm hg' h
  have e : (D.image g).image g.symm = D := by
    have : (g.symm ∘ g) = id := by funext x; simp
    rw [Finset.image_image, this, Finset.image_id]
  simpa [e] using this

/-- Components are carried by an adjacency-preserving bijection of the plane. -/
theorem edgeComponents_image (D : Diagram) :
    edgeComponents (D.image g) = (edgeComponents D).image (Finset.image g) := by
  unfold edgeComponents
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun x hx => ?_
  ext w
  simp only [Function.comp, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hr⟩
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨y, ⟨hy, (diagReach_image_iff g hg).mp hr⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hxy⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (diagReach_image_iff g hg).mpr hxy⟩

omit hg in
theorem card_image_equiv (D : Diagram) : (D.image g).card = D.card :=
  Finset.card_image_of_injective _ g.injective

end Maps

/-! ### Invariance and the involution -/

theorem cellAdj_add_iff (v a b : ℤ × ℤ) : CellAdj (a + v) (b + v) ↔ CellAdj a b := by
  simp only [cellAdj_iff, Prod.fst_add, Prod.snd_add]
  omega

theorem cellAdj_neg_iff (a b : ℤ × ℤ) : CellAdj (-a) (-b) ↔ CellAdj a b := by
  simp only [cellAdj_iff, Prod.fst_neg, Prod.snd_neg]
  omega

theorem cellAdj_swap_iff (a b : ℤ × ℤ) : CellAdj a.swap b.swap ↔ CellAdj a b := by
  simp only [cellAdj_iff, Prod.fst_swap, Prod.snd_swap]
  omega

/-- The components of a translate are the translates of the components. -/
theorem edgeComponents_translate (v : ℤ × ℤ) (D : Diagram) :
    edgeComponents (translate v D) = (edgeComponents D).image (translate v) :=
  edgeComponents_image (Equiv.addRight v) (fun a b => cellAdj_add_iff v a b) D

/-- The components of the rotation are the rotations of the components. -/
theorem edgeComponents_rotate (D : Diagram) :
    edgeComponents (rotate D) = (edgeComponents D).image rotate :=
  edgeComponents_image (Equiv.neg (ℤ × ℤ)) cellAdj_neg_iff D

/-- The components of the transpose are the transposes of the components. -/
theorem edgeComponents_transpose (D : Diagram) :
    edgeComponents (transpose D) = (edgeComponents D).image transpose :=
  edgeComponents_image (Equiv.prodComm ℤ ℤ) cellAdj_swap_iff D

theorem translate_injective' (v : ℤ × ℤ) : Function.Injective (translate v) :=
  fun _ _ h => translate_injective v h

theorem rotate_injective : Function.Injective rotate := fun A B h => by
  rw [← rotate_rotate (D := A), h, rotate_rotate]

theorem transpose_injective : Function.Injective transpose := fun A B h => by
  rw [← transpose_transpose (D := A), h, transpose_transpose]

theorem isConnectedSkew_translate_iff (v : ℤ × ℤ) {D : Diagram} :
    IsConnectedSkew (translate v D) ↔ IsConnectedSkew D := by
  refine ⟨fun h => ?_, isConnectedSkew_translate v⟩
  have := isConnectedSkew_translate (-v) h
  rwa [translate_neg_translate_cancel] at this

theorem isConnectedSkew_rotate_iff {D : Diagram} : IsConnectedSkew (rotate D) ↔ IsConnectedSkew D :=
  ⟨fun h => by simpa [rotate_rotate] using isConnectedSkew_rotate h, isConnectedSkew_rotate⟩

theorem isConnectedSkew_transpose_iff {D : Diagram} :
    IsConnectedSkew (transpose D) ↔ IsConnectedSkew D :=
  ⟨fun h => by simpa [transpose_transpose] using isConnectedSkew_transpose h,
    isConnectedSkew_transpose⟩

/-- `connectedSchur` is translation invariant. -/
theorem connectedSchur_translate (v : ℤ × ℤ) (C : Diagram) :
    connectedSchur (translate v C) = connectedSchur C := by
  by_cases hC : IsConnectedSkew C
  · rw [connectedSchur_of_isConnectedSkew hC,
      connectedSchur_of_isConnectedSkew ((isConnectedSkew_translate_iff v).mpr hC),
      cellProfile_translate hC]
  · simp [connectedSchur, hC, isConnectedSkew_translate_iff]

/-- `connectedSchur` is invariant under rotation. -/
theorem connectedSchur_rotate (C : Diagram) : connectedSchur (rotate C) = connectedSchur C := by
  by_cases hC : IsConnectedSkew C
  · rw [connectedSchur_of_isConnectedSkew hC,
      connectedSchur_of_isConnectedSkew (isConnectedSkew_rotate hC), cellProfile_rotate hC,
      Profile.schur_rotate]
  · simp [connectedSchur, hC, isConnectedSkew_rotate_iff]

/-- `connectedSchur` of the transpose is the image under `ι`. -/
theorem connectedSchur_transpose (C : Diagram) :
    connectedSchur (transpose C) = schurInvolution (connectedSchur C) := by
  by_cases hC : IsConnectedSkew C
  · rw [connectedSchur_of_isConnectedSkew hC,
      connectedSchur_of_isConnectedSkew (isConnectedSkew_transpose hC), cellProfile_transpose hC,
      schurInvolution_schur_transpose]
    rfl
  · simp [connectedSchur, hC, isConnectedSkew_transpose_iff]

/-- **`s` is translation invariant.** -/
theorem cellSchur_translate (v : ℤ × ℤ) (D : Diagram) :
    cellSchur (translate v D) = cellSchur D := by
  unfold cellSchur
  rw [edgeComponents_translate, Finset.prod_image fun A _ B _ h => translate_injective' v h]
  exact Finset.prod_congr rfl fun C _ => connectedSchur_translate v C

/-- **`s_{D*} = s_D`.** -/
theorem cellSchur_rotate (D : Diagram) : cellSchur (rotate D) = cellSchur D := by
  unfold cellSchur
  rw [edgeComponents_rotate, Finset.prod_image fun A _ B _ h => rotate_injective h]
  exact Finset.prod_congr rfl fun C _ => connectedSchur_rotate C

/-- **`s_{Dᵗ} = ι(s_D)`.** -/
theorem cellSchur_transpose (D : Diagram) :
    cellSchur (transpose D) = schurInvolution (cellSchur D) := by
  unfold cellSchur
  rw [edgeComponents_transpose, Finset.prod_image fun A _ B _ h => transpose_injective h, map_prod]
  exact Finset.prod_congr rfl fun C _ => connectedSchur_transpose C

/-- **`s_{AT(D)} = ι(s_D)`.** -/
theorem cellSchur_antitranspose (D : Diagram) :
    cellSchur (antitranspose D) = schurInvolution (cellSchur D) := by
  rw [antitranspose_eq_rotate_transpose, cellSchur_rotate, cellSchur_transpose]

/-! ### Homogeneity -/

open MvPolynomial

/-- The weight `h_k ↦ k` that grades `Λ` by degree. -/
def degWeight : ℕ+ → ℕ := fun k => (k : ℕ)

/-- `h_j` is homogeneous of degree `j` for `j ≥ 0`. -/
theorem isWeightedHomogeneous_hh {j : ℤ} (hj : 0 ≤ j) :
    IsWeightedHomogeneous degWeight (hh j) j.toNat := by
  have e : hh j = hPos j.toNat := by simp [hh, not_lt.mpr hj]
  rw [e]
  by_cases h : 0 < j.toNat
  · simp only [hPos, h, dite_true]
    exact isWeightedHomogeneous_X ℚ degWeight (⟨j.toNat, h⟩ : ℕ+)
  · have h0 : j.toNat = 0 := by omega
    rw [h0]
    simpa [hPos] using isWeightedHomogeneous_one ℚ (σ := ℕ+) degWeight

/-- The Jacobi--Trudi function of a profile is homogeneous of degree the sum of its row lengths. -/
theorem Profile.isWeightedHomogeneous_schur {n : ℕ} (P : Profile n) :
    IsWeightedHomogeneous degWeight P.schur (∑ i, P.r i) := by
  unfold Profile.schur
  rw [Matrix.det_apply']
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Lambda)).IsWeightedHomogeneous degWeight 0 := by
    rw [show ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Lambda)) =
      C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) by simp]
    exact isWeightedHomogeneous_C degWeight _
  have h2 : (∏ i : Fin (n + 1), (Matrix.of fun i j : Fin (n + 1) =>
      hh (P.xi i - P.zeta j)) (σ i) i).IsWeightedHomogeneous degWeight (∑ i, P.r i) := by
    by_cases hneg : ∃ i, P.xi (σ i) - P.zeta i < 0
    · obtain ⟨i, hi⟩ := hneg
      have : ∏ i : Fin (n + 1), (Matrix.of fun i j : Fin (n + 1) =>
          hh (P.xi i - P.zeta j)) (σ i) i = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hh_of_neg hi])
      rw [this]
      exact isWeightedHomogeneous_zero ℚ degWeight _
    · push Not at hneg
      have := IsWeightedHomogeneous.prod Finset.univ
        (fun i : Fin (n + 1) => (Matrix.of fun i j : Fin (n + 1) =>
          hh (P.xi i - P.zeta j)) (σ i) i)
        (fun i => (P.xi (σ i) - P.zeta i).toNat)
        (fun i _ => isWeightedHomogeneous_hh (hneg i))
      convert this using 1
      have hsum : ∑ i, ((P.xi (σ i) - P.zeta i).toNat : ℤ) = ∑ i, (P.r i : ℤ) := by
        rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hneg i),
          Finset.sum_sub_distrib]
        rw [Equiv.sum_comp σ P.xi, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => P.xi_sub_zeta i
      exact_mod_cast hsum.symm
  simpa using h1.mul h2

/-- The cell diagram of a profile has `∑ r_i` cells. -/
theorem Profile.card_cells {n : ℕ} (P : Profile n) : P.cells.card = ∑ i, P.r i := by
  unfold Profile.cells
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Int.card_Ico]
    have := P.xi_sub_zeta i
    omega
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx'
    simp only [Prod.mk.injEq] at hb
    exact hij (Fin.ext (by exact_mod_cast hb.1.symm))

/-- The function of a connected skew diagram is homogeneous of degree its number of cells. -/
theorem isWeightedHomogeneous_connectedSchur {C : Diagram} (hC : IsConnectedSkew C) :
    IsWeightedHomogeneous degWeight (connectedSchur C) C.card := by
  rw [connectedSchur_of_isConnectedSkew hC]
  obtain ⟨v, hv⟩ := hC.exists_translate_cells
  have e : C.card = (cellProfile C).2.cells.card := by
    conv_lhs => rw [hv]
    exact Finset.card_image_of_injective _ (add_left_injective _)
  rw [e, Profile.card_cells]
  exact Profile.isWeightedHomogeneous_schur _

/-- **Homogeneity.**  The function of a skew diagram is homogeneous of degree the number of its
cells. -/
theorem isWeightedHomogeneous_cellSchur {D : Diagram} (hD : IsSkew D) :
    IsWeightedHomogeneous degWeight (cellSchur D) D.card := by
  rw [card_eq_sum_edgeComponents (D := D), cellSchur]
  exact IsWeightedHomogeneous.prod _ _ _ fun C hC =>
    isWeightedHomogeneous_connectedSchur (isConnectedSkew_component hD hC)

/-! ### Irreducibility and connectedness -/

theorem eq_singleton_of_irreducible_prod {ι : Type*} (s : Finset ι) (f : ι → Lambda)
    (hf : ∀ i ∈ s, Irreducible (f i)) (h : Irreducible (∏ i ∈ s, f i)) : ∃ i, s = {i} := by
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have h1 : Irreducible (1 : Lambda) := by simpa only [Finset.prod_empty] using h
    exact not_irreducible_one h1
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, ?_⟩
  rw [← Finset.mul_prod_erase s f hi] at h
  have hunit : IsUnit (∏ j ∈ s.erase i, f j) := by
    rcases h.isUnit_or_isUnit rfl with h1 | h1
    · exact absurd h1 (hf i hi).not_isUnit
    · exact h1
  by_contra hne
  have : (s.erase i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hne
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hxi
      have : x ∈ s.erase i := Finset.mem_erase.mpr ⟨hxi, hx⟩
      rw [he] at this
      simp at this
    · rintro rfl; exact hi
  obtain ⟨j, hj⟩ := this
  have hdvd : f j ∣ ∏ k ∈ s.erase i, f k := Finset.dvd_prod_of_mem f hj
  exact (hf j (Finset.mem_of_mem_erase hj)).not_isUnit (isUnit_of_dvd_unit hdvd hunit)

/-- **Every skew diagram with the same function as a connected diagram is connected** (from the
irreducibility of the function of a connected diagram and the product formula). -/
theorem isConnectedSkew_of_cellSchur_eq {D D' : Diagram} (hD : IsConnectedSkew D)
    (hD' : IsSkew D') (h : cellSchur D' = cellSchur D) : IsConnectedSkew D' := by
  have hirr : Irreducible (∏ C ∈ edgeComponents D', (cellProfile C).2.schur) := by
    rw [← cellSchur_eq_prod hD', h, cellSchur_of_isConnectedSkew hD]
    exact barekatIrreducibility _ _
  obtain ⟨C, hC⟩ := eq_singleton_of_irreducible_prod (edgeComponents D') _
    (fun C _ => barekatIrreducibility _ _) hirr
  have hmem : C ∈ edgeComponents D' := by rw [hC]; exact Finset.mem_singleton_self C
  have hU := biUnion_edgeComponents (D := D')
  rw [hC, Finset.singleton_biUnion] at hU
  rw [← hU]
  exact isConnectedSkew_component hD' hmem

/-! ### Schur-equal connected diagrams have equal span -/

/-- Schur-equal connected diagrams have the same number of rows (`reinerRowInvariants`). -/
theorem numRows_eq_of_cellSchur_eq {C C' : Diagram} (hC : IsConnectedSkew C)
    (hC' : IsConnectedSkew C') (h : cellSchur C = cellSchur C') : numRows C = numRows C' := by
  rw [cellSchur_of_isConnectedSkew hC, cellSchur_of_isConnectedSkew hC'] at h
  have := (reinerRowInvariants _ _ _ _ h).1
  have h1 := (cellProfile_spec hC).1
  have h2 := (cellProfile_spec hC').1
  omega

/-- Schur-equal connected diagrams have the same number of columns: the transposes have equal
functions, by the involution. -/
theorem numCols_eq_of_cellSchur_eq {C C' : Diagram} (hC : IsConnectedSkew C)
    (hC' : IsConnectedSkew C') (h : cellSchur C = cellSchur C') : numCols C = numCols C' := by
  apply numRows_eq_of_cellSchur_eq (isConnectedSkew_transpose hC) (isConnectedSkew_transpose hC')
  rw [cellSchur_transpose, cellSchur_transpose, h]

/-- **Schur-equal connected outers have equal span**: they have the same number of rows and of
columns, and the span of a connected diagram is one less than their sum. -/
theorem span_eq_of_cellSchur_eq {C C' : Diagram} (hC : IsConnectedSkew C)
    (hC' : IsConnectedSkew C') (h : cellSchur C = cellSchur C') : span C = span C' := by
  have h1 := span_add_one_eq_numRows_add_numCols hC
  have h2 := span_add_one_eq_numRows_add_numCols hC'
  have h3 := numRows_eq_of_cellSchur_eq hC hC' h
  have h4 := numCols_eq_of_cellSchur_eq hC hC' h
  omega

/-! ### The three-cell class -/

theorem hook_cells_eq : hookProfile.cells = translate (0, 1) (skewOf [2, 1] []) := by decide

theorem hookRotated_cells_eq :
    hookRotatedProfile.cells = translate (0, 1) (skewOf [2, 2] [1]) := by decide

/-- `s_{(2,1)} = h₁ h₂ - h₃` on cells. -/
theorem cellSchur_hook : cellSchur (skewOf [2, 1] []) = X 1 * X 2 - X 3 := by
  have : skewOf [2, 1] [] = translate (0, -1) hookProfile.cells := by decide
  rw [this, cellSchur_translate, cellSchur_cells, schur_hook]

/-- `s_{(2,2)/(1)} = h₁ h₂ - h₃` on cells. -/
theorem cellSchur_hookRotated : cellSchur (skewOf [2, 2] [1]) = X 1 * X 2 - X 3 := by
  have : skewOf [2, 2] [1] = translate (0, -1) hookRotatedProfile.cells := by decide
  rw [this, cellSchur_translate, cellSchur_cells, schur_hookRotated]

/-- A profile with the function `h₁ h₂ - h₃` is the hook or the rotated hook. -/
theorem profile_eq_hook_or_rotated (G : AnyProfile) (h : G.2.schur = hookProfile.schur) :
    G = ⟨1, hookProfile⟩ ∨ G = ⟨1, hookRotatedProfile⟩ := by
  obtain ⟨m, P⟩ := G
  obtain ⟨hm, hr, hg⟩ := reinerRowInvariants m 1 P hookProfile h
  subst hm
  have hmem : ∀ i, P.r i = 2 ∨ P.r i = 1 := by
    intro i
    have : P.r i ∈ hookProfile.rowMultiset := by
      rw [← hr]; exact Profile.mem_rowMultiset.mpr ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := Profile.mem_rowMultiset.mp this
    fin_cases j <;> simp [hookProfile] at hj <;> omega
  have h2 : ∃ i, P.r i = 2 := by
    have : (2 : ℕ) ∈ P.rowMultiset := by
      rw [hr]; exact Profile.mem_rowMultiset.mpr ⟨0, rfl⟩
    exact Profile.mem_rowMultiset.mp this
  have h1 : ∃ i, P.r i = 1 := by
    have : (1 : ℕ) ∈ P.rowMultiset := by
      rw [hr]; exact Profile.mem_rowMultiset.mpr ⟨1, rfl⟩
    exact Profile.mem_rowMultiset.mp this
  have hg0 : P.g 0 = 0 := by
    have : P.g 0 ∈ hookProfile.gapMultiset := by
      rw [← hg]; exact Profile.mem_gapMultiset.mpr ⟨0, rfl⟩
    obtain ⟨j, hj⟩ := Profile.mem_gapMultiset.mp this
    fin_cases j
    simpa [hookProfile] using hj.symm
  obtain ⟨i2, hi2⟩ := h2
  obtain ⟨i1, hi1⟩ := h1
  have hr0 := hmem 0
  have hr1 := hmem 1
  have hne : i1 ≠ i2 := by rintro rfl; omega
  have hgfun : P.g = hookProfile.g := by
    funext j; fin_cases j; simpa [hookProfile] using hg0
  have key : (P.r 0 = 2 ∧ P.r 1 = 1) ∨ (P.r 0 = 1 ∧ P.r 1 = 2) := by
    fin_cases i1 <;> fin_cases i2 <;> simp at hi1 hi2 hne <;> omega
  rcases key with ⟨k0, k1⟩ | ⟨k0, k1⟩
  · left
    have : P = hookProfile :=
      Profile.ext (funext fun i => by fin_cases i <;> simp [hookProfile, k0, k1]) hgfun
    rw [this]
  · right
    have : P = hookRotatedProfile := Profile.ext
      (funext fun i => by fin_cases i <;> simp [hookRotatedProfile, k0, k1]) (by
        funext j; fin_cases j; simpa [hookRotatedProfile] using hg0)
    rw [this]

/-- **The class of the hook** (`sec:minimal-fibers`).  A finite skew diagram has function
`h₁ h₂ - h₃` exactly when it is a translate of the hook `H = (2, 1)` or of its rotation
`H* = (2, 2) / (1)`.

**Differs from the paper's route.**  Irreducibility and the row invariants give the two hooks
directly, with no restriction to three cells and no enumeration. -/
theorem cellSchur_eq_hook_iff {D : Diagram} (hD : IsSkew D) :
    cellSchur D = X 1 * X 2 - X 3 ↔
      (∃ v, D = translate v (skewOf [2, 1] [])) ∨ (∃ v, D = translate v (skewOf [2, 2] [1])) := by
  constructor
  · intro h
    have hH : IsConnectedSkew hookProfile.cells := hookProfile.isConnectedSkew_cells
    have hHs : cellSchur hookProfile.cells = X 1 * X 2 - X 3 := by
      rw [cellSchur_cells, schur_hook]
    have hconn : IsConnectedSkew D := isConnectedSkew_of_cellSchur_eq hH hD (h.trans hHs.symm)
    rw [cellSchur_of_isConnectedSkew hconn] at h
    have h' : (cellProfile D).2.schur = hookProfile.schur := by rw [h, schur_hook]
    have hpr := profile_eq_hook_or_rotated _ h'
    obtain ⟨v, hv⟩ := hconn.exists_translate_cells
    rcases hpr with hpr | hpr
    · left
      rw [hpr] at hv
      exact ⟨v + (0, 1), by rw [hv, show (⟨1, hookProfile⟩ : AnyProfile).2.cells = _ from
        hook_cells_eq, translate_translate]⟩
    · right
      rw [hpr] at hv
      exact ⟨v + (0, 1), by rw [hv, show (⟨1, hookRotatedProfile⟩ : AnyProfile).2.cells = _ from
        hookRotated_cells_eq, translate_translate]⟩
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · rw [cellSchur_translate, cellSchur_hook]
    · rw [cellSchur_translate, cellSchur_hookRotated]

/-! ### Agreement with the tableau skew Schur function -/

section Tableau

/-- The Young diagram `lam` with every row of its first `L` rows moved `c` columns to the right
and the vacated cells filled in: the rows of the result are `lam_i + c` for `i < L`. -/
def shiftRows (lam : YoungDiagram) (L c : ℕ) (hL : ∀ x ∈ lam, x.1 < L) : YoungDiagram where
  cells := lam.cells.image (fun x => (x.1, x.2 + c)) ∪ (Finset.range L ×ˢ Finset.range c)
  isLowerSet := by
    intro x y hyx hx
    rw [Finset.mem_coe, Finset.mem_union] at hx ⊢
    obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp (show (y.1, y.2) ≤ (x.1, x.2) from hyx)
    rcases hx with hx | hx
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      by_cases hy : y.2 < c
      · right
        have := hL z hz
        simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨by omega, hy⟩
      · left
        refine Finset.mem_image.mpr ⟨(y.1, y.2 - c), ?_, by ext <;> simp; omega⟩
        exact lam.isLowerSet (show (y.1, y.2 - c) ≤ z from
          Prod.mk_le_mk.mpr ⟨h1, by simp at h2; omega⟩) hz
    · right
      simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
      exact ⟨by omega, by omega⟩

/-- Membership in `shiftRows`. -/
theorem mem_shiftRows {lam : YoungDiagram} {L c : ℕ} {hL : ∀ x ∈ lam, x.1 < L} {a b : ℕ} :
    (a, b) ∈ shiftRows lam L c hL ↔ (a < L ∧ b < c) ∨ (c ≤ b ∧ (a, b - c) ∈ lam) := by
  change (a, b) ∈ (lam.cells.image (fun x => (x.1, x.2 + c)) ∪
    (Finset.range L ×ˢ Finset.range c)) ↔ _
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro (⟨z, hz, rfl, rfl⟩ | h)
    · right; exact ⟨by omega, by simpa using hz⟩
    · left; exact h
  · rintro (h | ⟨h1, h2⟩)
    · right; exact h
    · left; exact ⟨(a, b - c), h2, rfl, by omega⟩

/-- The cell diagram of the skew shape `λ / μ`, as a set of cells of `ℤ × ℤ`. -/
def skewDiagram (lam mu : YoungDiagram) : Diagram :=
  (Shields.skewCells lam mu).image fun c => ((c.1 : ℤ), (c.2 : ℤ))

/-- Membership in the cell diagram of a skew shape. -/
theorem mem_skewDiagram_nat {lam mu : YoungDiagram} (i j : ℕ) :
    ((i : ℤ), (j : ℤ)) ∈ skewDiagram lam mu ↔ (i, j) ∈ Shields.skewCells lam mu := by
  simp only [skewDiagram, Finset.mem_image, Prod.mk.injEq, Nat.cast_inj]
  constructor
  · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨(i, j), h, rfl, rfl⟩

theorem nat_cell_of_mem_skewDiagram {lam mu : YoungDiagram} {x : ℤ × ℤ}
    (h : x ∈ skewDiagram lam mu) : ∃ i j : ℕ, x = ((i : ℤ), (j : ℤ)) := by
  simp only [skewDiagram, Finset.mem_image] at h
  obtain ⟨⟨i, j⟩, -, rfl⟩ := h
  exact ⟨i, j, rfl⟩

/-- The skew cells of the shifted shapes are those of the shape moved `c` columns to the right. -/
theorem skewCells_shiftRows {lam mu : YoungDiagram} (hmu : mu ≤ lam) (L c : ℕ)
    (hL : ∀ x ∈ lam, x.1 < L) (a b : ℕ) :
    (a, b) ∈ Shields.skewCells (shiftRows lam L c hL) (shiftRows mu L c fun x hx => hL x (hmu hx))
      ↔ c ≤ b ∧ (a, b - c) ∈ Shields.skewCells lam mu := by
  rw [Shields.mem_skewCells, Shields.mem_skewCells, mem_shiftRows, mem_shiftRows]
  by_cases hb : b < c
  · constructor
    · rintro ⟨h1, h2⟩
      exfalso
      apply h2
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · omega
    · rintro ⟨h, -⟩; omega
  · push Not at hb
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨hb, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · omega
        · exact h1.2
      · intro hm
        exact h2 (Or.inr ⟨hb, hm⟩)
    · rintro ⟨-, h1, h2⟩
      refine ⟨Or.inr ⟨hb, h1⟩, ?_⟩
      rintro (h | h)
      · omega
      · exact h2 h.2

/-- The tableau skew Schur polynomial of `λ / μ` depends only on the cell diagram up to
translation: if the cell diagram of `λ / μ` is a translate of the cell diagram of a profile,
it is the tableau polynomial of the profile's shape. -/
theorem skewSchur_eq_of_translate {R : Type*} [CommRing R] {lam mu : YoungDiagram} (hmu : mu ≤ lam)
    {n : ℕ} (P : Profile n) (v : ℤ × ℤ) (hv : skewDiagram lam mu = translate v P.cells)
    (b : ℕ) (β : ℕ → R) : Shields.skewSchur lam mu b β = Shields.skewSchur P.lam P.mu b β := by
  set L := lam.colLen 0 with hLdef
  have hL : ∀ x ∈ lam, x.1 < L := by
    intro x hx
    rw [hLdef, ← YoungDiagram.mem_iff_lt_colLen]
    exact lam.isLowerSet
      (show ((x.1, 0) : ℕ × ℕ) ≤ x from Prod.mk_le_mk.mpr ⟨le_refl _, Nat.zero_le _⟩) hx
  set c : ℕ := (-v.2).toNat with hc
  have hvc : 0 ≤ v.2 + c := by omega
  have hv1 : 0 ≤ v.1 := by
    have e : (v.1, v.2 + P.zeta 0) - v = (0, P.zeta 0) := by ext <;> simp
    have h1 : (v.1, v.2 + P.zeta 0) ∈ skewDiagram lam mu := by
      rw [hv, mem_translate, e]; exact P.mem_cells_top
    obtain ⟨i, j, hij⟩ := nat_cell_of_mem_skewDiagram h1
    have := congrArg Prod.fst hij
    simp only at this
    omega
  set lam' := shiftRows lam L c hL with hlam'
  set mu' := shiftRows mu L c (fun x hx => hL x (hmu hx)) with hmu'
  -- step 1: shift `λ / μ` to the right by `c`
  have step1 : Shields.skewSchur lam' mu' b β = Shields.skewSchur lam mu b β := by
    refine Shields.skewSchur_translate (lam := lam') (mu := mu') (lam' := lam) (mu' := mu)
      (di := 0) (dj := c) (fun i j => ?_) (fun i j hc' => ?_) β
    · rw [Nat.add_zero, skewCells_shiftRows hmu L c hL i (j + c), Nat.add_sub_cancel]
      simp
    · have := (skewCells_shiftRows hmu L c hL i j).mp hc'
      exact ⟨Nat.zero_le _, this.1⟩
  -- the shifted shape is a translate of the cell diagram of the profile
  have hdiag : ∀ i j : ℕ, (i, j) ∈ Shields.skewCells lam' mu' ↔
      ((i : ℤ) - v.1, (j : ℤ) - (v.2 + c)) ∈ P.cells := by
    intro i j
    rw [skewCells_shiftRows hmu L c hL]
    have e : ((i : ℤ) - v.1, (j : ℤ) - (v.2 + c)) =
        ((i : ℤ), (j : ℤ) - c) - v := by ext <;> simp; ring
    rw [e, ← mem_translate, ← hv]
    constructor
    · rintro ⟨hj, h⟩
      have : ((j : ℤ) - c) = ((j - c : ℕ) : ℤ) := by push_cast [Nat.cast_sub hj]; ring
      rw [this]
      exact (mem_skewDiagram_nat i (j - c)).mpr h
    · intro h
      obtain ⟨i', j', hij⟩ := nat_cell_of_mem_skewDiagram h
      have h1 : (i : ℤ) = i' := congrArg Prod.fst hij
      have h2 : (j : ℤ) - c = j' := congrArg Prod.snd hij
      have hj : c ≤ j := by omega
      have hi : i = i' := by omega
      have hj' : j - c = j' := by omega
      subst hi hj'
      exact ⟨hj, (mem_skewDiagram_nat i (j - c)).mp (by
        have : ((j : ℤ) - c) = ((j - c : ℕ) : ℤ) := by push_cast [Nat.cast_sub hj]; ring
        rw [this] at h; exact h)⟩
  -- step 2: compare with the shape of the profile
  have step2 : Shields.skewSchur lam' mu' b β = Shields.skewSchur P.lam P.mu b β := by
    refine Shields.skewSchur_translate (lam := lam') (mu := mu') (lam' := P.lam) (mu' := P.mu)
      (di := v.1.toNat) (dj := (v.2 + c).toNat) (fun i j => ?_) (fun i j hc' => ?_) β
    · rw [hdiag]
      have e : (((i + v.1.toNat : ℕ) : ℤ) - v.1, ((j + (v.2 + c).toNat : ℕ) : ℤ) - (v.2 + c)) =
          ((i : ℤ), (j : ℤ)) := by
        push_cast
        rw [Int.toNat_of_nonneg hv1, Int.toNat_of_nonneg hvc]
        ext <;> simp
      rw [e, P.mem_cells_nat]
    · have h := (hdiag i j).mp hc'
      have h1 := P.row_of_mem_cells h
      have h2 := P.nonneg_col_of_mem_cells h
      simp only at h1 h2
      omega
  rw [← step1, step2]

/-- **Agreement with the tableau skew Schur function** for a connected skew diagram.  If the cell
diagram of `λ / μ` is connected, then specializing `h_k` to the complete homogeneous polynomial
in `b` variables sends `s_D`, `D = λ / μ`, to the tableau skew Schur polynomial of `λ / μ`.  The
shape `λ / μ` may sit anywhere in the quadrant. -/
theorem aeval_cellSchur_skewDiagram {R : Type*} [CommRing R] [Algebra ℚ R] {lam mu : YoungDiagram}
    (hmu : mu ≤ lam) (hD : IsConnectedSkew (skewDiagram lam mu)) (b : ℕ) (β : ℕ → R) :
    MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom b k β) (cellSchur (skewDiagram lam mu))
      = Shields.skewSchur lam mu b β := by
  rw [cellSchur_of_isConnectedSkew hD, Profile.aeval_schur_eq_skewSchur]
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  exact (skewSchur_eq_of_translate hmu _ v hv b β).symm

end Tableau

/-! ### Diagrams with no adjacent cells, and an example -/

/-- The profile of a single cell. -/
def singleCellProfile : Profile 0 where
  r := ![1]
  g := Fin.elim0
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

theorem singleCellProfile_cells : singleCellProfile.cells = {(0, 0)} := by decide

theorem schur_singleCellProfile : singleCellProfile.schur = X 1 := by
  have h1 : singleCellProfile.xi 0 = 1 := by decide
  have h2 : singleCellProfile.zeta 0 = 0 := by decide
  have e1 : hh 1 = X 1 := by simpa using hh_pnat 1
  rw [Profile.schur, Matrix.det_succ_row_zero]
  simp [h1, h2, e1]

theorem singleton_eq_translate (x : ℤ × ℤ) :
    ({x} : Diagram) = translate x singleCellProfile.cells := by
  rw [singleCellProfile_cells]
  ext y
  simp [mem_translate, Prod.ext_iff, sub_eq_zero]

theorem isConnectedSkew_singleton (x : ℤ × ℤ) : IsConnectedSkew ({x} : Diagram) := by
  rw [singleton_eq_translate]
  exact isConnectedSkew_translate x singleCellProfile.isConnectedSkew_cells

/-- The function of a single cell is `h₁`. -/
theorem cellSchur_singleton (x : ℤ × ℤ) : cellSchur {x} = X 1 := by
  rw [singleton_eq_translate, cellSchur_translate, cellSchur_cells, schur_singleCellProfile]

/-- `connectedSchur` of a single cell is `h₁`. -/
theorem connectedSchur_singleton (x : ℤ × ℤ) : connectedSchur {x} = X 1 := by
  rw [connectedSchur_of_isConnectedSkew (isConnectedSkew_singleton x),
    ← cellSchur_of_isConnectedSkew (isConnectedSkew_singleton x), cellSchur_singleton]

/-- In a diagram with no two adjacent cells, the components are the single cells. -/
theorem edgeComponents_of_noAdjacent {D : Diagram} (h : ∀ a ∈ D, ∀ b ∈ D, ¬ CellAdj a b) :
    edgeComponents D = D.image fun x => ({x} : Diagram) := by
  have hr : ∀ x y : ℤ × ℤ, DiagReach D x y → y = x := by
    intro x y hxy
    induction hxy with
    | refl => rfl
    | @tail b c _ hbc ih => exact absurd hbc.2.2 (h _ hbc.1 _ hbc.2.1)
  ext C
  rw [mem_edgeComponents, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    ext y
    simp only [Finset.mem_singleton, Finset.mem_filter]
    constructor
    · rintro rfl; exact ⟨hx, Relation.ReflTransGen.refl⟩
    · rintro ⟨-, hy⟩; exact hr x y hy
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    ext y
    simp only [Finset.mem_singleton, Finset.mem_filter]
    constructor
    · rintro rfl; exact ⟨hx, Relation.ReflTransGen.refl⟩
    · rintro ⟨-, hy⟩; exact hr x y hy

/-- **The function of a diagram with no two adjacent cells** is `h₁` to the number of cells: every
cell is a component. -/
theorem cellSchur_of_noAdjacent {D : Diagram} (h : ∀ a ∈ D, ∀ b ∈ D, ¬ CellAdj a b) :
    cellSchur D = X 1 ^ D.card := by
  rw [cellSchur, edgeComponents_of_noAdjacent h,
    Finset.prod_image fun a _ b _ hab => by simpa using hab]
  rw [Finset.prod_congr rfl fun x _ => connectedSchur_singleton x, Finset.prod_const]

/-- The disconnected skew diagram `(2, 1) / (1)` has two components, both single cells, so
`s = h₁²`. -/
example : cellSchur (skewOf [2, 1] [1]) = X 1 ^ 2 := by
  have h : ∀ a ∈ skewOf [2, 1] [1], ∀ b ∈ skewOf [2, 1] [1], ¬ CellAdj a b := by decide
  rw [cellSchur_of_noAdjacent h]
  have : (skewOf [2, 1] [1]).card = 2 := by decide
  rw [this]

end SkewGluing
