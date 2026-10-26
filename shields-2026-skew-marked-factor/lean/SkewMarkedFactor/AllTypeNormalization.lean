/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.RowUnions
import SkewMarkedFactor.OrdinaryAction
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.OrdinaryAssemble
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase

/-!
# The all-type modified composition

«The algebra map and the weighted operator» (`eq:full-normalization`) of
`shields-2026-skew-marked-factor.tex`: for every legal mark and connected outer `D`,
`Ψ_η(s_D) = ε_η(D) A^{|D|-r(D)} B^{|D|-c(D)} C^{|D|-N_D} s_{D ∘_η E}`.

The route: the modified composition (`modComp` for the ordinary cases, `modCompC` for case (c))
kills the kernel of the Schur map on the shape space and is multiplicative and translation
invariant; every skew diagram is, modulo that kernel, a combination of unions of separated rows,
and on these the algebra map and the modified composition agree by definition of `Ψ_η`.
Case (d) follows from case (c) by whole rotation.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

namespace Gluing.Plan

section Corner

variable {ω : MarkedInner}

theorem corner_step {Y : ShapeSpace} (hY : Y ∈ skewSpace) (hC : CornerCompat ω) {m : ℕ}
    (hm : 0 < m) : Flin (modCompC ω) (rightOp m Y) = Flin (modCompC ω) (leftOp m Y) := by
  refine ext_skew ((Flin (modCompC ω)).comp (rightOp m)) ((Flin (modCompC ω)).comp (leftOp m))
    (fun X hX => ?_) hY
  simp only [LinearMap.comp_apply, Flin_rightOp_shape, Flin_leftOp_shape]
  exact (hC X hX m hm).2

theorem leftOp_rightOp_comm' {Y : ShapeSpace} (hY : Y ∈ skewSpace) (m n : ℕ) :
    leftOp m (rightOp n Y) = rightOp n (leftOp m Y) :=
  ext_skew ((leftOp m).comp (rightOp n)) ((rightOp n).comp (leftOp m))
    (fun _ hX => leftOp_rightOp_comm hX m n) hY

theorem leftOp_rightWord {Y : ShapeSpace} (hY : Y ∈ skewSpace) (m : ℕ) (ν : List ℕ) :
    leftOp m (rightWord ν Y) = rightWord ν (leftOp m Y) := by
  induction ν generalizing Y with
  | nil => rfl
  | cons n ν ih =>
    rw [rightWord_cons, rightWord_cons, leftOp_rightOp_comm' (rightWord_mem ν hY), ih hY]

theorem corner_word (hC : CornerCompat ω) (ν : List ℕ) (hν : ∀ m ∈ ν, 0 < m) :
    ∀ {Y : ShapeSpace}, Y ∈ skewSpace →
      Flin (modCompC ω) (rightWord ν Y) = Flin (modCompC ω) (leftWord ν Y) := by
  induction ν with
  | nil => intro Y _; rfl
  | cons m ν ih =>
    intro Y hY
    have hm : 0 < m := hν m (by simp)
    have hν' : ∀ a ∈ ν, 0 < a := fun a ha => hν a (List.mem_cons_of_mem _ ha)
    rw [rightWord_cons, corner_step (rightWord_mem ν hY) hC hm, leftOp_rightWord hY,
      ih hν' (leftOp_mem hY m), leftWord_cons]

/-- The corner modified composition kills the kernel of the Schur map. -/
theorem corner_kernel (hC : CornerCompat ω) (hT : ∀ (t : ℤ × ℤ) (X : Diagram),
    modCompC ω (translate t X) = modCompC ω X) :
    shapeKernelSpan ≤ LinearMap.ker (Flin (modCompC ω)) := by
  unfold shapeKernelSpan
  rw [Submodule.span_le]
  rintro h (⟨X, v, hX, rfl⟩ | ⟨ν, Z, hν, hZ, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Flin_shape, Flin_shape, hT, sub_self]
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub,
      corner_word hC ν hν (shape_mem_skewSpace hZ), sub_self]

end Corner

end Gluing.Plan

/-- Every element of `Λ` is a rational combination of products of complete functions. -/
theorem exists_hPos_expansion (f : Lambda) :
    ∃ s : List (ℚ × List ℕ), f = (s.map fun p => C p.1 * (p.2.map hPos).prod).sum := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨[(a, [])], by simp⟩
  | add f g hf hg =>
    obtain ⟨s, hs⟩ := hf
    obtain ⟨t, ht⟩ := hg
    exact ⟨s ++ t, by rw [List.map_append, List.sum_append, hs, ht]⟩
  | mul_X f j hf =>
    obtain ⟨s, hs⟩ := hf
    refine ⟨s.map fun p => (p.1, j.val :: p.2), ?_⟩
    rw [hs, ← List.sum_map_mul_right]
    simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    rw [← hPos_pnat j]
    ring

/-- A multiplicative, translation-invariant function of skew diagrams that kills the kernel of the
Schur map and takes the value `Ψ(h_j)` on a row of `j` cells agrees with `Ψ ∘ s` on every skew
diagram. -/
theorem algHom_cellSchur_eq_of_kernel (Ψ : Lambda →ₐ[ℚ] Lambda) (F : Diagram → Lambda)
    (hker : shapeKernelSpan ≤ LinearMap.ker (Flin F))
    (hU : ∀ A B : Diagram, Disjoint A B → NonAdjacent A B → F (A ∪ B) = F A * F B)
    (hT : ∀ (t : ℤ × ℤ) (X : Diagram), F (translate t X) = F X) (hE : F ∅ = 1)
    (hrow : ∀ j : ℕ, F (rowCells 0 (j : ℤ)) = Ψ (hPos j)) {X : Diagram} (hX : IsSkew X) :
    Ψ (cellSchur X) = F X := by
  obtain ⟨s, hs⟩ := exists_hPos_expansion (cellSchur X)
  set g : ShapeSpace := (s.map fun p => p.1 • shape (rowUnion p.2 0 0)).sum with hg
  have hrowU : ∀ l : List ℕ, F (rowUnion l 0 0) = Ψ ((l.map hPos).prod) := by
    intro l
    rw [rowUnion_mul F hU hT hE l 0 0, map_list_prod]
    simp only [List.map_map, Function.comp_def, hrow]
  have hgS : shapeSchur g = cellSchur X := by
    rw [hg, map_list_sum, hs]
    simp only [List.map_map, Function.comp_def, map_smul]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    have : shapeSchur (shape (rowUnion p.2 0 0)) = cellSchur (rowUnion p.2 0 0) :=
      Flin_shape cellSchur _
    rw [this, cellSchur_rowUnion, MvPolynomial.smul_eq_C_mul]
  have hgmem : g ∈ skewSpace := by
    rw [hg]
    refine list_sum_mem fun x hx => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    exact Submodule.smul_mem _ _ (shape_mem_skewSpace (isSkew_rowUnion _ _ _))
  have hmem : shape X - g ∈ skewSpace := sub_mem (shape_mem_skewSpace hX) hgmem
  have h0 : shapeSchur (shape X - g) = 0 := by
    rw [map_sub, hgS]
    have : shapeSchur (shape X) = cellSchur X := Flin_shape cellSchur _
    rw [this, sub_self]
  have hk := hker (kernel_schur (mem_skewSpace.mp hmem) h0)
  rw [LinearMap.mem_ker, map_sub, Flin_shape, sub_eq_zero] at hk
  rw [hk, hg, map_list_sum, hs, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_smul, map_mul]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [Flin_shape, hrowU, MvPolynomial.smul_eq_C_mul]
  have hC : Ψ (C p.1) = C p.1 := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [hC]

theorem edgeComponents_empty' : edgeComponents (∅ : Diagram) = ∅ := edgeComponents_empty

theorem modCompC_empty (ω : MarkedInner) : modCompC ω ∅ = 1 := by
  unfold modCompC
  rw [edgeComponents_empty', Finset.prod_empty]

theorem card_rowCells (j : ℕ) : (rowCells 0 (j : ℤ)).card = j := by
  unfold rowCells
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
  simp

theorem numRows_rowCells {j : ℕ} (hj : 1 ≤ j) : numRows (rowCells 0 (j : ℤ)) = 1 := by
  unfold numRows rowSet rowCells
  rw [Finset.image_image]
  have : ((Prod.fst : ℤ × ℤ → ℤ) ∘ fun x : ℤ => ((0 : ℤ), x)) = fun _ => (0 : ℤ) := rfl
  rw [this, Finset.image_const]
  · simp
  · exact ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hj⟩⟩

theorem numCols_rowCells {j : ℕ} : numCols (rowCells 0 (j : ℤ)) = j := by
  rw [numCols_eq_card_image_snd]
  unfold rowCells
  rw [Finset.image_image]
  have : ((Prod.snd : ℤ × ℤ → ℤ) ∘ fun x : ℤ => ((0 : ℤ), x)) = id := rfl
  rw [this, Finset.image_id, Int.card_Ico]
  simp

theorem span_rowCells' {j : ℕ} : span (rowCells 0 (j : ℤ)) = j := by
  rw [span_rowCells]; simp

theorem northbound_rowCells (η : MarkedInner) (j : ℕ) : northbound η (rowCells 0 (j : ℤ)) = 0 := by
  unfold northbound
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b⟩ hx hs
  have h1 := hs.1
  rw [mem_rowCells] at h1 hx
  simp only at h1 hx
  omega

/-- The row value of the modified composition is the generator value of `Ψ_η`. -/
theorem componentT_row (η : MarkedInner) {j : ℕ} (hj : 1 ≤ j) :
    componentT η (rowCells 0 (j : ℤ)) = compositionMap η (hPos j) := by
  rw [compositionMap_hPos η hj, componentT, card_rowCells, numRows_rowCells hj, numCols_rowCells,
    span_rowCells']
  simp [normalizerRow]

theorem componentT_eq_normalization (η : MarkedInner) (D : Diagram) :
    componentT η D = normalizationFactor η D * cellSchur (η.compose D) := by
  unfold componentT normalizationFactor normalizerRow normalizerColumn normalizerDiagonal
  ring

theorem rowCells_zero_zero : rowCells 0 ((0 : ℕ) : ℤ) = ∅ := by
  ext ⟨a, b⟩; simp [mem_rowCells]

/-- The sign exponent `n(D)` of `eq:full-normalization`: the number of cells of `D` with a cell
directly north of them on the same boundary ribbon (northwest boundary in case (c), southeast in
case (d)), which is the sum of the heights of the boundary ribbons of the decomposition.  In the
ordinary cases no cell qualifies. -/
def signExponent (η : MarkedInner) (D : Diagram) : ℕ := northbound η D

/-- The normalizer `𝓝_η(D) = ε_η(D) A^{|D|-r(D)} B^{|D|-c(D)} C^{|D|-N_D}`. -/
def fullNormalizer (η : MarkedInner) (D : Diagram) : Lambda :=
  (-1 : Lambda) ^ signExponent η D * normalizationFactor η D

theorem signExponent_ordinary {η : MarkedInner} (ho : η.IsOrdinary) (D : Diagram) :
    signExponent η D = 0 := by
  unfold signExponent northbound
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d _ hs
  have := hs.2
  unfold MarkedInner.IsOrdinary AttachCase.IsMixed at ho
  revert this
  cases hc : η.case <;> simp_all [Gluing.MarkedInner.SameRibbon]

theorem pDeriv_ordinary_kernel {η : MarkedInner} (hη : η.IsLegal)
    (hc : η.case = .a ∨ η.case = .b) :
    shapeKernelSpan ≤ LinearMap.ker (Flin (modComp η)) := by
  have hE : EdgeCompat η := by
    rcases hc with hc | hc
    · exact edgeCompat_a hη hc
    · exact edgeCompat_b hη hc
  exact edge_kernel hη hc hE

/-- **The all-type normalization, ordinary cases** (`eq:full-normalization`). -/
theorem compositionMap_cellSchur_ordinary {η : MarkedInner} (hη : η.IsLegal)
    (hc : η.case = .a ∨ η.case = .b) {D : Diagram} (hD : IsConnectedSkew D) :
    compositionMap η (cellSchur D) = fullNormalizer η D * cellSchur (η.compose D) := by
  have ho : η.IsOrdinary := by
    unfold MarkedInner.IsOrdinary AttachCase.IsMixed
    rcases hc with h | h <;> simp [h]
  have h1 := algHom_cellSchur_eq_of_kernel (compositionMap η) (modComp η)
    (pDeriv_ordinary_kernel hη hc) (fun A B hd hn => modComp_union hd hn)
    (fun t X => modComp_translate η t X) (modComp_empty η) (fun j => by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [rowCells_zero_zero, modComp_empty, hPos_zero, map_one]
      · rw [modComp_connected (isConnectedSkew_rowCells (by exact_mod_cast hj)),
          componentT_row η hj]) hD.1
  rw [h1, modComp_connected hD, componentT_eq_normalization, fullNormalizer,
    signExponent_ordinary ho, pow_zero, one_mul]

/-- **The all-type normalization, case (c)** (`eq:full-normalization`). -/
theorem compositionMap_cellSchur_c {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .c)
    {D : Diagram} (hD : IsConnectedSkew D) :
    compositionMap η (cellSchur D) = fullNormalizer η D * cellSchur (η.compose D) := by
  have h1 := algHom_cellSchur_eq_of_kernel (compositionMap η) (modCompC η)
    (Plan.corner_kernel (cornerCompat_c hη hc) (modCompC_translate η))
    (fun A B hd hn => Plan.Corner.modCompC_union hd hn)
    (fun t X => modCompC_translate η t X) (modCompC_empty η) (fun j => by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [rowCells_zero_zero, modCompC_empty, hPos_zero, map_one]
      · rw [modCompC_connected (isConnectedSkew_rowCells (by exact_mod_cast hj)), componentTc,
          northbound_rowCells, pow_zero, one_mul, componentT_row η hj]) hD.1
  rw [h1, modCompC_connected hD, componentTc, componentT_eq_normalization, fullNormalizer,
    signExponent]
  ring


theorem northbound_rotate_c {η : MarkedInner} (hc : η.case = .c) (D : Diagram) :
    northbound η D = northbound η.rotate (Gluing.rotate D) := by
  unfold northbound
  refine Finset.card_bij (fun d _ => -(d.1 - 1, d.2)) ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact (Gluing.MarkedInner.sameRibbon_rotate_c hc D d).mp hd
  · intro a _ b _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
    exact Prod.ext (by omega) (by omega)
  · intro e he
    rw [Finset.mem_filter] at he
    have hd : -((1 - e.1) - 1, -e.2) = e := by ext <;> simp
    refine ⟨(1 - e.1, -e.2), ?_, hd⟩
    rw [Finset.mem_filter]
    apply (Gluing.MarkedInner.sameRibbon_rotate_c hc D (1 - e.1, -e.2)).mpr
    rw [hd]
    exact he

theorem northbound_rotate_d {η : MarkedInner} (hd : η.case = .d) (D : Diagram) :
    northbound η D = northbound η.rotate (Gluing.rotate D) := by
  have hc : η.rotate.case = .c := by simp [Gluing.MarkedInner.rotate, hd, AttachCase.rotate]
  have := northbound_rotate_c hc (Gluing.rotate D)
  rw [Gluing.rotate_rotate, Gluing.MarkedInner.rotate_rotate] at this
  exact this.symm


theorem normalizationFactor_rotate {η : MarkedInner} (hη : η.IsLegal) (D : Diagram) :
    normalizationFactor η.rotate (Gluing.rotate D) = normalizationFactor η D := by
  unfold normalizationFactor normalizerRow normalizerColumn normalizerDiagonal
  rw [Gluing.Plan.MarkedInner.cellSchur_W_rotate,
    Gluing.Plan.MarkedInner.cellSchur_hatMarkFin_rotate hη.1 hη.2.2.1,
    Gluing.Plan.MarkedInner.cellSchur_hatMiddleFin_rotate, Gluing.Plan.MarkedInner.numRows_rotate,
    Gluing.Plan.MarkedInner.numCols_rotate, Gluing.span_rotate, Gluing.Plan.MarkedInner.card_rotate']

/-- **The all-type normalization, case (d)**, from case (c) by whole rotation. -/
theorem compositionMap_cellSchur_d {η : MarkedInner} (hη : η.IsLegal) (hd : η.case = .d)
    {D : Diagram} (hD : IsConnectedSkew D) :
    compositionMap η (cellSchur D) = fullNormalizer η D * cellSchur (η.compose D) := by
  have hc : η.rotate.case = .c := by simp [Gluing.MarkedInner.rotate, hd, AttachCase.rotate]
  have hl := Gluing.MarkedInner.isLegal_rotate hη
  have hDr : IsConnectedSkew (Gluing.rotate D) := Gluing.isConnectedSkew_rotate hD
  have h1 := compositionMap_cellSchur_c hl hc hDr
  rw [compositionMap_rotate, cellSchur_rotate] at h1
  rw [h1, fullNormalizer, fullNormalizer, signExponent, signExponent,
    normalizationFactor_rotate hη, ← northbound_rotate_d hd,
    ← Gluing.cellSchur_rotate (η.compose D), Gluing.MarkedInner.rotate_compose hD.2.1 η]

/-- **The all-type modified-composition theorem** (`eq:full-normalization`): for every legal mark
and connected outer, `Ψ_η(s_D) = ε_η(D) A^{|D|-r(D)} B^{|D|-c(D)} C^{|D|-N_D} s_{D ∘_η E}`, the
sign being `(-1)^{n(D)}` with `n(D)` the number of cells having a cell directly north on the same
boundary ribbon (zero in the ordinary cases). -/
theorem compositionMap_cellSchur {η : MarkedInner} (hη : η.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) :
    compositionMap η (cellSchur D) = fullNormalizer η D * cellSchur (η.compose D) := by
  cases hc : η.case
  · exact compositionMap_cellSchur_ordinary hη (Or.inl hc) hD
  · exact compositionMap_cellSchur_ordinary hη (Or.inr hc) hD
  · exact compositionMap_cellSchur_c hη hc hD
  · exact compositionMap_cellSchur_d hη hc hD

end SkewMarkedFactor
