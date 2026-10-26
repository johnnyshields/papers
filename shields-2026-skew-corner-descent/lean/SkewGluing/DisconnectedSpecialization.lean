import SkewGluing.DisconnectedTableau

/-!
# Specialization of every skew cell diagram

TODO-COPIED from `skew-factor-gluing/lean/SkewGluing/CellSchurTableau.lean`,
adapted to the proof-parameter cell Schur API. Supports
`shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:corner-factors`, `lem:cofactor`). Sorry-free.
-/

namespace SkewGluing

open Shields

attribute [local instance 10] Classical.propDecidable

/-- **Agreement with the tableau skew Schur function for every skew shape.**  For Young diagrams
`μ ≤ λ`, connected or not, the specialization `h_k ↦ completeHom b k β` sends `s_D`,
`D = λ / μ`, to the tableau skew Schur polynomial `skewSchur λ μ b β`.  The tableau sum factors
over the edge-connected components because no row and no column of a skew shape meets two of
them; each component is a skew shape of Young diagrams (`exists_young_pair_of_isSkew`) and is
handled by `aeval_cellSchur_skewDiagram`.  The paper cites the product formula; here it is
proved, by induction on the number of cells, splitting off one component at a time. -/
theorem aeval_cellSchur_skewDiagram_all {R : Type*} [CommRing R] [Algebra ℚ R]
    {lam mu : YoungDiagram} (hmu : mu ≤ lam) (b : ℕ) (β : ℕ → R) :
    MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom b k β)
      (cellSchur (skewDiagram lam mu) (isSkew_skewDiagram lam mu)) =
        Shields.skewSchur lam mu b β := by
  suffices h : ∀ n : ℕ, ∀ lam mu : YoungDiagram, mu ≤ lam → (skewDiagram lam mu).card = n →
      MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom b k β)
        (cellSchur (skewDiagram lam mu) (isSkew_skewDiagram lam mu)) =
          Shields.skewSchur lam mu b β from
    h _ lam mu hmu rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lam mu hmu hn
  set D := skewDiagram lam mu with hDdef
  have hs : IsSkew D := isSkew_skewDiagram lam mu
  change (MvPolynomial.aeval fun k : ℕ+ => completeHom b k β) (cellSchur D hs) = _
  have hnn : ∀ y ∈ D, 0 ≤ y.1 ∧ 0 ≤ y.2 := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hy
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  by_cases hemp : D = ∅
  · -- the empty shape: both sides are `1`
    have hcells : skewCells lam mu = ∅ := by
      have : D.card = 0 := by rw [hemp]; rfl
      simpa [hDdef, skewDiagram] using this
    have : Unique (BoundedSkewSSYT lam mu b) :=
      ⟨⟨BoundedSkewSSYT.ofEmpty lam mu b hcells⟩,
        fun T => BoundedSkewSSYT.eq_of_skewCells_eq_empty hcells _ _⟩
    have hem : cellSchur D hs = 1 :=
      (cellSchur_congr hemp hs (by simp [IsSkew])).trans (cellSchur_empty _)
    rw [hem, map_one, skewSchur, Fintype.sum_unique]
    exact (Finset.prod_eq_one fun c hc => by
      rw [hcells] at hc; exact absurd hc (Finset.notMem_empty _)).symm
  by_cases hconn : IsEdgeConnected D
  · exact aeval_cellSchur_skewDiagram hmu ⟨hs, hconn⟩ b β
  -- a component `C` and the rest `D' = D \ C`
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
  set C : Diagram := D.filter (DiagReach D x) with hCdef
  have hC : C ∈ edgeComponents D := mem_edgeComponents.mpr ⟨x, hx, rfl⟩
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
  have hCsub : C ⊆ D := component_subset hC
  have hCne : C ≠ D := fun h => hconn (h ▸ isEdgeConnected_component hC)
  set D' : Diagram := D \ C with hD'def
  have hcardC : C.card < n := hn ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hCsub, hCne⟩)
  have hcardD' : D'.card < n := hn ▸ Finset.card_lt_card (by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => ?_⟩
    have : x ∈ D' := h ▸ hx
    exact (Finset.mem_sdiff.mp this).2 hxC)
  obtain ⟨lam₁, mu₁, hmu₁, hC₁⟩ := exists_young_pair_of_isSkew (isSkew_component hs hC)
    (fun y hy => hnn y (hCsub hy))
  obtain ⟨lam₂, mu₂, hmu₂, hD₂⟩ := exists_young_pair_of_isSkew (isSkew_sdiff_component hs hC)
    (fun y hy => hnn y (Finset.sdiff_subset hy))
  -- the split of the tableau shape
  have key : ∀ (l m : YoungDiagram) (i j : ℕ),
      (i, j) ∈ skewCells l m ↔ ((i : ℤ), (j : ℤ)) ∈ skewDiagram l m :=
    fun l m i j => (mem_skewDiagram_nat i j).symm
  have hcellD : ∀ i j : ℕ, (i, j) ∈ skewCells lam mu ↔ ((i : ℤ), (j : ℤ)) ∈ D :=
    fun i j => key lam mu i j
  have hcell₁ : ∀ i j : ℕ, (i, j) ∈ skewCells lam₁ mu₁ ↔ ((i : ℤ), (j : ℤ)) ∈ C := by
    intro i j; rw [key, hC₁]
  have hcell₂ : ∀ i j : ℕ, (i, j) ∈ skewCells lam₂ mu₂ ↔ ((i : ℤ), (j : ℤ)) ∈ D' := by
    intro i j; rw [key, hD₂]
  have hrowcol : ∀ y ∈ C, ∀ z ∈ D', ¬ DiagReach D y z := fun y hy z hz hr =>
    (Finset.mem_sdiff.mp hz).2 (mem_component_of_reach hC hy hr)
  have S : SkewSplit lam mu lam₁ mu₁ lam₂ mu₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext ⟨i, j⟩
      rw [Finset.mem_union, hcellD, hcell₁, hcell₂, hD'def, Finset.mem_sdiff]
      constructor
      · intro h
        by_cases hc : ((i : ℤ), (j : ℤ)) ∈ C
        · exact Or.inl hc
        · exact Or.inr ⟨h, hc⟩
      · rintro (h | h)
        · exact hCsub h
        · exact h.1
    · rw [Finset.disjoint_left]
      rintro ⟨i, j⟩ h1 h2
      rw [hcell₁] at h1
      rw [hcell₂, hD'def, Finset.mem_sdiff] at h2
      exact h2.2 h1
    · intro i j₁ j₂ h1 h2
      rw [hcell₁] at h1
      rw [hcell₂] at h2
      exact hrowcol _ h1 _ h2 (hs.reach_row (hCsub h1) (Finset.sdiff_subset h2))
    · intro i₁ i₂ j h1 h2
      rw [hcell₁] at h1
      rw [hcell₂] at h2
      exact hrowcol _ h1 _ h2 (hs.reach_col (hCsub h1) (Finset.sdiff_subset h2))
  -- the functions multiply
  have hsC := isSkew_component hs hC
  have hsD' := isSkew_sdiff_component hs hC
  have hu : IsSkew (C ∪ D') := by rw [Finset.union_sdiff_of_subset hCsub]; exact hs
  have hcs : cellSchur D hs = cellSchur C hsC * cellSchur D' hsD' := by
    have he := cellSchur_union hsC hsD' hu Finset.disjoint_sdiff
      (fun a ha b hb hadj => hrowcol a ha b hb
        (Relation.ReflTransGen.single ⟨hCsub ha, Finset.sdiff_subset hb, hadj⟩))
    simpa only [Finset.union_sdiff_of_subset hCsub] using he
  have ih₁ := ih _ (by rw [hC₁]; exact hcardC) lam₁ mu₁ hmu₁ rfl
  have ih₂ := ih _ (by rw [hD₂]; exact hcardD') lam₂ mu₂ hmu₂ rfl
  rw [cellSchur_congr hC₁ (isSkew_skewDiagram _ _) hsC] at ih₁
  rw [cellSchur_congr hD₂ (isSkew_skewDiagram _ _) hsD'] at ih₂
  rw [hcs, map_mul, ih₁, ih₂, S.skewSchur_mul]

end SkewGluing
