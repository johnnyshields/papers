/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.UnitExpansion
import SkewCoframeRigidity.Coframe.Defs

/-!
# The zero-free core of a diagram

Formalizes the first sentence of `sec:unit-restoration` in
`shields-2026-skew-coframe-rigidity.tex`: deleting all common betas (the unit rows and columns)
gives a connected zero-free diagram of the same span, called the zero-free core.  The core
rows and columns are enumerated in order, and the counting identity

  `1 + #{core columns before c} ≤ #{core rows up to c}`

gives interlacing `col'_k < row'_k` and connectedness of the core.  A unit row is matched to a
unit column that lies strictly earlier, which is the whole content of the count.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity.Coframe Finset
open scoped Classical

variable {n : ℕ}

/-- The row indices that are not common betas. -/
noncomputable def coreRows (D : BetaDiagram n) : Finset (Fin n) :=
  univ.filter fun i => i ∉ unitRows D.row D.col

/-- The column indices that are not common betas. -/
noncomputable def coreCols (D : BetaDiagram n) : Finset (Fin n) :=
  univ.filter fun j => j ∉ unitCols D.row D.col

theorem mem_coreRows {D : BetaDiagram n} {i : Fin n} :
    i ∈ coreRows D ↔ i ∉ unitRows D.row D.col := by simp [coreRows]

theorem mem_coreCols {D : BetaDiagram n} {j : Fin n} :
    j ∈ coreCols D ↔ j ∉ unitCols D.row D.col := by simp [coreCols]

/-- A unit row is matched to a strictly earlier unit column. -/
theorem lt_of_row_eq_col (D : BetaDiagram n) {i j : Fin n} (h : D.row i = D.col j) : j < i := by
  have h1 : D.row i < D.row j := by rw [h]; exact D.row_nonempty j
  exact D.row_strictAnti.lt_iff_gt.mp h1

theorem card_coreRows_eq (D : BetaDiagram n) : (coreRows D).card = (coreCols D).card := by
  obtain ⟨φ, -⟩ := exists_unit_equiv D.row D.col D.row_strictAnti.injective
    D.col_strictAnti.injective
  have h1 := Fintype.card_congr φ
  have h2 := Fintype.card_subtype_compl (fun i => i ∈ unitRows D.row D.col)
  have h3 := Fintype.card_subtype_compl (fun i => i ∈ unitCols D.row D.col)
  have h4 : (coreRows D).card = Fintype.card {i // i ∉ unitRows D.row D.col} := by
    rw [coreRows, Fintype.card_subtype]
  have h5 : (coreCols D).card = Fintype.card {i // i ∉ unitCols D.row D.col} := by
    rw [coreCols, Fintype.card_subtype]
  rw [h4, h5]
  simp only [Fintype.card_subtype_compl] at *
  omega

/-- The counting identity: up to any position there are more core rows than core columns before
it. -/
theorem card_coreCols_lt_card_coreRows_le (D : BetaDiagram n) (c : Fin n) :
    1 + ((coreCols D).filter (· < c)).card ≤ ((coreRows D).filter (· ≤ c)).card := by
  set UR := (Iic c).filter fun i => i ∈ unitRows D.row D.col with hUR
  set UC := (Iio c).filter fun j => j ∈ unitCols D.row D.col with hUC
  have hinj : UR.card ≤ UC.card := by
    let f : Fin n → Fin n := fun i =>
      if h : ∃ j, D.row i = D.col j then Classical.choose h else i
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro i hi
      simp only [hUR, coe_filter, Set.mem_setOf_eq, mem_Iic] at hi
      obtain ⟨hic, hu⟩ := hi
      have h : ∃ j, D.row i = D.col j := hu
      have hf : f i = Classical.choose h := dif_pos h
      have hs := Classical.choose_spec h
      simp only [hUC, coe_filter, Set.mem_setOf_eq, mem_Iio]
      refine ⟨?_, ?_⟩
      · rw [hf]; exact lt_of_lt_of_le (lt_of_row_eq_col D hs) hic
      · rw [hf]; exact ⟨i, hs⟩
    · intro i hi i' hi' hii
      simp only [hUR, coe_filter, Set.mem_setOf_eq, mem_Iic] at hi hi'
      have h : ∃ j, D.row i = D.col j := hi.2
      have h' : ∃ j, D.row i' = D.col j := hi'.2
      have hf : f i = Classical.choose h := dif_pos h
      have hf' : f i' = Classical.choose h' := dif_pos h'
      have e1 := Classical.choose_spec h
      have e2 := Classical.choose_spec h'
      have : D.row i = D.row i' := by
        rw [e1, e2]
        congr 1
        rw [← hf, ← hf']; exact hii
      exact D.row_strictAnti.injective this
  have h1 : (Iic c).card = c.val + 1 := Fin.card_Iic c
  have h2 : (Iio c).card = c.val := Fin.card_Iio c
  have h3 := Finset.card_filter_add_card_filter_not (s := Iic c)
    (fun i => i ∈ unitRows D.row D.col)
  have h4 := Finset.card_filter_add_card_filter_not (s := Iio c)
    (fun i => i ∈ unitCols D.row D.col)
  have e1 : (coreRows D).filter (· ≤ c) = (Iic c).filter fun i => i ∉ unitRows D.row D.col := by
    ext i; simp [mem_coreRows, and_comm]
  have e2 : (coreCols D).filter (· < c) = (Iio c).filter fun i => i ∉ unitCols D.row D.col := by
    ext i; simp [mem_coreCols, and_comm]
  rw [e1, e2]
  simp only [hUR, hUC] at hinj
  omega

/-! ### Order embeddings -/

section Embedding

variable {m : ℕ} (S : Finset (Fin n)) (hS : S.card = m)

theorem card_filter_lt_orderEmbOfFin (k : Fin m) :
    (S.filter (· < S.orderEmbOfFin hS k)).card = k := by
  have : S.filter (· < S.orderEmbOfFin hS k) = (Iio k).map (S.orderEmbOfFin hS).toEmbedding := by
    ext x
    simp only [mem_filter, mem_map, mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have : x ∈ Set.range (S.orderEmbOfFin hS) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨l, rfl⟩ := this
      exact ⟨l, (S.orderEmbOfFin hS).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S hS l, (S.orderEmbOfFin hS).lt_iff_lt.mpr hl⟩
  rw [this, card_map, Fin.card_Iio]

theorem orderEmbOfFin_le_of_card (k : Fin m) (c : Fin n)
    (h : (k : ℕ) + 1 ≤ (S.filter (· ≤ c)).card) : S.orderEmbOfFin hS k ≤ c := by
  by_contra hc
  push_neg at hc
  have hsub : S.filter (· ≤ c) ⊆ S.filter (· < S.orderEmbOfFin hS k) := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_le_of_lt hx.2 hc⟩
  have := Finset.card_le_card hsub
  rw [card_filter_lt_orderEmbOfFin S hS k] at this
  omega

end Embedding

/-- The number of core rows, which is also the number of core columns. -/
noncomputable def coreCount (D : BetaDiagram n) : ℕ := (coreRows D).card

theorem card_coreCols_eq (D : BetaDiagram n) : (coreCols D).card = coreCount D :=
  (card_coreRows_eq D).symm

theorem card_coreRows_eq_count (D : BetaDiagram n) : (coreRows D).card = coreCount D := rfl

/-- The order-preserving enumeration of the core rows. -/
noncomputable def coreRowEmb (D : BetaDiagram n) : Fin (coreCount D) ↪o Fin n :=
  (coreRows D).orderEmbOfFin (card_coreRows_eq_count D)

/-- The order-preserving enumeration of the core columns. -/
noncomputable def coreColEmb (D : BetaDiagram n) : Fin (coreCount D) ↪o Fin n :=
  (coreCols D).orderEmbOfFin (card_coreCols_eq D)

theorem coreRowEmb_mem (D : BetaDiagram n) (k : Fin (coreCount D)) :
    coreRowEmb D k ∉ unitRows D.row D.col :=
  mem_coreRows.mp (Finset.orderEmbOfFin_mem _ _ k)

theorem coreColEmb_mem (D : BetaDiagram n) (k : Fin (coreCount D)) :
    coreColEmb D k ∉ unitCols D.row D.col :=
  mem_coreCols.mp (Finset.orderEmbOfFin_mem _ _ k)

theorem exists_coreRowEmb (D : BetaDiagram n) {i : Fin n} (hi : i ∉ unitRows D.row D.col) :
    ∃ k, coreRowEmb D k = i := by
  have : i ∈ Set.range (coreRowEmb D) := by
    unfold coreRowEmb; rw [Finset.range_orderEmbOfFin (coreRows D) (card_coreRows_eq_count D)]; exact mem_coreRows.mpr hi
  exact this

theorem exists_coreColEmb (D : BetaDiagram n) {j : Fin n} (hj : j ∉ unitCols D.row D.col) :
    ∃ k, coreColEmb D k = j := by
  have : j ∈ Set.range (coreColEmb D) := by
    unfold coreColEmb; rw [Finset.range_orderEmbOfFin]; exact mem_coreCols.mpr hj
  exact this

/-- Interlacing: the `k`-th core row index does not exceed the `k`-th core column index. -/
theorem coreRowEmb_le_coreColEmb (D : BetaDiagram n) (k : Fin (coreCount D)) :
    coreRowEmb D k ≤ coreColEmb D k := by
  apply orderEmbOfFin_le_of_card
  have h1 := card_coreCols_lt_card_coreRows_le D (coreColEmb D k)
  have h2 := card_filter_lt_orderEmbOfFin (coreCols D) (card_coreCols_eq D) k
  have h4 : (coreCols D).orderEmbOfFin (card_coreCols_eq D) k = coreColEmb D k := rfl
  rw [h4] at h2
  omega

/-- The first core row is the top row of the diagram. -/
theorem coreCount_pos_of_pos (D : BetaDiagram n) (hn : 0 < n) : 0 < coreCount D := by
  have h := card_coreCols_lt_card_coreRows_le D ⟨n - 1, by omega⟩
  have : ((coreRows D).filter (· ≤ (⟨n - 1, by omega⟩ : Fin n))).card ≤ coreCount D :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- The core is a beta diagram: the rows and columns of the core, in order. -/
noncomputable def coreDiagram (D : BetaDiagram n) : BetaDiagram (coreCount D) where
  row k := D.row (coreRowEmb D k)
  col k := D.col (coreColEmb D k)
  row_strictAnti := D.row_strictAnti.comp_strictMono (coreRowEmb D).strictMono
  col_strictAnti := D.col_strictAnti.comp_strictMono (coreColEmb D).strictMono
  row_nonempty k :=
    lt_of_lt_of_le (D.row_nonempty (coreColEmb D k))
      (D.row_strictAnti.antitone (coreRowEmb_le_coreColEmb D k))

@[simp] theorem coreDiagram_row (D : BetaDiagram n) (k : Fin (coreCount D)) :
    (coreDiagram D).row k = D.row (coreRowEmb D k) := rfl

@[simp] theorem coreDiagram_col (D : BetaDiagram n) (k : Fin (coreCount D)) :
    (coreDiagram D).col k = D.col (coreColEmb D k) := rfl

/-- Deleting the common betas of a connected diagram leaves a connected diagram. -/
theorem coreDiagram_connected {D : BetaDiagram n} (hD : D.Connected) :
    (coreDiagram D).Connected := by
  refine ⟨coreCount_pos_of_pos D hD.1, fun k hk => ?_⟩
  set k' : Fin (coreCount D) := k with hk'
  set k'' : Fin (coreCount D) := ⟨k.val + 1, hk⟩ with hk''
  have hlt : coreColEmb D k' < coreColEmb D k'' :=
    (coreColEmb D).strictMono (by simp [hk', hk'', Fin.lt_def])
  have hnc : (coreColEmb D k').val + 1 < n := by
    have := (coreColEmb D k'').isLt
    have : (coreColEmb D k').val < (coreColEmb D k'').val := hlt
    omega
  set c : Fin n := ⟨(coreColEmb D k').val + 1, hnc⟩ with hc
  have hrow : coreRowEmb D k'' ≤ c := by
    apply orderEmbOfFin_le_of_card
    have h1 := card_coreCols_lt_card_coreRows_le D c
    have hsub : (Iic k').image (coreColEmb D) ⊆ (coreCols D).filter (· < c) := by
      intro x hx
      simp only [mem_image, mem_Iic] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      simp only [mem_filter]
      refine ⟨Finset.orderEmbOfFin_mem _ _ l, ?_⟩
      have : coreColEmb D l ≤ coreColEmb D k' := (coreColEmb D).monotone hl
      rw [hc, Fin.lt_def]
      have : (coreColEmb D l).val ≤ (coreColEmb D k').val := this
      simp only; omega
    have h2 := Finset.card_le_card hsub
    rw [card_image_of_injective _ (coreColEmb D).injective, Fin.card_Iic] at h2
    have : (k'' : ℕ) = k.val + 1 := rfl
    simp only [hk'] at h2
    unfold coreRowEmb at *
    omega
  have h3 : D.col (coreColEmb D k') ≤ D.row c := hD.2 (coreColEmb D k') hnc
  exact le_trans h3 (D.row_strictAnti.antitone hrow)

/-! ### The pairing of core rows with core columns -/

/-- The core rows, as the type of the core letter matrix, enumerated in order. -/
noncomputable def coreRowEquiv (D : BetaDiagram n) :
    Fin (coreCount D) ≃ {i // i ∉ unitRows D.row D.col} where
  toFun k := ⟨coreRowEmb D k, coreRowEmb_mem D k⟩
  invFun i := Classical.choose (exists_coreRowEmb D i.2)
  left_inv k := by
    apply (coreRowEmb D).injective
    exact Classical.choose_spec (exists_coreRowEmb D (coreRowEmb_mem D k))
  right_inv i := Subtype.ext (Classical.choose_spec (exists_coreRowEmb D i.2))

/-- The core columns, enumerated in order. -/
noncomputable def coreColEquiv (D : BetaDiagram n) :
    Fin (coreCount D) ≃ {j // j ∉ unitCols D.row D.col} where
  toFun k := ⟨coreColEmb D k, coreColEmb_mem D k⟩
  invFun j := Classical.choose (exists_coreColEmb D j.2)
  left_inv k := by
    apply (coreColEmb D).injective
    exact Classical.choose_spec (exists_coreColEmb D (coreColEmb_mem D k))
  right_inv j := Subtype.ext (Classical.choose_spec (exists_coreColEmb D j.2))

/-- The canonical core pairing: the `k`-th core row with the `k`-th core column. -/
noncomputable def corePairing (D : BetaDiagram n) :
    {i // i ∉ unitRows D.row D.col} ≃ {j // j ∉ unitCols D.row D.col} :=
  (coreRowEquiv D).symm.trans (coreColEquiv D)

theorem corePairing_coreRowEquiv (D : BetaDiagram n) (k : Fin (coreCount D)) :
    corePairing D (coreRowEquiv D k) = coreColEquiv D k := by
  simp [corePairing]

/-- The unique pairing of unit rows with unit columns of equal beta. -/
noncomputable def unitPairing (D : BetaDiagram n) :
    {i // i ∈ unitRows D.row D.col} ≃ {j // j ∈ unitCols D.row D.col} :=
  Classical.choose (exists_unit_equiv D.row D.col D.row_strictAnti.injective
    D.col_strictAnti.injective)

theorem unitPairing_spec (D : BetaDiagram n) (i : {i // i ∈ unitRows D.row D.col}) :
    D.row i.1 = D.col (unitPairing D i).1 :=
  Classical.choose_spec (exists_unit_equiv D.row D.col D.row_strictAnti.injective
    D.col_strictAnti.injective) i

/-- Any matching of unit rows to unit columns of equal beta is the unit pairing. -/
theorem unitPairing_unique (D : BetaDiagram n)
    (φ : {i // i ∈ unitRows D.row D.col} ≃ {j // j ∈ unitCols D.row D.col})
    (hφ : ∀ i, D.row i.1 = D.col (φ i).1) : φ = unitPairing D := by
  ext i
  exact congrArg Fin.val (D.col_strictAnti.injective ((hφ i).symm.trans (unitPairing_spec D i)))

/-- The simultaneous sorting sign: the sign of the permutation taking each unit row to its
matching unit column and the `k`-th core row to the `k`-th core column. -/
noncomputable def sortingSign (D : BetaDiagram n) : ℤˣ :=
  Equiv.Perm.sign (sortPerm D.row D.col (unitPairing D) (corePairing D))

/-- The core letter matrix for the canonical pairing is the Jacobi--Trudi matrix of the core
diagram. -/
theorem det_coreMatrix_corePairing {R : Type*} [CommRing R] (h : ℕ → R) (D : BetaDiagram n) :
    (coreMatrix h D.row D.col (corePairing D)).det = schurOf h (coreDiagram D) := by
  unfold schurOf
  rw [← Matrix.det_submatrix_equiv_self (coreRowEquiv D)]
  congr 1
  ext a b
  have hb := congrArg Subtype.val (corePairing_coreRowEquiv D b)
  simp only [coreMatrix, fullMatrixOf, Matrix.of_apply, Matrix.submatrix_apply, coreDiagram_row,
    coreDiagram_col]
  have : ((coreRowEquiv D) b : Fin n) = coreRowEmb D b := rfl
  rw [this] at *
  simp only [coreRowEquiv, Equiv.coe_fn_mk] at hb ⊢
  rw [hb]
  rfl

end SkewCoframeRigidity.UnitRestoration
