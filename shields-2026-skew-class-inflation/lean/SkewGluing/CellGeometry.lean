/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/CellProfile.lean;
-- retained the cell, connectivity, translation-uniqueness, and content-interval interface.
-- The profile sum is spelled explicitly instead of importing the transpose interface.
import SkewGluing.Diagram
import SkewGluing.Profile

/-!
# Connected cell geometry of full row profiles

Actual cell intervals, skew connectivity, profile recovery up to translation,
and the full content span.  Sorry-free.
-/

namespace SkewGluing

/-! ### Rows of a diagram -/

/-- Cells `x`, `y` are joined by a chain of cells of `D`, consecutive ones sharing an edge. -/
abbrev DiagReach (D : Diagram) : ℤ × ℤ → ℤ × ℤ → Prop :=
  Relation.ReflTransGen fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b

theorem DiagReach.symm {D : Diagram} {x y : ℤ × ℤ} (h : DiagReach D x y) : DiagReach D y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.head ⟨hab.2.1, hab.1, hab.2.2.symm'⟩ ih

theorem DiagReach.trans {D : Diagram} {x y z : ℤ × ℤ} (h : DiagReach D x y)
    (h' : DiagReach D y z) : DiagReach D x z :=
  Relation.ReflTransGen.trans h h'

/-- The columns of the cells of `D` in row `a`. -/
def rowCols (D : Diagram) (a : ℤ) : Finset ℤ := (D.filter fun x => x.1 = a).image Prod.snd

theorem mem_rowCols {D : Diagram} {a b : ℤ} : b ∈ rowCols D a ↔ (a, b) ∈ D := by
  simp only [rowCols, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hxy, rfl⟩, rfl⟩
    exact hxy
  · intro h
    exact ⟨a, b, ⟨h, rfl⟩, rfl⟩

/-- Cells in one row of a skew diagram are joined by a chain inside the row. -/
theorem IsSkew.reach_row {D : Diagram} (hs : IsSkew D) {a b c : ℤ} (hb : (a, b) ∈ D)
    (hc : (a, c) ∈ D) : DiagReach D (a, b) (a, c) := by
  have key : ∀ b c : ℤ, b ≤ c → (a, b) ∈ D → (a, c) ∈ D → DiagReach D (a, b) (a, c) := by
    intro b c hbc
    induction c, hbc using Int.leInduction with
    | base => intro _ _; exact Relation.ReflTransGen.refl
    | succ c hbc ih =>
      intro hb hc
      have hc' : (a, c) ∈ D := hs.mem hb hc (le_refl a) (by omega) (le_refl a) (le_refl a)
        (by omega) (by omega)
      refine Relation.ReflTransGen.tail (ih hb hc') ⟨hc', hc, ?_⟩
      rw [cellAdj_iff]; simp
  rcases le_total b c with h | h
  · exact key b c h hb hc
  · exact (key c b h hc hb).symm

/-- A diagram all of whose cells are joined to one cell is edge-connected. -/
theorem isEdgeConnected_of_reach {D : Diagram} {c₀ : ℤ × ℤ} (h₀ : c₀ ∈ D)
    (h : ∀ x ∈ D, DiagReach D c₀ x) : IsEdgeConnected D :=
  ⟨⟨c₀, h₀⟩, fun x hx y hy => (h x hx).symm.trans (h y hy)⟩

/-- **Discrete intermediate value theorem for rows.**  An edge-connected diagram meets every
row between two of its rows. -/
theorem IsEdgeConnected.exists_row {D : Diagram} (hD : IsEdgeConnected D) {x y : ℤ × ℤ}
    (hx : x ∈ D) (hy : y ∈ D) {i : ℤ} (h1 : min x.1 y.1 ≤ i) (h2 : i ≤ max x.1 y.1) :
    ∃ z ∈ D, z.1 = i := by
  have key : ∀ y, DiagReach D x y → ∀ i, min x.1 y.1 ≤ i → i ≤ max x.1 y.1 → ∃ z ∈ D, z.1 = i := by
    intro y hxy
    induction hxy with
    | refl =>
      intro i h1 h2
      exact ⟨x, hx, by simp at h1 h2; omega⟩
    | @tail b c _ hab ih =>
      intro i h1 h2
      have hadj := cellAdj_iff.mp hab.2.2
      by_cases hin : min x.1 b.1 ≤ i ∧ i ≤ max x.1 b.1
      · exact ih i hin.1 hin.2
      · refine ⟨c, hab.2.1, ?_⟩
        simp only [min_def, max_def] at hin h1 h2
        split_ifs at hin h1 h2 <;> omega
  exact key y (hD.2 x hx y hy) i h1 h2

/-- An edge-connected diagram has a pair of vertically adjacent cells across every horizontal
line that separates two of its cells. -/
theorem IsEdgeConnected.exists_vertical {D : Diagram} (hD : IsEdgeConnected D) {x y : ℤ × ℤ}
    (hx : x ∈ D) (hy : y ∈ D) {a : ℤ} (h1 : x.1 ≤ a) (h2 : a < y.1) :
    ∃ c, (a, c) ∈ D ∧ (a + 1, c) ∈ D := by
  have key : ∀ y, DiagReach D x y → a < y.1 → ∃ c, (a, c) ∈ D ∧ (a + 1, c) ∈ D := by
    intro y hxy
    induction hxy with
    | refl => intro h; omega
    | @tail b c _ hab ih =>
      intro h
      by_cases hb : a < b.1
      · exact ih hb
      · have hadj := cellAdj_iff.mp hab.2.2
        have hb1 : b.1 = a := by omega
        refine ⟨b.2, ?_, ?_⟩
        · have : b = (a, b.2) := Prod.ext hb1 rfl
          rw [← this]; exact hab.1
        · have hc : c = (a + 1, b.2) := Prod.ext (by omega) (by omega)
          rw [← hc]; exact hab.2.1
  exact key y (hD.2 x hx y hy) h2

/-- The first (leftmost) column `s_a` of row `a` (`0` if the row is empty). -/
def rowLo (D : Diagram) (a : ℤ) : ℤ :=
  if h : (rowCols D a).Nonempty then (rowCols D a).min' h else 0

/-- The last (rightmost) column of row `a` (`0` if the row is empty). -/
def rowHi (D : Diagram) (a : ℤ) : ℤ :=
  if h : (rowCols D a).Nonempty then (rowCols D a).max' h else 0

/-- The number of cells in row `a`. -/
def rowLength (D : Diagram) (a : ℤ) : ℕ := (rowCols D a).card

/-- The number of columns in which rows `a` and `a + 1` both have a cell. -/
def rowOverlap (D : Diagram) (a : ℤ) : ℕ := (rowCols D a ∩ rowCols D (a + 1)).card

/-- The set of occupied rows. -/
def rowSet (D : Diagram) : Finset ℤ := D.image Prod.fst

/-- The number of occupied rows. -/
def numRows (D : Diagram) : ℕ := (rowSet D).card

theorem mem_rowSet {D : Diagram} {a : ℤ} : a ∈ rowSet D ↔ (rowCols D a).Nonempty := by
  simp only [rowSet, Finset.mem_image, Prod.exists, Finset.Nonempty, mem_rowCols]
  constructor
  · rintro ⟨x, y, h, rfl⟩; exact ⟨y, h⟩
  · rintro ⟨y, h⟩; exact ⟨a, y, h, rfl⟩

theorem rowLo_mem {D : Diagram} {a : ℤ} (h : (rowCols D a).Nonempty) : (a, rowLo D a) ∈ D := by
  simp only [rowLo, h, dite_true]
  exact mem_rowCols.mp (Finset.min'_mem _ h)

theorem rowHi_mem {D : Diagram} {a : ℤ} (h : (rowCols D a).Nonempty) : (a, rowHi D a) ∈ D := by
  simp only [rowHi, h, dite_true]
  exact mem_rowCols.mp (Finset.max'_mem _ h)

theorem rowLo_le {D : Diagram} {a b : ℤ} (h : (a, b) ∈ D) : rowLo D a ≤ b := by
  have hne : (rowCols D a).Nonempty := ⟨b, mem_rowCols.mpr h⟩
  simp only [rowLo, hne, dite_true]
  exact Finset.min'_le _ _ (mem_rowCols.mpr h)

theorem le_rowHi {D : Diagram} {a b : ℤ} (h : (a, b) ∈ D) : b ≤ rowHi D a := by
  have hne : (rowCols D a).Nonempty := ⟨b, mem_rowCols.mpr h⟩
  simp only [rowHi, hne, dite_true]
  exact Finset.le_max' _ _ (mem_rowCols.mpr h)

/-- In a skew diagram a nonempty row is the interval `[s_a, h_a]`. -/
theorem IsSkew.mem_iff_row {D : Diagram} (hs : IsSkew D) {a b : ℤ}
    (h : (rowCols D a).Nonempty) : (a, b) ∈ D ↔ rowLo D a ≤ b ∧ b ≤ rowHi D a := by
  constructor
  · intro hb; exact ⟨rowLo_le hb, le_rowHi hb⟩
  · rintro ⟨h1, h2⟩
    exact hs.mem (rowLo_mem h) (rowHi_mem h) (le_refl a) (by omega) (le_refl a) (le_refl a) h1 h2

theorem IsSkew.rowCols_eq {D : Diagram} (hs : IsSkew D) {a : ℤ} (h : (rowCols D a).Nonempty) :
    rowCols D a = Finset.Icc (rowLo D a) (rowHi D a) := by
  ext b
  rw [mem_rowCols, hs.mem_iff_row h, Finset.mem_Icc]

/-- **Rows of a connected skew diagram.**  The occupied rows form an interval of integers. -/
theorem IsConnectedSkew.exists_rows {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ t : ℤ, ∃ n : ℕ, ∀ a : ℤ, (rowCols D a).Nonempty ↔ t ≤ a ∧ a ≤ t + n := by
  have hne : (rowSet D).Nonempty := hD.2.1.image _
  refine ⟨(rowSet D).min' hne, ((rowSet D).max' hne - (rowSet D).min' hne).toNat, fun a => ?_⟩
  have hle : (rowSet D).min' hne ≤ (rowSet D).max' hne := Finset.min'_le_max' _ hne
  rw [← mem_rowSet]
  constructor
  · intro ha
    have h1 := Finset.min'_le _ _ ha
    have h2 := Finset.le_max' _ _ ha
    omega
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    obtain ⟨y, hy, hyy⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    obtain ⟨z, hz, hza⟩ := hD.2.exists_row hx hy (i := a) (by omega) (by omega)
    exact Finset.mem_image.mpr ⟨z, hz, hza⟩

/-- In a connected diagram, two consecutive nonempty rows share a column. -/
theorem IsEdgeConnected.exists_overlap {D : Diagram} (hD : IsEdgeConnected D) {a : ℤ}
    (h1 : (rowCols D a).Nonempty) (h2 : (rowCols D (a + 1)).Nonempty) :
    ∃ c, (a, c) ∈ D ∧ (a + 1, c) ∈ D :=
  hD.exists_vertical (rowLo_mem h1) (rowLo_mem h2) (le_refl a) (by simp)

/-- **Skew conditions on consecutive rows.**  For consecutive nonempty rows of a connected skew
diagram, the lower row starts and ends no later, and the two rows overlap. -/
theorem IsConnectedSkew.row_step {D : Diagram} (hD : IsConnectedSkew D) {a : ℤ}
    (h1 : (rowCols D a).Nonempty) (h2 : (rowCols D (a + 1)).Nonempty) :
    rowLo D (a + 1) ≤ rowLo D a ∧ rowHi D (a + 1) ≤ rowHi D a ∧ rowLo D a ≤ rowHi D (a + 1) := by
  obtain ⟨c, hc1, hc2⟩ := hD.2.exists_overlap h1 h2
  have l1 := rowLo_le hc1
  have l2 := le_rowHi hc2
  have h3 : (a + 1, rowLo D a) ∈ D :=
    hD.1.mem (rowLo_mem h1) hc2 (by omega) l1 (by omega) (by omega) (le_refl _) l1
  have h4 : (a, rowHi D (a + 1)) ∈ D :=
    hD.1.mem hc1 (rowHi_mem h2) (by omega) l2 (le_refl _) (by omega) l2 (le_refl _)
  exact ⟨rowLo_le h3, le_rowHi h4, by omega⟩


end SkewGluing

namespace SkewGluing

namespace Profile

variable {n : ℕ}

/-- The cell diagram of a profile `P` with beta lists `ξ`, `ζ`: row `i` (`0 ≤ i ≤ n`, from the
top) occupies the columns `[ζ_i + i, ξ_i + i)`. -/
def cells (P : Profile n) : Diagram :=
  Finset.univ.biUnion fun i : Fin (n + 1) =>
    (Finset.Ico (P.zeta i + i) (P.xi i + i)).image fun j => ((i : ℤ), j)

/-- Membership in the cell diagram of a profile. -/
theorem mem_cells {P : Profile n} {a b : ℤ} :
    (a, b) ∈ P.cells ↔ ∃ i : Fin (n + 1), (i : ℤ) = a ∧ P.zeta i + i ≤ b ∧ b < P.xi i + i := by
  simp only [cells, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨i, j, hj, rfl, rfl⟩
    exact ⟨i, rfl, hj⟩
  · rintro ⟨i, rfl, hj⟩
    exact ⟨i, b, hj, rfl, rfl⟩

/-- Membership in row `i` of the cell diagram of a profile. -/
theorem mem_cells_fin (P : Profile n) (i : Fin (n + 1)) (b : ℤ) :
    ((i : ℤ), b) ∈ P.cells ↔ P.zeta i + i ≤ b ∧ b < P.xi i + i := by
  rw [mem_cells]
  constructor
  · rintro ⟨i', hi', h⟩
    have : i' = i := Fin.ext (by exact_mod_cast hi')
    subst this
    exact h
  · intro h
    exact ⟨i, rfl, h⟩

theorem row_of_mem_cells {P : Profile n} {x : ℤ × ℤ} (h : x ∈ P.cells) :
    0 ≤ x.1 ∧ x.1 ≤ n := by
  obtain ⟨a, b⟩ := x
  obtain ⟨i, hi, -⟩ := mem_cells.mp h
  have := i.isLt
  simp only at hi ⊢
  omega

theorem content_of_mem_cells {P : Profile n} {i : Fin (n + 1)} {b : ℤ}
    (h : ((i : ℤ), b) ∈ P.cells) : P.zeta i ≤ b - i ∧ b - i < P.xi i := by
  rw [mem_cells_fin] at h
  omega

/-- The cell diagram of a profile has exactly `r_i` cells in row `i`. -/
theorem card_cells_row (P : Profile n) (i : Fin (n + 1)) :
    (P.cells.filter fun x => x.1 = ((i : ℕ) : ℤ)).card = P.r i := by
  have h : P.cells.filter (fun x => x.1 = ((i : ℕ) : ℤ)) =
      (Finset.Ico (P.zeta i + i) (P.xi i + i)).image fun j => ((i : ℤ), j) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨b, (mem_cells_fin P i b).mp hc, rfl, rfl⟩
    · rintro ⟨j, hj, rfl, rfl⟩
      exact ⟨(mem_cells_fin P i j).mpr hj, rfl⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Int.card_Ico]
  have := P.xi_sub_zeta i
  omega

/-! ### The cell diagram of a profile is connected skew -/

theorem xi_add_antitone (P : Profile n) {i i' : Fin (n + 1)} (h : i ≤ i') :
    P.xi i' + i' ≤ P.xi i + i := by
  have ha : Antitone (fun j : Fin (n + 1) => P.xi j + (j.val : ℤ)) := by
    rw [Fin.antitone_iff_succ_le]
    intro j
    have he := P.xi_strictAnti (Fin.castSucc_lt_succ (i := j))
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    omega
  exact ha h

theorem zeta_add_antitone (P : Profile n) {i i' : Fin (n + 1)} (h : i ≤ i') :
    P.zeta i' + i' ≤ P.zeta i + i := by
  have ha : Antitone (fun j : Fin (n + 1) => P.zeta j + (j.val : ℤ)) := by
    rw [Fin.antitone_iff_succ_le]
    intro j
    have he := P.zeta_strictAnti (Fin.castSucc_lt_succ (i := j))
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    omega
  exact ha h

/-- The cell diagram of a profile is skew. -/
theorem isSkew_cells (P : Profile n) : IsSkew P.cells := by
  intro x hx y hy hxy1 hxy2 i hi j hj
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨i₁, hi₁, hb₁, hb₂⟩ := mem_cells.mp hx
  obtain ⟨i₂, hi₂, hd₁, hd₂⟩ := mem_cells.mp hy
  simp only [Finset.mem_Icc] at hi hj hxy1 hxy2
  have hi₀ : 0 ≤ i := by omega
  have hin : i.toNat < n + 1 := by have := i₂.isLt; omega
  set k : Fin (n + 1) := ⟨i.toNat, hin⟩ with hk
  have hkv : ((k : ℕ) : ℤ) = i := by simp [hk]; omega
  have h1 : i₁ ≤ k := by rw [Fin.le_def]; simp only [hk]; omega
  have h2 : k ≤ i₂ := by rw [Fin.le_def]; simp only [hk]; omega
  have e1 := P.zeta_add_antitone h1
  have e2 := P.xi_add_antitone h2
  rw [← hkv, mem_cells_fin]
  omega

/-- The cell diagram of a profile is nonempty. -/
theorem cells_nonempty (P : Profile n) : P.cells.Nonempty :=
  ⟨((0 : Fin (n + 1)) , P.zeta 0 + 0), by
    simp only [Fin.val_zero, Nat.cast_zero]
    have := (mem_cells_fin P 0 (P.zeta 0 + 0)).mpr ⟨by simp, by have := P.r_pos 0
                                                                have := P.xi_sub_zeta 0
                                                                simp; omega⟩
    simpa using this⟩

theorem xi_succ_add_le (P : Profile n) (j : Fin n) :
    P.xi j.succ + (j.succ : ℕ) ≤ P.xi j.castSucc + (j.castSucc : ℕ) :=
  P.xi_add_antitone (Fin.castSucc_le_succ j)

/-- Consecutive rows of a profile cell diagram contain a vertically adjacent pair of cells, in the
column `ζ_i + i`. -/
theorem mem_cells_vertical (P : Profile n) (j : Fin n) :
    (((j.castSucc : ℕ) : ℤ), P.zeta j.castSucc + (j.castSucc : ℕ)) ∈ P.cells ∧
    (((j.succ : ℕ) : ℤ), P.zeta j.castSucc + (j.castSucc : ℕ)) ∈ P.cells := by
  have hz := P.zeta_strictAnti (Fin.castSucc_lt_succ (i := j))
  have hg := P.xi_succ_sub_zeta_castSucc j
  have hr := P.xi_sub_zeta j.castSucc
  have hr' := P.r_pos j.castSucc
  have hgn := P.g_lt_succ j
  have hjs : ((j.succ : ℕ) : ℤ) = (j.castSucc : ℕ) + 1 := by simp
  constructor
  · rw [mem_cells_fin]; omega
  · rw [mem_cells_fin]; omega

/-- The cell diagram of a profile is edge-connected. -/
theorem isEdgeConnected_cells (P : Profile n) : IsEdgeConnected P.cells := by
  have hbase : ∀ m : ℕ, ∀ hm : m < n + 1, ∀ b : ℤ, ((m : ℤ), b) ∈ P.cells →
      DiagReach P.cells (0, P.zeta 0) ((m : ℤ), b) := by
    intro m
    induction m with
    | zero =>
      intro hm b hb
      have h0 : ((0 : ℤ), P.zeta 0) ∈ P.cells := by
        have := (mem_cells_fin P 0 (P.zeta 0 + ((0 : Fin (n + 1)) : ℕ))).mpr
          ⟨by simp, by have := P.xi_sub_zeta 0; have := P.r_pos 0; simp; omega⟩
        simpa using this
      exact (P.isSkew_cells.reach_row h0 (by simpa using hb))
    | succ m ih =>
      intro hm b hb
      have hmn : m < n := by omega
      set j : Fin n := ⟨m, hmn⟩ with hj
      obtain ⟨hv1, hv2⟩ := P.mem_cells_vertical j
      have hjc : ((j.castSucc : ℕ) : ℤ) = m := by simp [hj]
      have hjs : ((j.succ : ℕ) : ℤ) = (m : ℤ) + 1 := by simp [hj]
      rw [hjc] at hv1
      rw [hjs] at hv2
      have hr1 := ih (by omega) _ hv1
      have hstep : DiagReach P.cells (m, P.zeta j.castSucc + (j.castSucc : ℕ))
          ((m : ℤ) + 1, P.zeta j.castSucc + (j.castSucc : ℕ)) :=
        Relation.ReflTransGen.single ⟨hv1, hv2, by rw [cellAdj_iff]; simp⟩
      have hrow := P.isSkew_cells.reach_row hv2 (show (((m + 1 : ℕ) : ℤ), b) ∈ P.cells from hb)
      have : (((m + 1 : ℕ) : ℤ), b) = ((m : ℤ) + 1, b) := by push_cast; rfl
      rw [this]
      exact (hr1.trans hstep).trans hrow
  refine isEdgeConnected_of_reach (c₀ := (0, P.zeta 0)) ?_ ?_
  · have := (mem_cells_fin P 0 (P.zeta 0 + ((0 : Fin (n + 1)) : ℕ))).mpr
      ⟨by simp, by have := P.xi_sub_zeta 0; have := P.r_pos 0; simp; omega⟩
    simpa using this
  · rintro ⟨a, b⟩ hx
    obtain ⟨i, hi, -⟩ := mem_cells.mp hx
    have := hbase i i.isLt b (by rw [hi]; exact hx)
    rw [hi] at this
    exact this

/-- **The cell diagram of a profile is a connected skew diagram.** -/
theorem isConnectedSkew_cells (P : Profile n) : IsConnectedSkew P.cells :=
  ⟨P.isSkew_cells, P.isEdgeConnected_cells⟩

end Profile

namespace Profile

variable {n : ℕ}

/-- A profile is determined by its cell diagram. -/
theorem eq_of_cells_eq_cells {P Q : Profile n} (h : P.cells = Q.cells) : P = Q := by
  have key : ∀ (i : Fin (n + 1)) (b : ℤ),
      (P.zeta i + i ≤ b ∧ b < P.xi i + i) ↔ (Q.zeta i + i ≤ b ∧ b < Q.xi i + i) := by
    intro i b
    rw [← mem_cells_fin, ← mem_cells_fin, h]
  have hr := fun i => P.xi_sub_zeta i
  have hr' := fun i => Q.xi_sub_zeta i
  have hp := fun i => P.r_pos i
  have hq := fun i => Q.r_pos i
  have hz : P.zeta = Q.zeta := by
    funext i
    have h1 := (key i (P.zeta i + i)).mp ⟨le_refl _, by have := hr i; have := hp i; omega⟩
    have h2 := (key i (Q.zeta i + i)).mpr ⟨le_refl _, by have := hr' i; have := hq i; omega⟩
    omega
  have hx : P.xi = Q.xi := by
    funext i
    have h1 := (key i (P.xi i + i - 1)).mp ⟨by have := hr i; have := hp i; omega, by omega⟩
    have h2 := (key i (Q.xi i + i - 1)).mpr ⟨by have := hr' i; have := hq i; omega, by omega⟩
    omega
  exact eq_of_beta_eq hx hz

theorem mem_cells_diag (P : Profile n) : ((n : ℤ), (n : ℤ)) ∈ P.cells := by
  have := (mem_cells_fin P (Fin.last n) n).mpr
    ⟨by simp [zeta_last], by have := P.xi_pos (Fin.last n); simp; omega⟩
  simpa using this

theorem mem_cells_top (P : Profile n) : ((0 : ℤ), P.zeta 0) ∈ P.cells := by
  have := (mem_cells_fin P 0 (P.zeta 0 + ((0 : Fin (n + 1)) : ℕ))).mpr
    ⟨by simp, by have := P.xi_sub_zeta 0; have := P.r_pos 0; simp; omega⟩
  simpa using this

end Profile

/-- **The profile is determined by the diagram up to translation**: if two profiles have
translate-equal cell diagrams, they are equal (with the same number of rows). -/
theorem sigma_eq_of_translate_cells {n m : ℕ} {P : Profile n} {Q : Profile m} {v w : ℤ × ℤ}
    (h : translate v P.cells = translate w Q.cells) :
    (⟨n, P⟩ : (k : ℕ) × Profile k) = ⟨m, Q⟩ := by
  have key : ∀ y : ℤ × ℤ, y ∈ P.cells ↔ y + (v - w) ∈ Q.cells := by
    intro y
    have := congrArg (fun S => y + v ∈ S) h
    simp only [mem_translate, add_sub_cancel_right] at this
    rw [this]
    have : y + v - w = y + (v - w) := by abel
    rw [this]
  set u := v - w with hu
  have hu1 : u.1 = 0 := by
    have h1 := (key _).mp P.mem_cells_top
    have h2 := Profile.row_of_mem_cells h1
    obtain ⟨a, b⟩ := Q.mem_cells_top |> fun h => ((0 : ℤ), Q.zeta 0)
    have h3 : (((0 : ℤ), Q.zeta 0) + (-u)) ∈ P.cells := by
      rw [key]; simpa using Q.mem_cells_top
    have h4 := Profile.row_of_mem_cells h3
    simp only [Prod.fst_add, Prod.fst_neg] at h2 h4
    omega
  have hnm : n = m := by
    have h1 := (key _).mp P.mem_cells_diag
    have h2 := Profile.row_of_mem_cells h1
    have h3 : (((m : ℤ), (m : ℤ)) + (-u)) ∈ P.cells := by
      rw [key]; simpa using Q.mem_cells_diag
    have h4 := Profile.row_of_mem_cells h3
    simp only [Prod.fst_add, Prod.fst_neg] at h2 h4
    omega
  subst hnm
  have hu2 : u.2 = 0 := by
    have h1 := (key _).mp P.mem_cells_diag
    have h3 : (((n : ℤ), (n : ℤ)) + (-u)) ∈ P.cells := by
      rw [key]; simpa using Q.mem_cells_diag
    have q1 : ((n : ℤ), (n : ℤ)) + u = ((n : ℤ), (n : ℤ) + u.2) := by ext <;> simp [hu1]
    have q2 : ((n : ℤ), (n : ℤ)) + -u = ((n : ℤ), (n : ℤ) + -u.2) := by ext <;> simp [hu1]
    rw [q1] at h1
    rw [q2] at h3
    have e1 := (Profile.mem_cells_fin Q (Fin.last n) (n + u.2)).mp (by simpa using h1)
    have e2 := (Profile.mem_cells_fin P (Fin.last n) (n + -u.2)).mp (by simpa using h3)
    simp only [Profile.zeta_last] at e1 e2
    simp at e1 e2
    omega
  have hu0 : u = 0 := Prod.ext hu1 hu2
  have hc : P.cells = Q.cells := by
    ext y
    rw [key, hu0, add_zero]
  rw [Profile.eq_of_cells_eq_cells hc]

namespace Profile

variable {n : ℕ}

/-- The contents of the cell diagram of `P` are `[0, ξ₀ - 1]`. -/
theorem contents_cells (P : Profile n) : contents P.cells = Finset.Icc 0 (P.xi 0 - 1) := by
  ext k
  rw [mem_contents_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i', hi', h1, h2⟩ := mem_cells.mp hi
    have := P.zeta_nonneg i'
    have h3 := P.xi_add_antitone (Fin.zero_le i')
    simp only [Fin.val_zero] at h3
    omega
  · rintro ⟨h1, h2⟩
    set S : Finset (Fin (n + 1)) := Finset.univ.filter fun i => k < P.xi i with hS
    have hne : S.Nonempty := ⟨0, by simp [hS]; omega⟩
    set i := S.max' hne with hi
    have hik : k < P.xi i := by
      have := Finset.max'_mem S hne
      simpa [hS] using this
    have hz : P.zeta i ≤ k := by
      by_cases hl : i = Fin.last n
      · rw [hl, P.zeta_last]; omega
      · have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hl
        have hn : (i.val : ℕ) < n := by simpa [Fin.lt_def] using hlt
        set j : Fin n := ⟨i.val, hn⟩ with hj
        have hjc : j.castSucc = i := Fin.ext rfl
        have hnot : ¬ k < P.xi j.succ := by
          intro hk
          have hmem : j.succ ∈ S := by simp [hS, hk]
          have := Finset.le_max' S _ hmem
          rw [← hi] at this
          have : (j.succ : Fin (n + 1)).val ≤ i.val := this
          simp [hj] at this
        have := P.zeta_le_xi_succ j
        rw [hjc] at this
        omega
    exact ⟨i, (mem_cells_fin P i _).mpr ⟨by omega, by omega⟩⟩

/-- The span of the cell diagram of `P` is `ξ₀`. -/
theorem span_cells (P : Profile n) : (span P.cells : ℤ) = P.xi 0 := by
  unfold span
  rw [contents_cells, Int.card_Icc]
  have := P.xi_pos 0
  omega

end Profile
end SkewGluing
