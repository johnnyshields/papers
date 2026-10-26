import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import SkewGluing.Diagram
import SkewGluing.TransposeSchur

/-!
# Cell diagrams and profiles

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the paragraph on profiles before `lem:gluing-row-action`: a connected diagram has a profile
`(r; g)`, its row lengths and adjacent overlaps minus one, top to bottom, and the profile
determines the diagram up to translation.

A diagram is a finite set of cells of `ℤ × ℤ`.  This file connects these cell diagrams with the
profiles of `SkewGluing.Profile`.

* `Profile.cells P`: the cell diagram of a profile, with row `i` on the columns
  `[ζ_i + i, ξ_i + i)` (`Profile.isConnectedSkew_cells`).
* `IsConnectedSkew.exists_profile`, `sigma_eq_of_translate_cells`: every connected skew diagram
  is a translate of `P.cells` for exactly one profile `P`.
* `cellProfile D`: the profile of a connected skew diagram, as an `AnyProfile`;
  `cellProfile_cells`, `IsConnectedSkew.exists_translate_cells`, `cellProfile_translate`,
  `cellProfile_eq_iff`: the two directions are inverse up to translation.
* `cellProfile_spec`: the profile is read off the rows (`rowLength`, `rowOverlap`, `numRows`,
  `topRow`): row lengths and adjacent overlaps minus one, top to bottom.
* `cellProfile_rotate`, `cellProfile_transpose`, `cellProfile_antitranspose`: compatibility with
  `rotate`, `transpose`, `antitranspose` (and `Profile.cells_rotate`, `Profile.cells_transpose`
  on cells).
* `span_add_one_eq_numRows_add_numCols`: the span is the number of rows plus the number of
  columns minus one.

Examples from the paper (the hooks, the row `(3)` and the column, the inner `(4, 4, 2) / (2)`)
are checked at the end.

Sorry-free.
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
  have h1 := P.lamRows_antitone h
  have h2 := P.xi_pos i
  have h3 := P.xi_pos i'
  simp only [lamRows] at h1
  omega

theorem zeta_add_antitone (P : Profile n) {i i' : Fin (n + 1)} (h : i ≤ i') :
    P.zeta i' + i' ≤ P.zeta i + i := by
  have h1 := P.muRows_antitone h
  have h2 := P.zeta_nonneg i
  have h3 := P.zeta_nonneg i'
  simp only [muRows] at h1
  omega

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

/-- **Every connected skew diagram is a translate of the cell diagram of a profile.** -/
theorem IsConnectedSkew.exists_profile {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ (n : ℕ) (P : Profile n) (v : ℤ × ℤ), D = translate v P.cells := by
  obtain ⟨t, n, hrows⟩ := hD.exists_rows
  have hne : ∀ k : ℤ, 0 ≤ k → k ≤ n → (rowCols D (t + k)).Nonempty :=
    fun k h1 h2 => (hrows _).mpr ⟨by omega, by omega⟩
  have hstep : ∀ j : Fin n, rowLo D (t + ((j.succ : ℕ) : ℤ)) ≤ rowLo D (t + ((j.castSucc : ℕ) : ℤ))
      ∧ rowHi D (t + ((j.succ : ℕ) : ℤ)) ≤ rowHi D (t + ((j.castSucc : ℕ) : ℤ))
      ∧ rowLo D (t + ((j.castSucc : ℕ) : ℤ)) ≤ rowHi D (t + ((j.succ : ℕ) : ℤ)) := by
    intro j
    have hj := j.isLt
    have e : t + ((j.succ : ℕ) : ℤ) = t + ((j.castSucc : ℕ) : ℤ) + 1 := by simp; ring
    rw [e]
    have h1 : (rowCols D (t + ((j.castSucc : ℕ) : ℤ))).Nonempty :=
      hne _ (by omega) (by omega)
    have h2 : (rowCols D (t + ((j.castSucc : ℕ) : ℤ) + 1)).Nonempty := by
      rw [← e]; exact hne _ (by omega) (by omega)
    exact hD.row_step h1 h2
  let σ : ℤ := rowLo D (t + n)
  let B : Profile.BetaPair n :=
    { xi := fun i => rowHi D (t + ((i : ℕ) : ℤ)) + 1 - σ + n - ((i : ℕ) : ℤ)
      zeta := fun i => rowLo D (t + ((i : ℕ) : ℤ)) - σ + n - ((i : ℕ) : ℤ)
      xi_strictAnti := by
        rw [Fin.strictAnti_iff_succ_lt]
        intro j
        have := (hstep j).2.1
        have e : ((j.succ : ℕ) : ℤ) = ((j.castSucc : ℕ) : ℤ) + 1 := by simp
        simp only [e] at this ⊢
        omega
      zeta_strictAnti := by
        rw [Fin.strictAnti_iff_succ_lt]
        intro j
        have := (hstep j).1
        have e : ((j.succ : ℕ) : ℤ) = ((j.castSucc : ℕ) : ℤ) + 1 := by simp
        simp only [e] at this ⊢
        omega
      zeta_last := by simp [σ]
      zeta_le_xi_succ := by
        intro j
        have := (hstep j).2.2
        have e : ((j.succ : ℕ) : ℤ) = ((j.castSucc : ℕ) : ℤ) + 1 := by simp
        simp only [e] at this ⊢
        omega
      xi_last_pos := by
        have h := rowLo_le (rowHi_mem (hne n (by omega) (le_refl _)))
        simp only [Fin.val_last, σ] at h ⊢
        omega }
  refine ⟨n, Profile.ofBetaPair B, (t, σ - n), ?_⟩
  have hxi : (Profile.ofBetaPair B).xi = B.xi := by
    have := Profile.equivBetaPair.right_inv B
    exact congrArg Profile.BetaPair.xi this
  have hzeta : (Profile.ofBetaPair B).zeta = B.zeta := by
    have := Profile.equivBetaPair.right_inv B
    exact congrArg Profile.BetaPair.zeta this
  ext ⟨a, b⟩
  rw [mem_translate]
  simp only [Prod.mk_sub_mk]
  rw [Profile.mem_cells]
  simp only [hxi, hzeta, B, σ]
  constructor
  · intro hab
    have hrow : (rowCols D a).Nonempty := ⟨b, mem_rowCols.mpr hab⟩
    obtain ⟨h1, h2⟩ := (hrows a).mp hrow
    have hlo := rowLo_le hab
    have hhi := le_rowHi hab
    have hk : (a - t).toNat < n + 1 := by omega
    have hi : (((a - t).toNat : ℕ) : ℤ) = a - t := Int.toNat_of_nonneg (by omega)
    refine ⟨⟨(a - t).toNat, hk⟩, by simpa using hi, ?_⟩
    simp only [hi, show t + (a - t) = a by ring]
    omega
  · rintro ⟨i, hi, h1, h2⟩
    have hrow := hne i (by omega) (by have := i.isLt; omega)
    have ha : a = t + i := by omega
    rw [ha, hD.1.mem_iff_row hrow]
    omega

/-! ### Uniqueness of the profile up to translation -/

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
    (⟨n, P⟩ : AnyProfile) = ⟨m, Q⟩ := by
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

/-- The profile of a connected skew diagram: its row lengths `r` and adjacent overlaps minus one
`g`, top to bottom, as a profile with any number of rows.  For a diagram that is not connected
skew the value is the junk profile of the row `(3)`; use it only through `IsConnectedSkew`. -/
noncomputable def cellProfile (D : Diagram) : AnyProfile :=
  if h : IsConnectedSkew D then
    ⟨h.exists_profile.choose, h.exists_profile.choose_spec.choose⟩
  else ⟨0, rowProfile⟩

/-- A diagram that is a translate of the cell diagram of `P` has profile `P`. -/
theorem cellProfile_of_eq_translate {D : Diagram} {n : ℕ} {P : Profile n} {v : ℤ × ℤ}
    (h : D = translate v P.cells) : cellProfile D = ⟨n, P⟩ := by
  have hD : IsConnectedSkew D := by
    rw [h]; exact isConnectedSkew_translate v P.isConnectedSkew_cells
  unfold cellProfile
  simp only [hD, dite_true]
  exact sigma_eq_of_translate_cells
    (hD.exists_profile.choose_spec.choose_spec.choose_spec.symm.trans h)

/-- The profile of the cell diagram of `P` is `P`. -/
theorem cellProfile_cells {n : ℕ} (P : Profile n) : cellProfile P.cells = ⟨n, P⟩ :=
  cellProfile_of_eq_translate (v := 0) (by rw [translate_zero])

/-- The profile of a translate of the cell diagram of `P` is `P`. -/
theorem cellProfile_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) :
    cellProfile (translate v P.cells) = ⟨n, P⟩ :=
  cellProfile_of_eq_translate rfl

/-- **A connected skew diagram is a translate of the cell diagram of its profile.** -/
theorem IsConnectedSkew.exists_translate_cells {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ v, D = translate v (cellProfile D).2.cells := by
  have e : cellProfile D = ⟨_, hD.exists_profile.choose_spec.choose⟩ := by
    simp only [cellProfile, hD, dite_true]
  rw [e]
  exact ⟨_, hD.exists_profile.choose_spec.choose_spec.choose_spec⟩

/-- **The profile is translation invariant.** -/
theorem cellProfile_translate {D : Diagram} (hD : IsConnectedSkew D) (v : ℤ × ℤ) :
    cellProfile (translate v D) = cellProfile D := by
  obtain ⟨w, hw⟩ := hD.exists_translate_cells
  have : translate v D = translate (v + w) (cellProfile D).2.cells := by
    conv_lhs => rw [hw]
    rw [translate_translate]
  rw [cellProfile_of_eq_translate this]

/-- **Diagrams with the same profile are translates of each other.** -/
theorem exists_translate_of_cellProfile_eq {D D' : Diagram} (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (h : cellProfile D = cellProfile D') : ∃ v, D' = translate v D := by
  obtain ⟨w, hw⟩ := hD.exists_translate_cells
  obtain ⟨w', hw'⟩ := hD'.exists_translate_cells
  refine ⟨w' - w, ?_⟩
  rw [hw', hw, ← h, translate_translate]
  have : w' - w + w = w' := by abel
  rw [this]

/-- Two connected skew diagrams are translates of each other exactly when they have the same
profile. -/
theorem cellProfile_eq_iff {D D' : Diagram} (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') :
    cellProfile D = cellProfile D' ↔ ∃ v, D' = translate v D := by
  constructor
  · exact exists_translate_of_cellProfile_eq hD hD'
  · rintro ⟨v, rfl⟩
    exact (cellProfile_translate hD v).symm

/-! ### The profile read off the rows -/

/-- The topmost occupied row (`0` for the empty diagram). -/
def topRow (D : Diagram) : ℤ := if h : (rowSet D).Nonempty then (rowSet D).min' h else 0

theorem rowCols_translate (v : ℤ × ℤ) (D : Diagram) (a : ℤ) :
    rowCols (translate v D) a = (rowCols D (a - v.1)).image (· + v.2) := by
  ext b
  simp only [mem_rowCols, Finset.mem_image]
  rw [mem_translate]
  have e : ((a, b) : ℤ × ℤ) - v = (a - v.1, b - v.2) := rfl
  rw [e]
  constructor
  · intro h
    exact ⟨b - v.2, h, by ring⟩
  · rintro ⟨c, hc, rfl⟩
    have e2 : c + v.2 - v.2 = c := by ring
    rw [e2]
    exact hc

theorem Profile.rowCols_cells {n : ℕ} (P : Profile n) (i : Fin (n + 1)) :
    rowCols P.cells ((i : ℕ) : ℤ) = Finset.Ico (P.zeta i + i) (P.xi i + i) := by
  ext b
  rw [mem_rowCols, P.mem_cells_fin, Finset.mem_Ico]

theorem Profile.rowCols_cells_eq_empty {n : ℕ} (P : Profile n) {a : ℤ} (h : a < 0 ∨ (n : ℤ) < a) :
    rowCols P.cells a = ∅ := by
  ext b
  rw [mem_rowCols]
  simp only [Finset.notMem_empty, iff_false]
  intro hb
  have := P.row_of_mem_cells hb
  simp only at this
  omega

theorem rowSet_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) :
    rowSet (translate v P.cells) = Finset.Icc v.1 (v.1 + n) := by
  ext a
  rw [mem_rowSet, Finset.mem_Icc, rowCols_translate]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h
    obtain ⟨c, hc, -⟩ := Finset.mem_image.mp hb
    have := P.row_of_mem_cells (mem_rowCols.mp hc)
    simp only at this
    omega
  · rintro ⟨h1, h2⟩
    have hk : (a - v.1).toNat < n + 1 := by omega
    have hi : (((a - v.1).toNat : ℕ) : ℤ) = a - v.1 := Int.toNat_of_nonneg (by omega)
    have := P.rowCols_cells ⟨(a - v.1).toNat, hk⟩
    simp only [hi] at this
    rw [this]
    have hr := P.xi_sub_zeta ⟨(a - v.1).toNat, hk⟩
    have hp := P.r_pos ⟨(a - v.1).toNat, hk⟩
    refine Finset.Nonempty.image ⟨P.zeta ⟨(a - v.1).toNat, hk⟩ + (a - v.1),
      Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩ _
    · omega
    · omega

/-- A translate of the cell diagram of a profile with `n + 1` rows has `n + 1` occupied rows. -/
theorem numRows_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) :
    numRows (translate v P.cells) = n + 1 := by
  unfold numRows
  rw [rowSet_translate_cells, Int.card_Icc]
  omega

/-- The top row of a translate of the cell diagram of a profile by `v` is `v₁`. -/
theorem topRow_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) :
    topRow (translate v P.cells) = v.1 := by
  have hne : (rowSet (translate v P.cells)).Nonempty := by
    rw [rowSet_translate_cells]; exact ⟨v.1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
  simp only [topRow, hne, dite_true]
  have hmem : v.1 ∈ rowSet (translate v P.cells) := by
    rw [rowSet_translate_cells]; exact Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩
  have h : (rowSet (translate v P.cells)).min' hne ∈ Finset.Icc v.1 (v.1 + n) := by
    rw [← rowSet_translate_cells P v]; exact Finset.min'_mem _ hne
  exact le_antisymm (Finset.min'_le _ _ hmem) (Finset.mem_Icc.mp h).1

/-- The length of row `v₁ + i` of a translate of the cell diagram of `P` is `r_i`. -/
theorem rowLength_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) (i : Fin (n + 1)) :
    rowLength (translate v P.cells) (v.1 + (i : ℕ)) = P.r i := by
  unfold rowLength
  rw [rowCols_translate, Finset.card_image_of_injective _ (add_left_injective _)]
  have : v.1 + ((i : ℕ) : ℤ) - v.1 = ((i : ℕ) : ℤ) := by ring
  rw [this, P.rowCols_cells, Int.card_Ico]
  have := P.xi_sub_zeta i
  omega

/-- Rows `v₁ + j` and `v₁ + j + 1` of a translate of the cell diagram of `P` share `g_j + 1`
columns. -/
theorem rowOverlap_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) (j : Fin n) :
    rowOverlap (translate v P.cells) (v.1 + (j : ℕ)) = P.g j + 1 := by
  unfold rowOverlap
  rw [rowCols_translate, rowCols_translate, ← Finset.image_inter _ _ (add_left_injective _),
    Finset.card_image_of_injective _ (add_left_injective _)]
  have e1 : v.1 + ((j : ℕ) : ℤ) - v.1 = ((j.castSucc : ℕ) : ℤ) := by simp
  have e2 : v.1 + ((j : ℕ) : ℤ) + 1 - v.1 = ((j.succ : ℕ) : ℤ) := by simp; ring
  rw [e1, e2, P.rowCols_cells, P.rowCols_cells]
  have hz := P.zeta_strictAnti (Fin.castSucc_lt_succ (i := j))
  have hg := P.xi_succ_sub_zeta_castSucc j
  have hx := P.xi_strictAnti (Fin.castSucc_lt_succ (i := j))
  have hjs : ((j.succ : ℕ) : ℤ) = (j.castSucc : ℕ) + 1 := by simp
  have : Finset.Ico (P.zeta j.castSucc + ((j.castSucc : ℕ) : ℤ))
      (P.xi j.castSucc + ((j.castSucc : ℕ) : ℤ)) ∩
      Finset.Ico (P.zeta j.succ + ((j.succ : ℕ) : ℤ)) (P.xi j.succ + ((j.succ : ℕ) : ℤ))
      = Finset.Ico (P.zeta j.castSucc + ((j.castSucc : ℕ) : ℤ))
        (P.xi j.succ + ((j.succ : ℕ) : ℤ)) := by
    ext b
    simp only [Finset.mem_inter, Finset.mem_Ico]
    omega
  rw [this, Int.card_Ico]
  omega

/-- **The profile of a connected skew diagram, read off its rows.**  The profile has
`numRows D` rows, its row lengths are the numbers of cells in the rows of `D` from the top, and
its overlaps minus one are the numbers of columns shared by consecutive rows, minus one. -/
theorem cellProfile_spec {D : Diagram} (hD : IsConnectedSkew D) :
    (cellProfile D).1 + 1 = numRows D ∧
    (∀ i : Fin ((cellProfile D).1 + 1),
      ((cellProfile D).2.r i : ℕ) = rowLength D (topRow D + (i : ℕ))) ∧
    (∀ j : Fin (cellProfile D).1,
      (cellProfile D).2.g j + 1 = rowOverlap D (topRow D + (j : ℕ))) := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have ht := topRow_translate_cells (cellProfile D).2 v
  have hn := numRows_translate_cells (cellProfile D).2 v
  rw [← hv] at ht hn
  refine ⟨hn.symm, fun i => ?_, fun j => ?_⟩
  · have := rowLength_translate_cells (cellProfile D).2 v i
    rw [← hv] at this
    rw [ht]
    exact this.symm
  · have := rowOverlap_translate_cells (cellProfile D).2 v j
    rw [← hv] at this
    rw [ht]
    exact this.symm

/-! ### Rotation, transpose and antitransposition -/

theorem rotate_translate_eq (v : ℤ × ℤ) (D : Diagram) :
    rotate (translate v D) = translate (-v) (rotate D) := by
  ext y
  rw [mem_rotate, mem_translate, mem_translate, mem_rotate]
  have : -y - v = -(y + v) := by abel
  rw [this]
  constructor <;> intro h <;> simpa using h

theorem transpose_translate_eq (v : ℤ × ℤ) (D : Diagram) :
    transpose (translate v D) = translate v.swap (transpose D) := by
  ext y
  rw [mem_transpose, mem_translate, mem_translate, mem_transpose]
  rfl

theorem antitranspose_translate_eq (v : ℤ × ℤ) (D : Diagram) :
    antitranspose (translate v D) = translate (-v.2, -v.1) (antitranspose D) := by
  ext y
  rw [mem_antitranspose, mem_translate, mem_translate, mem_antitranspose]
  have : (-y.2, -y.1) - v = (-y.2 - v.1, -y.1 - v.2) := rfl
  rw [this]
  have h2 : (-(y - (-v.2, -v.1)).2, -(y - (-v.2, -v.1)).1) = (-y.2 - v.1, -y.1 - v.2) := by
    ext <;> simp <;> ring
  rw [h2]

namespace Profile

variable {n : ℕ}

/-- **Rotation.**  The cell diagram of the rotated profile is the rotated cell diagram, up to
the translation `(n, ξ₀ + n - 1)`. -/
theorem cells_rotate (P : Profile n) :
    P.rotate.cells = translate (n, P.xi 0 + n - 1) (SkewGluing.rotate P.cells) := by
  ext ⟨a, b⟩
  rw [mem_translate, mem_rotate, mem_cells (P := P.rotate), mem_cells (P := P)]
  have e : -(((a, b) : ℤ × ℤ) - ((n : ℤ), P.xi 0 + n - 1)) = ((n : ℤ) - a, P.xi 0 + n - 1 - b) := by
    ext <;> simp
  rw [e]
  have hrv : ∀ i : Fin (n + 1), ((i.rev : ℕ) : ℤ) = n - i := by
    intro i; rw [Fin.val_rev]; push_cast; omega
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    rw [P.zeta_rotate] at h1
    rw [P.xi_rotate] at h2
    refine ⟨i.rev, by rw [hrv]; omega, ?_, ?_⟩ <;> rw [hrv] <;> omega
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨i.rev, by rw [hrv]; omega, ?_⟩
    rw [P.zeta_rotate, P.xi_rotate, Fin.rev_rev, hrv]
    omega

end Profile

namespace Profile

variable {n : ℕ}

/-- The cells of `P.cells` in natural coordinates are the cells of the skew shape `λ / μ`. -/
theorem mem_cells_nat (P : Profile n) (a b : ℕ) :
    (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)) ∈ P.cells ↔ (a, b) ∈ Shields.skewCells P.lam P.mu := by
  by_cases ha : a < n + 1
  · rw [show (a, b) = (((⟨a, ha⟩ : Fin (n + 1)) : ℕ), b) from rfl, P.mem_skewCells_row]
    exact P.mem_cells_fin ⟨a, ha⟩ b
  · constructor
    · intro h
      have := P.row_of_mem_cells h
      simp only [Nat.cast_le] at this
      omega
    · intro h
      rw [Shields.mem_skewCells] at h
      have := ((mem_lam P a b).mp h.1).1
      omega

theorem nonneg_col_of_mem_cells (P : Profile n) {x : ℤ × ℤ} (h : x ∈ P.cells) : 0 ≤ x.2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨i, hi, h1, -⟩ := mem_cells.mp h
  have := P.zeta_nonneg i
  simp only
  omega

theorem nat_cell_of_mem_cells (P : Profile n) {x : ℤ × ℤ} (h : x ∈ P.cells) :
    ∃ a b : ℕ, x = ((a : ℤ), (b : ℤ)) := by
  obtain ⟨a, b⟩ := x
  have h1 := P.row_of_mem_cells h
  have h2 := P.nonneg_col_of_mem_cells h
  simp only at h1 h2
  exact ⟨a.toNat, b.toNat, by ext <;> simp <;> omega⟩

/-- Cells of the transpose, read through the cells of `P`. -/
theorem mem_cells_transpose (P : Profile n) (i c : ℤ) :
    (i, c) ∈ P.transpose.cells ↔ (c - P.lastCol, n + i) ∈ P.cells := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := P.transpose.nat_cell_of_mem_cells h
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    rw [P.transpose.mem_cells_nat] at h
    have hl := P.le_of_mem_cells_transpose h
    obtain ⟨k, rfl⟩ : ∃ k, b = k + P.lastCol := ⟨b - P.lastCol, by omega⟩
    have := (P.mem_cells_transpose_iff a k).mp h
    have e : (((k + P.lastCol : ℕ) : ℤ) - P.lastCol) = (k : ℤ) := by push_cast; ring
    rw [e]
    have := (P.mem_cells_nat k (n + a)).mpr this
    simpa using this
  · intro h
    obtain ⟨a, b, hab⟩ := P.nat_cell_of_mem_cells h
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hnat := (P.mem_cells_nat a b).mp (by rw [← h1, ← h2]; exact h)
    have hb := P.le_of_mem_cells hnat
    obtain ⟨m, rfl⟩ : ∃ m, b = n + m := ⟨b - n, by omega⟩
    have hi : i = (m : ℤ) := by push_cast at h2; omega
    have hc : c = ((a + P.lastCol : ℕ) : ℤ) := by push_cast; omega
    rw [hi, hc]
    rw [P.transpose.mem_cells_nat]
    exact (P.mem_cells_transpose_iff m a).mpr hnat

/-- **Transpose.**  The cell diagram of the transposed profile is the transposed cell diagram,
up to the translation `(-n, lastCol)`. -/
theorem cells_transpose (P : Profile n) :
    P.transpose.cells = translate (-(n : ℤ), (P.lastCol : ℤ)) (SkewGluing.transpose P.cells) := by
  ext ⟨i, c⟩
  rw [mem_translate, mem_transpose, mem_cells_transpose]
  have e : ((i, c) - (-(n : ℤ), (P.lastCol : ℤ)) : ℤ × ℤ).swap = (c - P.lastCol, i + n) := by
    ext <;> simp
  rw [e, add_comm (n : ℤ) i]

end Profile

/-- Translating by `w` and then by `-w` is the identity. -/
theorem translate_neg_translate_cancel (w : ℤ × ℤ) (D : Diagram) :
    translate (-w) (translate w D) = D := by
  rw [translate_translate, neg_add_cancel, translate_zero]

/-- The profile of the rotation of a translate of `P.cells` is `P*`. -/
theorem cellProfile_rotate_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) :
    cellProfile (rotate (translate v P.cells)) = ⟨n, P.rotate⟩ := by
  have h2 : rotate P.cells = translate (-((n : ℤ), P.xi 0 + n - 1)) P.rotate.cells := by
    rw [P.cells_rotate, translate_neg_translate_cancel]
  refine cellProfile_of_eq_translate (v := -v + -((n : ℤ), P.xi 0 + n - 1)) ?_
  rw [rotate_translate_eq, h2, translate_translate]

/-- **Compatibility with rotation.**  The profile of the rotation of a connected skew diagram is
the rotation of its profile (`Diagram.rotate` ↔ `Profile.rotate`). -/
theorem cellProfile_rotate {D : Diagram} (hD : IsConnectedSkew D) :
    cellProfile (rotate D) = ⟨(cellProfile D).1, (cellProfile D).2.rotate⟩ := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have := cellProfile_rotate_translate_cells (cellProfile D).2 v
  rw [← hv] at this
  exact this

/-- The profile of the transpose of a translate of `P.cells` is `Pᵗ`. -/
theorem cellProfile_transpose_translate_cells {n : ℕ} (P : Profile n) (v : ℤ × ℤ) :
    cellProfile (transpose (translate v P.cells)) = ⟨P.lastCol, P.transpose⟩ := by
  have h2 : transpose P.cells = translate (-(-(n : ℤ), (P.lastCol : ℤ))) P.transpose.cells := by
    rw [P.cells_transpose, translate_neg_translate_cancel]
  refine cellProfile_of_eq_translate (v := v.swap + -(-(n : ℤ), (P.lastCol : ℤ))) ?_
  rw [transpose_translate_eq, h2, translate_translate]

/-- **Compatibility with transposition.**  The profile of the transpose of a connected skew
diagram is the transpose of its profile (`Diagram.transpose` ↔ `Profile.transpose`). -/
theorem cellProfile_transpose {D : Diagram} (hD : IsConnectedSkew D) :
    cellProfile (transpose D) = transposeAny (cellProfile D) := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have := cellProfile_transpose_translate_cells (cellProfile D).2 v
  rw [← hv] at this
  exact this

/-- `AT(D)` is the rotation of the transpose. -/
theorem antitranspose_eq_rotate_transpose (D : Diagram) :
    antitranspose D = rotate (transpose D) := by
  ext y
  rw [mem_antitranspose, mem_rotate, mem_transpose]
  rfl

/-- **Compatibility with antitransposition.**  The profile of `AT(D)` is the antitranspose of the
profile of `D` (`Diagram.antitranspose` ↔ `Profile.antitranspose`). -/
theorem cellProfile_antitranspose {D : Diagram} (hD : IsConnectedSkew D) :
    cellProfile (antitranspose D) =
      ⟨(cellProfile D).2.lastCol, (cellProfile D).2.antitranspose⟩ := by
  rw [antitranspose_eq_rotate_transpose, cellProfile_rotate (isConnectedSkew_transpose hD),
    cellProfile_transpose hD]
  rfl


/-! ### Span -/

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

/-- **Span of a connected diagram: rows plus columns minus one**, on profiles: the number of
rows of `P` is `n + 1`, the number of rows of `Pᵗ` is `lastCol + 1`, and the span is `ξ₀`. -/
theorem span_cells_eq (P : Profile n) : (span P.cells : ℤ) + 1 = (n + 1) + (P.lastCol + 1) := by
  rw [span_cells, P.lastCol_eq]
  ring

end Profile

/-- The number of columns of a diagram: the number of rows of its transpose. -/
def numCols (D : Diagram) : ℕ := numRows (transpose D)

/-- The number of columns is the number of occupied columns. -/
theorem numCols_eq_card_image_snd (D : Diagram) : numCols D = (D.image Prod.snd).card := by
  unfold numCols numRows rowSet transpose
  rw [Finset.image_image]
  rfl

/-- **The span of a connected skew diagram is the number of rows plus the number of columns
minus one.** -/
theorem span_add_one_eq_numRows_add_numCols {D : Diagram} (hD : IsConnectedSkew D) :
    (span D : ℤ) + 1 = (numRows D : ℤ) + numCols D := by
  obtain ⟨v, hv⟩ := hD.exists_translate_cells
  have h1 := cellProfile_spec hD
  have h2 := cellProfile_spec (isConnectedSkew_transpose hD)
  rw [cellProfile_transpose hD] at h2
  have h3 := (cellProfile D).2.span_cells_eq
  have e := span_translate (D := (cellProfile D).2.cells) v
  rw [← hv] at e
  have h4 : numRows D = (cellProfile D).1 + 1 := h1.1.symm
  have h5 : numCols D = (cellProfile D).2.lastCol + 1 := h2.1.symm
  rw [e, h4, h5]
  exact h3

/-! ### Examples from the paper -/

section Examples

/-- The cell diagram of the hook profile is the hook `(2, 1)`, shifted one column to the right. -/
example : hookProfile.cells = translate (0, 1) (skewOf [2, 1] []) := by decide

/-- The profile of the hook `(2, 1)` is `(2, 1; 0)`. -/
theorem cellProfile_hook : cellProfile (skewOf [2, 1] []) = ⟨1, hookProfile⟩ :=
  cellProfile_of_eq_translate (v := (0, -1)) (by decide)

/-- The profile of the rotated hook `(2, 2) / (1)` is `(1, 2; 0)`. -/
theorem cellProfile_hookRotated : cellProfile (skewOf [2, 2] [1]) = ⟨1, hookRotatedProfile⟩ :=
  cellProfile_of_eq_translate (v := (0, -1)) (by decide)

/-- Rotation of the hook, on cells and on profiles. -/
example : cellProfile (rotate (skewOf [2, 1] [])) = ⟨1, hookRotatedProfile⟩ := by
  rw [cellProfile_rotate (by decide), cellProfile_hook]
  rw [hookRotatedProfile_eq_rotate]

/-- The row `(3)` has profile `(3)` and its transpose, the column, has profile `(1, 1, 1; 0, 0)`. -/
theorem cellProfile_row : cellProfile (skewOf [3] []) = ⟨0, rowProfile⟩ :=
  cellProfile_of_eq_translate (v := (0, 0)) (by decide)

/-- The profile of the column `(1, 1, 1)`. -/
theorem cellProfile_column : cellProfile (skewOf [1, 1, 1] []) = ⟨2, columnProfile⟩ :=
  cellProfile_of_eq_translate (v := (0, -2)) (by decide)

/-- Transposition of the row `(3)` gives the column, on cells and on profiles. -/
example : cellProfile (transpose (skewOf [3] [])) = cellProfile (skewOf [1, 1, 1] []) := by
  rw [cellProfile_transpose (by decide), cellProfile_row, cellProfile_column]
  exact Sigma.ext (by decide) (heq_of_eq transpose_rowProfile)

/-- The profile `(2, 4, 2; 1, 1)`: the inner `(4, 4, 2) / (2)` of the gauge example. -/
def innerExampleProfile : Profile 2 where
  r := ![2, 4, 2]
  g := ![1, 1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The profile of the inner `(4, 4, 2) / (2)` of the gauge example is `(2, 4, 2; 1, 1)`. -/
theorem cellProfile_inner : cellProfile (skewOf [4, 4, 2] [2]) = ⟨2, innerExampleProfile⟩ :=
  cellProfile_of_eq_translate (v := (0, -2)) (by decide)

/-- Row counts and the span formula on the inner `(4, 4, 2) / (2)`: three rows, four columns,
span six. -/
example : numRows (skewOf [4, 4, 2] [2]) = 3 ∧ numCols (skewOf [4, 4, 2] [2]) = 4 ∧
    span (skewOf [4, 4, 2] [2]) = 6 := by decide

example : rowLength (skewOf [4, 4, 2] [2]) 0 = 2 ∧ rowLength (skewOf [4, 4, 2] [2]) 1 = 4 ∧
    rowOverlap (skewOf [4, 4, 2] [2]) 0 = 2 ∧ rowOverlap (skewOf [4, 4, 2] [2]) 1 = 2 := by
  decide

end Examples

end SkewGluing
