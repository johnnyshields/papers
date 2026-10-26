import SkewBase.SchurEqualConnected
import SkewBase.Copied.Diagram

/-!
# A cell-set diagram Schur-equal to a connected diagram is connected

Formalizes `shields-2026-skew-base-computational.tex`, `lem:invariants`: let `F` be connected and
`s_H = s_F`; then `H` is connected, `|H| = |F|`, and `H` has the row lengths, the gaps, and for
every `k ≥ 1` the numbers of columns shared by `k` consecutive rows of `F`.

Here `H` is a cell set `H ⊆ ℤ × ℤ` (`SkewGluing.Diagram`) and connectedness is `IsConnectedSkew`,
skew and edge-connected.  The skew Schur function of a cell set is read through a presentation
of it by beta lists (`BetaRows.cells`, `HasSchur`): `H` is a translate of the cells of a
`BetaRows` diagram `B`, and `s_H = s_B`, the Jacobi–Trudi determinant `det (h_{ξ_i - ζ_j})`.
Every presentation of `H` with `s_B = s_F` is covered, so no choice among presentations enters.

The route is a bridge from the row form of `lem:invariants` (`BetaRows.connected_of_schur_eq`:
the nonempty rows are consecutive and adjacent ones share a column) to cell sets: the cells of a
`BetaRows` diagram are a skew set (`BetaRows.isSkew_cells`), consecutive nonempty rows with
adjacent rows sharing a column are edge-connected (`BetaRows.isEdgeConnected_cells`), and the
numbers of columns shared by `k` consecutive rows, counted on cells, are the row overlap
partitions of the beta lists (`BetaRows.overlapPartition_cells`).  The irreducibility of the skew
Schur function of a connected diagram is not used.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-! ### Row overlaps counted on cells -/

/-- The columns of the cells in row `i` of a diagram. -/
def columnsOfRow (D : Diagram) (i : ℤ) : Finset ℤ := (D.filter fun x => x.1 = i).image Prod.snd

/-- The number of columns shared by the `k` consecutive rows `i, …, i + k - 1` of a diagram. -/
def sharedColumns (D : Diagram) (k : ℕ) (i : ℤ) : ℕ :=
  ((columnsOfRow D i).filter fun c => ∀ t : ℕ, t < k → (i + t, c) ∈ D).card

/-- The row overlap partition `ρ^{(k)}` of a diagram, `k ≥ 1`: the positive numbers of columns
shared by `k` consecutive rows, as a multiset over the starting rows. -/
def overlapPartition (D : Diagram) (k : ℕ) : Multiset ℕ :=
  ((D.image Prod.fst).filter fun i => 0 < sharedColumns D k i).val.map (sharedColumns D k)

/-- The multiset of row lengths of a diagram: the numbers of cells in its nonempty rows. -/
def rowLengths (D : Diagram) : Multiset ℕ :=
  (D.image Prod.fst).val.map fun i => (D.filter fun x => x.1 = i).card

/-- The multiset of gaps of a diagram: the numbers of columns shared by two adjacent rows, minus
one, over the pairs of adjacent rows that share a column. -/
def gapMultiset (D : Diagram) : Multiset ℕ := (overlapPartition D 2).map (· - 1)

theorem card_filter_row (D : Diagram) (i : ℤ) :
    (D.filter fun x => x.1 = i).card = (columnsOfRow D i).card := by
  unfold columnsOfRow
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
  exact Prod.ext (hx.2.trans hy.2.symm) hxy

theorem mem_columnsOfRow {D : Diagram} {i c : ℤ} : c ∈ columnsOfRow D i ↔ (i, c) ∈ D := by
  unfold columnsOfRow
  simp only [Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨h1, h2⟩, h3⟩
    subst h2 h3
    exact h1
  · intro h
    exact ⟨i, c, ⟨h, rfl⟩, rfl⟩

theorem rowLengths_eq_overlapPartition_one (D : Diagram) :
    rowLengths D = overlapPartition D 1 := by
  have hs : ∀ i, sharedColumns D 1 i = (columnsOfRow D i).card := by
    intro i
    unfold sharedColumns
    congr 1
    refine Finset.filter_true_of_mem fun c hc => ?_
    intro t ht
    have : t = 0 := by omega
    subst this
    simpa using mem_columnsOfRow.mp hc
  have hpos : ∀ i ∈ D.image Prod.fst, 0 < sharedColumns D 1 i := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    rw [hs]
    exact Finset.card_pos.mpr ⟨x.2, mem_columnsOfRow.mpr hx⟩
  unfold overlapPartition rowLengths
  rw [Finset.filter_true_of_mem hpos]
  refine Multiset.map_congr rfl fun i _ => ?_
  rw [hs, card_filter_row]

/-- The area of a diagram is the sum of its row lengths. -/
theorem card_eq_sum_rowLengths (D : Diagram) : D.card = (rowLengths D).sum := by
  rw [rowLengths, Finset.card_eq_sum_card_image Prod.fst D, Finset.sum_eq_multiset_sum]

/-! ### The cells of a diagram given by beta lists -/

namespace BetaRows

variable {ℓ : ℕ}

/-- The cells of the diagram with beta lists `ξ`, `ζ`: row `i < ℓ` occupies the columns
`[ζ_i + i, ξ_i + i)`. -/
def cells (B : BetaRows ℓ) : Diagram :=
  (Finset.range ℓ).biUnion fun i =>
    (Finset.Ico (B.zeta i + i) (B.xi i + i)).image fun j => ((i : ℤ), j)

theorem mem_cells {B : BetaRows ℓ} {i : ℕ} {j : ℤ} :
    ((i : ℤ), j) ∈ B.cells ↔ i < ℓ ∧ B.zeta i + i ≤ j ∧ j < B.xi i + i := by
  simp only [cells, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Ico,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, c, hc, hkc, rfl⟩
    have : k = i := by exact_mod_cast hkc
    subst this
    exact ⟨hk, hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨i, h1, j, h2, rfl, rfl⟩

theorem exists_mem_cells {B : BetaRows ℓ} {x : ℤ × ℤ} (hx : x ∈ B.cells) :
    ∃ i : ℕ, x.1 = i ∧ i < ℓ ∧ B.zeta i + i ≤ x.2 ∧ x.2 < B.xi i + i := by
  simp only [cells, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Ico] at hx
  obtain ⟨k, hk, c, hc, rfl⟩ := hx
  exact ⟨k, rfl, hk, hc⟩

theorem zeta_add_le (B : BetaRows ℓ) {i k : ℕ} (hik : i ≤ k) (hk : k < ℓ) :
    B.zeta k + k ≤ B.zeta i + i := by
  have := B.zeta_gap (i := i) (k - i) (by omega)
  rw [show i + (k - i) = k by omega] at this
  have e : ((k - i : ℕ) : ℤ) = (k : ℤ) - i := by omega
  omega

theorem xi_add_le (B : BetaRows ℓ) {i k : ℕ} (hik : i ≤ k) (hk : k < ℓ) :
    B.xi k + k ≤ B.xi i + i := by
  have := B.xi_gap (i := i) (k - i) (by omega)
  rw [show i + (k - i) = k by omega] at this
  have e : ((k - i : ℕ) : ℤ) = (k : ℤ) - i := by omega
  omega

/-- The cells of a diagram given by beta lists form a skew set. -/
theorem isSkew_cells (B : BetaRows ℓ) : IsSkew B.cells := by
  intro x hx y hy hxy1 hxy2 p hp q hq
  obtain ⟨i, hi, hiℓ, hi1, hi2⟩ := exists_mem_cells hx
  obtain ⟨i', hi', hi'ℓ, hi'1, hi'2⟩ := exists_mem_cells hy
  rw [Finset.mem_Icc] at hp hq
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k := ⟨p.toNat, by omega⟩
  have hik : i ≤ k := by omega
  have hki : k ≤ i' := by omega
  have a1 := B.zeta_add_le hik (by omega)
  have a2 := B.xi_add_le hki hi'ℓ
  exact mem_cells.mpr ⟨by omega, by omega, by omega⟩

end BetaRows

/-- Chains of adjacent cells of a diagram can be reversed. -/
theorem reach_symm {D : Diagram} {x y : ℤ × ℤ}
    (h : Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) x y) :
    Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact (Relation.ReflTransGen.single ⟨hbc.2.1, hbc.1, hbc.2.2.symm'⟩).trans ih

/-- Two cells of one row of a diagram are joined by a chain of cells of the diagram. -/
theorem row_reach (D : Diagram) (i : ℤ) :
    ∀ (d : ℕ) (j : ℤ), (i, j) ∈ D → (i, j + d) ∈ D →
      (∀ c, j ≤ c → c ≤ j + d → (i, c) ∈ D) →
      Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) (i, j) (i, j + d) := by
  intro d
  induction d with
  | zero => intro j _ _ _; simp only [Nat.cast_zero, add_zero]; exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro j hj hj' hall
    have h1 : (i, j + 1) ∈ D := hall (j + 1) (by omega) (by push_cast; omega)
    have step : Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) (i, j) (i, j + 1) :=
      Relation.ReflTransGen.single ⟨hj, h1, by rw [cellAdj_iff]; simp⟩
    have rest := ih (j + 1) h1
      (by rw [show j + 1 + (d : ℤ) = j + ((d + 1 : ℕ) : ℤ) by push_cast; ring]; exact hj')
      (fun c hc1 hc2 => hall c (by omega) (by push_cast at hc2 ⊢; omega))
    rw [show j + ((d + 1 : ℕ) : ℤ) = j + 1 + d by push_cast; ring]
    exact step.trans rest

namespace BetaRows

variable {ℓ : ℕ}

/-- Consecutive nonempty rows `a, …, a + n`, with adjacent rows sharing a column, form an
edge-connected diagram. -/
theorem isEdgeConnected_cells (B : BetaRows ℓ) {a n : ℕ} (hlt : a + n < ℓ)
    (hrows : ∀ i, i < ℓ → (B.zeta i < B.xi i ↔ a ≤ i ∧ i ≤ a + n))
    (hov : ∀ j, j < n → 0 < B.overlap 1 (a + j)) : IsEdgeConnected B.cells := by
  have hrow : ∀ i : ℕ, i < ℓ → ∀ j : ℤ, B.zeta i + i ≤ j → j < B.xi i + i →
      ((i : ℤ), j) ∈ B.cells := fun i hi j h1 h2 => mem_cells.mpr ⟨hi, h1, h2⟩
  have hne : ∀ i : ℕ, a ≤ i → i ≤ a + n → B.zeta i < B.xi i := fun i h1 h2 =>
    (hrows i (by omega)).mpr ⟨h1, h2⟩
  set R := fun x y : ℤ × ℤ => Relation.ReflTransGen
    (fun a b => a ∈ B.cells ∧ b ∈ B.cells ∧ CellAdj a b) x y with hR
  -- two cells of one row are joined
  have rowR : ∀ (i : ℕ) (j j' : ℤ), ((i : ℤ), j) ∈ B.cells → ((i : ℤ), j') ∈ B.cells →
      R ((i : ℤ), j) ((i : ℤ), j') := by
    have key : ∀ (i : ℕ) (j j' : ℤ), j ≤ j' → ((i : ℤ), j) ∈ B.cells → ((i : ℤ), j') ∈ B.cells →
        R ((i : ℤ), j) ((i : ℤ), j') := by
      intro i j j' hjj hj hj'
      obtain ⟨d, hd⟩ : ∃ d : ℕ, j' = j + d := ⟨(j' - j).toNat, by omega⟩
      subst hd
      obtain ⟨hiℓ, h1, h2⟩ := mem_cells.mp hj
      obtain ⟨-, h3, h4⟩ := mem_cells.mp hj'
      exact row_reach B.cells i d j hj hj' (fun c hc1 hc2 => hrow i hiℓ c (by omega) (by omega))
    intro i j j' hj hj'
    rcases le_total j j' with h | h
    · exact key i j j' h hj hj'
    · exact reach_symm (key i j' j h hj' hj)
  have symmR : ∀ x y, R x y → R y x := fun _ _ h => reach_symm h
  set base : ℤ × ℤ := ((a : ℤ), B.zeta a + a) with hbase
  have hbaseMem : base ∈ B.cells :=
    hrow a (by omega) _ le_rfl (by have := hne a le_rfl (by omega); omega)
  -- every cell of row `a + m` is joined to the base cell
  have toBase : ∀ m : ℕ, m ≤ n → ∀ j : ℤ, (((a + m : ℕ) : ℤ), j) ∈ B.cells →
      R (((a + m : ℕ) : ℤ), j) base := by
    intro m
    induction m with
    | zero =>
      intro _ j hj
      exact rowR a j _ (by simpa using hj) hbaseMem
    | succ m ih =>
      intro hm j hj
      have hov' := hov m (by omega)
      simp only [overlap] at hov'
      have hz := B.zeta_lt (a + m) (a + (m + 1)) (by omega) (by omega)
      have e1 : a + m + 1 = a + (m + 1) := by omega
      rw [e1] at hov'
      have hmem1 : (((a + m : ℕ) : ℤ), B.zeta (a + m) + ((a + m : ℕ) : ℤ)) ∈ B.cells :=
        hrow (a + m) (by omega) _ le_rfl (by have := hne (a + m) (by omega) (by omega); omega)
      have hmem2 : (((a + (m + 1) : ℕ) : ℤ), B.zeta (a + m) + ((a + m : ℕ) : ℤ)) ∈ B.cells :=
        hrow (a + (m + 1)) (by omega) _ (by push_cast at hz ⊢; omega)
          (by push_cast at hov' ⊢; omega)
      have vert : R (((a + (m + 1) : ℕ) : ℤ), B.zeta (a + m) + ((a + m : ℕ) : ℤ))
          (((a + m : ℕ) : ℤ), B.zeta (a + m) + ((a + m : ℕ) : ℤ)) :=
        Relation.ReflTransGen.single ⟨hmem2, hmem1, by rw [cellAdj_iff]; push_cast; omega⟩
      exact (rowR (a + (m + 1)) j _ hj hmem2).trans (vert.trans (ih (by omega) _ hmem1))
  refine ⟨⟨base, hbaseMem⟩, fun x hx y hy => ?_⟩
  have reach : ∀ z ∈ B.cells, R z base := by
    intro z hz
    obtain ⟨i, hi1, hiℓ, hi2, hi3⟩ := exists_mem_cells hz
    have hr := (hrows i hiℓ).mp (by omega)
    obtain ⟨m, hm⟩ : ∃ m, i = a + m := ⟨i - a, by omega⟩
    subst hm
    obtain ⟨z1, z2⟩ := z
    simp only at hi1 hi2 hi3
    subst hi1
    exact toBase m (by omega) z2 hz
  exact (reach x hx).trans (symmR _ _ (reach y hy))

end BetaRows

namespace BetaRows

variable {ℓ : ℕ}

theorem mem_columnsOfRow_cells {B : BetaRows ℓ} {i : ℕ} {c : ℤ} :
    c ∈ columnsOfRow B.cells i ↔ i < ℓ ∧ B.zeta i + i ≤ c ∧ c < B.xi i + i := by
  rw [mem_columnsOfRow, mem_cells]

/-- The number of columns shared by `k ≥ 1` consecutive rows, counted on the cells, is the
overlap `overlap (k - 1) i` of the beta lists when the `k` rows lie in the diagram, and `0`
otherwise. -/
theorem sharedColumns_cells (B : BetaRows ℓ) {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    sharedColumns B.cells k i = if i + (k - 1) < ℓ then B.overlap (k - 1) i else 0 := by
  have hcast : ∀ t : ℕ, ((i : ℤ) + (t : ℤ)) = ((i + t : ℕ) : ℤ) := fun t => by push_cast; ring
  split_ifs with h
  · rw [overlap_eq_ncard B (k - 1) h]
    unfold sharedColumns
    rw [← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, rowColumns, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩ t ht1 ht2
      have := h2 (t - i) (by omega)
      rw [hcast, show i + (t - i) = t by omega, mem_cells] at this
      exact ⟨this.2.1, this.2.2⟩
    · intro hc
      refine ⟨mem_columnsOfRow_cells.mpr ⟨by omega, (hc i le_rfl (by omega)).1,
        (hc i le_rfl (by omega)).2⟩, fun t ht => ?_⟩
      rw [hcast, mem_cells]
      exact ⟨by omega, (hc (i + t) (by omega) (by omega)).1, (hc (i + t) (by omega) (by omega)).2⟩
  · unfold sharedColumns
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hall
    have := hall (k - 1) (by omega)
    rw [hcast, mem_cells] at this
    omega

end BetaRows

theorem mem_translate_mk {D : Diagram} {v : ℤ × ℤ} {a b : ℤ} :
    (a, b) ∈ translate v D ↔ (a - v.1, b - v.2) ∈ D := by
  rw [mem_translate]
  rfl

/-- Translating a diagram translates its rows and leaves the columns shared by consecutive rows
unchanged. -/
theorem sharedColumns_translate (D : Diagram) (v : ℤ × ℤ) (k : ℕ) (i : ℤ) :
    sharedColumns (translate v D) k (i + v.1) = sharedColumns D k i := by
  unfold sharedColumns
  have e : ∀ t : ℕ, i + v.1 + (t : ℤ) - v.1 = i + t := fun t => by ring
  have hset : (columnsOfRow (translate v D) (i + v.1)).filter
        (fun c => ∀ t : ℕ, t < k → (i + v.1 + t, c) ∈ translate v D) =
      ((columnsOfRow D i).filter fun c => ∀ t : ℕ, t < k → (i + t, c) ∈ D).image (· + v.2) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, mem_columnsOfRow, mem_translate_mk]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨c - v.2, ⟨?_, fun t ht => ?_⟩, by ring⟩
      · simpa using h1
      · simpa [e t] using h2 t ht
    · rintro ⟨c0, ⟨h1, h2⟩, rfl⟩
      refine ⟨by simpa using h1, fun t ht => ?_⟩
      simpa [e t] using h2 t ht
  rw [hset, Finset.card_image_of_injective _ (add_left_injective v.2)]

theorem overlapPartition_translate (D : Diagram) (v : ℤ × ℤ) (k : ℕ) :
    overlapPartition (translate v D) k = overlapPartition D k := by
  unfold overlapPartition
  have hrows : (translate v D).image Prod.fst = (D.image Prod.fst).image (· + v.1) := by
    ext i
    simp only [Finset.mem_image, Prod.exists, mem_translate_mk, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨b, h⟩
      exact ⟨i - v.1, ⟨_, h⟩, by ring⟩
    · rintro ⟨a, ⟨b, h⟩, rfl⟩
      exact ⟨b + v.2, by simpa using h⟩
  have hS : ((translate v D).image Prod.fst).filter
        (fun i => 0 < sharedColumns (translate v D) k i) =
      ((D.image Prod.fst).filter fun i => 0 < sharedColumns D k i).image (· + v.1) := by
    ext i
    constructor
    · intro hi'
      obtain ⟨hi, hpos⟩ := Finset.mem_filter.mp hi'
      have hi2 : i ∈ (D.image Prod.fst).image (· + v.1) := hrows ▸ hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi2
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, by rwa [sharedColumns_translate] at hpos⟩, rfl⟩
    · intro hi'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi'
      obtain ⟨ha, hpos⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hrows]; exact Finset.mem_image_of_mem _ ha
      · rwa [sharedColumns_translate]
  rw [hS, Finset.image_val_of_injOn (fun a _ b _ hab => add_right_cancel hab), Multiset.map_map]
  refine Multiset.map_congr rfl fun a _ => ?_
  exact sharedColumns_translate D v k a


namespace BetaRows

variable {ℓ : ℕ}

/-- The row overlap partition `ρ^{(k)}` of the cells of a diagram given by beta lists, counted
on cells, is the row overlap partition of the beta lists. -/
theorem overlapPartition_cells (B : BetaRows ℓ) {k : ℕ} (hk : 1 ≤ k) :
    overlapPartition B.cells k = B.rowOverlaps k := by
  have hS : (B.cells.image Prod.fst).filter (fun i => 0 < sharedColumns B.cells k i) =
      ((Finset.range (ℓ - (k - 1))).filter fun i => 0 < B.overlap (k - 1) i).image
        (fun i : ℕ => (i : ℤ)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxr, hpos⟩ := Finset.mem_filter.mp hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxr
      obtain ⟨i, hi1, hiℓ, -, -⟩ := exists_mem_cells hy
      rw [hi1, sharedColumns_cells B hk] at hpos
      split_ifs at hpos with h
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hpos⟩, hi1.symm⟩
      · exact absurd hpos (lt_irrefl 0)
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
      rw [Finset.mem_range] at hi1
      have hpos : 0 < sharedColumns B.cells k i := by
        rw [sharedColumns_cells B hk]
        simp only [show i + (k - 1) < ℓ by omega, ↓reduceIte]
        exact hi2
      refine Finset.mem_filter.mpr ⟨?_, hpos⟩
      obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
      have := mem_columnsOfRow.mp (Finset.mem_filter.mp hc).1
      exact Finset.mem_image.mpr ⟨_, this, rfl⟩
  rw [overlapPartition, hS, Finset.image_val_of_injOn (fun a _ b _ hab => by exact_mod_cast hab),
    Multiset.map_map, rowOverlaps, overlaps, Multiset.filter_map, ← Finset.filter_val]
  have hS2 : (Finset.range (ℓ - (k - 1))).filter ((fun x => 0 < x) ∘ B.overlap (k - 1)) =
      (Finset.range (ℓ - (k - 1))).filter fun i => 0 < B.overlap (k - 1) i :=
    Finset.filter_congr fun _ _ => Iff.rfl
  rw [hS2]
  refine Multiset.map_congr rfl fun i hi => ?_
  obtain ⟨hi1, -⟩ := Finset.mem_filter.mp (Finset.mem_val.mp hi)
  rw [Finset.mem_range] at hi1
  rw [Function.comp_apply, sharedColumns_cells B hk]
  simp only [show i + (k - 1) < ℓ by omega, ↓reduceIte]

end BetaRows

/-- The skew Schur function of a cell-set diagram `D`, read through a presentation by beta lists:
`D` is a translate of the cells of a diagram `B` with `s_B = f`.  Every skew diagram has such a
presentation with the Jacobi–Trudi determinant of its beta lists; the results below hold for
every presentation. -/
def HasSchur (D : Diagram) (f : Lambda) : Prop :=
  ∃ (ℓ : ℕ) (B : BetaRows ℓ) (v : ℤ × ℤ), D = translate v B.cells ∧ B.schur = f

/-- The diagram of a profile, as a cell set, has the skew Schur function of the profile. -/
theorem hasSchur_profile {n : ℕ} (F : Profile n) : HasSchur F.toBetaRows.cells F.schur :=
  ⟨n + 1, F.toBetaRows, 0, translate_zero.symm, Profile.toBetaRows_schur F⟩

/-- **`lem:invariants`, for cell-set diagrams.**  Let `F` be connected and `s_H = s_F` for a
cell-set diagram `H`.  Then `H` is a connected skew diagram (`IsConnectedSkew`), `|H| = |F|`, and
`H` has the row lengths and the gaps of `F`; more generally, for every `k ≥ 1` the numbers of
columns shared by `k` consecutive rows of `H` and of `F` agree. -/
theorem isConnectedSkew_of_hasSchur_eq {n : ℕ} (F : Profile n) {H : Diagram}
    (h : HasSchur H F.schur) :
    IsConnectedSkew H ∧ H.card = ∑ i, F.r i ∧ rowLengths H = F.rowMultiset ∧
      gapMultiset H = F.gapMultiset ∧
      ∀ k, 1 ≤ k → overlapPartition H k = F.toBetaRows.rowOverlaps k := by
  obtain ⟨ℓ, B, v, rfl, hB⟩ := h
  have hF : B.schur = F.toBetaRows.schur := by rw [Profile.toBetaRows_schur]; exact hB
  obtain ⟨a, hlt, hrows, hov⟩ := BetaRows.connected_of_schur_eq F B hB
  have hconn : IsConnectedSkew B.cells := ⟨B.isSkew_cells, B.isEdgeConnected_cells hlt hrows hov⟩
  have key : ∀ k, 1 ≤ k →
      overlapPartition (translate v B.cells) k = F.toBetaRows.rowOverlaps k := fun k hk => by
    rw [overlapPartition_translate, BetaRows.overlapPartition_cells B hk,
      BetaRows.rowOverlaps_eq_of_schur_eq ℓ (n + 1) B F.toBetaRows hF k]
  have hrow : rowLengths (translate v B.cells) = F.rowMultiset := by
    rw [rowLengths_eq_overlapPartition_one, key 1 le_rfl, Profile.rowOverlaps_one_toBetaRows]
  refine ⟨isConnectedSkew_translate v hconn, ?_, hrow, ?_, key⟩
  · rw [card_eq_sum_rowLengths, hrow, Profile.rowMultiset, ← Finset.sum_eq_multiset_sum]
  · rw [gapMultiset, key 2 (by norm_num), Profile.rowOverlaps_two_toBetaRows, Multiset.map_map]
    simp

end SkewBase
