/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.TenNegativeFamilies

/-!
# Finite cells of the ten-negative presentations

The integer cell chart `eq:ten-chart` and the four unions
`eq:ten-family-a-unions`, `eq:ten-cell-unions` of
`shields-2026-skew-jacobi-negative.tex`.  Geometric hypotheses are stated
in cells, independently of the determinant identities.
-/

namespace SkewJacobiNegative
namespace TenCells

abbrev Cell := ℤ × ℤ
abbrev Cells := Finset Cell

/-- One finite horizontal interval, with an excluded right endpoint. -/
def intervalRow (r l u : ℤ) : Cells := {r} ×ˢ Finset.Ico l u

@[simp] theorem mem_intervalRow (p : Cell) (r l u : ℤ) :
    p ∈ intervalRow r l u ↔ p.1 = r ∧ l ≤ p.2 ∧ p.2 < u := by
  rcases p with ⟨i, j⟩
  simp only [intervalRow, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico, Prod.fst, Prod.snd]

/-- Literal translation of the finite cell set. -/
def translate (S : Cells) (t : Cell) : Cells :=
  S.image fun p => (p.1 + t.1, p.2 + t.2)

@[simp] theorem mem_translate (p t : Cell) (S : Cells) :
    p ∈ translate S t ↔ (p.1 - t.1, p.2 - t.2) ∈ S := by
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    have h1 := congrArg Prod.fst hqp
    have h2 := congrArg Prod.snd hqp
    have he : (p.1 - t.1, p.2 - t.2) = q := by
      ext <;> dsimp at h1 h2 ⊢ <;> omega
    simpa only [he] using hq
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(p.1 - t.1, p.2 - t.2), h, ?_⟩
    ext <;> dsimp <;> omega

/-- Integer content of a cell, in the cited work's coordinates. -/
def content (p : Cell) : ℤ := p.2 - p.1

/-- The hatted middle shape is McNamara--van Willigenburg's northwest interior. -/
def hat (S : Cells) : Cells := S.filter fun p => (p.1 + 1, p.2 + 1) ∈ S

/-- The actual row intervals represented by full beta lists.
The common shift by six fixes exactly the normalization used for the seven-row chart. -/
def betaCells (D : BetaDiagram 7) : Cells :=
  Finset.univ.biUnion fun i : Fin 7 =>
    intervalRow i.val (D.col i + i.val - 6) (D.row i + i.val - 6)

/-- Interval geometry of a nonempty connected skew diagram: ordered endpoints,
positive rows, and a cell in every adjacent row intersection. -/
def ConnectedIntervals (S : Cells) : Prop :=
  ∃ (n : ℕ) (z : ℤ) (l u : Fin n → ℤ), 0 < n ∧
    S = Finset.univ.biUnion (fun i : Fin n => intervalRow (z + i.val) (l i) (u i)) ∧
    Antitone l ∧ Antitone u ∧ (∀ i, l i < u i) ∧
    ∀ i : Fin n, ∀ hi : i.val + 1 < n, l i < u ⟨i.val + 1, hi⟩

variable (P : TenParameters)

def L : ℤ := P.a + P.d
def M : ℤ := P.b + P.d
def beta : ℤ := P.b - 1

/-- The exact two-row chart, including its overlap when `d = 0`. -/
def E : Cells := intervalRow 0 (beta P) (beta P + L P) ∪ intervalRow 1 0 (M P)
def Wsw : Cells := intervalRow 1 0 (L P)
def Wne : Cells := intervalRow 0 (beta P) (beta P + L P)
def middle : Cells := intervalRow 1 (L P) (M P)

theorem bounds : 0 < L P ∧ L P ≤ beta P ∧ beta P < M P ∧ L P < M P := by
  have ha := P.a_pos
  have hd := P.d_nonneg
  have hb := P.separated
  dsimp [L, M, beta]
  omega

theorem E_connected : ConnectedIntervals (E P) := by
  have h := bounds P
  refine ⟨2, 0, ![beta P, 0], ![beta P + L P, M P], by decide,
    ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    simp [E, Fin.exists_fin_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num
    all_goals omega
  · intro i j hij
    have ha := P.a_pos
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num
    all_goals dsimp [beta, L, M] at *
    all_goals omega
  · intro i
    have ha := P.a_pos
    have hd := P.d_nonneg
    have hb := P.separated
    fin_cases i <;> norm_num <;> dsimp [beta, L, M] at * <;> omega
  · intro i hi
    fin_cases i
    all_goals norm_num at hi
    all_goals norm_num
    all_goals omega

/-- The marked occurrences are translates of the same row. -/
theorem occurrences_eq : translate (Wsw P) (-1, beta P) = Wne P := by
  ext p
  simp [Wsw, Wne]
  omega

/-- The actual amalgamation identifies exactly the marked overlap. -/
theorem amalgamation_overlap : E P ∩ translate (E P) (-1, beta P) = Wne P := by
  have h := bounds P
  ext p
  simp [E, Wne]
  omega

/-- Removing the northeast occurrence leaves precisely the lower row. -/
theorem delete_ne : E P \ Wne P = intervalRow 1 0 (M P) := by
  ext p
  simp [E, Wne]
  omega

/-- Removing the southwest occurrence leaves two genuine row intervals. -/
theorem delete_sw : E P \ Wsw P =
    intervalRow 0 (beta P) (beta P + L P) ∪ intervalRow 1 (L P) (M P) := by
  have h := bounds P
  ext p
  simp [E, Wsw]
  omega

theorem delete_both : (E P \ Wsw P) \ Wne P = middle P := by
  rw [delete_sw]
  ext p
  simp [Wne, middle]
  omega

/-- The southwest occurrence contains every cell on its content diagonals,
which already implies simultaneous top-and-bottom maximality in Hypothesis I. -/
theorem content_maximal_sw (p : Cell) (hp : p ∈ E P)
    (hd : ∃ q ∈ Wsw P, content q = content p) : p ∈ Wsw P := by
  have h := bounds P
  obtain ⟨q, hq, hc⟩ := hd
  simp only [E, Finset.mem_union, mem_intervalRow] at hp
  simp only [Wsw, mem_intervalRow] at hq ⊢
  dsimp [content] at hc
  omega

/-- An extension of the northeast occurrence must also fit in the southwest
occurrence after alignment.  Maximality is simultaneous, not a claim that
the northeast content diagonals meet no other cell of `E`. -/
theorem content_maximal_ne (p : Cell) (hp : p ∈ E P)
    (hbottom : (p.1 + 1, p.2 - beta P) ∈ E P) : p ∈ Wne P := by
  simp only [E, Finset.mem_union, mem_intervalRow] at hp hbottom
  simp only [Wne, mem_intervalRow]
  omega
/-- Hypothesis I in its simultaneous-extension form: no larger shape can
fit at both of the aligned occurrences.  No diagonal restriction is needed
for this chart, so in particular an extension on the same diagonals cannot exist. -/
theorem simultaneous_maximal (S : Cells) (hmark : Wne P ⊆ S)
    (htop : S ⊆ E P) (hbottom : translate S (1, -beta P) ⊆ E P) :
    S = Wne P := by
  apply Finset.Subset.antisymm
  · intro p hp
    apply content_maximal_ne P p (htop hp)
    apply hbottom
    apply Finset.mem_image.mpr
    refine ⟨p, hp, ?_⟩
    ext <;> simp [sub_eq_add_neg]
  · exact hmark


/-- Simultaneous marked maximality in the sense of `hyp:initial`,
item `ite:maximal`, of McNamara--van Willigenburg.  A candidate extends
the top marking on exactly the same content diagonals and has a translated
copy in the parent containing its southwesternmost cell.  Quantification
over all finite cell sets is stronger than quantification over connected
skew diagrams.  The top anchor is already in the marking being extended. -/
def SimultaneousMarkedMaximal (parent marking : Cells) (southwest : Cell) : Prop :=
  ∀ (S : Cells) (t : Cell), marking ⊆ S → S ⊆ parent →
    S.image content = marking.image content →
    translate S t ⊆ parent → southwest ∈ translate S t → S = marking

/-- Hypothesis I with arbitrary bottom-copy translation, not merely the
original alignment of the two copies of `W`. -/
theorem hypothesis_one :
    (0, beta P + L P - 1) ∈ Wne P ∧
    SimultaneousMarkedMaximal (E P) (Wne P) (1, 0) := by
  refine ⟨?_, ?_⟩
  · have h := bounds P
    apply (mem_intervalRow (0, beta P + L P - 1) 0 (beta P) (beta P + L P)).mpr
    exact ⟨rfl, by omega, by omega⟩
  intro S t hmark htop hdiags hbottom hanchor
  have hb := bounds P
  have he : (0, beta P) ∈ S := by
    apply hmark
    apply (mem_intervalRow (0, beta P) 0 (beta P) (beta P + L P)).mpr
    exact ⟨rfl, le_rfl, by omega⟩
  have het : (t.1, beta P + t.2) ∈ E P := by
    apply hbottom
    apply Finset.mem_image.mpr
    refine ⟨(0, beta P), he, ?_⟩
    simp
  have hq : (1 - t.1, -t.2) ∈ S := by
    simpa only [mem_translate, Prod.fst, Prod.snd, zero_sub] using hanchor
  have hdiag : content (1 - t.1, -t.2) ∈ (Wne P).image content := by
    rw [← hdiags]
    exact Finset.mem_image.mpr ⟨(1 - t.1, -t.2), hq, rfl⟩
  obtain ⟨w, hw, hcontent⟩ := Finset.mem_image.mp hdiag
  simp only [Wne, mem_intervalRow] at hw
  dsimp [content] at hcontent
  apply Finset.Subset.antisymm
  · intro p hp
    have hpE := htop hp
    have hpt : (p.1 + t.1, p.2 + t.2) ∈ E P := by
      apply hbottom
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simp only [E, Finset.mem_union, mem_intervalRow, Prod.fst, Prod.snd] at het hpE hpt
    simp only [Wne, mem_intervalRow]
    omega
  · exact hmark

/-- Hypothesis II: an explicit empty content diagonal between the occurrences. -/
theorem separated_diagonal :
    (∀ p ∈ Wsw P, content p < L P - 1) ∧
    (∀ p ∈ Wne P, L P - 1 < content p) := by
  have h := bounds P
  constructor <;> intro p hp
  · simp only [Wsw, mem_intervalRow] at hp
    dsimp [content]
    omega
  · simp only [Wne, mem_intervalRow] at hp
    dsimp [content]
    omega

theorem clearance : 2 ≤ P.b - P.a - P.d + 1 := by
  have h := P.separated
  omega

/-- The overlap in the southwest-deleted chart has exactly `d+1` cells. -/
theorem deleted_sw_overlap :
    (Finset.Ico (beta P) (M P)).card = (P.d + 1).toNat := by
  simp [beta, M]
  all_goals congr 1
  all_goals ring

/-- Hypothesis III for the northeast deletion. -/
theorem delete_ne_connected : ConnectedIntervals (E P \ Wne P) := by
  rw [delete_ne]
  have h := bounds P
  refine ⟨1, 1, ![0], ![M P], by decide, ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    simp [Fin.exists_fin_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp
  · intro i
    fin_cases i
    simp
    dsimp [M]
    have ha := P.a_pos
    have hd := P.d_nonneg
    have hb := P.separated
    omega
  · intro i hi
    have := i.isLt
    omega

/-- Hypothesis III for the southwest deletion. -/
theorem delete_sw_connected : ConnectedIntervals (E P \ Wsw P) := by
  rw [delete_sw]
  have h := bounds P
  refine ⟨2, 0, ![beta P, L P], ![beta P + L P, M P], by decide,
    ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    simp [Fin.exists_fin_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num
    all_goals omega
  · intro i j hij
    have ha := P.a_pos
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num
    all_goals dsimp [beta, L, M] at *
    all_goals omega
  · intro i
    fin_cases i <;> norm_num <;> omega
  · intro i hi
    fin_cases i
    all_goals norm_num at hi
    all_goals norm_num
    all_goals omega

/-- The middle shape has no northwest-interior cells. -/
theorem hat_middle_empty : hat (middle P) = ∅ := by
  ext p
  simp [hat, middle]
  omega

/-- Hypothesis IV, uniformly over all copies in the infinite amalgamation:
no hatted middle cell exists, so it cannot meet or neighbor a hatted marked cell. -/
theorem hypothesis_four (S : Set Cell) (t : Cell) :
    ∀ p ∈ translate (hat (middle P)) t, ∀ q ∈ S,
      ¬ (|p.1 - q.1| + |p.2 - q.2| = 1) := by
  rw [hat_middle_empty]
  simp [translate]

/-- Exact case-(c) endpoint attachments: the southwest one is horizontal and
not vertical, while the northeast one is vertical and not horizontal. -/
theorem attachment_c :
    (1, L P - 1) ∈ Wsw P ∧ (1, L P) ∈ middle P ∧
    (0, M P - 1) ∈ Wne P ∧ (1, M P - 1) ∈ middle P ∧
    (2, L P) ∉ Wsw P ∧ (1, M P) ∉ Wne P := by
  have h := bounds P
  have ha := P.a_pos
  simp [Wsw, Wne, middle, L, M, beta] at *
  omega

/-- The two actual connected, nontrivial outer skew diagrams in `eq:ten-chart`. -/
def outerA : Cells := intervalRow 0 1 4 ∪ intervalRow 1 0 4 ∪ intervalRow 2 0 4
def outerB : Cells := intervalRow 0 1 3 ∪ intervalRow 1 0 3 ∪
  intervalRow 2 0 3 ∪ intervalRow 3 0 3

theorem outerA_connected : ConnectedIntervals outerA := by
  refine ⟨3, 0, ![1, 0, 0], ![4, 4, 4], by decide, ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    simp [outerA, Fin.exists_fin_succ]
    all_goals tauto
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i hi
    fin_cases i
    all_goals norm_num at hi
    all_goals norm_num

theorem outerB_connected : ConnectedIntervals outerB := by
  refine ⟨4, 0, ![1, 0, 0, 0], ![3, 3, 3, 3], by decide, ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    simp [outerB, Fin.exists_fin_succ]
    all_goals tauto
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i hi
    fin_cases i
    all_goals norm_num at hi
    all_goals norm_num

/-- Properness excludes each of the three trivial factorization shapes:
the outer shape has two distinct cells, the marking is nonempty, and the
inner chart has a cell outside it. -/
theorem proper_outer :
    (0, 1) ∈ outerA ∧ (0, 2) ∈ outerA ∧
    (0, 1) ∈ outerB ∧ (0, 2) ∈ outerB ∧
    (1, 0) ∈ Wsw P ∧ (1, L P) ∈ E P ∧ (1, L P) ∉ Wsw P := by
  have h := bounds P
  simp [outerA, outerB, Wsw, E]
  omega

/-- Translation of copy number `j` on ribbon level `k`. -/
def copyShift (P : TenParameters) (k j : ℤ) : Cell :=
  (k - j, k + j * (P.b - 1))

private theorem range_six : Finset.range 6 = {0, 1, 2, 3, 4, 5} := by decide
private theorem range_four : Finset.range 4 = {0, 1, 2, 3} := by decide

/-- The common ten-copy union from the manuscript. -/
def common : Cells :=
  (Finset.range 6).biUnion (fun j => translate (E P) (copyShift P 0 j)) ∪
  (Finset.range 4).biUnion (fun j => translate (E P) (copyShift P 1 (j + 1 : ℕ)))

/-- The four explicit unions, with precisely the supplemental interfaces
listed in the manuscript.  This definition does not assert a composition theorem. -/
def union : TenKind → Cells
  | .fa => common P ∪ translate (E P) (copyShift P 2 2)
  | .ha => common P ∪ translate (E P) (copyShift P 2 3)
  | .fb => common P ∪ translate (E P) (copyShift P 2 2) ∪
      translate (Wne P) (copyShift P 2 3)
  | .hb => common P ∪ translate (E P) (copyShift P 2 3) ∪
      translate (Wne P) (copyShift P 2 1)

private theorem diagram_row (k : TenKind) (i : Fin 7) :
    (P.diagram k).row i = P.rowBase k i + P.d := rfl

private theorem diagram_col (k : TenKind) (i : Fin 7) :
    (P.diagram k).col i = P.column i := rfl

private theorem E_rows (p : Cell) (hp : p ∈ E P) : p.1 = 0 ∨ p.1 = 1 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Or.inl ((mem_intervalRow _ _ _ _).mp hp).1
  · exact Or.inr ((mem_intervalRow _ _ _ _).mp hp).1

private theorem copy_E_rows (l j : ℤ) (p : Cell)
    (hp : p ∈ translate (E P) (copyShift P l j)) :
    p.1 = l - j ∨ p.1 = l - j + 1 := by
  have h := E_rows P _ ((mem_translate _ _ _).mp hp)
  dsimp [copyShift] at h
  omega

private theorem copy_Wne_row (l j : ℤ) (p : Cell)
    (hp : p ∈ translate (Wne P) (copyShift P l j)) : p.1 = l - j := by
  have h := ((mem_intervalRow _ _ _ _).mp ((mem_translate _ _ _).mp hp)).1
  dsimp [copyShift] at h
  omega

private theorem common_row_support (p : Cell) (hp : p ∈ common P) :
    -5 ≤ p.1 ∧ p.1 ≤ 1 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    have hj' : (j : ℤ) < 6 := by exact_mod_cast Finset.mem_range.mp hj
    have hj0 : (0 : ℤ) ≤ j := by omega
    have h := copy_E_rows P 0 j p hp
    omega
  · obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    have hj' : (j : ℤ) < 4 := by exact_mod_cast Finset.mem_range.mp hj
    have hj0 : (0 : ℤ) ≤ j := by omega
    have h := copy_E_rows P 1 (j + 1 : ℕ) p hp
    push_cast at h
    omega

/-- Every displayed union has only the seven physical rows, without any
restriction on column coordinates or parameter-dependent row widths. -/
theorem union_row_support (k : TenKind) (p : Cell) (hp : p ∈ union P k) :
    -5 ≤ p.1 ∧ p.1 ≤ 1 := by
  cases k with
  | fa =>
    rcases Finset.mem_union.mp hp with hp | hp
    · exact common_row_support P p hp
    · have h := copy_E_rows P 2 2 p hp
      omega
  | ha =>
    rcases Finset.mem_union.mp hp with hp | hp
    · exact common_row_support P p hp
    · have h := copy_E_rows P 2 3 p hp
      omega
  | fb =>
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact common_row_support P p hp
      · have h := copy_E_rows P 2 2 p hp
        omega
    · have h := copy_Wne_row P 2 3 p hp
      omega
  | hb =>
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact common_row_support P p hp
      · have h := copy_E_rows P 2 3 p hp
        omega
    · have h := copy_Wne_row P 2 1 p hp
      omega

private theorem normalized_union_row_support (k : TenKind) (p : Cell)
    (hp : p ∈ translate (union P k) (5, 0)) : 0 ≤ p.1 ∧ p.1 ≤ 6 := by
  have h := union_row_support P k _ ((mem_translate _ _ _).mp hp)
  dsimp at h
  omega

private theorem beta_row_support (D : BetaDiagram 7) (p : Cell)
    (hp : p ∈ betaCells D) : 0 ≤ p.1 ∧ p.1 ≤ 6 := by
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  have hr := ((mem_intervalRow _ _ _ _).mp hp).1
  have hi' : (i.val : ℤ) < 7 := by exact_mod_cast i.isLt
  have hi0 : (0 : ℤ) ≤ i.val := by omega
  omega

private theorem union_outside_membership (k : TenKind) (r c : ℤ)
    (hr : r < 0 ∨ 6 < r) :
    (r,c) ∈ translate (union P k) (5,0) ↔ (r,c) ∈ betaCells (P.diagram k) := by
  constructor
  · intro hp
    have h := normalized_union_row_support P k (r,c) hp
    dsimp at h
    omega
  · intro hp
    have h := beta_row_support (P.diagram k) (r,c) hp
    dsimp at h
    omega

-- Each fixed physical row is normalized before arithmetic is invoked.
macro "ten_beta_row" p:term : tactic => `(tactic|
  (have ha := ($p).a_pos
   have hd := ($p).d_nonneg
   have hb := ($p).separated
   norm_num [union, common, betaCells, E, Wne, copyShift, L, M, beta,
     diagram_row, diagram_col, TenParameters.rowBase, TenParameters.column,
     range_six, range_four, mem_translate, mem_intervalRow, Fin.exists_fin_succ]
   all_goals omega))

private theorem union_fa_row0 (c : ℤ) :
    (0,c) ∈ translate (union P .fa) (5,0) ↔ (0,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_row1 (c : ℤ) :
    (1,c) ∈ translate (union P .fa) (5,0) ↔ (1,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_row2 (c : ℤ) :
    (2,c) ∈ translate (union P .fa) (5,0) ↔ (2,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_row3 (c : ℤ) :
    (3,c) ∈ translate (union P .fa) (5,0) ↔ (3,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_row4 (c : ℤ) :
    (4,c) ∈ translate (union P .fa) (5,0) ↔ (4,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_row5 (c : ℤ) :
    (5,c) ∈ translate (union P .fa) (5,0) ↔ (5,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_row6 (c : ℤ) :
    (6,c) ∈ translate (union P .fa) (5,0) ↔ (6,c) ∈ betaCells (P.diagram .fa) := by ten_beta_row P
private theorem union_fa_outside (r c : ℤ) (hr : r < 0 ∨ 6 < r) :
    (r,c) ∈ translate (union P .fa) (5,0) ↔ (r,c) ∈ betaCells (P.diagram .fa) :=
  union_outside_membership P .fa r c hr

private theorem union_ha_row0 (c : ℤ) :
    (0,c) ∈ translate (union P .ha) (5,0) ↔ (0,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_row1 (c : ℤ) :
    (1,c) ∈ translate (union P .ha) (5,0) ↔ (1,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_row2 (c : ℤ) :
    (2,c) ∈ translate (union P .ha) (5,0) ↔ (2,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_row3 (c : ℤ) :
    (3,c) ∈ translate (union P .ha) (5,0) ↔ (3,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_row4 (c : ℤ) :
    (4,c) ∈ translate (union P .ha) (5,0) ↔ (4,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_row5 (c : ℤ) :
    (5,c) ∈ translate (union P .ha) (5,0) ↔ (5,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_row6 (c : ℤ) :
    (6,c) ∈ translate (union P .ha) (5,0) ↔ (6,c) ∈ betaCells (P.diagram .ha) := by ten_beta_row P
private theorem union_ha_outside (r c : ℤ) (hr : r < 0 ∨ 6 < r) :
    (r,c) ∈ translate (union P .ha) (5,0) ↔ (r,c) ∈ betaCells (P.diagram .ha) :=
  union_outside_membership P .ha r c hr

private theorem union_fb_row0 (c : ℤ) :
    (0,c) ∈ translate (union P .fb) (5,0) ↔ (0,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_row1 (c : ℤ) :
    (1,c) ∈ translate (union P .fb) (5,0) ↔ (1,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_row2 (c : ℤ) :
    (2,c) ∈ translate (union P .fb) (5,0) ↔ (2,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_row3 (c : ℤ) :
    (3,c) ∈ translate (union P .fb) (5,0) ↔ (3,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_row4 (c : ℤ) :
    (4,c) ∈ translate (union P .fb) (5,0) ↔ (4,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_row5 (c : ℤ) :
    (5,c) ∈ translate (union P .fb) (5,0) ↔ (5,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_row6 (c : ℤ) :
    (6,c) ∈ translate (union P .fb) (5,0) ↔ (6,c) ∈ betaCells (P.diagram .fb) := by ten_beta_row P
private theorem union_fb_outside (r c : ℤ) (hr : r < 0 ∨ 6 < r) :
    (r,c) ∈ translate (union P .fb) (5,0) ↔ (r,c) ∈ betaCells (P.diagram .fb) :=
  union_outside_membership P .fb r c hr

private theorem union_hb_row0 (c : ℤ) :
    (0,c) ∈ translate (union P .hb) (5,0) ↔ (0,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_row1 (c : ℤ) :
    (1,c) ∈ translate (union P .hb) (5,0) ↔ (1,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_row2 (c : ℤ) :
    (2,c) ∈ translate (union P .hb) (5,0) ↔ (2,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_row3 (c : ℤ) :
    (3,c) ∈ translate (union P .hb) (5,0) ↔ (3,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_row4 (c : ℤ) :
    (4,c) ∈ translate (union P .hb) (5,0) ↔ (4,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_row5 (c : ℤ) :
    (5,c) ∈ translate (union P .hb) (5,0) ↔ (5,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_row6 (c : ℤ) :
    (6,c) ∈ translate (union P .hb) (5,0) ↔ (6,c) ∈ betaCells (P.diagram .hb) := by ten_beta_row P
private theorem union_hb_outside (r c : ℤ) (hr : r < 0 ∨ 6 < r) :
    (r,c) ∈ translate (union P .hb) (5,0) ↔ (r,c) ∈ betaCells (P.diagram .hb) :=
  union_outside_membership P .hb r c hr

/-- The normalization adds five rows and no columns.  Every family-row
membership equivalence is proved separately, including all outside cells. -/
theorem union_eq_betaCells (k : TenKind) :
    translate (union P k) (5, 0) = betaCells (P.diagram k) := by
  apply Finset.ext
  rintro ⟨r, c⟩
  by_cases hr : r < 0 ∨ 6 < r
  · cases k with
    | fa => exact union_fa_outside P r c hr
    | ha => exact union_ha_outside P r c hr
    | fb => exact union_fb_outside P r c hr
    | hb => exact union_hb_outside P r c hr
  · have h0 : 0 ≤ r := by omega
    have h6 : r ≤ 6 := by omega
    cases k with
    | fa =>
      interval_cases r
      · exact union_fa_row0 P c
      · exact union_fa_row1 P c
      · exact union_fa_row2 P c
      · exact union_fa_row3 P c
      · exact union_fa_row4 P c
      · exact union_fa_row5 P c
      · exact union_fa_row6 P c
    | ha =>
      interval_cases r
      · exact union_ha_row0 P c
      · exact union_ha_row1 P c
      · exact union_ha_row2 P c
      · exact union_ha_row3 P c
      · exact union_ha_row4 P c
      · exact union_ha_row5 P c
      · exact union_ha_row6 P c
    | fb =>
      interval_cases r
      · exact union_fb_row0 P c
      · exact union_fb_row1 P c
      · exact union_fb_row2 P c
      · exact union_fb_row3 P c
      · exact union_fb_row4 P c
      · exact union_fb_row5 P c
      · exact union_fb_row6 P c
    | hb =>
      interval_cases r
      · exact union_hb_row0 P c
      · exact union_hb_row1 P c
      · exact union_hb_row2 P c
      · exact union_hb_row3 P c
      · exact union_hb_row4 P c
      · exact union_hb_row5 P c
      · exact union_hb_row6 P c

/-- The normalized row starts are exactly `(6-r)(b-1)`. -/
theorem beta_left_endpoint (k : TenKind) (i : Fin 7) :
    (P.diagram k).col i + i.val - 6 = (6 - (i.val : ℤ)) * (P.b - 1) := by
  fin_cases i <;> simp [TenParameters.diagram, TenParameters.column] <;> ring

/-- The normalized half-turns of the two outer diagrams. -/
def outerARev : Cells := intervalRow 0 0 4 ∪ intervalRow 1 0 4 ∪ intervalRow 2 0 3
def outerBRev : Cells := intervalRow 0 0 3 ∪ intervalRow 1 0 3 ∪
  intervalRow 2 0 3 ∪ intervalRow 3 0 2

/-- The finite outer cell sets, independent of the inner integer parameters. -/
def outer : TenKind → Cells
  | .fa => outerARev
  | .ha => outerA
  | .fb => outerB
  | .hb => outerBRev

theorem outer_finite_cells (k : TenKind) :
    outer k = match k with
    | .fa => {(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3),
        (2,0), (2,1), (2,2)}
    | .ha => {(0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3),
        (2,0), (2,1), (2,2), (2,3)}
    | .fb => {(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2),
        (3,0), (3,1), (3,2)}
    | .hb => {(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1),
        (2,2), (3,0), (3,1)} := by
  cases k <;> decide

/-- The northwest ribbon level counts preceding cells on the northwest diagonal.
For these outer skew diagrams the diagonal is an interval, so this is the
successive northwest-border-removal decomposition. -/
def ribbonDepth (S : Cells) (p : Cell) : ℕ :=
  (S.filter fun q => q.1 ≤ p.1 ∧ p.1 - q.1 = p.2 - q.2).card - 1

def ribbonIndex (k : TenKind) (p : Cell) : ℤ :=
  content p + match k with | .fa | .ha => 2 | .fb | .hb => 3

/-- Northwest-border membership agrees with the computed ribbon level. -/
theorem ribbon_depth_zero_iff (k : TenKind) (p : Cell) (hp : p ∈ outer k) :
    ribbonDepth (outer k) p = 0 ↔ (p.1 - 1, p.2 - 1) ∉ outer k := by
  cases k <;> rw [outer_finite_cells] at hp ⊢ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Each northwest predecessor lies on the previous ribbon level. -/
theorem ribbon_diagonal_step (k : TenKind) (p : Cell) (hp : p ∈ outer k)
    (hn : (p.1 - 1, p.2 - 1) ∈ outer k) :
    ribbonDepth (outer k) p = ribbonDepth (outer k) (p.1 - 1, p.2 - 1) + 1 := by
  cases k <;> rw [outer_finite_cells] at hp hn ⊢ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try norm_num at hn) <;> decide

/-- A west-to-east step on one northwest ribbon advances by the amalgamation shift. -/
theorem west_ribbon_placement (k : TenKind) (p : Cell)
    (h : ribbonDepth (outer k) (p.1, p.2 + 1) = ribbonDepth (outer k) p) :
    copyShift P (ribbonDepth (outer k) (p.1, p.2 + 1))
      (ribbonIndex k (p.1, p.2 + 1)) =
    let t := copyShift P (ribbonDepth (outer k) p) (ribbonIndex k p)
    (t.1 - 1, t.2 + beta P) := by
  rw [h]
  cases k <;> ext <;> simp [copyShift, ribbonIndex, content, beta] <;> ring

/-- A south-to-north step on one ribbon has the same shift; its extra
southeast marking is included separately in `compositionC`. -/
theorem north_ribbon_placement (k : TenKind) (p : Cell)
    (h : ribbonDepth (outer k) (p.1 - 1, p.2) = ribbonDepth (outer k) p) :
    copyShift P (ribbonDepth (outer k) (p.1 - 1, p.2))
      (ribbonIndex k (p.1 - 1, p.2)) =
    let t := copyShift P (ribbonDepth (outer k) p) (ribbonIndex k p)
    (t.1 - 1, t.2 + beta P) := by
  rw [h]
  cases k <;> ext <;> simp [copyShift, ribbonIndex, content, beta] <;> ring

/-- Adjacent northwest ribbons have exactly the southeast displacement
required by rule (c)(iii), not an independently chosen placement. -/
theorem diagonal_ribbon_placement (k : TenKind) (p : Cell)
    (hp : p ∈ outer k) (hn : (p.1 - 1, p.2 - 1) ∈ outer k) :
    copyShift P (ribbonDepth (outer k) p) (ribbonIndex k p) =
    let t := copyShift P (ribbonDepth (outer k) (p.1 - 1, p.2 - 1))
      (ribbonIndex k (p.1 - 1, p.2 - 1))
    (t.1 + 1, t.2 + 1) := by
  rw [ribbon_diagonal_step k p hp hn]
  cases k <;> ext <;> simp [copyShift, ribbonIndex, content] <;> push_cast <;> ring

theorem outerA_reverse_cells :
    outerA.image (fun p => (2 - p.1, 3 - p.2)) = outerARev := by decide

theorem outerB_reverse_cells :
    outerB.image (fun p => (3 - p.1, 2 - p.2)) = outerBRev := by decide

/-- Case-(c) composition, with one inner copy per outer cell and an extra
marked copy on every vertical same-ribbon interface.  The extra copy is
the southeast translate of the overlap, exactly operation (C) in the
cited definition of the dotted attachment. -/
def compositionC (k : TenKind) : Cells :=
  (outer k).biUnion (fun p => translate (E P)
    (copyShift P (ribbonDepth (outer k) p) (ribbonIndex k p))) ∪
  ((outer k).filter fun p => (p.1 - 1, p.2) ∈ outer k ∧
    ribbonDepth (outer k) (p.1 - 1, p.2) = ribbonDepth (outer k) p).biUnion
    (fun p => translate (Wne P)
      (copyShift P (ribbonDepth (outer k) p + 1 : ℕ) (ribbonIndex k p)))

/-- Coordinates computed from the actual northwest ribbons, before inserting inner cells. -/
def copyCoordinates (k : TenKind) : Finset Cell :=
  (outer k).image fun p => ((ribbonDepth (outer k) p : ℤ), ribbonIndex k p)

/-- Coordinates of the actual vertical same-ribbon supplemental interfaces. -/
def supplementalCoordinates (k : TenKind) : Finset Cell :=
  ((outer k).filter fun p => (p.1 - 1, p.2) ∈ outer k ∧
    ribbonDepth (outer k) (p.1 - 1, p.2) = ribbonDepth (outer k) p).image
    fun p => ((ribbonDepth (outer k) p + 1 : ℕ), ribbonIndex k p)

theorem copyCoordinates_eq (k : TenKind) :
    copyCoordinates k =
      {(0,0), (0,1), (0,2), (0,3), (0,4), (0,5),
       (1,1), (1,2), (1,3), (1,4)} ∪
      (match k with | .fa | .fb => {(2,2)} | .ha | .hb => {(2,3)}) := by
  cases k <;> decide

theorem supplementalCoordinates_eq (k : TenKind) :
    supplementalCoordinates k = match k with
    | .fa => {(1,0), (1,1), (2,1)}
    | .ha => {(1,0), (1,2), (2,2)}
    | .fb => {(1,0), (1,1), (1,3), (2,1), (2,3)}
    | .hb => {(1,0), (1,1), (1,2), (2,1), (2,2)} := by
  cases k <;> decide

/-- Parameter-dependent copies inserted at the proved ribbon and interface coordinates. -/
def coordinateComposition (k : TenKind) : Cells :=
  (copyCoordinates k).biUnion (fun z => translate (E P) (copyShift P z.1 z.2)) ∪
  (supplementalCoordinates k).biUnion
    (fun z => translate (Wne P) (copyShift P z.1 z.2))

/-- Separating parameter-free ribbon coordinates from parameter-dependent inner copies
does not change any constructed cell. -/
theorem compositionC_eq_coordinates (k : TenKind) :
    compositionC P k = coordinateComposition P k := by
  apply Finset.ext
  intro p
  simp [compositionC, coordinateComposition, copyCoordinates, supplementalCoordinates]

private theorem copy_coordinate_support (k : TenKind) (z : Cell)
    (hz : z ∈ copyCoordinates k) : -5 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 0 := by
  rcases z with ⟨l, j⟩
  cases k <;>
    simp only [copyCoordinates_eq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq] at hz <;> omega

private theorem supplemental_coordinate_support (k : TenKind) (z : Cell)
    (hz : z ∈ supplementalCoordinates k) : -5 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 1 := by
  rcases z with ⟨l, j⟩
  cases k <;>
    simp only [supplementalCoordinates_eq, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq] at hz <;> omega

/-- The legal composition's physical support follows from the proved ribbon
coordinates, independently of every column interval. -/
theorem coordinateComposition_row_support (k : TenKind) (p : Cell)
    (hp : p ∈ coordinateComposition P k) : -5 ≤ p.1 ∧ p.1 ≤ 1 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨z, hz, hp⟩ := Finset.mem_biUnion.mp hp
    have hs := copy_coordinate_support k z hz
    have hr := copy_E_rows P z.1 z.2 p hp
    omega
  · obtain ⟨z, hz, hp⟩ := Finset.mem_biUnion.mp hp
    have hs := supplemental_coordinate_support k z hz
    have hr := copy_Wne_row P z.1 z.2 p hp
    omega

private theorem composition_outside_membership (k : TenKind) (r c : ℤ)
    (hr : r < -5 ∨ 1 < r) :
    (r,c) ∈ coordinateComposition P k ↔ (r,c) ∈ union P k := by
  constructor
  · intro hp
    have h := coordinateComposition_row_support P k (r,c) hp
    dsimp at h
    omega
  · intro hp
    have h := union_row_support P k (r,c) hp
    dsimp at h
    omega

-- Finite-coordinate normalization is performed for just one actual row.
macro "ten_composition_row" p:term : tactic => `(tactic|
  (have ha := ($p).a_pos
   have hd := ($p).d_nonneg
   have hb := ($p).separated
   norm_num [coordinateComposition, copyCoordinates_eq, supplementalCoordinates_eq,
     union, common, range_six, range_four, copyShift, E, Wne, L, M, beta,
     mem_translate, mem_intervalRow]
   all_goals omega))

private theorem composition_fa_row0 (c : ℤ) :
    (-5,c) ∈ coordinateComposition P .fa ↔ (-5,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_row1 (c : ℤ) :
    (-4,c) ∈ coordinateComposition P .fa ↔ (-4,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_row2 (c : ℤ) :
    (-3,c) ∈ coordinateComposition P .fa ↔ (-3,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_row3 (c : ℤ) :
    (-2,c) ∈ coordinateComposition P .fa ↔ (-2,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_row4 (c : ℤ) :
    (-1,c) ∈ coordinateComposition P .fa ↔ (-1,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_row5 (c : ℤ) :
    (0,c) ∈ coordinateComposition P .fa ↔ (0,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_row6 (c : ℤ) :
    (1,c) ∈ coordinateComposition P .fa ↔ (1,c) ∈ union P .fa := by ten_composition_row P
private theorem composition_fa_outside (r c : ℤ) (hr : r < -5 ∨ 1 < r) :
    (r,c) ∈ coordinateComposition P .fa ↔ (r,c) ∈ union P .fa :=
  composition_outside_membership P .fa r c hr

private theorem composition_ha_row0 (c : ℤ) :
    (-5,c) ∈ coordinateComposition P .ha ↔ (-5,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_row1 (c : ℤ) :
    (-4,c) ∈ coordinateComposition P .ha ↔ (-4,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_row2 (c : ℤ) :
    (-3,c) ∈ coordinateComposition P .ha ↔ (-3,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_row3 (c : ℤ) :
    (-2,c) ∈ coordinateComposition P .ha ↔ (-2,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_row4 (c : ℤ) :
    (-1,c) ∈ coordinateComposition P .ha ↔ (-1,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_row5 (c : ℤ) :
    (0,c) ∈ coordinateComposition P .ha ↔ (0,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_row6 (c : ℤ) :
    (1,c) ∈ coordinateComposition P .ha ↔ (1,c) ∈ union P .ha := by ten_composition_row P
private theorem composition_ha_outside (r c : ℤ) (hr : r < -5 ∨ 1 < r) :
    (r,c) ∈ coordinateComposition P .ha ↔ (r,c) ∈ union P .ha :=
  composition_outside_membership P .ha r c hr

private theorem composition_fb_row0 (c : ℤ) :
    (-5,c) ∈ coordinateComposition P .fb ↔ (-5,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_row1 (c : ℤ) :
    (-4,c) ∈ coordinateComposition P .fb ↔ (-4,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_row2 (c : ℤ) :
    (-3,c) ∈ coordinateComposition P .fb ↔ (-3,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_row3 (c : ℤ) :
    (-2,c) ∈ coordinateComposition P .fb ↔ (-2,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_row4 (c : ℤ) :
    (-1,c) ∈ coordinateComposition P .fb ↔ (-1,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_row5 (c : ℤ) :
    (0,c) ∈ coordinateComposition P .fb ↔ (0,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_row6 (c : ℤ) :
    (1,c) ∈ coordinateComposition P .fb ↔ (1,c) ∈ union P .fb := by ten_composition_row P
private theorem composition_fb_outside (r c : ℤ) (hr : r < -5 ∨ 1 < r) :
    (r,c) ∈ coordinateComposition P .fb ↔ (r,c) ∈ union P .fb :=
  composition_outside_membership P .fb r c hr

private theorem composition_hb_row0 (c : ℤ) :
    (-5,c) ∈ coordinateComposition P .hb ↔ (-5,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_row1 (c : ℤ) :
    (-4,c) ∈ coordinateComposition P .hb ↔ (-4,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_row2 (c : ℤ) :
    (-3,c) ∈ coordinateComposition P .hb ↔ (-3,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_row3 (c : ℤ) :
    (-2,c) ∈ coordinateComposition P .hb ↔ (-2,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_row4 (c : ℤ) :
    (-1,c) ∈ coordinateComposition P .hb ↔ (-1,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_row5 (c : ℤ) :
    (0,c) ∈ coordinateComposition P .hb ↔ (0,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_row6 (c : ℤ) :
    (1,c) ∈ coordinateComposition P .hb ↔ (1,c) ∈ union P .hb := by ten_composition_row P
private theorem composition_hb_outside (r c : ℤ) (hr : r < -5 ∨ 1 < r) :
    (r,c) ∈ coordinateComposition P .hb ↔ (r,c) ∈ union P .hb :=
  composition_outside_membership P .hb r c hr

/-- The northwest-ribbon composition is assembled from independently proved
literal membership equalities for each family and each physical row. -/
theorem compositionC_eq_union (k : TenKind) : compositionC P k = union P k := by
  rw [compositionC_eq_coordinates]
  apply Finset.ext
  rintro ⟨r, c⟩
  by_cases hr : r < -5 ∨ 1 < r
  · cases k with
    | fa => exact composition_fa_outside P r c hr
    | ha => exact composition_ha_outside P r c hr
    | fb => exact composition_fb_outside P r c hr
    | hb => exact composition_hb_outside P r c hr
  · have h0 : -5 ≤ r := by omega
    have h1 : r ≤ 1 := by omega
    cases k with
    | fa =>
      interval_cases r
      · exact composition_fa_row0 P c
      · exact composition_fa_row1 P c
      · exact composition_fa_row2 P c
      · exact composition_fa_row3 P c
      · exact composition_fa_row4 P c
      · exact composition_fa_row5 P c
      · exact composition_fa_row6 P c
    | ha =>
      interval_cases r
      · exact composition_ha_row0 P c
      · exact composition_ha_row1 P c
      · exact composition_ha_row2 P c
      · exact composition_ha_row3 P c
      · exact composition_ha_row4 P c
      · exact composition_ha_row5 P c
      · exact composition_ha_row6 P c
    | fb =>
      interval_cases r
      · exact composition_fb_row0 P c
      · exact composition_fb_row1 P c
      · exact composition_fb_row2 P c
      · exact composition_fb_row3 P c
      · exact composition_fb_row4 P c
      · exact composition_fb_row5 P c
      · exact composition_fb_row6 P c
    | hb =>
      interval_cases r
      · exact composition_hb_row0 P c
      · exact composition_hb_row1 P c
      · exact composition_hb_row2 P c
      · exact composition_hb_row3 P c
      · exact composition_hb_row4 P c
      · exact composition_hb_row5 P c
      · exact composition_hb_row6 P c

/-- The actual legal-rule cell composition, not merely its determinant,
is the seven-row beta diagram after the specified translation. -/
theorem compositionC_eq_betaCells (k : TenKind) :
    translate (compositionC P k) (5, 0) = betaCells (P.diagram k) := by
  rw [compositionC_eq_union]
  exact union_eq_betaCells P k

/-- Connectedness of every actual outer shape, including its half-turn. -/
theorem outer_connected (k : TenKind) : ConnectedIntervals (outer k) := by
  cases k with
  | ha => exact outerA_connected
  | fb => exact outerB_connected
  | fa =>
    refine ⟨3, 0, ![0, 0, 0], ![4, 4, 3], by decide, ?_, ?_, ?_, ?_, ?_⟩
    · ext p
      simp [outer, outerARev, Fin.exists_fin_succ]
      all_goals tauto
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals norm_num at hij
      all_goals norm_num
    · intro i
      fin_cases i <;> norm_num
    · intro i hi
      fin_cases i
      all_goals norm_num at hi
      all_goals norm_num
  | hb =>
    refine ⟨4, 0, ![0, 0, 0, 0], ![3, 3, 3, 2], by decide, ?_, ?_, ?_, ?_, ?_⟩
    · ext p
      simp [outer, outerBRev, Fin.exists_fin_succ]
      all_goals tauto
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals norm_num at hij
      all_goals norm_num
    · intro i
      fin_cases i <;> norm_num
    · intro i hi
      fin_cases i
      all_goals norm_num at hi
      all_goals norm_num

/-- Each outer diagram has more than one cell, uniformly including reversal. -/
theorem outer_proper (k : TenKind) : (0, 1) ∈ outer k ∧ (0, 2) ∈ outer k := by
  cases k <;> decide

end TenCells
end SkewJacobiNegative
