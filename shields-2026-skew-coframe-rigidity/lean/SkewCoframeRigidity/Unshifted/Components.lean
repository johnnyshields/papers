/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Defs
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Rotation and strict components

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Diagrams, full flags, and coherent units»
(the normalized half-turn `A*` and the strict components of a weak proper matrix) and the
structural inputs of «Unshifted opposite-end exclusion» (`ph:unshifted-exclusion`).

* The half-turn `rotation D` has lists `M - Y`, `M - X`, where `M` is the span; it is an
  involution on the nose, fixes the span, the Jacobi–Trudi determinant for every letter
  sequence, connectivity and the signed proper corner, and exchanges the row and column
  positions.  The left coframe of `D` is the right coframe of `rotation D`.
* The proper matrix `T_D` is block triangular for the blocks cut at the indices `c` with
  `X_{c+2} < Y_c` in the paper's numbering.  Its determinant is the product of the determinants
  of the blocks.  A block with a unit diagonal entry is a single `1 × 1` unit; every other block
  is a connected diagram retaining its absolute row and column positions.

Sorry-free.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- Reversing both indices of a transpose does not change the determinant. -/
theorem _root_.Matrix.det_transpose_submatrix_rev {R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) :
    (M.transpose.submatrix Fin.rev Fin.rev).det = M.det := by
  have := Matrix.det_submatrix_equiv_self Fin.revPerm M.transpose
  rw [Matrix.det_transpose] at this
  exact this

/-! ### The normalized half-turn -/

end SkewCoframeRigidity.Coframe

namespace SkewCofactorIndependence.BetaDiagram

variable {n : ℕ}

/-- The half-turn of a diagram: the lists `M - Y` and `M - X`, in the order they inherit, where
`M` is the span. -/
def rotation (D : BetaDiagram (n + 1)) : BetaDiagram (n + 1) where
  row i := D.largestLabel - D.col i.rev
  col i := D.largestLabel - D.row i.rev
  row_strictAnti := fun i j hij => by
    have := D.col_strictAnti (Fin.rev_lt_rev.mpr hij)
    change D.largestLabel - D.col j.rev < D.largestLabel - D.col i.rev
    omega
  col_strictAnti := fun i j hij => by
    have := D.row_strictAnti (Fin.rev_lt_rev.mpr hij)
    change D.largestLabel - D.row j.rev < D.largestLabel - D.row i.rev
    omega
  row_nonempty := fun i => by
    have := D.row_nonempty i.rev
    change D.largestLabel - D.row i.rev < D.largestLabel - D.col i.rev
    omega

@[simp] theorem rotation_row (D : BetaDiagram (n + 1)) (i : Fin (n + 1)) :
    D.rotation.row i = D.largestLabel - D.col i.rev := rfl

@[simp] theorem rotation_col (D : BetaDiagram (n + 1)) (i : Fin (n + 1)) :
    D.rotation.col i = D.largestLabel - D.row i.rev := rfl

/-- The half-turn preserves the largest label, that is the span. -/
@[simp] theorem rotation_largestLabel (D : BetaDiagram (n + 1)) :
    D.rotation.largestLabel = D.largestLabel := by
  simp [largestLabel]

/-- The half-turn is an involution. -/
@[simp] theorem rotation_rotation (D : BetaDiagram (n + 1)) : D.rotation.rotation = D := by
  cases D with
  | mk row col r c e =>
    simp only [rotation, largestLabel, Fin.rev_rev, Fin.rev_last, Fin.rev_zero]
    congr 1 <;> funext i <;> simp

/-- The half-turn is a rotation equivalence with constant `M`. -/
theorem rotationEquivalent_rotation (D : BetaDiagram (n + 1)) :
    D.RotationEquivalent D.rotation :=
  ⟨D.largestLabel, fun i => by simp, fun i => by simp⟩

/-- The half-turn of a normalized diagram is normalized. -/
theorem rotation_col_last (D : BetaDiagram (n + 1)) (h : D.col (Fin.last n) = 0) :
    D.rotation.col (Fin.last n) = 0 := by
  simp [largestLabel, h]

/-- The half-turn preserves connectivity. -/
theorem Connected.rotation {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    D.rotation.Connected := by
  refine ⟨Nat.succ_pos n, fun i hi => ?_⟩
  have hk : n - (i.val + 1) + 1 < n + 1 := by omega
  have h := hD.2 ⟨n - (i.val + 1), by omega⟩ hk
  have e1 : (⟨n - (i.val + 1), by omega⟩ : Fin (n + 1)) =
      (⟨i.val + 1, hi⟩ : Fin (n + 1)).rev := by ext; simp [Fin.val_rev]
  have e2 : (⟨n - (i.val + 1) + 1, by omega⟩ : Fin (n + 1)) = i.rev := by
    ext; simp [Fin.val_rev]; omega
  have h' : D.col (⟨i.val + 1, hi⟩ : Fin (n + 1)).rev ≤ D.row i.rev := by
    rw [← e1, ← e2]; exact h
  change D.largestLabel - D.row i.rev ≤ D.largestLabel - D.col (⟨i.val + 1, hi⟩ : Fin (n + 1)).rev
  omega

/-- The actual (complete-homogeneous) Schur polynomial is half-turn invariant. -/
theorem schur_rotation (D : BetaDiagram (n + 1)) : D.rotation.schur = D.schur := by
  have : D.rotation.matrix = (D.matrix.transpose).submatrix Fin.rev Fin.rev := by
    ext i j
    simp only [matrix, Matrix.of_apply, rotation_row, rotation_col,
      Matrix.submatrix_apply, Matrix.transpose_apply]
    congr 1; ring_nf
  unfold schur
  rw [this]; exact Matrix.det_transpose_submatrix_rev _

end SkewCofactorIndependence.BetaDiagram

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The span of the half-turn. -/
@[simp] theorem span_rotation (D : BetaDiagram (n + 1)) : span D.rotation = span D := by
  simp [span]

/-- Matrix entries of the half-turn: the transpose of the original under the reversal. -/
theorem fullMatrixOf_rotation {L : Type*} [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1)) :
    fullMatrixOf h D.rotation = ((fullMatrixOf h D).transpose).submatrix Fin.rev Fin.rev := by
  ext i j
  simp only [fullMatrixOf, Matrix.of_apply, BetaDiagram.rotation_row, BetaDiagram.rotation_col,
    Matrix.submatrix_apply, Matrix.transpose_apply]
  congr 1; omega

/-- The half-turn preserves the Jacobi–Trudi determinant for every letter sequence. -/
theorem schurOf_rotation {L : Type*} [CommRing L] (h : ℕ → L) (D : BetaDiagram (n + 1)) :
    schurOf h D.rotation = schurOf h D := by
  unfold schurOf
  rw [fullMatrixOf_rotation]; exact Matrix.det_transpose_submatrix_rev _

/-- The proper matrix of the half-turn is the transpose of the original under the reversal of
the proper indices. -/
theorem properMatrixOf_rotation {L : Type*} [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1)) :
    properMatrixOf h D.rotation =
      ((properMatrixOf h D).transpose).submatrix Fin.rev Fin.rev := by
  ext i j
  simp only [properMatrixOf, Matrix.of_apply, BetaDiagram.rotation_row,
    BetaDiagram.rotation_col, Matrix.submatrix_apply, Matrix.transpose_apply]
  have e1 : (i.succ).rev = i.rev.castSucc := Fin.rev_succ i
  have e2 : (j.castSucc).rev = j.rev.succ := Fin.rev_castSucc j
  rw [e1, e2]
  congr 1; omega

/-- The signed proper corner is half-turn invariant. -/
theorem cornerOf_rotation {L : Type*} [CommRing L] (h : ℕ → L) (D : BetaDiagram (n + 1)) :
    cornerOf h D.rotation = cornerOf h D := by
  unfold cornerOf
  rw [properMatrixOf_rotation, Matrix.det_transpose_submatrix_rev]

/-- Row and column positions are exchanged by the half-turn. -/
theorem colPos_rotation_add (D : BetaDiagram (n + 1)) (j : Fin n) :
    colPos D.rotation j + rowPos D j.rev = span D := by
  have e : (j.castSucc).rev = j.rev.succ := Fin.rev_castSucc j
  have h1 : D.row (j.rev.succ) ≤ D.row 0 := D.row_strictAnti.antitone (Fin.zero_le _)
  have h2 := D.col_strictAnti.antitone (Fin.le_last (j.rev.castSucc))
  have h3 := D.row_nonempty j.rev.succ
  have h4 : D.col (Fin.last n) ≤ D.col j.rev.succ := D.col_strictAnti.antitone (Fin.le_last _)
  have h5 := D.row_strictAnti.antitone (Fin.zero_le j.castSucc.rev)
  simp only [colPos, rowPos, span, BetaDiagram.largestLabel, BetaDiagram.rotation_col,
    Fin.rev_last, e]
  omega

/-- Row and column positions are exchanged by the half-turn. -/
theorem rowPos_rotation_add (D : BetaDiagram (n + 1)) (i : Fin n) :
    rowPos D.rotation i + colPos D i.rev = span D := by
  have e : (i.succ).rev = i.rev.castSucc := Fin.rev_succ i
  have h1 : D.col (i.rev.castSucc) ≤ D.row 0 := by
    have := D.row_nonempty 0
    have := D.col_strictAnti.antitone (Fin.zero_le i.rev.castSucc)
    omega
  have h2 : D.col (Fin.last n) ≤ D.col (i.rev.castSucc) := D.col_strictAnti.antitone (Fin.le_last _)
  simp only [colPos, rowPos, span, BetaDiagram.largestLabel, BetaDiagram.rotation_row,
    BetaDiagram.rotation_col, Fin.rev_last, e]
  omega

/-- The left coframe of a diagram: the right coframe of its half-turn. -/
noncomputable def leftCoframe (D : BetaDiagram (n + 1)) : CohField[X] := coframe D.rotation

theorem leftCoframe_def (D : BetaDiagram (n + 1)) : leftCoframe D = coframe D.rotation := rfl

/-- The left coframe of the half-turn is the right coframe. -/
theorem leftCoframe_rotation (D : BetaDiagram (n + 1)) : leftCoframe D.rotation = coframe D := by
  simp [leftCoframe]

/-! ### Translation -/

end SkewCoframeRigidity.Coframe

namespace SkewCofactorIndependence.BetaDiagram

variable {n : ℕ}

/-- Translate both beta lists by `c`. -/
def translate (D : BetaDiagram n) (c : ℤ) : BetaDiagram n where
  row i := D.row i + c
  col i := D.col i + c
  row_strictAnti := fun i j hij => by
    have := D.row_strictAnti hij
    change D.row j + c < D.row i + c
    omega
  col_strictAnti := fun i j hij => by
    have := D.col_strictAnti hij
    change D.col j + c < D.col i + c
    omega
  row_nonempty := fun i => by
    have := D.row_nonempty i
    change D.col i + c < D.row i + c
    omega

theorem translate_translationEquivalent (D : BetaDiagram n) (c : ℤ) :
    (D.translate c).TranslationEquivalent D :=
  ⟨c, fun _ => rfl, fun _ => rfl⟩

/-- The translate of a connected diagram is connected. -/
theorem Connected.translate {D : BetaDiagram n} (hD : D.Connected) (c : ℤ) :
    (D.translate c).Connected :=
  ⟨hD.1, fun i hi => by
    have := hD.2 i hi
    change D.col i + c ≤ D.row ⟨i.val + 1, hi⟩ + c
    omega⟩

/-- The translation that sets the last column beta to zero. -/
def normalize (D : BetaDiagram (n + 1)) : BetaDiagram (n + 1) := D.translate (-D.col (Fin.last n))

theorem normalize_col_last (D : BetaDiagram (n + 1)) : D.normalize.col (Fin.last n) = 0 := by
  simp [normalize, translate]

end SkewCofactorIndependence.BetaDiagram

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-! ### Strict components of the proper matrix

The proper matrix `T_D` has rows `X_2, …, X_r` and columns `Y_1, …, Y_{r-1}`; in the zero-based
indices of this file its entry `(i, j)` is the letter of `row i.succ - col j.castSucc`.  A
*cut* at `c > 0` is a place where every row below `c` lies strictly left of every column above:
`row c.succ < col (c - 1)`.  The blocks are the intervals between consecutive cuts. -/

/-- A cut of the proper matrix before the index `c`: `X_{c+2} < Y_c` in the paper's numbering. -/
def IsCut (D : BetaDiagram (n + 1)) (c : Fin n) : Prop :=
  ∃ j : Fin n, j.val + 1 = c.val ∧ D.row c.succ < D.col j.castSucc

/-- The block of a proper index: the number of cuts at or before it. -/
noncomputable def blockIdx (D : BetaDiagram (n + 1)) (i : Fin n) : ℕ :=
  open Classical in (Finset.univ.filter fun c : Fin n => c ≤ i ∧ IsCut D c).card

theorem blockIdx_mono (D : BetaDiagram (n + 1)) {i j : Fin n} (hij : i ≤ j) :
    blockIdx D i ≤ blockIdx D j := by
  classical
  unfold blockIdx
  exact Finset.card_le_card fun c hc => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.trans hij, hc.2⟩

theorem blockIdx_lt_of_cut (D : BetaDiagram (n + 1)) {i j c : Fin n} (hic : i < c) (hcj : c ≤ j)
    (hc : IsCut D c) : blockIdx D i < blockIdx D j := by
  classical
  unfold blockIdx
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨c, ?_, ?_⟩)
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact ⟨hd.1.trans (hic.le.trans hcj), hd.2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hcj, hc⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; exact absurd h (not_le.mpr hic)

/-- Distinct blocks are separated by a cut. -/
theorem exists_cut_of_blockIdx_lt (D : BetaDiagram (n + 1)) {i j : Fin n}
    (h : blockIdx D j < blockIdx D i) : ∃ c : Fin n, j < c ∧ c ≤ i ∧ IsCut D c := by
  classical
  by_contra hno
  push Not at hno
  have : blockIdx D i ≤ blockIdx D j := by
    unfold blockIdx
    refine Finset.card_le_card fun c hc => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨not_lt.mp fun hjc => hno c hjc hc.1 |>.elim hc.2 |> fun x => x, hc.2⟩
  omega

/-- The proper matrix vanishes from a later block into an earlier one. -/
theorem properMatrixOf_eq_zero {L : Type*} [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1))
    {i j : Fin n} (hij : blockIdx D j < blockIdx D i) : properMatrixOf h D i j = 0 := by
  obtain ⟨c, hjc, hci, j0, hj0, hlt⟩ := exists_cut_of_blockIdx_lt D hij
  have h1 : D.row i.succ ≤ D.row c.succ :=
    D.row_strictAnti.antitone (Fin.succ_le_succ_iff.mpr hci)
  have h2 : D.col j0.castSucc ≤ D.col j.castSucc :=
    D.col_strictAnti.antitone (Fin.castSucc_le_castSucc_iff.mpr (by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_def] at hjc; omega))
  simp only [properMatrixOf, Matrix.of_apply, letterOf]
  exact if_pos (by omega)

/-- The proper matrix is block triangular for the strict components. -/
theorem properMatrixOf_blockTriangular {L : Type*} [Zero L] (h : ℕ → L)
    (D : BetaDiagram (n + 1)) : (properMatrixOf h D).BlockTriangular (blockIdx D) :=
  fun _ _ hij => properMatrixOf_eq_zero h D hij

/-- The determinant of the proper matrix is the product of the determinants of its strict
components, retaining every crossing entry (which sit in the triangle and do not contribute). -/
theorem properMatrixOf_det_eq_prod {L : Type*} [CommRing L] (h : ℕ → L)
    (D : BetaDiagram (n + 1)) :
    (properMatrixOf h D).det = ∏ k ∈ Finset.univ.image (blockIdx D),
      ((properMatrixOf h D).toSquareBlock (blockIdx D) k).det := by
  classical
  exact (properMatrixOf_blockTriangular h D).det

/-- The signed proper corner as a signed product over the strict components. -/
theorem cornerOf_eq_prod {L : Type*} [CommRing L] (h : ℕ → L) (D : BetaDiagram (n + 1)) :
    cornerOf h D = (-1) ^ n * ∏ k ∈ Finset.univ.image (blockIdx D),
      ((properMatrixOf h D).toSquareBlock (blockIdx D) k).det := by
  unfold cornerOf; rw [properMatrixOf_det_eq_prod]

/-- A unit: the diagonal entry of the proper matrix at `i` is the true unit `h_0`. -/
def IsUnit' (D : BetaDiagram (n + 1)) (i : Fin n) : Prop := D.row i.succ = D.col i.castSucc

/-- The diagonal of the proper matrix is nonnegative for a connected diagram. -/
theorem diag_le_row {D : BetaDiagram (n + 1)} (hD : D.Connected) (i : Fin n) :
    D.col i.castSucc ≤ D.row i.succ := by
  have := hD.2 i.castSucc (by simp only [Fin.val_castSucc]; omega)
  exact this

/-- A unit forms a block by itself. -/
theorem blockIdx_eq_imp_of_unit {D : BetaDiagram (n + 1)} {i : Fin n} (hu : IsUnit' D i)
    {j : Fin n} (hj : blockIdx D j = blockIdx D i) : j = i := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- cut at `i`
    have hi : 0 < i.val := by rw [Fin.lt_def] at hlt; omega
    have hcut : IsCut D i := by
      refine ⟨⟨i.val - 1, by omega⟩, by simp; omega, ?_⟩
      rw [hu]
      exact D.col_strictAnti (by rw [Fin.lt_def]; simp; omega)
    have := blockIdx_lt_of_cut D hlt le_rfl hcut
    omega
  · have hc : i.val + 1 < n := by rw [Fin.lt_def] at hgt; omega
    have hcut : IsCut D ⟨i.val + 1, hc⟩ := by
      refine ⟨i, rfl, ?_⟩
      rw [← hu]
      exact D.row_strictAnti (by rw [Fin.lt_def]; simp)
    have := blockIdx_lt_of_cut D (show i < ⟨i.val + 1, hc⟩ from by
      rw [Fin.lt_def]; simp) (show (⟨i.val + 1, hc⟩ : Fin n) ≤ j from by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_def] at hgt; simp; omega) hcut
    omega

/-- Two adjacent indices of one block are not separated by a cut. -/
theorem col_le_row_of_same_block {D : BetaDiagram (n + 1)} {i : Fin n} (hi : i.val + 1 < n)
    (hb : blockIdx D i = blockIdx D ⟨i.val + 1, hi⟩) :
    D.col i.castSucc ≤ D.row (⟨i.val + 2, by omega⟩ : Fin (n + 1)) := by
  by_contra hlt
  push Not at hlt
  have hcut : IsCut D ⟨i.val + 1, hi⟩ := ⟨i, rfl, hlt⟩
  have := blockIdx_lt_of_cut D (show i < ⟨i.val + 1, hi⟩ from by
    rw [Fin.lt_def]; simp) le_rfl hcut
  omega

/-! ### Blocks as diagrams -/

/-- The inclusion of the interval `[s, s + m)` into the proper indices. -/
def blockEmb (s m : ℕ) (hsm : s + m ≤ n) (i : Fin m) : Fin n := ⟨s + i.val, by omega⟩

/-- The block on the proper indices `[s, s + m)` as a diagram, retaining the absolute row and
column positions; it is a diagram exactly when every diagonal entry of the block is positive. -/
def blockDiagram (D : BetaDiagram (n + 1)) (s m : ℕ) (hsm : s + m ≤ n)
    (hpos : ∀ i : Fin m, D.col (blockEmb s m hsm i).castSucc < D.row (blockEmb s m hsm i).succ) :
    BetaDiagram m where
  row i := D.row (blockEmb s m hsm i).succ
  col i := D.col (blockEmb s m hsm i).castSucc
  row_strictAnti := fun i j hij => D.row_strictAnti (by
    rw [Fin.lt_def]; simp [blockEmb]; exact hij)
  col_strictAnti := fun i j hij => D.col_strictAnti (by
    rw [Fin.lt_def]; simp [blockEmb]; exact hij)
  row_nonempty := hpos

/-- The Jacobi–Trudi matrix of the block diagram is the corresponding principal submatrix of the
proper matrix. -/
theorem fullMatrixOf_blockDiagram {L : Type*} [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1))
    (s m : ℕ) (hsm : s + m ≤ n) (hpos) :
    fullMatrixOf h (blockDiagram D s m hsm hpos) =
      (properMatrixOf h D).submatrix (blockEmb s m hsm) (blockEmb s m hsm) := rfl

/-- A connected diagram has connected blocks whenever all of an interval lies in one block. -/
theorem blockDiagram_connected {D : BetaDiagram (n + 1)} (s m : ℕ) (hsm : s + m ≤ n) (hpos)
    (hm : 0 < m) (hsame : ∀ i : ℕ, ∀ hi : i + 1 < m,
      blockIdx D (blockEmb s m hsm ⟨i, by omega⟩) = blockIdx D (blockEmb s m hsm ⟨i + 1, hi⟩)) :
    (blockDiagram D s m hsm hpos).Connected := by
  refine ⟨hm, fun i hi => ?_⟩
  have := col_le_row_of_same_block (D := D) (i := blockEmb s m hsm i)
    (by simp [blockEmb]; omega) (hsame i.val hi)
  exact this

/-- The principal submatrix of a block, as the determinant of the square block. -/
theorem det_toSquareBlock_eq {L : Type*} [CommRing L] (M : Matrix (Fin n) (Fin n) L)
    (b : Fin n → ℕ) (k : ℕ) (s m : ℕ) (hsm : s + m ≤ n)
    (hfib : ∀ i : Fin n, b i = k ↔ s ≤ i.val ∧ i.val < s + m) :
    (M.toSquareBlock b k).det = (M.submatrix (blockEmb s m hsm) (blockEmb s m hsm)).det := by
  have hmem : ∀ i : Fin m, b (blockEmb s m hsm i) = k := fun i =>
    (hfib _).mpr ⟨by simp [blockEmb], by simp [blockEmb]⟩
  let ε : Fin m ≃ {a // b a = k} := Equiv.ofBijective (fun i => ⟨blockEmb s m hsm i, hmem i⟩)
    ⟨fun i j hij => by
      have := congrArg (fun x : {a // b a = k} => x.1.val) hij
      simp only [blockEmb] at this
      exact Fin.ext (by omega),
     fun ⟨a, ha⟩ => by
      have := (hfib a).mp ha
      exact ⟨⟨a.val - s, by omega⟩, Subtype.ext (Fin.ext (by simp [blockEmb]; omega))⟩⟩
  rw [← Matrix.det_submatrix_equiv_self ε (M.toSquareBlock b k)]
  rfl

/-- Every block is an interval. -/
theorem exists_block_interval (D : BetaDiagram (n + 1)) {k : ℕ}
    (hk : k ∈ Finset.univ.image (blockIdx D)) :
    ∃ s m : ℕ, ∃ hsm : s + m ≤ n, 0 < m ∧
      ∀ i : Fin n, blockIdx D i = k ↔ s ≤ i.val ∧ i.val < s + m := by
  classical
  obtain ⟨i0, -, hk0⟩ := Finset.mem_image.mp hk
  set F : Finset (Fin n) := Finset.univ.filter fun i => blockIdx D i = k with hF
  have hne : F.Nonempty := ⟨i0, by simp [hF, hk0]⟩
  refine ⟨(F.min' hne).val, (F.max' hne).val + 1 - (F.min' hne).val, ?_, ?_, ?_⟩
  · have := (F.max' hne).isLt
    have := Fin.le_iff_val_le_val.mp (F.min'_le _ (F.max'_mem hne))
    omega
  · have := Fin.le_iff_val_le_val.mp (F.min'_le _ (F.max'_mem hne))
    omega
  · intro i
    have hmin := F.min'_mem hne
    have hmax := F.max'_mem hne
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hmin hmax
    have hle := Fin.le_iff_val_le_val.mp (F.min'_le _ (F.max'_mem hne))
    constructor
    · intro hi
      have h1 := Fin.le_iff_val_le_val.mp (F.min'_le i (by simp [hF, hi]))
      have h2 := Fin.le_iff_val_le_val.mp (F.le_max' i (by simp [hF, hi]))
      omega
    · intro ⟨h1, h2⟩
      apply le_antisymm
      · rw [← hmax]
        exact blockIdx_mono D (i := i) (j := F.max' hne) (by rw [Fin.le_iff_val_le_val]; omega)
      · rw [← hmin]
        exact blockIdx_mono D (i := F.min' hne) (j := i) (by rw [Fin.le_iff_val_le_val]; omega)

/-- Each strict component is either a single true unit or an actual connected diagram,
translated from its absolute position, whose Jacobi–Trudi determinant is the determinant of the
block. -/
theorem strict_component {L : Type*} [CommRing L] (h : ℕ → L) {D : BetaDiagram (n + 1)}
    (hD : D.Connected) {k : ℕ} (hk : k ∈ Finset.univ.image (blockIdx D)) :
    ∃ s m : ℕ, ∃ hsm : s + m ≤ n, 0 < m ∧
      (∀ i : Fin n, blockIdx D i = k ↔ s ≤ i.val ∧ i.val < s + m) ∧
      ((m = 1 ∧ (∀ i : Fin n, i.val = s → IsUnit' D i) ∧
        ((properMatrixOf h D).toSquareBlock (blockIdx D) k).det = h 0) ∨
       ∃ hpos, (blockDiagram D s m hsm hpos).Connected ∧
        ((properMatrixOf h D).toSquareBlock (blockIdx D) k).det =
          schurOf h (blockDiagram D s m hsm hpos)) := by
  obtain ⟨s, m, hsm, hm, hfib⟩ := exists_block_interval D hk
  refine ⟨s, m, hsm, hm, hfib, ?_⟩
  have hdet := det_toSquareBlock_eq (properMatrixOf h D) (blockIdx D) k s m hsm hfib
  have hin : ∀ i : Fin m, blockIdx D (blockEmb s m hsm i) = k := fun i =>
    (hfib _).mpr ⟨by simp [blockEmb], by simp [blockEmb]⟩
  by_cases hu : ∃ i : Fin m, IsUnit' D (blockEmb s m hsm i)
  · obtain ⟨i, hi⟩ := hu
    have hsing : ∀ j : Fin m, j = i := fun j => by
      have := blockIdx_eq_imp_of_unit hi ((hin j).trans (hin i).symm)
      exact Fin.ext (by
        have := congrArg Fin.val this
        simp only [blockEmb] at this
        omega)
    have hm1 : m = 1 := by
      have h0 := hsing ⟨0, hm⟩
      have h1 := hsing ⟨m - 1, by omega⟩
      have := congrArg Fin.val (h0.trans h1.symm)
      simp only at this
      omega
    subst hm1
    left
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    have hs : ∀ i' : Fin n, i'.val = s → IsUnit' D i' := by
      intro i' hi'
      have : i' = blockEmb s 1 hsm 0 := Fin.ext (by simp [blockEmb, hi'])
      rw [this]; exact hi
    refine ⟨rfl, hs, ?_⟩
    rw [hdet, Matrix.det_unique]
    have : D.row (blockEmb s 1 hsm 0).succ - D.col (blockEmb s 1 hsm 0).castSucc = 0 := by
      have := hi; unfold IsUnit' at this; omega
    simp [properMatrixOf, letterOf, this]
    intro hlt; omega
  · right
    push Not at hu
    have hpos : ∀ i : Fin m,
        D.col (blockEmb s m hsm i).castSucc < D.row (blockEmb s m hsm i).succ := fun i =>
      lt_of_le_of_ne (diag_le_row hD _) (fun e => hu i e.symm)
    refine ⟨hpos, blockDiagram_connected s m hsm hpos hm fun i hi => ?_, ?_⟩
    · exact (hin _).trans (hin _).symm
    · rw [hdet]; rfl

end SkewCoframeRigidity.Coframe
