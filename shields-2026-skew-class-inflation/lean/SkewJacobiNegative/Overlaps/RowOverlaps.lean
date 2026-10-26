/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/Overlaps/RowOverlaps.lean

import SkewJacobiNegative.Overlaps.ShiftedDeterminant
import SkewJacobiNegative.Gluing.RowInvariants

/-!
# Row overlap partitions are invariants of the skew Schur function

Formalizes `shields-2026-skew-base-computational.tex`, `lem:invariants`: for every `k ≥ 1` the
multiset of the numbers of columns shared by `k` consecutive rows, the row overlap partition
`ρ^{(k)}` of Reiner–Shaw–van Willigenburg, Def. 8.2, is determined by the skew Schur function
(their Cor. 8.11, by induction on the number of rows through Lemma 8.5 and Thm. 8.10).

A skew diagram with `ℓ` rows, some possibly empty, is a pair of strictly decreasing lists
`ξ_i = λ_i - i`, `ζ_i = μ_i - i` with `ζ_i ≤ ξ_i` (`BetaRows`); its skew Schur function is
`det (h_{ξ_i - ζ_j})`.  Row `i` is the column interval `[ζ_i + i, ξ_i + i)`, and the rows
`i, …, i + k - 1` share `max (0, ξ_{i+k-1} - ζ_i + k - 1)` columns (`BetaRows.overlap`).

The diagram `D̂` of Lemma 8.5, with the top cell of every column removed, has the beta lists
`ξ̂_i = ξ_{i+1}`, `ζ̂_i = min (ξ_{i+1}, ζ_i - 1)` (`BetaRows.hat`), and its row overlaps are
`ρ^{(k)}(D̂) = ρ^{(k+1)}(D)` (`BetaRows.rowOverlaps_hat`).  The ring homomorphism
`Λ → Λ[X]`, `h_a ↦ ∑_{m ≤ a} X^m h_{a-m}` (`shiftHom`) takes `s_D` to a polynomial in `X` of degree
`c`, whose leading coefficient is `s_{D̂}` (`shifted_coeff`); equal skew Schur functions give equal
degrees and equal leading coefficients, so `s_D` determines `s_{D̂}`
(`schur_hat_eq_of_schur_eq`).  This replaces the coefficient extraction `[h_{ℓ+c}] φ_ℓ` and the
bijection of pictures in the reference, and uses no Littlewood–Richardson expansion.  The
smallest overlap partition `ρ^{(1)}` is the multiset of row lengths, recovered as the exponent of
the monomial of least weight (`rows_eq_of_schur_eq`).

Sorry-free.
-/

namespace SkewJacobiNegative.Overlaps

open SkewJacobiNegative.Gluing
open scoped Polynomial

/-- The ring homomorphism `Λ → Λ[X]` with `h_a ↦ ∑_{m ≤ a} X^m h_{a-m}`. -/
noncomputable def shiftHom : Lambda →ₐ[ℚ] Lambda[X] :=
  MvPolynomial.aeval fun v : ℕ+ => shiftEntry hh (v : ℤ)

theorem shiftHom_hh (a : ℤ) : shiftHom (hh a) = shiftEntry hh a := by
  by_cases ha : a < 0
  · have : a.toNat = 0 := by omega
    simp [shiftEntry, this, hh_of_neg ha]
  · by_cases h0 : a = 0
    · subst h0
      simp [shiftEntry]
    · have hpos : 0 < a.toNat := by omega
      have e : hh a = MvPolynomial.X (Nat.toPNat a.toNat hpos) := by
        rw [hh, ite_eq_right ha, hPos, dite_eq_left hpos]
        rfl
      rw [e]
      rw [shiftHom, MvPolynomial.aeval_X]
      congr 1
      change ((a.toNat : ℕ) : ℤ) = a
      omega

/-- A skew diagram with `ℓ` rows, some possibly empty, by the beta lists `ξ_i = λ_i - i` and
`ζ_i = μ_i - i` of its rows `i < ℓ`: both strictly decrease and `ζ_i ≤ ξ_i`.  The functions
are read only below `ℓ`. -/
structure BetaRows (ℓ : ℕ) where
  /-- The list `ξ_i = λ_i - i`. -/
  xi : ℕ → ℤ
  /-- The list `ζ_i = μ_i - i`. -/
  zeta : ℕ → ℤ
  xi_lt : ∀ i j, i < j → j < ℓ → xi j < xi i
  zeta_lt : ∀ i j, i < j → j < ℓ → zeta j < zeta i
  zeta_le : ∀ i, i < ℓ → zeta i ≤ xi i

namespace BetaRows

variable {ℓ : ℕ}

/-- The list `ξ` on `Fin ℓ`. -/
def xiFin (B : BetaRows ℓ) : Fin ℓ → ℤ := fun i => B.xi i

/-- The list `ζ` on `Fin ℓ`. -/
def zetaFin (B : BetaRows ℓ) : Fin ℓ → ℤ := fun i => B.zeta i

theorem xiFin_strictAnti (B : BetaRows ℓ) : StrictAnti B.xiFin :=
  fun a b hab => B.xi_lt a b hab b.2

theorem zetaFin_strictAnti (B : BetaRows ℓ) : StrictAnti B.zetaFin :=
  fun a b hab => B.zeta_lt a b hab b.2

theorem zetaFin_le (B : BetaRows ℓ) (i : Fin ℓ) : B.zetaFin i ≤ B.xiFin i :=
  B.zeta_le i i.2

/-- The skew Schur function `det (h_{ξ_i - ζ_j})`. -/
noncomputable def schur (B : BetaRows ℓ) : Lambda := betaDet B.xiFin B.zetaFin

/-- The diagram `D̂` of Lemma 8.5, with the top cell of every column removed: `ξ̂_i = ξ_{i+1}`,
`ζ̂_i = min (ξ_{i+1}, ζ_i - 1)`. -/
def hat {n : ℕ} (B : BetaRows (n + 1)) : BetaRows n where
  xi i := B.xi (i + 1)
  zeta i := min (B.xi (i + 1)) (B.zeta i - 1)
  xi_lt i j hij hj := B.xi_lt (i + 1) (j + 1) (by omega) (by omega)
  zeta_lt i j hij hj := by
    have h1 := B.xi_lt (i + 1) (j + 1) (by omega) (by omega)
    have h2 := B.zeta_lt i j hij (by omega)
    omega
  zeta_le i _ := min_le_left _ _

theorem schur_hat {n : ℕ} (B : BetaRows (n + 1)) :
    B.hat.schur = betaDetOf hh (fun i : Fin n => B.xiFin i.succ) (hatLower B.xiFin B.zetaFin) := by
  unfold schur betaDetOf betaDet
  congr 2

/-- `s_D` is the Jacobi–Trudi determinant `betaDetOf hh`. -/
theorem schur_eq_betaDetOf (B : BetaRows ℓ) :
    B.schur = betaDetOf hh B.xiFin B.zetaFin := rfl

/-- The image of `s_D` under `h_a ↦ ∑ X^m h_{a-m}` is the determinant of the shifted entries. -/
theorem shiftHom_schur (B : BetaRows ℓ) :
    shiftHom B.schur =
      (Matrix.of fun i j : Fin ℓ => shiftEntry hh (B.xiFin i - B.zetaFin j)).det := by
  have := RingHom.map_det (shiftHom : Lambda →+* Lambda[X])
    (Matrix.of fun i j : Fin ℓ => hh (B.xiFin i - B.zetaFin j))
  rw [schur, betaDet]
  refine this.trans ?_
  congr 1
  ext i j
  simp [shiftHom_hh]

theorem schur_hat_ne_zero {n : ℕ} (B : BetaRows (n + 1)) : B.hat.schur ≠ 0 := by
  have := (betaDet_extremal B.hat.xiFin_strictAnti B.hat.zetaFin_strictAnti
    B.hat.zetaFin_le).1
  intro h0
  rw [schur] at h0
  rw [h0] at this
  simp at this

/-- **Thm. 8.10** (Reiner–Shaw–van Willigenburg).  The image of `s_D` under `shiftHom` has degree
`shiftDegree` and leading coefficient `s_{D̂}`. -/
theorem shiftHom_schur_natDegree {n : ℕ} (B : BetaRows (n + 1)) :
    (shiftHom B.schur).natDegree = shiftDegree B.xiFin B.zetaFin ∧
      (shiftHom B.schur).coeff (shiftDegree B.xiFin B.zetaFin) = B.hat.schur := by
  have hc := shifted_coeff hh (fun a ha => hh_of_neg ha) hh_zero B.xiFin_strictAnti
    B.zetaFin_strictAnti B.zetaFin_le
  rw [← shiftHom_schur] at hc
  have h2 : (shiftHom B.schur).coeff (shiftDegree B.xiFin B.zetaFin) = B.hat.schur := by
    rw [hc.2, schur_hat]
  refine ⟨?_, h2⟩
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hc.1
  · rw [h2]; exact schur_hat_ne_zero B

/-- **Thm. 8.10**: `s_D` determines `s_{D̂}`. -/
theorem schur_hat_eq_of_schur_eq {n n' : ℕ} {B : BetaRows (n + 1)} {B' : BetaRows (n' + 1)}
    (h : B.schur = B'.schur) : B.hat.schur = B'.hat.schur := by
  obtain ⟨d1, c1⟩ := shiftHom_schur_natDegree B
  obtain ⟨d2, c2⟩ := shiftHom_schur_natDegree B'
  have hp : shiftHom B.schur = shiftHom B'.schur := by rw [h]
  have hd : shiftDegree B.xiFin B.zetaFin = shiftDegree B'.xiFin B'.zetaFin := by
    rw [← d1, ← d2, hp]
  rw [← c1, ← c2, hd, hp]

/-! ### Overlaps of consecutive rows -/

/-- Rows `i, …, i + j` share `max (0, ξ_{i+j} - ζ_i + j)` columns. -/
def overlap (B : BetaRows ℓ) (j i : ℕ) : ℕ := (B.xi (i + j) - B.zeta i + j).toNat

/-- The numbers of columns shared by `k` consecutive rows, including zeros: the row overlap
composition of Def. 8.2 for `k ≥ 1`, as a multiset.  (`k = 0` is read as `k = 1`.) -/
def overlaps (B : BetaRows ℓ) (k : ℕ) : Multiset ℕ :=
  (Finset.range (ℓ - (k - 1))).val.map (B.overlap (k - 1))

/-- The row overlap partition `ρ^{(k)}` of Def. 8.2: the positive parts of `overlaps`. -/
def rowOverlaps (B : BetaRows ℓ) (k : ℕ) : Multiset ℕ := (B.overlaps k).filter (0 < ·)

theorem xi_gap (B : BetaRows ℓ) {i : ℕ} (d : ℕ) (h : i + d < ℓ) :
    B.xi (i + d) + d ≤ B.xi i := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := B.xi_lt (i + d) (i + (d + 1)) (by omega) h
    omega

theorem rowOverlaps_one_eq_zero_of_rows (B : BetaRows ℓ) (k : ℕ)
    (h : B.rowOverlaps 1 = 0) : B.rowOverlaps k = 0 := by
  have hrow : ∀ i, i < ℓ → B.xi i ≤ B.zeta i := by
    intro i hi
    have hmem : B.overlap 0 i ∈ B.overlaps 1 := by
      simp only [overlaps, Multiset.mem_map, Finset.mem_val, Finset.mem_range]
      exact ⟨i, by omega, by simp⟩
    by_contra hcon
    have hp : 0 < B.overlap 0 i := by simp only [overlap, Nat.add_zero, Nat.cast_zero]; omega
    have : B.overlap 0 i ∈ B.rowOverlaps 1 := Multiset.mem_filter.mpr ⟨hmem, hp⟩
    rw [h] at this
    simp at this
  rw [rowOverlaps, Multiset.filter_eq_nil]
  intro a ha
  simp only [overlaps, Multiset.mem_map, Finset.mem_val, Finset.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  simp only [overlap, not_lt, nonpos_iff_eq_zero]
  have h1 := B.xi_gap (i := i) (k - 1) (by omega)
  have h2 := hrow i (by omega)
  omega

/-- **Lemma 8.5**: the `k`-row overlaps of `D̂` are the `(k+1)`-row overlaps of `D`. -/
theorem overlaps_hat {n : ℕ} (B : BetaRows (n + 1)) (m : ℕ) :
    B.hat.overlaps (m + 1) = B.overlaps (m + 2) := by
  have e0 : m + 2 - 1 = m + 1 := rfl
  simp only [overlaps, e0, Nat.add_sub_cancel]
  have hr : n + 1 - (m + 1) = n - m := by omega
  rw [hr]
  refine Multiset.map_congr rfl fun i hi => ?_
  simp only [Finset.mem_val, Finset.mem_range] at hi
  have hgap := B.xi_gap (i := i + 1) m (by omega)
  have e : i + 1 + m = i + m + 1 := by omega
  rw [e] at hgap
  simp only [overlap, hat]
  have e2 : i + (m + 1) = i + m + 1 := by omega
  rw [e2]
  push_cast
  omega

theorem rowOverlaps_hat {n : ℕ} (B : BetaRows (n + 1)) (m : ℕ) :
    B.hat.rowOverlaps (m + 1) = B.rowOverlaps (m + 2) := by
  rw [rowOverlaps, rowOverlaps, overlaps_hat]

theorem count_map_range (g : ℕ → ℕ) (ℓ a : ℕ) :
    Multiset.count a ((Finset.range ℓ).val.map g) =
      Multiset.count a (Finset.univ.val.map (fun i : Fin ℓ => g i)) := by
  rw [Multiset.count_map, Multiset.count_map]
  have h1 := Finset.card_filter (fun x => a = g x) (Finset.range ℓ)
  have h2 := Finset.card_filter (fun i : Fin ℓ => a = g i) (Finset.univ)
  have h3 := Fin.sum_univ_eq_sum_range (fun x => if a = g x then 1 else 0) ℓ
  have e1 : (Multiset.filter (fun x => a = g x) (Finset.range ℓ).val).card =
      ∑ i ∈ Finset.range ℓ, if a = g i then 1 else 0 := h1
  have e2 : (Multiset.filter (fun i : Fin ℓ => a = g i) Finset.univ.val).card =
      ∑ i : Fin ℓ, if a = g i then 1 else 0 := h2
  rw [e1, e2, h3]

/-- **Prop. 6.2(ii)** (Reiner–Shaw–van Willigenburg): `ρ^{(1)}`, the multiset of nonzero row
lengths, is determined by the skew Schur function. -/
theorem rowOverlaps_one_eq_of_schur_eq {ℓ' : ℕ} {B : BetaRows ℓ} {B' : BetaRows ℓ'}
    (h : B.schur = B'.schur) : B.rowOverlaps 1 = B'.rowOverlaps 1 := by
  have hmon := betaMon_eq_of_betaDet_eq B.xiFin_strictAnti B.zetaFin_strictAnti B.zetaFin_le
    B'.xiFin_strictAnti B'.zetaFin_strictAnti B'.zetaFin_le h
  have key : ∀ {k : ℕ} (C : BetaRows k) (v : ℕ+),
      (C.rowOverlaps 1).count (v : ℕ) = betaMon C.xiFin C.zetaFin v := by
    intro k C v
    rw [rowOverlaps, Multiset.count_filter_of_pos v.pos, betaMon_apply, overlaps]
    simp only [Nat.sub_self, Nat.sub_zero]
    rw [count_map_range]
    simp only [overlap, xiFin, zetaFin, Nat.cast_zero, add_zero]
  refine Multiset.ext.mpr fun a => ?_
  by_cases ha : 0 < a
  · have e1 := key B ⟨a, ha⟩
    have e2 := key B' ⟨a, ha⟩
    rw [PNat.mk_coe] at e1 e2
    rw [e1, e2, hmon]
  · have h0 : a = 0 := by omega
    subst h0
    simp [rowOverlaps]

/-- **Cor. 8.11** (Reiner–Shaw–van Willigenburg): the skew Schur function determines every row
overlap partition `ρ^{(k)}`, `k ≥ 1`.  The diagrams may have different numbers of rows, some of
them empty. -/
theorem rowOverlaps_eq_of_schur_eq : ∀ (ℓ ℓ' : ℕ) (B : BetaRows ℓ) (B' : BetaRows ℓ'),
    B.schur = B'.schur → ∀ k, B.rowOverlaps k = B'.rowOverlaps k := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro ℓ' B B' h k
    have h0 : B.rowOverlaps 1 = 0 := by simp [rowOverlaps, overlaps]
    have h1 := rowOverlaps_one_eq_of_schur_eq h
    rw [h0] at h1
    rw [B'.rowOverlaps_one_eq_zero_of_rows k h1.symm]
    simp [rowOverlaps, overlaps]
  | succ n ih =>
    intro ℓ' B B' h k
    rcases ℓ' with _ | n'
    · have h0 : B'.rowOverlaps 1 = 0 := by simp [rowOverlaps, overlaps]
      have h1 := rowOverlaps_one_eq_of_schur_eq h
      rw [h0] at h1
      rw [B.rowOverlaps_one_eq_zero_of_rows k h1]
      simp [rowOverlaps, overlaps]
    · rcases k with _ | _ | m
      · exact rowOverlaps_one_eq_of_schur_eq h
      · exact rowOverlaps_one_eq_of_schur_eq h
      · rw [← rowOverlaps_hat, ← rowOverlaps_hat]
        exact ih n' B.hat B'.hat (schur_hat_eq_of_schur_eq h) (m + 1)

theorem zeta_gap (B : BetaRows ℓ) {i : ℕ} (d : ℕ) (h : i + d < ℓ) :
    B.zeta (i + d) + d ≤ B.zeta i := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := B.zeta_lt (i + d) (i + (d + 1)) (by omega) h
    omega

/-- The columns of row `i`: the interval `[ζ_i + i, ξ_i + i)`. -/
def rowColumns (B : BetaRows ℓ) (i : ℕ) : Set ℤ := Set.Ico (B.zeta i + i) (B.xi i + i)

/-- **Def. 8.2.**  The overlap of the `j + 1` consecutive rows `i, …, i + j` is the number of
columns common to all of them. -/
theorem overlap_eq_ncard (B : BetaRows ℓ) {i : ℕ} (j : ℕ) (h : i + j < ℓ) :
    B.overlap j i =
      {c : ℤ | ∀ t, i ≤ t → t ≤ i + j → c ∈ B.rowColumns t}.ncard := by
  have hset : {c : ℤ | ∀ t, i ≤ t → t ≤ i + j → c ∈ B.rowColumns t} =
      Set.Ico (B.zeta i + i) (B.xi (i + j) + ((i + j : ℕ) : ℤ)) := by
    ext c
    simp only [Set.mem_ofPred_eq, rowColumns, Set.mem_Ico]
    constructor
    · intro hc
      exact ⟨(hc i le_rfl (by omega)).1, (hc (i + j) (by omega) le_rfl).2⟩
    · rintro ⟨h1, h2⟩ t ht1 ht2
      have a1 := B.zeta_gap (i := i) (t - i) (by omega)
      have a2 := B.xi_gap (i := t) (i + j - t) (by omega)
      have e1 : i + (t - i) = t := by omega
      have e2 : t + (i + j - t) = i + j := by omega
      rw [e1] at a1
      rw [e2] at a2
      have e3 : ((t - i : ℕ) : ℤ) = (t : ℤ) - i := by omega
      have e4 : ((i + j - t : ℕ) : ℤ) = ((i + j : ℕ) : ℤ) - t := by omega
      rw [e3] at a1
      rw [e4] at a2
      constructor <;> omega
  rw [hset]
  have : Set.Ico (B.zeta i + i) (B.xi (i + j) + ((i + j : ℕ) : ℤ)) =
      ↑(Finset.Ico (B.zeta i + i) (B.xi (i + j) + ((i + j : ℕ) : ℤ))) := by
    simp
  rw [this, Set.ncard_coe_finset, Int.card_Ico]
  simp only [overlap]
  congr 1
  push_cast
  omega

end BetaRows

end SkewJacobiNegative.Overlaps

/-! ### Profiles -/

namespace SkewJacobiNegative.Gluing.Profile

open SkewJacobiNegative.Overlaps

variable {n : ℕ}

/-- The beta lists of a connected diagram, as a diagram with `n + 1` nonempty rows. -/
def toBetaRows (P : Profile n) : BetaRows (n + 1) where
  xi i := if h : i < n + 1 then P.xi ⟨i, h⟩ else 0
  zeta i := if h : i < n + 1 then P.zeta ⟨i, h⟩ else 0
  xi_lt i j hij hj := by
    have := P.xi_strictAnti (show (⟨i, by omega⟩ : Fin (n + 1)) < ⟨j, hj⟩ from hij)
    simpa [hj, show i < n + 1 by omega] using this
  zeta_lt i j hij hj := by
    have := P.zeta_strictAnti (show (⟨i, by omega⟩ : Fin (n + 1)) < ⟨j, hj⟩ from hij)
    simpa [hj, show i < n + 1 by omega] using this
  zeta_le i hi := by
    have := P.xi_sub_zeta ⟨i, hi⟩
    have := P.r_pos ⟨i, hi⟩
    simp only [hi, dite_true]
    omega

theorem toBetaRows_xi (P : Profile n) (i : Fin (n + 1)) : P.toBetaRows.xi i = P.xi i := by
  change (if h : (i : ℕ) < n + 1 then P.xi ⟨i, h⟩ else 0) = P.xi i
  rw [dite_eq_left i.2]

theorem toBetaRows_zeta (P : Profile n) (i : Fin (n + 1)) : P.toBetaRows.zeta i = P.zeta i := by
  change (if h : (i : ℕ) < n + 1 then P.zeta ⟨i, h⟩ else 0) = P.zeta i
  rw [dite_eq_left i.2]

theorem toBetaRows_xiFin (P : Profile n) : P.toBetaRows.xiFin = P.xi :=
  funext fun i => toBetaRows_xi P i

theorem toBetaRows_zetaFin (P : Profile n) : P.toBetaRows.zetaFin = P.zeta :=
  funext fun i => toBetaRows_zeta P i

theorem toBetaRows_schur (P : Profile n) : P.toBetaRows.schur = P.schur := by
  rw [BetaRows.schur, toBetaRows_xiFin, toBetaRows_zetaFin]
  rfl

/-- The row overlap composition of Def. 8.2, as a multiset: the numbers of columns shared by `k`
consecutive rows, `k ≥ 1`, with zeros. -/
def rowOverlapPartition (P : Profile n) (k : ℕ) : Multiset ℕ := P.toBetaRows.overlaps k

/-- The row lengths are the overlaps of one row. -/
theorem rowOverlapPartition_one (P : Profile n) : P.rowOverlapPartition 1 = P.rowMultiset := by
  rw [rowOverlapPartition, BetaRows.overlaps, rowMultiset]
  simp only [Nat.sub_self, Nat.sub_zero]
  have : (Finset.range (n + 1)).val.map (P.toBetaRows.overlap 0) =
      Finset.univ.val.map fun i : Fin (n + 1) => P.toBetaRows.overlap 0 i := by
    refine Multiset.ext.mpr fun a => ?_
    exact BetaRows.count_map_range _ _ _
  rw [this]
  refine Multiset.map_congr rfl fun i _ => ?_
  have := P.xi_sub_zeta i
  have e : P.toBetaRows.xi i = P.xi i := toBetaRows_xi P i
  have e2 : P.toBetaRows.zeta i = P.zeta i := toBetaRows_zeta P i
  simp only [BetaRows.overlap, Nat.cast_zero, add_zero, e, e2]
  omega

/-- The overlaps of two adjacent rows are the gaps plus one. -/
theorem rowOverlapPartition_two (P : Profile n) :
    P.rowOverlapPartition 2 = P.gapMultiset.map (· + 1) := by
  rw [rowOverlapPartition, BetaRows.overlaps, gapMultiset, Multiset.map_map]
  simp only [Nat.add_one_sub_one]
  have : (Finset.range n).val.map (P.toBetaRows.overlap 1) =
      Finset.univ.val.map fun i : Fin n => P.toBetaRows.overlap 1 i := by
    refine Multiset.ext.mpr fun a => ?_
    exact BetaRows.count_map_range _ _ _
  rw [this]
  refine Multiset.map_congr rfl fun i _ => ?_
  have := P.xi_succ_sub_zeta_castSucc i
  have e : P.toBetaRows.xi (i + 1) = P.xi i.succ := toBetaRows_xi P i.succ
  have e2 : P.toBetaRows.zeta i = P.zeta i.castSucc := toBetaRows_zeta P i.castSucc
  simp only [BetaRows.overlap, Function.comp_apply, e, e2]
  push_cast
  omega

/-- **Cor. 8.11 for connected diagrams** (Reiner–Shaw–van Willigenburg): Schur-equal connected
diagrams have the same row overlap partitions `ρ^{(k)}` for every `k ≥ 1`. -/
theorem rowOverlapPartition_eq_of_schur_eq {m : ℕ} {P : Profile n} {Q : Profile m}
    (h : P.schur = Q.schur) (k : ℕ) : P.rowOverlapPartition k = Q.rowOverlapPartition k := by
  obtain ⟨hmn, -⟩ := rows_eq_of_schur_eq h
  subst hmn
  have hpos := BetaRows.rowOverlaps_eq_of_schur_eq _ _ P.toBetaRows Q.toBetaRows
    (by rw [toBetaRows_schur, toBetaRows_schur]; exact h) k
  refine multiset_eq_of_count_pnat (fun v => ?_) ?_
  · have h1 := Multiset.count_filter_of_pos (p := (0 < ·)) (a := (v : ℕ)) v.pos
      (s := P.toBetaRows.overlaps k)
    have h2 := Multiset.count_filter_of_pos (p := (0 < ·)) (a := (v : ℕ)) v.pos
      (s := Q.toBetaRows.overlaps k)
    unfold rowOverlapPartition
    rw [← h1, ← h2]
    exact congrArg (Multiset.count (v : ℕ)) hpos
  · simp [rowOverlapPartition, BetaRows.overlaps]

end SkewJacobiNegative.Gluing.Profile

/-! ### Checks on small diagrams -/

open SkewJacobiNegative.Gluing in
/-- The column of three cells has overlap partitions `(1, 1, 1)`, `(1, 1)`, `(1)`; the hook has
`(2, 1)`, `(1)`. -/
example : columnProfile.rowOverlapPartition 1 = {1, 1, 1} ∧
    columnProfile.rowOverlapPartition 2 = {1, 1} ∧ columnProfile.rowOverlapPartition 3 = {1} ∧
    hookProfile.rowOverlapPartition 1 = {2, 1} ∧ hookProfile.rowOverlapPartition 2 = {1} := by
  decide +kernel

open SkewJacobiNegative.Gluing in
/-- Three rows of length two, adjacent rows sharing one column: the first and last rows share
none. -/
def SkewJacobiNegative.Overlaps.staircaseProfile : Profile 2 where
  r := ![2, 2, 2]
  g := ![0, 0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

open SkewJacobiNegative.Gluing SkewJacobiNegative.Overlaps in
example : staircaseProfile.rowOverlapPartition 2 = {1, 1} ∧
    staircaseProfile.rowOverlapPartition 3 = {0} := by
  decide +kernel
