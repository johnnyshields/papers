-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/SchurBridge.lean
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Shields.Combinatorics.Young.LGVTableau
import GluingCore.SchurFunction

/-!
# The bridge from profile Jacobi--Trudi determinants to tableau skew Schur polynomials

Formalizes `shields-2026-skew-factor-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the paragraph on profiles: the skew Schur function of a connected diagram is
`det (h_{ξ_i - ζ_j})`, Jacobi--Trudi being a theorem.

A profile `P` determines a pair of Young diagrams `λ = P.lam`, `μ = P.mu` with rows
`λ_i = ξ_i + i` and `μ_i = ζ_i + i` (rows indexed from `0`), whose skew diagram `λ / μ` has row
lengths `r_i` and adjacent overlaps `g_i + 1` (`Profile.skewRowLen_lam_mu`,
`Profile.card_overlap`).  The bridge theorem `Profile.aeval_schur_eq_skewSchur` says that
specializing `h_k` to the complete homogeneous polynomial `h_k(β₀, …, β_{b-1})` in `b` variables
sends `P.schur` to the tableau skew Schur polynomial `Shields.skewSchur λ μ b β`, for every
number of variables `b` and every commutative `ℚ`-algebra of values.  It rests on the identity of
a Jacobi--Trudi determinant with the tableau skew Schur polynomial,
`Shields.jacobiTrudiDet_eq_skewSchur`, proved in `Shields.Combinatorics.Young.LGVTableau`.

Sorry-free.
-/

namespace GluingCore

open MvPolynomial

/-- The cells `(i, j)` with `i ≤ n` and `j < a i`. -/
def rowsFinset {n : ℕ} (a : Fin (n + 1) → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion fun i : Fin (n + 1) => (Finset.range (a i)).image fun j => ((i : ℕ), j)

theorem mem_rowsFinset {n : ℕ} (a : Fin (n + 1) → ℕ) (c : ℕ × ℕ) :
    c ∈ rowsFinset a ↔ ∃ h : c.1 < n + 1, c.2 < a ⟨c.1, h⟩ := by
  obtain ⟨i, j⟩ := c
  simp only [rowsFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', j', hj', rfl, rfl⟩
    exact ⟨i'.isLt, hj'⟩
  · rintro ⟨h, hj⟩
    exact ⟨⟨i, h⟩, j, hj, rfl, rfl⟩

/-- The Young diagram with row lengths `a 0 ≥ a 1 ≥ ⋯ ≥ a n` and no further rows. -/
def youngOfRows {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : Antitone a) : YoungDiagram where
  cells := rowsFinset a
  isLowerSet := by
    intro x y hyx hx
    rw [Finset.mem_coe, mem_rowsFinset] at hx ⊢
    obtain ⟨h, hj⟩ := hx
    have h1 : y.1 ≤ x.1 := (Prod.mk_le_mk.mp hyx).1
    have h2 : y.2 ≤ x.2 := (Prod.mk_le_mk.mp hyx).2
    refine ⟨by omega, ?_⟩
    have : a ⟨x.1, h⟩ ≤ a ⟨y.1, by omega⟩ := ha (Fin.mk_le_mk.mpr h1)
    omega

theorem mem_youngOfRows {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : Antitone a) (c : ℕ × ℕ) :
    c ∈ youngOfRows a ha ↔ ∃ h : c.1 < n + 1, c.2 < a ⟨c.1, h⟩ :=
  mem_rowsFinset a c

theorem rowLen_youngOfRows {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : Antitone a) (i : Fin (n + 1)) :
    (youngOfRows a ha).rowLen i = a i := by
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    have h1 : (i.1, a i) ∈ youngOfRows a ha := YoungDiagram.mem_iff_lt_rowLen.mpr hcon
    obtain ⟨h, hj⟩ := (mem_youngOfRows a ha _).mp h1
    simp at hj
  · by_contra hcon
    push Not at hcon
    have h1 : (i.1, (youngOfRows a ha).rowLen i) ∈ youngOfRows a ha :=
      (mem_youngOfRows a ha _).mpr ⟨i.isLt, by simpa using hcon⟩
    have := YoungDiagram.mem_iff_lt_rowLen.mp h1
    simp at this

theorem rowLen_youngOfRows_of_le {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : Antitone a) {i : ℕ}
    (hi : n + 1 ≤ i) : (youngOfRows a ha).rowLen i = 0 := by
  by_contra hcon
  have h1 : (i, 0) ∈ youngOfRows a ha := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  obtain ⟨h, -⟩ := (mem_youngOfRows a ha _).mp h1
  simp at h
  omega

namespace Profile

variable {n : ℕ}

/-- The outer row lengths `λ_i = ξ_i + i` of the pair of Young diagrams of a profile. -/
def lamRows (P : Profile n) (i : Fin (n + 1)) : ℕ := (P.xi i + i).toNat

/-- The inner row lengths `μ_i = ζ_i + i` of the pair of Young diagrams of a profile. -/
def muRows (P : Profile n) (i : Fin (n + 1)) : ℕ := (P.zeta i + i).toNat

theorem lamRows_antitone (P : Profile n) : Antitone P.lamRows := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  have := P.xi_strictAnti (Fin.castSucc_lt_succ (i := j))
  simp only [lamRows, Fin.val_succ, Fin.val_castSucc]
  omega

theorem muRows_antitone (P : Profile n) : Antitone P.muRows := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  have := P.zeta_strictAnti (Fin.castSucc_lt_succ (i := j))
  simp only [muRows, Fin.val_succ, Fin.val_castSucc]
  omega

/-- The outer Young diagram `λ`, with rows `ξ_i + i`. -/
def lam (P : Profile n) : YoungDiagram := youngOfRows P.lamRows P.lamRows_antitone

/-- The inner Young diagram `μ`, with rows `ζ_i + i`. -/
def mu (P : Profile n) : YoungDiagram := youngOfRows P.muRows P.muRows_antitone

theorem rowLen_lam (P : Profile n) (i : Fin (n + 1)) : P.lam.rowLen i = (P.xi i + i).toNat :=
  rowLen_youngOfRows _ _ i

theorem rowLen_mu (P : Profile n) (i : Fin (n + 1)) : P.mu.rowLen i = (P.zeta i + i).toNat :=
  rowLen_youngOfRows _ _ i

theorem mu_le_lam (P : Profile n) : P.mu ≤ P.lam := by
  intro c hc
  have hc' := (mem_youngOfRows _ _ _).mp hc
  obtain ⟨h, hj⟩ := hc'
  refine (mem_youngOfRows _ _ _).mpr ⟨h, ?_⟩
  have h1 := P.xi_sub_zeta ⟨c.1, h⟩
  have h2 := P.r_pos ⟨c.1, h⟩
  simp only [muRows, lamRows] at *
  omega

theorem rowLen_lam_of_le (P : Profile n) {i : ℕ} (hi : n + 1 ≤ i) : P.lam.rowLen i = 0 :=
  rowLen_youngOfRows_of_le _ _ hi

/-- The skew diagram `λ / μ` of a profile has row lengths `r_i`. -/
theorem skewRowLen_lam_mu (P : Profile n) (i : Fin (n + 1)) :
    Shields.skewRowLen P.lam P.mu i = P.r i := by
  have h1 := P.xi_sub_zeta i
  have h2 := P.zeta_nonneg i
  have h3 := P.r_pos i
  simp only [Shields.skewRowLen, rowLen_lam, rowLen_mu]
  omega

theorem mem_lam (P : Profile n) (i j : ℕ) :
    (i, j) ∈ P.lam ↔ ∃ h : i < n + 1, (j : ℤ) < P.xi ⟨i, h⟩ + i := by
  rw [lam]
  refine (mem_youngOfRows _ _ _).trans ?_
  simp only [lamRows]
  constructor
  · rintro ⟨h, hj⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, hj⟩
    exact ⟨h, by omega⟩

theorem mem_mu (P : Profile n) (i j : ℕ) :
    (i, j) ∈ P.mu ↔ ∃ h : i < n + 1, (j : ℤ) < P.zeta ⟨i, h⟩ + i := by
  rw [mu]
  refine (mem_youngOfRows _ _ _).trans ?_
  simp only [muRows]
  constructor
  · rintro ⟨h, hj⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, hj⟩
    exact ⟨h, by omega⟩

theorem mem_skewCells_row (P : Profile n) (i : Fin (n + 1)) (c : ℕ) :
    ((i : ℕ), c) ∈ Shields.skewCells P.lam P.mu ↔
      P.zeta i + i ≤ c ∧ (c : ℤ) < P.xi i + i := by
  rw [Shields.mem_skewCells, mem_lam, mem_mu]
  simp only [Fin.eta, i.isLt, exists_true_left]
  omega

/-- **Adjacent overlaps.**  Rows `j` and `j + 1` of the skew diagram `λ / μ` of a profile share
exactly `g_j + 1` columns. -/
theorem card_overlap (P : Profile n) (j : Fin n) :
    ((Shields.skewCells P.lam P.mu).filter
      fun c => c.1 = (j : ℕ) ∧ (j.val + 1, c.2) ∈ Shields.skewCells P.lam P.mu).card
      = P.g j + 1 := by
  have h1 := P.xi_succ_sub_zeta_castSucc j
  have hx := P.xi_strictAnti (Fin.castSucc_lt_succ (i := j))
  have hz := P.zeta_strictAnti (Fin.castSucc_lt_succ (i := j))
  have hz0 := P.zeta_nonneg j.succ
  have key : (Shields.skewCells P.lam P.mu).filter
      (fun c => c.1 = (j : ℕ) ∧ (j.val + 1, c.2) ∈ Shields.skewCells P.lam P.mu)
      = (Finset.Ico (P.zeta j.castSucc + j).toNat (P.xi j.succ + j + 1).toNat).image
          fun c => ((j : ℕ), c) := by
    ext ⟨a, c⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨hmem, rfl, hmem2⟩
      have e1 := (P.mem_skewCells_row j.castSucc c).mp (by simpa using hmem)
      have e2 := (P.mem_skewCells_row j.succ c).mp (by simpa using hmem2)
      simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
      exact ⟨c, by omega, rfl, rfl⟩
    · rintro ⟨c', hc', rfl, rfl⟩
      have e1 : (P.zeta j.castSucc + j ≤ c' ∧ (c' : ℤ) < P.xi j.castSucc + j) := by omega
      have e2 : (P.zeta j.succ + (j.succ : ℕ) ≤ c' ∧ (c' : ℤ) < P.xi j.succ + (j.succ : ℕ)) := by
        simp only [Fin.val_succ]
        omega
      refine ⟨?_, rfl, ?_⟩
      · simpa using (P.mem_skewCells_row j.castSucc c').mpr e1
      · simpa using (P.mem_skewCells_row j.succ c').mpr e2
  rw [key, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2), Nat.card_Ico]
  omega

section Bridge

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem aeval_hh (b : ℕ) (β : ℕ → R) (j : ℤ) :
    aeval (fun k : ℕ+ => Shields.completeHom b k β) (hh j)
      = if j < 0 then 0 else Shields.completeHom b j.toNat β := by
  unfold hh
  split_ifs with h
  · simp
  · by_cases h0 : 0 < j.toNat
    · have hp := hPos_pnat ⟨j.toNat, h0⟩
      simp only [PNat.mk_coe] at hp
      rw [hp]
      exact aeval_X (fun k : ℕ+ => Shields.completeHom b k β) (⟨j.toNat, h0⟩ : ℕ+)
    · have : j.toNat = 0 := by omega
      rw [this]
      simp [Shields.completeHom_zero]

/-- **The bridge to tableaux** (Jacobi--Trudi).  For every number `b` of variables and every
commutative `ℚ`-algebra `R` of values `β₀, β₁, …`, specializing each `h_k` to the complete
homogeneous polynomial `h_k(β₀, …, β_{b-1})` sends `P.schur` to the tableau skew Schur polynomial
of the skew diagram `P.lam / P.mu`, whose row lengths and adjacent overlaps are those of the
profile (`skewRowLen_lam_mu`, `card_overlap`). -/
theorem aeval_schur_eq_skewSchur (b : ℕ) (β : ℕ → R) (P : Profile n) :
    aeval (fun k : ℕ+ => Shields.completeHom b k β) P.schur = Shields.skewSchur P.lam P.mu b β := by
  rw [← Shields.jacobiTrudiDet_eq_skewSchur (b := b) (m := n + 1) β P.lam P.mu P.mu_le_lam
    fun i hi => P.rowLen_lam_of_le hi]
  rw [schur, AlgHom.map_det, Shields.jacobiTrudiDet]
  congr 1
  ext u v
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_hh,
    Shields.jtCoeff, rowLen_lam, rowLen_mu]
  have h1 := P.xi_pos u
  have h2 := P.zeta_nonneg v
  have h3 := P.zeta_nonneg u
  split_ifs with ha hb hb
  · omega
  · rfl
  · congr 2
    omega
  · omega

end Bridge

end Profile

/-- The hook `(2,1)` is the skew diagram `(3,2) / (1,1)`, and its rotation is `(3,3) / (2,1)`. -/
example : hookProfile.lamRows = ![3, 2] ∧ hookProfile.muRows = ![1, 1] ∧
    hookRotatedProfile.lamRows = ![3, 3] ∧ hookRotatedProfile.muRows = ![2, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> decide

end GluingCore
