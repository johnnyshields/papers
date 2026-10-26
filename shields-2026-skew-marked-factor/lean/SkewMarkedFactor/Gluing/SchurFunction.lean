/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/SchurFunction.lean
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import SkewMarkedFactor.Gluing.Profile

/-!
# Skew Schur functions of connected diagrams, from their profiles

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the paragraph on profiles and Jacobi--Trudi, and «Source-minimal fibers»
(`sec:minimal-fibers`), the hook-class computation and the involution `ι` in «Component keys».

The ring of symmetric functions is modeled as `Λ = ℚ[h₁, h₂, …]`, the polynomial ring on the
variables `h_j`, `j ≥ 1` (`Lambda`), with `h₀ = 1` and `h_j = 0` for `j < 0` (`hh`).  The skew
Schur function of a connected diagram is the Jacobi--Trudi determinant `det (h_{ξ_i - ζ_j})` of
its profile (`Profile.schur`); the bridge identifying it with the tableau skew Schur polynomial is
in `SkewMarkedFactor.Gluing.SchurBridge`.  Here we compute the four connected
three-cell diagrams, prove that
the profile function is rotation invariant, define the involution `ι` with `ι(h_j) = e_j` and
prove it is an involution, and state the two literature inputs the paper consumes as named
propositions (`BarekatIrreducibility`, `ReinerRowInvariants`).

* `Profile.schur`, `Profile.schur_rotate`: the function of a profile; rotation invariance.
* `schur_hook`, `schur_hookRotated`, `schur_row`, `schur_column`: the four connected three-cell
  diagrams.
* `elem`, `schurInvolution`, `schurInvolution_involutive`: the elementary functions `e_j`, the
  involution `ι`, and `ι ∘ ι = id`.
* `schurInvolution_schur_row`, `schurInvolution_schur_hook`: `ι(s_{(3)}) = s_{(1,1,1)}` and the
  hook is fixed.
* `BarekatIrreducibility`, `ReinerRowInvariants`: the two literature inputs, as propositions.
  They are proved in `SkewMarkedFactor.Gluing.Irreducibility` (`barekatIrreducibility`) and
  `SkewMarkedFactor.Gluing.RowInvariants` (`reinerRowInvariants`).

The identity `ι(s_D) = s_{Dᵗ}` is proved in `SkewMarkedFactor.Gluing.TransposeSchur`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

open MvPolynomial

/-- The ring `Λ = ℚ[h₁, h₂, …]` of symmetric functions, as the polynomial ring on the variables
`h_j`, `j ≥ 1`. -/
abbrev Lambda : Type := MvPolynomial ℕ+ ℚ

/-- The complete homogeneous function `h_k` for `k ≥ 0`: the variable `h_k` for `k ≥ 1` and
`h₀ = 1`. -/
noncomputable def hPos (k : ℕ) : Lambda := if h : 0 < k then X ⟨k, h⟩ else 1

/-- The Jacobi--Trudi entry `h_j`, with `h_j = 0` for `j < 0` and `h₀ = 1`. -/
noncomputable def hh (j : ℤ) : Lambda := if j < 0 then 0 else hPos j.toNat

@[simp]
theorem hh_of_neg {j : ℤ} (hj : j < 0) : hh j = 0 := by simp [hh, hj]

@[simp]
theorem hh_zero : hh 0 = 1 := by simp [hh, hPos]

theorem hh_natCast (k : ℕ) : hh (k : ℤ) = hPos k := by simp [hh]

@[simp]
theorem hPos_zero : hPos 0 = 1 := by simp [hPos]

theorem hPos_pnat (k : ℕ+) : hPos k = X k := by
  simp only [hPos, k.pos, dite_true]
  rfl

theorem hh_pnat (k : ℕ+) : hh (k : ℤ) = X k := by
  rw [hh_natCast, hPos_pnat]

namespace Profile

variable {n : ℕ}

/-- **The skew Schur function of a connected diagram with profile `P`**, as its
Jacobi--Trudi determinant `det (h_{ξ_i - ζ_j})_{i,j}`, with `h₀ = 1` and `h_j = 0` for `j < 0`. -/
noncomputable def schur (P : Profile n) : Lambda :=
  (Matrix.of fun i j : Fin (n + 1) => hh (P.xi i - P.zeta j)).det

/-- Rotation does not change the skew Schur function of a profile: the Jacobi--Trudi matrix of
the rotation is the transpose of the original, reindexed by reversal. -/
theorem schur_rotate (P : Profile n) : P.rotate.schur = P.schur := by
  unfold schur
  have h : (Matrix.of fun i j : Fin (n + 1) => hh (P.rotate.xi i - P.rotate.zeta j))
      = ((Matrix.of fun i j : Fin (n + 1) => hh (P.xi i - P.zeta j)).transpose).submatrix
          Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Fin.revPerm_apply,
      xi_rotate, zeta_rotate]
    rw [show P.xi 0 - P.zeta i.rev - (P.xi 0 - P.xi j.rev) = P.xi j.rev - P.zeta i.rev by ring]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

end Profile

/-! ### The four connected three-cell diagrams -/

/-- The hook `(2,1)`: rows of length `2, 1`, overlap one. -/
def hookProfile : Profile 1 where
  r := ![2, 1]
  g := ![0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The rotated hook `(2,2)/(1)`: rows of length `1, 2`, overlap one. -/
def hookRotatedProfile : Profile 1 where
  r := ![1, 2]
  g := ![0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The row `(3)`. -/
def rowProfile : Profile 0 where
  r := ![3]
  g := Fin.elim0
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The column `(1,1,1)`: three rows of length one, each overlapping the next in one cell. -/
def columnProfile : Profile 2 where
  r := ![1, 1, 1]
  g := ![0, 0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

theorem hookRotatedProfile_eq_rotate : hookProfile.rotate = hookRotatedProfile := by
  refine Profile.ext (funext fun i => ?_) (funext fun j => ?_)
  · fin_cases i <;> rfl
  · fin_cases j
    rfl

/-- The beta lists of the hook `(2,1)` are `ξ = (3,1)`, `ζ = (1,0)`. -/
example : hookProfile.xi 0 = 3 ∧ hookProfile.xi 1 = 1 ∧ hookProfile.zeta 0 = 1 ∧
    hookProfile.zeta 1 = 0 := by
  decide

/-- `s_{(2,1)} = h₁ h₂ - h₃`. -/
theorem schur_hook : hookProfile.schur = X 1 * X 2 - X 3 := by
  have h1 : hookProfile.xi 0 = 3 := by decide
  have h2 : hookProfile.xi 1 = 1 := by decide
  have h3 : hookProfile.zeta 0 = 1 := by decide
  have h4 : hookProfile.zeta 1 = 0 := by decide
  have e1 : hh 1 = X 1 := by simpa using hh_pnat 1
  have e2 : hh 2 = X 2 := by simpa using hh_pnat 2
  have e3 : hh 3 = X 3 := by simpa using hh_pnat 3
  rw [Profile.schur, Matrix.det_fin_two]
  simp [h1, h2, h3, h4, e1, e2, e3]
  ring

/-- `s_{(2,2)/(1)} = h₁ h₂ - h₃`, so `s_{(2,2)/(1)} = s_{(2,1)}`. -/
theorem schur_hookRotated : hookRotatedProfile.schur = X 1 * X 2 - X 3 := by
  rw [← hookRotatedProfile_eq_rotate, Profile.schur_rotate, schur_hook]

/-- `s_{(3)} = h₃`. -/
theorem schur_row : rowProfile.schur = X 3 := by
  have h1 : rowProfile.xi 0 = 3 := by decide
  have h2 : rowProfile.zeta 0 = 0 := by decide
  have e3 : hh 3 = X 3 := by simpa using hh_pnat 3
  rw [Profile.schur, Matrix.det_succ_row_zero]
  simp [h1, h2, e3]

/-- `s_{(1,1,1)} = h₁³ - 2 h₁ h₂ + h₃`. -/
theorem schur_column : columnProfile.schur = X 1 ^ 3 - 2 * X 1 * X 2 + X 3 := by
  have h1 : columnProfile.xi 0 = 3 := by decide
  have h2 : columnProfile.xi 1 = 2 := by decide
  have h3 : columnProfile.xi 2 = 1 := by decide
  have h4 : columnProfile.zeta 0 = 2 := by decide
  have h5 : columnProfile.zeta 1 = 1 := by decide
  have h6 : columnProfile.zeta 2 = 0 := by decide
  have e1 : hh 1 = X 1 := by simpa using hh_pnat 1
  have e2 : hh 2 = X 2 := by simpa using hh_pnat 2
  have e3 : hh 3 = X 3 := by simpa using hh_pnat 3
  rw [Profile.schur, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove, h1, h2, h3, h4, h5, h6, e1, e2, e3]
  ring

/-! ### The involution `ι` -/

/-- The elementary function `e_j ∈ Λ`, defined from the complete homogeneous functions by the
relation `∑_{k=0}^{j} (-1)^k e_k h_{j-k} = 0` for `j ≥ 1`, with `e₀ = 1`. -/
noncomputable def elem : ℕ → Lambda
  | 0 => 1
  | j + 1 => ∑ k : Fin (j + 1), (-1) ^ (j + k.1) * elem k.1 * hPos (j + 1 - k.1)
decreasing_by exact k.isLt

/-- The alternating convolution `∑_{k=0}^{j} (-1)^k a_k b_{j-k}`. -/
noncomputable def altConv (a b : ℕ → Lambda) (j : ℕ) : Lambda :=
  ∑ k ∈ Finset.range (j + 1), (-1) ^ k * a k * b (j - k)

theorem altConv_comm (a b : ℕ → Lambda) (j : ℕ) : altConv a b j = (-1) ^ j * altConv b a j := by
  unfold altConv
  rw [Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : k < j + 1 := Finset.mem_range.mp hk
  have e1 : j + 1 - 1 - k = j - k := by omega
  have e2 : j - (j - k) = k := by omega
  rw [e1, e2]
  have h1 : (-1 : Lambda) ^ j = (-1) ^ (j - k) * (-1) ^ k := by
    rw [← pow_add]; congr 1; omega
  have h2 : (-1 : Lambda) ^ (j - k) * (-1) ^ (j - k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc (-1 : Lambda) ^ k * a k * b (j - k)
      = ((-1) ^ (j - k) * (-1) ^ (j - k)) * (-1) ^ k * (b (j - k) * a k) := by
        rw [h2]; ring
    _ = _ := by rw [h1]; ring

theorem altConv_elem_hPos (j : ℕ) (hj : 0 < j) : altConv elem hPos j = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  unfold altConv
  rw [Finset.sum_range_succ, Nat.sub_self, hPos_zero]
  have he : elem (m + 1) =
      ∑ k ∈ Finset.range (m + 1), (-1) ^ (m + k) * elem k * hPos (m + 1 - k) := by
    rw [elem]
    exact Fin.sum_univ_eq_sum_range (fun k => (-1) ^ (m + k) * elem k * hPos (m + 1 - k)) (m + 1)
  rw [he, Finset.mul_sum, mul_one, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : (-1 : Lambda) ^ (m + 1) * (-1) ^ (m + k) = - (-1) ^ k := by
    rw [← pow_add, show m + 1 + (m + k) = 2 * m + 1 + k by ring, pow_add, pow_add, pow_mul]
    simp
  linear_combination (elem k * hPos (m + 1 - k)) * this

/-- **The involution `ι`** of `Λ` with `ι(h_j) = e_j`, as the algebra endomorphism sending `h_j`
to `e_j`. -/
noncomputable def schurInvolution : Lambda →ₐ[ℚ] Lambda := aeval fun k : ℕ+ => elem k

theorem schurInvolution_X (k : ℕ+) : schurInvolution (X k) = elem k := by
  rw [schurInvolution, aeval_X]

theorem schurInvolution_hPos (k : ℕ) : schurInvolution (hPos k) = elem k := by
  by_cases hk : 0 < k
  · have h := hPos_pnat ⟨k, hk⟩
    simp only [PNat.mk_coe] at h
    rw [h]
    exact aeval_X (fun k : ℕ+ => elem k) (⟨k, hk⟩ : ℕ+)
  · obtain rfl : k = 0 := by omega
    simp [elem]

theorem schurInvolution_elem (j : ℕ) : schurInvolution (elem j) = hPos j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | m
    · simp [elem]
    · have h0 : altConv hPos elem (m + 1) = 0 := by
        rw [altConv_comm, altConv_elem_hPos _ (by omega), mul_zero]
      unfold altConv at h0
      rw [Finset.sum_range_succ, Nat.sub_self] at h0
      have he : elem (m + 1) = ∑ k ∈ Finset.range (m + 1),
          (-1) ^ (m + k) * elem k * hPos (m + 1 - k) := by
        rw [elem]
        exact Fin.sum_univ_eq_sum_range
          (fun k => (-1) ^ (m + k) * elem k * hPos (m + 1 - k)) (m + 1)
      rw [he, map_sum]
      have e1 : ∀ k ∈ Finset.range (m + 1), schurInvolution ((-1) ^ (m + k) * elem k *
          hPos (m + 1 - k)) = (-1) ^ (m + k) * hPos k * elem (m + 1 - k) := by
        intro k hk
        have hk : k < m + 1 := Finset.mem_range.mp hk
        rw [map_mul, map_mul, ih k hk, schurInvolution_hPos]
        simp
      rw [Finset.sum_congr rfl e1]
      have e2 : elem 0 = 1 := by simp [elem]
      rw [e2, mul_one] at h0
      have e3 : ∑ k ∈ Finset.range (m + 1), (-1 : Lambda) ^ (m + k) * hPos k * elem (m + 1 - k)
          = (-1) ^ m *
            ∑ k ∈ Finset.range (m + 1), (-1 : Lambda) ^ k * hPos k * elem (m + 1 - k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [pow_add]; ring
      have e4 : (-1 : Lambda) ^ m * (-1) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      rw [e3]
      have : ∑ k ∈ Finset.range (m + 1), (-1 : Lambda) ^ k * hPos k * elem (m + 1 - k)
          = (-1) ^ m * hPos (m + 1) := by
        have : (-1 : Lambda) ^ (m + 1) = -(-1) ^ m := by rw [pow_succ]; ring
        rw [this] at h0
        linear_combination h0
      rw [this]
      linear_combination (hPos (m + 1)) * e4

/-- **`ι` is an involution.** -/
theorem schurInvolution_involutive : Function.Involutive schurInvolution := by
  have h : schurInvolution.comp schurInvolution = AlgHom.id ℚ Lambda := by
    apply MvPolynomial.algHom_ext
    intro k
    have : schurInvolution (X k) = elem k := by rw [schurInvolution, aeval_X]
    simp only [AlgHom.comp_apply, this, schurInvolution_elem, AlgHom.id_apply, hPos_pnat]
  intro x
  exact congrArg (fun f : Lambda →ₐ[ℚ] Lambda => f x) h

theorem elem_succ (m : ℕ) : elem (m + 1) =
    ∑ k ∈ Finset.range (m + 1), (-1) ^ (m + k) * elem k * hPos (m + 1 - k) := by
  rw [elem]
  exact Fin.sum_univ_eq_sum_range (fun k => (-1) ^ (m + k) * elem k * hPos (m + 1 - k)) (m + 1)

theorem hPos_one : hPos 1 = X 1 := by simpa using hPos_pnat 1

theorem hPos_two : hPos 2 = X 2 := by simpa using hPos_pnat 2

theorem hPos_three : hPos 3 = X 3 := by simpa using hPos_pnat 3

/-- `e₁ = h₁`. -/
theorem elem_one : elem 1 = X 1 := by
  rw [elem_succ]
  simp [elem, hPos_one]

/-- `e₂ = h₁² - h₂`. -/
theorem elem_two : elem 2 = X 1 ^ 2 - X 2 := by
  rw [elem_succ]
  simp [Finset.sum_range_succ, elem_one, elem, hPos_one, hPos_two]
  ring

/-- `e₃ = h₁³ - 2 h₁ h₂ + h₃`. -/
theorem elem_three : elem 3 = X 1 ^ 3 - 2 * X 1 * X 2 + X 3 := by
  rw [elem_succ]
  simp [Finset.sum_range_succ, elem_one, elem_two, elem, hPos_one, hPos_two, hPos_three]
  ring

/-- `ι(s_{(3)}) = s_{(1,1,1)}`: the involution exchanges the row and the column. -/
theorem schurInvolution_schur_row : schurInvolution rowProfile.schur = columnProfile.schur := by
  rw [schur_row, schur_column, schurInvolution, aeval_X]
  exact elem_three

/-- `ι(s_{(2,1)}) = s_{(2,1)}`: the hook is fixed by the involution. -/
theorem schurInvolution_schur_hook : schurInvolution hookProfile.schur = hookProfile.schur := by
  have h1 : schurInvolution (X 1) = elem 1 := by simpa using schurInvolution_X 1
  have h2 : schurInvolution (X 2) = elem 2 := by simpa using schurInvolution_X 2
  have h3 : schurInvolution (X 3) = elem 3 := by simpa using schurInvolution_X 3
  rw [schur_hook, map_sub, map_mul, h1, h2, h3, elem_one, elem_two, elem_three]
  ring

/-! ### Literature inputs -/

/-- The theorem of `Barekat2009CoincidencesCorrigendum` (Thm. 1): the skew Schur function of a
connected diagram is irreducible in `Λ`.  Stated for every profile, i.e. every connected diagram;
proved as `barekatIrreducibility` in `SkewMarkedFactor.Gluing.Irreducibility`. -/
def BarekatIrreducibility : Prop := ∀ (n : ℕ) (P : Profile n), Irreducible P.schur

/-- The theorem of `Reiner2007Coincidences` (Cor. 8.11): connected diagrams with the same skew
Schur function have the same number of rows, the same multiset of row lengths, and the same
multiset of adjacent overlaps.  Stated for profiles `P`, `Q` of connected diagrams; proved as
`reinerRowInvariants` in `SkewMarkedFactor.Gluing.RowInvariants`. -/
def ReinerRowInvariants : Prop :=
  ∀ (m n : ℕ) (P : Profile m) (Q : Profile n), P.schur = Q.schur →
    m = n ∧ P.rowMultiset = Q.rowMultiset ∧ P.gapMultiset = Q.gapMultiset

end SkewMarkedFactor.Gluing
