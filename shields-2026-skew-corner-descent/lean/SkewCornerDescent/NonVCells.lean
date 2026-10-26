/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.NonVProfile
import SkewGluing.DiagramSchur
import SkewGluing.InteriorCofactor
import SkewGluing.ProfileStatistics

/-!
# Literal cells of the infinite ordinary family

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-family`, `eq:non-v-jt`). The stated coordinate rows are
identified with the connected profile before its polynomial formula is applied. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The stated bottom, middle, and top coordinate rows of `(k,k,2)/(k-2)`. -/
def nonVDiagram (k : ℕ) : Diagram :=
  ((Finset.Ico (0 : ℤ) 2).image fun j => (0, j)) ∪
    ((Finset.Ico (0 : ℤ) k).image fun j => (-1, j)) ∪
      ((Finset.Ico ((k : ℤ) - 2) k).image fun j => (-2, j))

/-- Membership describes the literal three coordinate intervals. -/
theorem mem_nonVDiagram (k : ℕ) (a b : ℤ) :
    (a, b) ∈ nonVDiagram k ↔
      (a = 0 ∧ 0 ≤ b ∧ b < 2) ∨
        (a = -1 ∧ 0 ≤ b ∧ b < k) ∨
          (a = -2 ∧ (k : ℤ) - 2 ≤ b ∧ b < k) := by
  simp [nonVDiagram, Finset.mem_image, Prod.mk.injEq, and_comm, and_left_comm, and_assoc,
    eq_comm]

/-- The actual coordinate diagram is the translated connected three-row profile. -/
theorem nonVDiagram_eq_profile (k : ℕ) (hk : 3 ≤ k) :
    nonVDiagram k = translate (-2, -2) (nonVProfile k hk).cells := by
  ext p
  obtain ⟨a, b⟩ := p
  rw [mem_nonVDiagram, mem_translate]
  change _ ↔ (a + 2, b + 2) ∈ (nonVProfile k hk).cells
  rw [Profile.mem_cells, nonVProfile_zeta, nonVProfile_xi]
  constructor
  · rintro (h | h | h)
    · refine ⟨2, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨1, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨0, ?_, ?_, ?_⟩ <;> simp <;> omega
  · rintro ⟨i, hi, hlo, hhi⟩
    fin_cases i <;> norm_num at hi hlo hhi <;> omega

/-- Connectedness and skewness are supplied by the actual profile presentation. -/
theorem nonVDiagram_isConnectedSkew (k : ℕ) (hk : 3 ≤ k) :
    IsConnectedSkew (nonVDiagram k) := by
  rw [nonVDiagram_eq_profile k hk]
  exact isConnectedSkew_translate _ (nonVProfile k hk).isConnectedSkew_cells

/-- The infinite-family determinant is the actual cell function of the stated diagram. -/
theorem nonVDiagram_schur (k : ℕ) (hk : 3 ≤ k) :
    cellSchur (nonVDiagram k) (nonVDiagram_isConnectedSkew k hk).1 =
      (hh 2)^2 * hh k - 2 * hh 1 * hh 2 * hh ((k : ℤ) + 1) +
        (hh 1)^2 * hh ((k : ℤ) + 2) := by
  rw [cellSchur_eq_profile (nonVDiagram_isConnectedSkew k hk) (nonVProfile k hk)
    (-2, -2) (nonVDiagram_eq_profile k hk), nonVProfile_schur]

/-- The actual geometric top is `k+2`, throughout the infinite family. -/
theorem nonVProfile_top (k : ℕ) (hk : 3 ≤ k) :
    ((nonVProfile k hk).topVar : ℕ) = k + 2 := by
  have ht := (nonVProfile k hk).topVar_coe
  rw [nonVProfile_xi] at ht
  norm_num at ht
  exact_mod_cast ht

/-- The original coordinate diagram has exactly the claimed top content span. -/
theorem nonVDiagram_span (k : ℕ) (hk : 3 ≤ k) :
    span (nonVDiagram k) = k + 2 := by
  rw [nonVDiagram_eq_profile k hk, span_translate, Profile.span_cells_eq_topVar,
    nonVProfile_top]

/-- Direct original-generator differentiation gives the finite-cap cofactor. -/
theorem nonVDiagram_pderiv (k : ℕ) (hk : 3 ≤ k) :
    MvPolynomial.pderiv (nonVProfile k hk).topVar
      (cellSchur (nonVDiagram k) (nonVDiagram_isConnectedSkew k hk).1) = (hh 1)^2 := by
  have ht : (((nonVProfile k hk).topVar : ℕ) : ℤ) = (k : ℤ) + 2 := by
    rw [nonVProfile_top, Nat.cast_add, Nat.cast_ofNat]
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have htwo : MvPolynomial.pderiv (nonVProfile k hk).topVar (2 : Lambda) = 0 :=
    Derivation.map_natCast _ 2
  rw [nonVDiagram_schur k hk]
  simp [map_add, map_sub, htwo, pderiv_hh, ht,
    show (1 : ℤ) ≠ (k : ℤ) + 2 by omega,
    show (2 : ℤ) ≠ (k : ℤ) + 2 by omega,
    show (k : ℤ) ≠ (k : ℤ) + 2 by omega,
    show (k : ℤ) + 1 ≠ (k : ℤ) + 2 by omega]

/-- The cofactor is the actual southeast-interior function, not merely a formal derivative. -/
theorem nonVDiagram_interiorSchur (k : ℕ) (hk : 3 ≤ k) :
    cellSchur (diagramInterior (nonVDiagram k))
      (nonVDiagram_isConnectedSkew k hk).1.interior = (hh 1)^2 := by
  have h := pderiv_cellSchur_eq_interiorSchur (nonVDiagram_isConnectedSkew k hk)
    (nonVProfile k hk) (-2, -2) (nonVDiagram_eq_profile k hk)
  rw [nonVDiagram_pderiv] at h
  simpa using h.symm

/-- The original southeast interior consists of the two literal cells stated by the family. -/
theorem nonVDiagram_interior (k : ℕ) (hk : 3 ≤ k) :
    diagramInterior (nonVDiagram k) = {(-1, 0), (-2, (k : ℤ) - 2)} := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  ext p
  obtain ⟨a, b⟩ := p
  rw [diagramInterior, Finset.mem_filter]
  simp only [eCell, Prod.mk_add_mk, mem_nonVDiagram, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  omega

end SkewCornerDescent
