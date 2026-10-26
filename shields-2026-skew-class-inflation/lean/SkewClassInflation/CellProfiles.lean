/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflationClasses
import SkewGluing.CellGeometry
import SkewGluing.SchurFunction
import SkewGluing.Mark

/-!
# Actual connected cell diagrams of the determinant profiles

The representation seam used by `subsec:marked-geometry`,
`prop:saturation-chart`, and `lem:subthreshold-transport` in
`shields-2026-skew-class-inflation.tex`.  The two profile structures are
identified by an explicit equivalence; their full beta lists and Schur
functions agree.  The cell realization is connected skew and determines
the original full profile up to translation.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The actual marked cells sharing an edge with the specified middle diagram. -/
def attachmentCells (W O : SkewGluing.Diagram) : SkewGluing.Diagram :=
  W.filter (fun x => ∃ y ∈ O, SkewGluing.CellAdj x y)

/-- The same literal profile in the marked-cell geometry interface. -/
def gluingProfile {n : ℕ} (P : Profile n) : SkewGluing.Profile n where
  r := P.r
  g := P.g
  r_pos := P.r_pos
  g_lt_castSucc := P.g_lt_castSucc
  g_lt_succ := P.g_lt_succ

/-- The inverse conversion retains every ordered row and gap. -/
def ofGluingProfile {n : ℕ} (P : SkewGluing.Profile n) : Profile n where
  r := P.r
  g := P.g
  r_pos := P.r_pos
  g_lt_castSucc := P.g_lt_castSucc
  g_lt_succ := P.g_lt_succ

/-- The bijective coordinate interface for the full profiles in `eq:beta-profile`.

**No consumer here:** this packages both conversion maps and their inverse laws;
the matrix and cell proofs use the individual coordinate maps directly. -/
def gluingProfileEquiv (n : ℕ) : Profile n ≃ SkewGluing.Profile n where
  toFun := gluingProfile
  invFun := ofGluingProfile
  left_inv _ := rfl
  right_inv _ := rfl

/-- The upper beta coordinates agree literally across the representation boundary. -/
theorem gluingProfile_xi {n : ℕ} (P : Profile n) : (gluingProfile P).xi = P.xi := rfl

/-- The lower beta coordinates agree with the same normalization. -/
theorem gluingProfile_zeta {n : ℕ} (P : Profile n) : (gluingProfile P).zeta = P.zeta := rfl

/-- Both libraries use exactly the same complete generator at every integer index. -/
theorem gluing_hh_eq_complete (k : ℤ) : SkewGluing.hh k = complete k := by
  by_cases hk : k < 0
  · rw [SkewGluing.hh_of_neg hk, complete_of_neg hk]
  · by_cases hz : k = 0
    · subst k
      rw [SkewGluing.hh_zero, complete_zero]
    · have hp : 0 < k := by omega
      let j : ℕ+ := ⟨k.toNat, by omega⟩
      have hj : (j.val : ℤ) = k := by dsimp [j]; omega
      have hc : complete k = MvPolynomial.X j := complete_of_pos hp
      have hh : SkewGluing.hh k = MvPolynomial.X j := by
        rw [← hj]
        exact SkewGluing.hh_pnat j
      exact hh.trans hc.symm

/-- The full Schur determinants agree entrywise across the profile equivalence. -/
theorem gluingProfile_schur {n : ℕ} (P : Profile n) :
    (gluingProfile P).schur = P.toBetaDiagram.schur := by
  rw [SkewGluing.Profile.schur, BetaDiagram.schur]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact gluing_hh_eq_complete (P.xi i - P.zeta j)

/-- The literal finite cell set associated with the original full determinant profile. -/
def profileCells {n : ℕ} (P : Profile n) : SkewGluing.Diagram := (gluingProfile P).cells

/-- The actual row interval, in integer top-to-bottom coordinates. -/
theorem mem_profileCells {n : ℕ} (P : Profile n) (a b : ℤ) :
    (a, b) ∈ profileCells P ↔
      ∃ i : Fin (n + 1), (i.val : ℤ) = a ∧ P.zeta i + i.val ≤ b ∧ b < P.xi i + i.val :=
  SkewGluing.Profile.mem_cells

/-- Every valid full profile produces a genuine connected skew cell diagram. -/
theorem profileCells_connected {n : ℕ} (P : Profile n) :
    SkewGluing.IsConnectedSkew (profileCells P) := (gluingProfile P).isConnectedSkew_cells

/-- Cell translation equality recovers the original full profile, including its row count. -/
theorem profileCells_translation_injective {n m : ℕ} (P : Profile n) (Q : Profile m)
    (v w : ℤ × ℤ)
    (he : SkewGluing.translate v (profileCells P) = SkewGluing.translate w (profileCells Q)) :
    (⟨n, P⟩ : ConnectedProfile) = ⟨m, Q⟩ := by
  have hh := SkewGluing.sigma_eq_of_translate_cells he
  exact congrArg (fun D : (k : ℕ) × SkewGluing.Profile k =>
    (⟨D.1, ofGluingProfile D.2⟩ : ConnectedProfile)) hh

/-- The full content interval is the actual normalized beta span. -/
theorem profileCells_contents {n : ℕ} (P : Profile n) :
    SkewGluing.contents (profileCells P) = Finset.Icc 0 (P.xi 0 - 1) :=
  (gluingProfile P).contents_cells

/-- The actual number of occupied content diagonals equals the normalized upper beta. -/
theorem profileCells_span {n : ℕ} (P : Profile n) :
    (SkewGluing.span (profileCells P) : ℤ) = P.xi 0 := (gluingProfile P).span_cells

/-- The general full span is the row sum minus the entire adjacent-gap sum. -/
theorem profile_span_sum {n : ℕ} (P : Profile n) :
    P.xi 0 = (∑ i : Fin (n + 1), (P.r i : ℤ)) - ∑ j : Fin n, (P.g j : ℤ) := by
  rw [Gluing.Profile.xi, Gluing.Profile.zeta]
  simp only [Fin.val_zero, Nat.zero_le, ite_true, Finset.sum_sub_distrib,
    Fin.sum_univ_succ]
  ring

/-- A two-row profile has these exact full cell intervals. -/
theorem mem_twoRow_profileCells (P : Profile 1) (a b : ℤ) :
    (a, b) ∈ profileCells P ↔
      (a = 0 ∧ (P.r 1 : ℤ) - P.g 0 ≤ b ∧ b < (P.r 0 : ℤ) + P.r 1 - P.g 0) ∨
      (a = 1 ∧ 1 ≤ b ∧ b < (P.r 1 : ℤ) + 1) := by
  have hz1 : P.zeta 1 = 0 := P.zeta_last
  have hz0 : P.zeta 0 = (P.r 1 : ℤ) - P.g 0 := by
    have he := P.zeta_castSucc (0 : Fin 1)
    change P.zeta 0 = P.zeta 1 + P.r 1 - P.g 0 at he
    rw [hz1, zero_add] at he
    exact he
  have hx0 : P.xi 0 = (P.r 0 : ℤ) + P.r 1 - P.g 0 := by
    have he := P.xi_sub_zeta 0
    rw [hz0] at he
    omega
  have hx1 : P.xi 1 = P.r 1 := by
    have he := P.xi_sub_zeta 1
    rw [hz1, sub_zero] at he
    exact he
  rw [mem_profileCells]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    fin_cases i
    · change P.zeta 0 + (0 : ℤ) ≤ b at hlo
      change b < P.xi 0 + (0 : ℤ) at hhi
      rw [hz0] at hlo
      rw [hx0] at hhi
      left
      norm_num at hi hlo hhi
      exact ⟨hi.symm, by omega, by omega⟩
    · change P.zeta 1 + (1 : ℤ) ≤ b at hlo
      change b < P.xi 1 + (1 : ℤ) at hhi
      rw [hz1] at hlo
      rw [hx1] at hhi
      right
      norm_num at hi hlo hhi
      exact ⟨hi.symm, by omega, by omega⟩
  · rintro (⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩)
    · refine ⟨0, rfl, ?_, ?_⟩
      · rw [hz0]; simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hlo
      · rw [hx0]; simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hhi
    · refine ⟨1, rfl, ?_, ?_⟩
      · rw [hz1]; simpa using hlo
      · rw [hx1]; simpa using hhi

end SkewClassInflation
