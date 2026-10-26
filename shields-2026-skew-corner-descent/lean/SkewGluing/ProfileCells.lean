/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import SkewGluing.Profile
import SkewGluing.CellComponents
import SkewGluing.SchurFunction

/-!
# Cell diagrams of profiles

Formalizes the profile-cell representation needed for `shields-2026-skew-corner-descent.tex`,
«Corner cofactors and common cores» (`sec:corner`, `eq:jt`, `eq:corner-factors`).

TODO-COPIED: the profile-cell representation and membership characterization are adapted from
`skew-factor-gluing/lean/SkewGluing/CellProfile.lean`.

This module defines the cell diagram of a profile and proves that each connected skew diagram is
a translate of one.

Sorry-free.
-/

namespace SkewGluing

/-! ### Row geometry used to recover a profile -/

/-- The columns occupied in row `a`. -/
def rowCols (D : Diagram) (a : ℤ) : Finset ℤ :=
  (D.filter fun x => x.1 = a).image Prod.snd

theorem mem_rowCols {D : Diagram} {a b : ℤ} :
    b ∈ rowCols D a ↔ (a, b) ∈ D := by
  simp only [rowCols, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hxy, rfl⟩, rfl⟩
    exact hxy
  · intro h
    exact ⟨a, b, ⟨h, rfl⟩, rfl⟩

/-- The first column of row `a`, or zero if the row is empty. -/
def rowLo (D : Diagram) (a : ℤ) : ℤ :=
  if h : (rowCols D a).Nonempty then (rowCols D a).min' h else 0

/-- The last column of row `a`, or zero if the row is empty. -/
def rowHi (D : Diagram) (a : ℤ) : ℤ :=
  if h : (rowCols D a).Nonempty then (rowCols D a).max' h else 0

theorem rowLo_mem {D : Diagram} {a : ℤ} (h : (rowCols D a).Nonempty) :
    (a, rowLo D a) ∈ D := by
  have hm : rowLo D a ∈ rowCols D a := by
    simp only [rowLo, h, dite_true]
    exact Finset.min'_mem _ h
  exact mem_rowCols.mp hm

theorem rowHi_mem {D : Diagram} {a : ℤ} (h : (rowCols D a).Nonempty) :
    (a, rowHi D a) ∈ D := by
  have hm : rowHi D a ∈ rowCols D a := by
    simp only [rowHi, h, dite_true]
    exact Finset.max'_mem _ h
  exact mem_rowCols.mp hm

theorem rowLo_le {D : Diagram} {a b : ℤ} (h : (a, b) ∈ D) :
    rowLo D a ≤ b := by
  have hn : (rowCols D a).Nonempty := ⟨b, mem_rowCols.mpr h⟩
  have hm : rowLo D a = (rowCols D a).min' hn := by simp [rowLo, hn]
  rw [hm]
  exact Finset.min'_le _ _ (mem_rowCols.mpr h)

theorem le_rowHi {D : Diagram} {a b : ℤ} (h : (a, b) ∈ D) :
    b ≤ rowHi D a := by
  have hn : (rowCols D a).Nonempty := ⟨b, mem_rowCols.mpr h⟩
  have hm : rowHi D a = (rowCols D a).max' hn := by simp [rowHi, hn]
  rw [hm]
  exact Finset.le_max' _ _ (mem_rowCols.mpr h)

/-- Cells in a row form an interval in a skew diagram. -/
theorem IsSkew.mem_iff_row {D : Diagram} (hs : IsSkew D) {a b : ℤ}
    (h : (rowCols D a).Nonempty) :
    (a, b) ∈ D ↔ rowLo D a ≤ b ∧ b ≤ rowHi D a := by
  constructor
  · intro hb
    have hne : (rowCols D a).Nonempty := h
    have hlo : rowLo D a = (rowCols D a).min' hne := by simp [rowLo, hne]
    have hhi : rowHi D a = (rowCols D a).max' hne := by simp [rowHi, hne]
    rw [hlo, hhi]
    exact ⟨Finset.min'_le _ _ (mem_rowCols.mpr hb),
      Finset.le_max' _ _ (mem_rowCols.mpr hb)⟩
  · rintro ⟨hl, hh⟩
    have hlo : (a, rowLo D a) ∈ D := by
      have hne : (rowCols D a).Nonempty := h
      have hmem : rowLo D a ∈ rowCols D a := by
        simp only [rowLo, h, dite_true]
        exact Finset.min'_mem _ h
      exact mem_rowCols.mp hmem
    have hhi : (a, rowHi D a) ∈ D := by
      have hne : (rowCols D a).Nonempty := h
      have hmem : rowHi D a ∈ rowCols D a := by
        simp only [rowHi, h, dite_true]
        exact Finset.max'_mem _ h
      exact mem_rowCols.mp hmem
    exact hs.mem hlo hhi le_rfl (by omega) le_rfl le_rfl hl hh

theorem IsEdgeConnected.exists_row {D : Diagram} (hD : IsEdgeConnected D) {x y : ℤ × ℤ}
    (hx : x ∈ D) (hy : y ∈ D) {i : ℤ} (h1 : min x.1 y.1 ≤ i)
    (h2 : i ≤ max x.1 y.1) : ∃ z ∈ D, z.1 = i := by
  have key : ∀ y, DiagReach D x y → ∀ i,
      min x.1 y.1 ≤ i → i ≤ max x.1 y.1 → ∃ z ∈ D, z.1 = i := by
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

/-- The integer row indices occupied by the diagram. -/
def rowSet (D : Diagram) : Finset ℤ := D.image Prod.fst

theorem mem_rowSet {D : Diagram} {a : ℤ} :
    a ∈ rowSet D ↔ (rowCols D a).Nonempty := by
  simp only [rowSet, Finset.mem_image, Prod.exists, Finset.Nonempty,
    mem_rowCols]
  constructor
  · rintro ⟨x, y, h, rfl⟩
    exact ⟨y, h⟩
  · rintro ⟨y, h⟩
    exact ⟨a, y, h, rfl⟩

/-- The occupied rows of a connected diagram form an integer interval. -/
theorem IsConnectedSkew.exists_rows {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ t : ℤ, ∃ n : ℕ, ∀ a : ℤ,
      (rowCols D a).Nonempty ↔ t ≤ a ∧ a ≤ t + n := by
  let rows := D.image Prod.fst
  have hne : rows.Nonempty := by
    obtain ⟨x, hx⟩ := hD.2.1
    exact ⟨x.1, Finset.mem_image_of_mem _ hx⟩
  refine ⟨rows.min' hne, (rows.max' hne - rows.min' hne).toNat, fun a => ?_⟩
  rw [← mem_rowSet]
  constructor
  · intro ha
    exact ⟨Finset.min'_le _ _ ha, by
      have := Finset.le_max' rows a ha
      omega⟩
  · rintro ⟨hlo, hhi⟩
    obtain ⟨x, hx, hxrow⟩ := Finset.mem_image.mp (Finset.min'_mem rows hne)
    obtain ⟨y, hy, hyrow⟩ := Finset.mem_image.mp (Finset.max'_mem rows hne)
    obtain ⟨z, hz, hza⟩ := hD.2.exists_row hx hy (i := a) (by omega) (by omega)
    exact Finset.mem_image.mpr ⟨z, hz, hza⟩

/-- Consecutive nonempty rows of an edge-connected diagram share a column. -/
theorem IsEdgeConnected.exists_overlap {D : Diagram} (hD : IsEdgeConnected D) {a : ℤ}
    (h1 : (rowCols D a).Nonempty) (h2 : (rowCols D (a + 1)).Nonempty) :
    ∃ c, (a, c) ∈ D ∧ (a + 1, c) ∈ D := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  have hxD := mem_rowCols.mp hx
  have hyD := mem_rowCols.mp hy
  have hreach := hD.2 (a, x) hxD (a + 1, y) hyD
  have key : ∀ z, DiagReach D (a, x) z → a < z.1 →
      ∃ c, (a, c) ∈ D ∧ (a + 1, c) ∈ D := by
    intro z hz
    induction hz with
    | refl => intro hz; omega
    | @tail b c hab hbc ih =>
      intro hz
      by_cases hb : a < b.1
      · exact ih hb
      · have hadj := cellAdj_iff.mp hbc.2.2
        have hb1 : b.1 = a := by omega
        refine ⟨b.2, ?_, ?_⟩
        · have : b = (a, b.2) := Prod.ext hb1 rfl
          rw [← this]
          exact hbc.1
        · have hc : c = (a + 1, b.2) := Prod.ext (by omega) (by omega)
          rw [← hc]
          exact hbc.2.1
  exact key _ hreach (by simp)

theorem IsConnectedSkew.row_step {D : Diagram} (hD : IsConnectedSkew D) {a : ℤ}
    (h1 : (rowCols D a).Nonempty) (h2 : (rowCols D (a + 1)).Nonempty) :
    rowLo D (a + 1) ≤ rowLo D a ∧ rowHi D (a + 1) ≤ rowHi D a ∧
      rowLo D a ≤ rowHi D (a + 1) := by
  obtain ⟨c, hc1, hc2⟩ := hD.2.exists_overlap h1 h2
  have l1 := rowLo_le hc1
  have l2 := le_rowHi hc2
  have h3 : (a + 1, rowLo D a) ∈ D :=
    hD.1.mem (rowLo_mem h1) hc2 (by omega) l1 (by omega) (by omega) (le_refl _) l1
  have h4 : (a, rowHi D (a + 1)) ∈ D :=
    hD.1.mem hc1 (rowHi_mem h2) (by omega) l2 (le_refl _) (by omega) l2 (le_refl _)
  exact ⟨rowLo_le h3, le_rowHi h4, by omega⟩

namespace Profile

variable {n : ℕ}


/-- The cell diagram of a profile: row `i` occupies columns `[ζᵢ + i, ξᵢ + i)`. -/
def cells (P : Profile n) : Diagram :=
  Finset.univ.biUnion fun i : Fin (n + 1) =>
    (Finset.Ico (P.zeta i + i) (P.xi i + i)).image fun j => ((i : ℤ), j)

/-- Membership in the cell diagram of a profile. -/
theorem mem_cells {P : Profile n} {a b : ℤ} :
    (a, b) ∈ P.cells ↔ ∃ i : Fin (n + 1), (i : ℤ) = a ∧
      P.zeta i + i ≤ b ∧ b < P.xi i + i := by
  simp only [cells, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
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

/-- Every row interval in a profile diagram is nonempty. -/
theorem cells_row_nonempty (P : Profile n) (i : Fin (n + 1)) :
    ∃ b : ℤ, ((i : ℤ), b) ∈ P.cells := by
  refine ⟨P.zeta i + i, ?_⟩
  rw [mem_cells_fin]
  have hr := P.xi_sub_zeta i
  have hp := P.r_pos i
  omega

end Profile

end SkewGluing
namespace SkewGluing

theorem IsConnectedSkew.exists_profile_cells {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ (n : ℕ) (P : Profile n) (v : ℤ × ℤ), D = translate v P.cells := by
  obtain ⟨t, n, hrows⟩ := hD.exists_rows
  have hne : ∀ k : ℤ, 0 ≤ k → k ≤ n → (rowCols D (t + k)).Nonempty :=
    fun k h1 h2 => (hrows _).mpr ⟨by omega, by omega⟩
  have hstep : ∀ j : Fin n,
      rowLo D (t + ((j.succ : ℕ) : ℤ)) ≤ rowLo D (t + ((j.castSucc : ℕ) : ℤ)) ∧
      rowHi D (t + ((j.succ : ℕ) : ℤ)) ≤ rowHi D (t + ((j.castSucc : ℕ) : ℤ)) ∧
      rowLo D (t + ((j.castSucc : ℕ) : ℤ)) ≤ rowHi D (t + ((j.succ : ℕ) : ℤ)) := by
    intro j
    have hj := j.isLt
    have e : t + ((j.succ : ℕ) : ℤ) = t + ((j.castSucc : ℕ) : ℤ) + 1 := by simp; ring
    rw [e]
    have h1 : (rowCols D (t + ((j.castSucc : ℕ) : ℤ))).Nonempty :=
      hne _ (by omega) (by omega)
    have h2 : (rowCols D (t + ((j.castSucc : ℕ) : ℤ) + 1)).Nonempty := by
      rw [← e]
      exact hne _ (by omega) (by omega)
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
 

end SkewGluing
