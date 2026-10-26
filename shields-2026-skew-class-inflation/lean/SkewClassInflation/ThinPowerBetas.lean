/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinReadings
import SkewClassInflation.ProfileJoinBetas
import SkewJacobiNegative.RestorationGeometry

/-!
# Full beta lists of a thin overlapped power

Formalizes the single-block calculation preceding `eq:thin-beta-lists`
in `shields-2026-skew-class-inflation.tex`.  Both lists retain all common
coordinates.  The formulas cover copy multiplicity one.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The positive block span parameter, in the manuscript's signed coordinate convention. -/
theorem boundary_q_eq : (B.boundary.q : ℤ) = (B.a : ℤ) + B.b - B.c := by
  have := B.c_lt_a
  dsimp [boundary, BoundaryParameters.ofThin]
  omega

/-- Ordered full upper betas of one overlapped power. -/
def powerUpper (m : ℕ) (i : Fin (m + 1)) : ℤ :=
  if i.val = 0 then (m : ℤ) * B.boundary.q
  else B.b + ((m : ℤ) - i.val) * B.boundary.q

/-- Ordered full lower betas, with the final zero coordinate retained. -/
def powerLower (m : ℕ) (i : Fin (m + 1)) : ℤ :=
  if i.val = m then 0
  else (B.b : ℤ) - B.c + ((m : ℤ) - i.val - 1) * B.boundary.q

/-- The candidate beta lists have exactly the required row differences. -/
theorem power_coordinates_rows (m : ℕ) (hm : 0 < m) (i : Fin (m + 1)) :
    B.powerUpper m i - B.powerLower m i = (B.innerPower m hm).r i := by
  have hi := i.isLt
  have hq := B.boundary_q_eq
  change B.powerUpper m i - B.powerLower m i = B.powerRows m i
  unfold powerUpper powerLower powerRows
  split_ifs <;> push_cast <;> nlinarith

/-- Every gap computed from these full lists is the constant inner gap. -/
theorem power_coordinates_gaps (m : ℕ) (hm : 0 < m) (j : Fin m) :
    B.powerUpper m j.succ - B.powerLower m j.castSucc = (B.innerPower m hm).g j := by
  have hj := j.isLt
  change B.powerUpper m j.succ - B.powerLower m j.castSucc = B.c
  rw [powerUpper, ite_eq_right (by simp only [Fin.val_succ]; omega),
    powerLower, ite_eq_right (by simp only [Fin.val_castSucc]; omega)]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact equality of the constructed and recursively normalized beta words. -/
theorem innerPower_beta (m : ℕ) (hm : 0 < m) :
    (B.innerPower m hm).xi = B.powerUpper m ∧ (B.innerPower m hm).zeta = B.powerLower m := by
  have hz : B.powerLower m (Fin.last m) = 0 := by simp [powerLower]
  have he := (B.innerPower m hm).eq_beta_of_equations hz
    (B.power_coordinates_rows m hm) (B.power_coordinates_gaps m hm)
  exact ⟨he.1.symm, he.2.symm⟩

/-- The normalized full span of a power is its exact copy multiplicity times `q`. -/
theorem innerPower_span (m : ℕ) (hm : 0 < m) :
    (B.innerPower m hm).xi 0 = (m : ℤ) * B.boundary.q := by
  rw [congrFun (B.innerPower_beta m hm).1 0]
  simp [powerUpper]

/-- Full upper beta support, before any cancellation of common entries. -/
theorem innerPower_rowSet (m : ℕ) (hm : 0 < m) :
    (B.innerPower m hm).toBetaDiagram.rowSet =
      {(m : ℤ) * B.boundary.q} ∪
        (Finset.range m).image (fun j : ℕ => (B.b : ℤ) + j * B.boundary.q) := by
  classical
  ext x
  simp only [BetaDiagram.rowSet, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    have hx : B.powerUpper m i = x := by
      simpa only [Gluing.Profile.toBetaDiagram, (B.innerPower_beta m hm).1] using hi
    by_cases hz : i.val = 0
    · left
      simpa only [powerUpper, ite_eq_left hz] using hx.symm
    · right
      refine ⟨m - i.val, by have := i.isLt; omega, ?_⟩
      rw [powerUpper, ite_eq_right hz] at hx
      have hi := i.isLt
      have hs : ((m - i.val : ℕ) : ℤ) = (m : ℤ) - i.val := by omega
      rw [hs]
      exact hx
  · rintro (hx | ⟨j, hj, hx⟩)
    · refine ⟨0, ?_⟩
      change (B.innerPower m hm).xi 0 = x
      rw [B.innerPower_span, hx]
    · let i : Fin (m + 1) := ⟨m - j, by omega⟩
      refine ⟨i, ?_⟩
      change (B.innerPower m hm).xi i = x
      rw [congrFun (B.innerPower_beta m hm).1 i, powerUpper,
        ite_eq_right (by dsimp [i]; omega)]
      have hi : ((m - j : ℕ) : ℤ) = (m : ℤ) - j := by omega
      dsimp [i]
      rw [hi]
      nlinarith [hx]

/-- Full lower beta support, including the terminal zero and all uncanceled common coordinates. -/
theorem innerPower_colSet (m : ℕ) (hm : 0 < m) :
    (B.innerPower m hm).toBetaDiagram.colSet =
      {0} ∪ (Finset.range m).image
        (fun j : ℕ => (B.b : ℤ) - B.c + j * B.boundary.q) := by
  classical
  ext x
  simp only [BetaDiagram.colSet, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    have hx : B.powerLower m i = x := by
      simpa only [Gluing.Profile.toBetaDiagram, (B.innerPower_beta m hm).2] using hi
    by_cases hz : i.val = m
    · left
      simpa only [powerLower, ite_eq_left hz] using hx.symm
    · right
      have hi := i.isLt
      refine ⟨m - i.val - 1, by omega, ?_⟩
      rw [powerLower, ite_eq_right hz] at hx
      have hs : ((m - i.val - 1 : ℕ) : ℤ) = (m : ℤ) - i.val - 1 := by omega
      rw [hs]
      exact hx
  · rintro (hx | ⟨j, hj, hx⟩)
    · refine ⟨Fin.last m, ?_⟩
      change (B.innerPower m hm).zeta (Fin.last m) = x
      rw [Gluing.Profile.zeta_last, hx]
    · let i : Fin (m + 1) := ⟨m - j - 1, by omega⟩
      refine ⟨i, ?_⟩
      change (B.innerPower m hm).zeta i = x
      rw [congrFun (B.innerPower_beta m hm).2 i, powerLower,
        ite_eq_right (by dsimp [i]; omega)]
      have hi : ((m - j - 1 : ℕ) : ℤ) = (m : ℤ) - j - 1 := by omega
      dsimp [i]
      rw [hi]
      nlinarith [hx]

end SkewClassInflation.ThinParameters
