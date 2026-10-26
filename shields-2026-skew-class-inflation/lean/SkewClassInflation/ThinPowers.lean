/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.HessenbergMembership
import SkewClassInflation.BoundaryInverse
import SkewClassInflation.BoundaryCoreGeometry

/-!
# The actual thin overlapped powers

Formalizes the parameters and blocks in `eq:thin-domain` and the geometric
input to `lem:two-row-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Every block has its full natural
connected profile, with one private shortest row.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Precisely the integer parameters assumed by the thin-family theorem. -/
structure ThinParameters where
  /-- The shorter endpoint row length. -/
  a : ℕ
  /-- The longer endpoint row length. -/
  b : ℕ
  /-- The positive distinguished overlap. -/
  c : ℕ
  c_pos : 0 < c
  c_lt_a : c < a
  a_lt_b : a < b

namespace ThinParameters

variable (B : ThinParameters)

/-- The exact boundary residue parameters, derived from the thin standing assumptions. -/
def boundary : BoundaryParameters :=
  BoundaryParameters.ofThin B.a B.b B.c (by have := B.c_pos; omega) B.c_lt_a B.a_lt_b

/-- Endpoint rows remain separate while the intermediate rows are genuine zero-seam mergers. -/
def powerRows (m : ℕ) (i : Fin (m + 1)) : ℕ :=
  if i.val = 0 then B.a else if i.val = m then B.b else B.a + B.b

/-- The literal profile `E_m`, including the one-copy two-row case. -/
def innerPower (m : ℕ) (_hm : 0 < m) : Profile m where
  r := B.powerRows m
  g _ := B.c
  r_pos i := by
    have := B.c_pos
    have := B.c_lt_a
    have := B.a_lt_b
    unfold powerRows
    split_ifs <;> omega
  g_lt_castSucc j := by
    have := B.c_lt_a
    have := B.a_lt_b
    unfold powerRows
    split_ifs <;> omega
  g_lt_succ j := by
    have := B.c_lt_a
    have := B.a_lt_b
    unfold powerRows
    split_ifs <;> omega

/-- The profile is genuinely Hessenberg at every positive copy multiplicity. -/
theorem innerPower_thick (m : ℕ) (hm : 0 < m) : Staircase.Thick (B.innerPower m hm) := by
  intro j k hjk
  have hi := congrArg Fin.val hjk
  have hj := j.isLt
  have hk := k.isLt
  have := B.c_lt_a
  have := B.a_lt_b
  change B.c + B.c < B.powerRows m j.succ
  unfold powerRows
  split_ifs <;> simp only [Fin.val_succ, Fin.val_castSucc] at * <;> omega

/-- The shortest row occurs at exactly one position, even when the power has two rows. -/
theorem innerPower_shortest (m : ℕ) (hm : 0 < m) (i : Fin (m + 1)) :
    B.a ≤ (B.innerPower m hm).r i ∧
      ((B.innerPower m hm).r i = B.a ↔ i = 0) := by
  have := B.c_pos
  have := B.c_lt_a
  have := B.a_lt_b
  change B.a ≤ B.powerRows m i ∧ (B.powerRows m i = B.a ↔ i = 0)
  by_cases hi : i = 0
  · subst i
    simp [powerRows]
  · have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [powerRows, ite_eq_right hi0]
    by_cases him : i.val = m
    · rw [ite_eq_left him]
      exact ⟨by omega, iff_of_false (by omega) hi⟩
    · rw [ite_eq_right him]
      exact ⟨by omega, iff_of_false (by omega) hi⟩

/-- All adjacent gaps are the actual constant inner gap. -/
theorem innerPower_gap (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (B.innerPower m hm).g j = B.c := rfl

/-- The first-row deletion in the private shortest-row coefficient is connected. -/
theorem innerPower_tail_connected (m : ℕ) (hm : 0 < m) :
    (firstRowTail (B.innerPower m hm).toBetaDiagram).Connected := by
  refine ⟨hm, ?_⟩
  intro i hi
  have h := (B.innerPower m hm).toBetaDiagram_connected.2 i.succ
    (by simp only [Fin.val_succ]; omega)
  exact h

end ThinParameters
end SkewClassInflation
