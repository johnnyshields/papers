/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PrivateResidueColumn

/-!
# The literal boundary core

Formalizes `eq:boundary-core-lists`, `eq:boundary-core-ordered`, and
`eq:boundary-residue-separation` in `shields-2026-skew-class-inflation.tex`.
Every subset of the proper suffix positions gives a connected zero-free
Hessenberg beta diagram.  No determinant equality or core property is
assumed.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The four strict residue inequalities satisfied by the thin family's boundary parameters. -/
structure BoundaryParameters where
  /-- The shorter endpoint row length. -/
  a : ℕ
  /-- The positive residue offset in the boundary beta lists. -/
  p : ℕ
  /-- The period of the boundary beta grids. -/
  q : ℕ
  p_pos : 0 < p
  p_lt_a : p < a
  ap_lt_q : a + p < q

namespace BoundaryParameters

/-- The manuscript's actual parameters produce the residue inequalities, not an extra premise. -/
def ofThin (a b c : ℕ) (hc : 1 ≤ c) (hca : c < a) (hab : a < b) : BoundaryParameters where
  a := a
  p := a - c
  q := a + b - c
  p_pos := by omega
  p_lt_a := by omega
  ap_lt_q := by omega

variable (B : BoundaryParameters)

/-- The suffix bit contributes either zero or the positive residue. -/
def bit (T : Finset ℕ) (k : ℕ) : ℕ := if k ∈ T then B.p else 0

theorem bit_le (T : Finset ℕ) (k : ℕ) : B.bit T k ≤ B.p := by
  unfold bit
  split_ifs <;> omega

/-- Ordered upper beta list, with its two leading entries retained also at total size one. -/
def upper (M : ℕ) (T : Finset ℕ) (i : Fin (M + 1)) : ℤ :=
  if i.val = 0 then B.q * M + B.p
  else if i.val = 1 then B.q * M
  else B.q * (M + 1 - i.val) + B.bit T (M + 1 - i.val)

/-- Fixed ordered lower beta list; it is independent of the suffix subset. -/
def lower (M : ℕ) (i : Fin (M + 1)) : ℤ :=
  if i.val = M then 0 else B.q * (M - i.val) - B.a

theorem upper_strictAnti (M : ℕ) (T : Finset ℕ) : StrictAnti (B.upper M T) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hidx : i.val < j.val := hij
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  have hbi := B.bit_le T (M + 1 - i.val)
  have hbj := B.bit_le T (M + 1 - j.val)
  have hstep : (B.q : ℤ) ≤ (B.q : ℤ) * ((j.val : ℤ) - i.val) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ B.q by omega)
      (show (0 : ℤ) ≤ (j.val : ℤ) - i.val - 1 by omega)]
  have htwo : 2 ≤ j.val → 2 * (B.q : ℤ) ≤ (B.q : ℤ) * j.val := by
    intro hj2
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ B.q by omega)
      (show (0 : ℤ) ≤ (j.val : ℤ) - 2 by omega)]
  unfold upper
  split_ifs
  all_goals first | nlinarith | (have ht := htwo (by omega); nlinarith)

theorem lower_strictAnti (M : ℕ) : StrictAnti (B.lower M) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hidx : i.val < j.val := hij
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  unfold lower
  split_ifs <;> push_cast <;> nlinarith

theorem lower_lt_upper (M : ℕ) (hM : 0 < M) (T : Finset ℕ) (i : Fin (M + 1)) :
    B.lower M i < B.upper M T i := by
  have hi := i.isLt
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  have hbi := B.bit_le T (M + 1 - i.val)
  unfold upper lower
  split_ifs <;> nlinarith

/-- The actual residual diagram, built from strict lists and positive rows. -/
def core (M : ℕ) (hM : 0 < M) (T : Finset ℕ) : BetaDiagram (M + 1) where
  row := B.upper M T
  col := B.lower M
  row_strictAnti := B.upper_strictAnti M T
  col_strictAnti := B.lower_strictAnti M
  row_nonempty := B.lower_lt_upper M hM T

theorem core_connected (M : ℕ) (hM : 0 < M) (T : Finset ℕ) :
    (B.core M hM T).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  have hi' := i.isLt
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  have hb := B.bit_le T (M - i.val)
  change B.lower M i ≤ B.upper M T ⟨i.val + 1, hi⟩
  simp only [lower, upper]
  split_ifs <;> push_cast <;> nlinarith

theorem core_last_col (M : ℕ) (hM : 0 < M) (T : Finset ℕ) :
    (B.core M hM T).col (Fin.last M) = 0 := by simp [core, lower]

end BoundaryParameters
end SkewClassInflation
