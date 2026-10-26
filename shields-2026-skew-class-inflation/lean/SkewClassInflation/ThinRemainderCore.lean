/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMergerRecovery
import SkewClassInflation.ThinPowerRigidity
import SkewClassInflation.ThinPowerBetas

/-!
# A fixed first block recovers the remaining total core

The positional peeling input for `thm:two-row-thin-class` in
`shields-2026-skew-class-inflation.tex`.  The merged-function hypothesis
first produces a literal thin power by the complete rigidity theorem;
its span then produces a positive remaining copy multiplicity, and the
literal positional inverse reconstructs the remaining core.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The actual merged function produces the remaining core and its positive order. -/
theorem remainder_of_merged_function {m k M : ℕ} (hm : 0 < m) (hM : 0 < M) (C : Profile k)
    (he : (Profile.merge (B.innerPower m hm) C 0 ((B.innerPower m hm).r_pos _)
        (C.r_pos _)).toBetaDiagram.schur = (B.innerPower M hM).toBetaDiagram.schur) :
    ∃ hk : 0 < k, M = m + k ∧ C = B.innerPower k hk := by
  let P := Profile.merge (B.innerPower m hm) C 0 ((B.innerPower m hm).r_pos _) (C.r_pos _)
  have hn := Nat.succ.inj
    (P.toBetaDiagram.row_count_of_schur_eq (B.innerPower M hM).toBetaDiagram he)
  change m + k = M at hn
  subst M
  have hfirst : P.r 0 = B.a := by
    have h := Profile.merge_r_left (B.innerPower m hm) C 0
      ((B.innerPower m hm).r_pos _) (C.r_pos _) (⟨0, hm⟩ : Fin m)
    change P.r 0 = (B.innerPower m hm).r (⟨0, hm⟩ : Fin m).castSucc at h
    have hr : (B.innerPower m hm).r (⟨0, hm⟩ : Fin m).castSucc = B.a := by
      simp [innerPower, powerRows]
    exact h.trans hr
  have hrot : (B.innerPower (m + k) hM).rotate.r 0 = B.b := by
    change (B.innerPower (m + k) hM).r (0 : Fin (m + k + 1)).rev = B.b
    rw [Fin.rev_zero]
    have hne : m + k ≠ 0 := Nat.ne_of_gt hM
    simpa [innerPower, powerRows, Fin.val_last] using
      (ite_eq_right hne : (if m + k = 0 then B.a else B.b) = B.b)
  have hshape : P = B.innerPower (m + k) hM := by
    rcases B.innerPower_rigidity (m + k) hM P he with h | h
    · exact h
    · have hv := congrArg (fun R : Profile (m + k) => R.r 0) h
      rw [hfirst, hrot] at hv
      exact False.elim ((Nat.ne_of_lt B.a_lt_b) hv)
  have hs := Profile.merge_span (B.innerPower m hm) C 0
    ((B.innerPower m hm).r_pos _) (C.r_pos _)
  change P.xi 0 = (B.innerPower m hm).xi 0 + C.xi 0 - (0 : ℕ) at hs
  rw [hshape, B.innerPower_span, B.innerPower_span] at hs
  simp only [Nat.cast_add, Nat.cast_zero, sub_zero, add_mul] at hs
  have hspan : (k : ℤ) * B.boundary.q = C.xi 0 := by linarith
  have hk : 0 < k := by
    by_contra h
    have hz : (k : ℤ) = 0 := by omega
    have hp := C.xi_pos 0
    have hzero : (k : ℤ) * B.boundary.q = 0 := by rw [hz, zero_mul]
    omega
  exact ⟨hk, rfl, B.right_power_of_merge hm hk C hshape⟩

end SkewClassInflation.ThinParameters
