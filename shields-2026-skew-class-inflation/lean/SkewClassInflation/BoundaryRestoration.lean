/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionSuffixes
import SkewJacobiNegative.RestorationComponents

/-!
# Restoring the actual boundary common betas

The common-position construction for `eq:boundary-beta-lists` in
`shields-2026-skew-class-inflation.tex`.  Proper suffix positions are
proved available in the literal boundary core before restoration.
Sorry-free.
-/

namespace SkewClassInflation.BoundaryParameters

open SkewJacobiNegative

variable (B : BoundaryParameters)

/-- The positive residue inequalities imply a positive modulus. -/
theorem q_pos : 0 < B.q := by
  have := B.p_pos
  have := B.p_lt_a
  have := B.ap_lt_q
  omega

/-- A grid point cannot acquire a strictly smaller nonzero residue. -/
theorem grid_eq_iff (x y : ℤ) (w : ℕ) (hw : w < B.q) :
    (B.q : ℤ) * x + w = (B.q : ℤ) * y ↔ x = y ∧ w = 0 := by
  constructor
  · intro h
    have he := congrArg (fun z : ℤ => z % (B.q : ℤ)) h
    have hw0 : (0 : ℤ) ≤ w := by omega
    have hwq : (w : ℤ) < B.q := by omega
    have hwz : w = 0 := by
      have he' : (w : ℤ) = 0 := by
        simpa [Int.add_emod, Int.mul_emod, Int.emod_eq_of_lt hw0 hwq] using he
      omega
    refine ⟨?_, hwz⟩
    have hq : (B.q : ℤ) ≠ 0 := by have := B.q_pos; omega
    exact mul_left_cancel₀ hq (by simpa [hwz] using h)
  · rintro ⟨rfl, rfl⟩
    simp

/-- Literal common betas at the first inflation boundary. -/
def commonBetas (T : Finset ℕ) : Finset ℤ := T.image (fun k : ℕ => (B.q : ℤ) * k)

/-- A restored suffix grid point is absent from the retained upper beta list. -/
theorem suffix_grid_not_upper (M : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.Ioo 0 M)
    (k : ℕ) (hk : k ∈ T) (i : Fin (M + 1)) : B.upper M T i ≠ (B.q : ℤ) * k := by
  have hk' := Finset.mem_Ioo.mp (hT hk)
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  intro he
  unfold upper at he
  split_ifs at he with hi0 hi1
  · have hz := (B.grid_eq_iff (M : ℤ) k B.p (by omega)).mp he
    omega
  · have hm : (M : ℤ) = k := mul_left_cancel₀
      (show (B.q : ℤ) ≠ 0 by have := B.q_pos; omega) he
    omega
  · have hi := i.isLt
    have hidx : ((M + 1 - i.val : ℕ) : ℤ) = (M : ℤ) + 1 - i.val := by omega
    have hbi := B.bit_le T (M + 1 - i.val)
    have hz := (B.grid_eq_iff (M + 1 - i.val : ℕ) k
      (B.bit T (M + 1 - i.val)) (by omega)).mp (by simpa only [hidx] using he)
    have heq : M + 1 - i.val = k := by exact_mod_cast hz.1
    have hb := hz.2
    rw [heq, bit, ite_eq_left hk] at hb
    omega

/-- No positive grid point is a retained column beta. -/
theorem suffix_grid_not_lower (M : ℕ) (k : ℕ) (hk : 0 < k) (i : Fin (M + 1)) :
    B.lower M i ≠ (B.q : ℤ) * k := by
  intro he
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  unfold lower at he
  split_ifs at he with hi
  · have hq := B.q_pos
    nlinarith
  · have hz := (B.grid_eq_iff k ((M : ℤ) - i.val) B.a (by omega)).mp
      (by linarith [he])
    omega

/-- Every common beta lies strictly inside the span and outside both residual lists. -/
theorem commonBetas_available (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) :
    B.commonBetas T ⊆ (B.core M hM T).availablePositions := by
  classical
  intro z hz
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
  have hk' := Finset.mem_Ioo.mp (hT hk)
  rw [(B.core M hM T).mem_availablePositions_sets_iff, B.core_last_col]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := B.q_pos
    have hkp : 0 < k := hk'.1
    positivity
  · change (B.q : ℤ) * k < B.upper M T 0
    simp only [upper, Fin.val_zero, ite_true]
    have := B.p_pos
    have hmul := Nat.mul_le_mul_left B.q (show k + 1 ≤ M by omega)
    nlinarith
  · intro hr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
    exact B.suffix_grid_not_upper M T hT k hk i hi
  · intro hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    exact B.suffix_grid_not_lower M k hk'.1 i hi

/-- The connected literal parent obtained by restoring exactly the common suffix betas. -/
noncomputable def restoredParent (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) : BetaDiagram (M + 1 + (B.commonBetas T).card) :=
  (B.core M hM T).restore (B.core_connected M hM T) (B.core_zeroFree M hM T)
    (B.commonBetas T) (B.commonBetas_available M hM T hT)

/-- Restoring common betas preserves genuine connectedness. -/
theorem restoredParent_connected (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) : (B.restoredParent M hM T hT).Connected :=
  (B.core M hM T).restore_connected _ _ _ _

/-- The smallest ordinary component of the restored parent really is nonzero. -/
theorem restoredParent_lowest_nonzero (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) :
    MvPolynomial.homogeneousComponent (M + 1) (B.restoredParent M hM T hT).schur ≠ 0 := by
  rw [← ordinaryComponent_eq_homogeneousComponent]
  apply (B.core M hM T).restoration_lowest_nonzero (B.core_zeroFree M hM T)
    (B.commonBetas T) ((B.core M hM T).available_disjoint_rows _
      (B.commonBetas_available M hM T hT))
    ((B.core M hM T).available_disjoint_cols _ (B.commonBetas_available M hM T hT))
  · exact (B.core M hM T).restore_rowSet _ _ _ _
  · exact (B.core M hM T).restore_colSet _ _ _ _

end SkewClassInflation.BoundaryParameters
