/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalDerivative
import SkewCornerDescent.Matrix.OriginalHessenbergTops

/-!
# Literal top indices are invariant under actual response equality

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
Partial differentiation in the larger protected generator distinguishes two monic
responses with strictly lower corrections. Equal actual retained responses therefore
have equal literal endpoint tops. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem residue_monic_not_lt (J K : ℕ+) (hNJ : c.top < J) (hNK : c.top < K)
    (A B : OtherField c.top) (hA : A ∈ residueLowerField c.top J)
    (hB : B ∈ residueLowerField c.top K)
    (heq : residueGenerator c.top ⟨J, ne_of_gt hNJ⟩ + A =
      residueGenerator c.top ⟨K, ne_of_gt hNK⟩ + B) (hJK : J < K) : False := by
  have hg := c.residue_other_mem_lower K J (ne_of_gt hNJ) hJK
  rw [c.residueMap_other J (ne_of_gt hNJ)] at hg
  change residueGenerator c.top ⟨J, ne_of_gt hNJ⟩ ∈ residueLowerField c.top K at hg
  have hAlower : A ∈ residueLowerField c.top K := residueLowerField_mono hJK.le hA
  have hd := congrArg (residueGeneratorDeriv c.top ⟨K, ne_of_gt hNK⟩) heq
  rw [map_add, map_add,
    residueGeneratorDeriv_lower c.top ⟨K, ne_of_gt hNK⟩ hg,
    residueGeneratorDeriv_lower c.top ⟨K, ne_of_gt hNK⟩ hAlower,
    residueGeneratorDeriv_lower c.top ⟨K, ne_of_gt hNK⟩ hB,
    residueGeneratorDeriv_generator, ite_eq_left rfl] at hd
  exact zero_ne_one (by simpa only [zero_add, add_zero] using hd)

/-- Equal monic actual residue coordinates cannot have different protected tops.
The corrections may be arbitrary rational functions of strictly lower generators. -/
theorem residue_monic_top_eq (J K : ℕ+) (hNJ : c.top < J) (hNK : c.top < K)
    (A B : OtherField c.top) (hA : A ∈ residueLowerField c.top J)
    (hB : B ∈ residueLowerField c.top K)
    (heq : residueGenerator c.top ⟨J, ne_of_gt hNJ⟩ + A =
      residueGenerator c.top ⟨K, ne_of_gt hNK⟩ + B) : J = K := by
  rcases lt_trichotomy J K with h | h | h
  · exact (c.residue_monic_not_lt J K hNJ hNK A B hA hB heq h).elim
  · exact h
  · exact (c.residue_monic_not_lt K J hNK hNJ B A hB hA heq.symm h).elim

/-- Literal endpoint tops agree whenever two actual diagonal response residues
agree, even across different original profiles and selected inventories. -/
theorem originalHessenberg_top_eq_of_residue_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : 0 < originalSelectedCount (hD := hD) P)
    (hQ : 0 < originalSelectedCount (hD := hD) Q)
    (i : Fin (originalSelectedCount (hD := hD) P + 1))
    (k : Fin (originalSelectedCount (hD := hD) Q + 1))
    (heq : c.regularResidue (c.originalHessenbergResponse P i i) =
      c.regularResidue (c.originalHessenbergResponse Q k k)) :
    c.originalHessenbergTop P hP i i le_rfl = c.originalHessenbergTop Q hQ k k le_rfl := by
  let J := c.originalHessenbergTop P hP i i le_rfl
  let K := c.originalHessenbergTop Q hQ k k le_rfl
  have hNJ : c.top < J := by
    have hd := c.originalHessenbergDistance_gt_top P hP i i le_rfl
    have hc := c.originalHessenbergTop_coe P hP i i le_rfl
    exact_mod_cast (show (c.top : ℤ) < (J : ℤ) by dsimp only [J]; omega)
  have hNK : c.top < K := by
    have hd := c.originalHessenbergDistance_gt_top Q hQ k k le_rfl
    have hc := c.originalHessenbergTop_coe Q hQ k k le_rfl
    exact_mod_cast (show (c.top : ℤ) < (K : ℤ) by dsimp only [K]; omega)
  obtain ⟨A, hA, hPA⟩ := c.originalHessenbergResponse_residue_triangular P hP i i le_rfl
  obtain ⟨B, hB, hQB⟩ := c.originalHessenbergResponse_residue_triangular Q hQ k k le_rfl
  rw [hPA, hQB, c.residueMap_other J (ne_of_gt hNJ),
    c.residueMap_other K (ne_of_gt hNK)] at heq
  exact c.residue_monic_top_eq J K hNJ hNK A B hA hB heq

end SkewCornerDescent.Matrix.SelectedCoordinate
