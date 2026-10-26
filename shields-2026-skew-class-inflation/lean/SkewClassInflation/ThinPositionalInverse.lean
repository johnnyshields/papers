/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinRemainderCore
import SkewClassInflation.ThinPrepend
import SkewClassInflation.ThinMateContraction
import SkewClassInflation.ZeroPeeling

/-!
# Positional reconstruction of every oriented thin mate

The ordered inverse for `thm:two-row-thin-class` in
`shields-2026-skew-class-inflation.tex`.  Actual constant and highest
unit coefficients produce the inputs to the recursive inverse.  Every
step peels the first zero-free power, then reconstructs the remaining
positive total core.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

variable (B : ThinParameters)

/-- The produced power factors and total core determine the entire oriented profile.

**Differs from the paper's route.** Positional peeling uses the complete rigidity
of the total power at each step instead of testing mixed block orientations. -/
theorem oriented_profile_reconstruction {k M : ℕ} (hM : 0 < M) (Q : Profile k)
    (hQ : Staircase.Thick Q) (hfirst : Q.r 0 = B.a)
    (fs : List CompleteRing) (hfs : ∀ p ∈ fs, B.IsPowerFunction p)
    (hconst : (unitSchur Q).coeff 0 = fs.prod)
    (hcore : (contractAllZeros Q).2.toBetaDiagram.schur =
      (B.innerPower M hM).toBetaDiagram.schur) :
    ∃ β : Composition M, (⟨k, Q⟩ : ConnectedProfile) = B.diagram β hM := by
  classical
  induction k using Nat.strong_induction_on generalizing M fs with
  | h k ih =>
    by_cases hz : ∃ j, Q.g j = 0
    · cases k with
      | zero => obtain ⟨j, _⟩ := hz; exact Fin.elim0 j
      | succ n =>
        obtain ⟨c, hc, hbefore⟩ := exists_first_zero Q hz
        let L := leftOfSeam Q c
        let R := rightOfSeam Q c
        have hL : Staircase.Thick L := slice_thick hQ 0 c.val (by omega)
        have hR : Staircase.Thick R :=
          slice_thick hQ (c.val + 1) (n - c.val) (by have := c.isLt; omega)
        have hzL := first_zero_prefix_zeroFree Q hQ c hbefore
        have hLc : (unitSchur L).coeff 0 = L.toBetaDiagram.schur := by
          rw [unitSchur_eq_C_of_zeroFree L hzL, Polynomial.coeff_C_zero]
        have hsplit : L.toBetaDiagram.schur * (unitSchur R).coeff 0 = fs.prod := by
          rw [← hconst, unit_zero_cut_constant Q c hc, hLc]
        obtain ⟨m, hm, hLm, hmem⟩ := B.connected_factor_of_power_product
          L.toBetaDiagram L.toBetaDiagram_connected fs hfs ⟨_, hsplit.symm⟩
        have hnm := Nat.succ.inj
          (L.toBetaDiagram.row_count_of_schur_eq (B.innerPower m hm).toBetaDiagram hLm)
        change c.val = m at hnm
        subst m
        have hLf : L.r 0 = B.a := by
          change Q.r (sliceEmbedding 0 c.val (by omega) 0) = B.a
          have hidx : sliceEmbedding 0 c.val (by omega) 0 = (0 : Fin (n + 2)) := by
            apply Fin.ext
            rfl
          rw [hidx, hfirst]
        have hshape : L = B.innerPower c.val hm :=
          B.innerPower_first_mate_eq c.val hm L hLm hLf
        have hreassemble := zero_cut_reassembly Q c hc
        change (⟨n + 1, Q⟩ : ConnectedProfile) = ConnectedProfile.zeroJoin ⟨c.val, L⟩
          ⟨n - c.val, R⟩ at hreassemble
        have hmerged : (Profile.merge (B.innerPower c.val hm) (contractAllZeros R).2 0
            ((B.innerPower c.val hm).r_pos _)
            ((contractAllZeros R).2.r_pos _)).toBetaDiagram.schur =
            (B.innerPower M hM).toBetaDiagram.schur := by
          have hzero := congrArg
            (fun D : ConnectedProfile => (contractAllZeros D.2).2.toBetaDiagram.schur) hreassemble
          change (contractAllZeros Q).2.toBetaDiagram.schur =
            (contractAllZeros (Profile.zeroJoin L R)).2.toBetaDiagram.schur at hzero
          rw [zero_prefix_contraction L R hL hR hzL, hshape] at hzero
          exact hzero.symm.trans hcore
        obtain ⟨ht, hMt, htail⟩ := B.remainder_of_merged_function hm hM
          (contractAllZeros R).2 hmerged
        let rest := fs.erase L.toBetaDiagram.schur
        have hrest : ∀ p ∈ rest, B.IsPowerFunction p :=
          fun p hp => hfs p (List.mem_of_mem_erase hp)
        have hrestconst : (unitSchur R).coeff 0 = rest.prod := by
          apply mul_left_cancel₀ L.toBetaDiagram.schur_ne_zero
          exact hsplit.trans (List.prod_erase hmem).symm
        have hRf : R.r 0 = B.a := by
          have hretain := contractAllZeros_first_row R hR
            (B.first_gap_positive_of_product R rest hrest hrestconst)
          rw [htail] at hretain
          exact hretain.symm
        have htailcore : (contractAllZeros R).2.toBetaDiagram.schur =
            (B.innerPower (contractAllZeros R).1 ht).toBetaDiagram.schur := by rw [htail]
        obtain ⟨β, hβ⟩ := ih (n - c.val) (by omega) ht R hR hRf rest hrest
          hrestconst htailcore
        subst M
        refine ⟨(Composition.single c.val hm).append β, ?_⟩
        rw [B.diagram_prepend hm β ht, ← hβ, ← hshape]
        exact hreassemble
    · have hpos : ∀ j, 0 < Q.g j := by
        intro j
        have hne : Q.g j ≠ 0 := fun h => hz ⟨j, h⟩
        omega
      rw [contractAllZeros_self Q hpos] at hcore
      have hrows := Nat.succ.inj
        (Q.toBetaDiagram.row_count_of_schur_eq (B.innerPower M hM).toBetaDiagram hcore)
      change k = M at hrows
      subst M
      have hshape := B.innerPower_first_mate_eq k hM Q hcore hfirst
      exact ⟨Composition.single k hM, by rw [B.diagram_single, hshape]⟩

end SkewClassInflation.ThinParameters
