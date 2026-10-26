/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DistinguishedPeeling
import SkewClassInflation.SaturationPowerFactors
import SkewClassInflation.SaturationMergedInverse
import SkewClassInflation.SaturationPrepend

/-!
# Positional reconstruction from the actual oriented total core

The oriented inverse in `lem:total-contraction-inverse` of
`shields-2026-skew-class-inflation.tex`.  The factor product and literal
total core are intermediate inputs, not extra standing hypotheses of a
full-class theorem.  At each first distinguished seam, the component
function supplies its row count and endpoints; the fixed literal core
then recovers both actual pieces, including a nonrigid one-copy piece.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase SkewJacobiNegative.GeneralHessenberg

variable (A : SaturationInner)

/-- Actual power factors and a fixed literal total core reconstruct the whole ordered source.

**Differs from the paper's route.** Reconstructs the first actual component
and the remaining literal core recursively; the paper splits all recovered
positions at once. -/
theorem oriented_profile_reconstruction {k M : ℕ} (hM : 0 < M) (Q : Profile k)
    (hQ : Thick Q) (hrQ : ∀ i, A.d < Q.r i)
    (fs : List CompleteRing) (hfs : ∀ p ∈ fs, A.IsPowerFunction p)
    (hconst : eraseGenerator A.largeLabel Q.toBetaDiagram.schur = fs.prod)
    (hcore : (contractAllMinimum Q A.largeLabel : ConnectedProfile) =
      ⟨M * A.k, A.power M hM⟩) :
    ∃ β : Composition M, (⟨k, Q⟩ : ConnectedProfile) = A.diagram β hM := by
  classical
  induction k using Nat.strong_induction_on generalizing M fs with
  | h k ih =>
    by_cases hv : ∃ j, Q.g j = A.d
    · cases k with
      | zero => obtain ⟨j, _⟩ := hv; exact Fin.elim0 j
      | succ n =>
        obtain ⟨c, hc, hbefore⟩ := exists_first_distinguished Q A.largeLabel hv
        let L := leftOfSeam Q c
        let R := rightOfSeam Q c
        have hL : Thick L := slice_thick hQ 0 c.val (by omega)
        have hR : Thick R :=
          slice_thick hQ (c.val + 1) (n - c.val) (by have := c.isLt; omega)
        have hrL : ∀ i, A.d < L.r i := fun i => hrQ _
        have hrR : ∀ i, A.d < R.r i := fun i => hrQ _
        have hgL : ∀ j, L.g j ≠ A.d := by
          intro j
          change Q.g ⟨0 + j.val, by have := j.isLt; omega⟩ ≠ A.d
          apply hbefore
          change 0 + j.val < c.val
          simpa only [Nat.zero_add] using j.isLt
        obtain ⟨hcutL, hcutR, hreassemble⟩ := distinguished_cut_reassembly Q c A.d hc
        have hJ : Thick (Profile.join L R A.d (hrL _) (hrR _)) := by
          have hh := congrArg (fun D : ConnectedProfile => Thick D.2) hreassemble
          exact Eq.mp hh hQ
        have hschur := congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.schur) hreassemble
        change Q.toBetaDiagram.schur =
          (Profile.join L R A.d (hrL _) (hrR _)).toBetaDiagram.schur at hschur
        have hsplit : L.toBetaDiagram.schur * eraseGenerator A.largeLabel R.toBetaDiagram.schur =
            fs.prod := by
          rw [← distinguished_join_constant L R A.largeLabel hL hrL hrR hgL hJ]
          change eraseGenerator A.largeLabel
            (Profile.join L R A.d (hrL _) (hrR _)).toBetaDiagram.schur = fs.prod
          rw [← hschur]
          exact hconst
        obtain ⟨j, hj, hLj, hmem⟩ := A.connected_factor_of_power_product
          L.toBetaDiagram L.toBetaDiagram_connected fs hfs ⟨_, hsplit.symm⟩
        have hzero := congrArg (fun D : ConnectedProfile =>
          (contractAllMinimum D.2 A.largeLabel : ConnectedProfile)) hreassemble
        have hmerged :
            (⟨c.val + (contractAllMinimum R A.largeLabel).1,
              Profile.merge L (contractAllMinimum R A.largeLabel).2 A.d (hrL _)
                (contractAllMinimum_rows_above R A.largeLabel hrR _)⟩ : ConnectedProfile) =
              ⟨M * A.k, A.power M hM⟩ :=
          (distinguished_prefix_contraction L R A.largeLabel hL hR hrL hrR hgL hJ).symm.trans
            (hzero.symm.trans hcore)
        obtain ⟨t, ht, hMt, hleft, htail⟩ := A.merged_power_inverse_of_function hj hM L
          (contractAllMinimum R A.largeLabel).2 hrL
          (contractAllMinimum_rows_above R A.largeLabel hrR) hLj hmerged
        let rest := fs.erase L.toBetaDiagram.schur
        have hrest : ∀ p ∈ rest, A.IsPowerFunction p :=
          fun p hp => hfs p (List.mem_of_mem_erase hp)
        have hrestconst : eraseGenerator A.largeLabel R.toBetaDiagram.schur = rest.prod := by
          apply mul_left_cancel₀ L.toBetaDiagram.schur_ne_zero
          exact hsplit.trans (List.prod_erase hmem).symm
        obtain ⟨β, hβ⟩ := ih (n - c.val) (by omega) ht R hR hrR rest hrest hrestconst htail
        subst M
        refine ⟨(Composition.single j hj).append β, ?_⟩
        rw [A.diagram_prepend hj β ht]
        have hleftJoin := Profile.join_left_congr (⟨c.val, L⟩ : ConnectedProfile)
          (⟨j * A.k, A.power j hj⟩ : ConnectedProfile) R A.d (hrL _)
          (A.power_rows_above_seam j hj _) (hrR _) hleft
        have hrightJoin := Profile.join_right_congr (A.power j hj)
          (⟨n - c.val, R⟩ : ConnectedProfile) (A.diagram β ht) A.d
          (A.power_rows_above_seam j hj _) (hrR _) (A.diagram_rows_above_seam β ht _) hβ
        exact hreassemble.trans (hleftJoin.trans hrightJoin)
    · have hg : ∀ j, Q.g j ≠ A.d := by
        intro j hj
        exact hv ⟨j, hj⟩
      rw [contractAllMinimum_self Q A.largeLabel hg] at hcore
      exact ⟨Composition.single M hM, by rw [A.diagram_single]; exact hcore⟩

end SkewClassInflation.SaturationInner
