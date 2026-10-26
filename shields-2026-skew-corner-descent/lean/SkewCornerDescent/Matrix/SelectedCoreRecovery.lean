/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreProfiles
import SkewCornerDescent.Matrix.EndpointVisibleSupport
import Mathlib.Data.Finset.Sort

/-!
# Selected-core beta lists from the actual early endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Every proper selected-core profile position has positive
distance strictly below the selected span and a produced nonzero coefficient.
Thus jets below half an interval of span greater than twice that selected span
recover both complete selected-core beta lists, not merely their Schur function.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

private theorem image_fin_succ {n : ℕ} {α : Type*} [DecidableEq α] (f : Fin (n + 1) → α) :
    Finset.univ.image f = insert (f 0) (Finset.univ.image fun i : Fin n => f i.succ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.exists_fin_succ, eq_comm]

private theorem image_fin_castSucc {n : ℕ} {α : Type*} [DecidableEq α] (f : Fin (n + 1) → α) :
    Finset.univ.image f = insert (f (Fin.last n))
      (Finset.univ.image fun i : Fin n => f i.castSucc) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.exists_iff_castSucc, eq_comm]

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every original proper left-core distance is positive and strictly below the
selected span; no profile term is lost to a truncated natural subtraction. -/
theorem selected_core_left_distances {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) :
    0 < P.xi 0 - P.xi i.succ ∧ P.xi 0 - P.xi i.succ < (c.top : ℤ) := by
  have hlt := P.xi_strictAnti (Fin.succ_pos i)
  have hpos := P.xi_pos i.succ
  have htop := P.topVar_coe
  rw [← c.top_eq_profile P hP] at htop
  omega

/-- The proper right-core distances have the same strict range. -/
theorem selected_core_right_distances {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) :
    0 < P.zeta i.castSucc - P.zeta (Fin.last n) ∧
      P.zeta i.castSucc - P.zeta (Fin.last n) < (c.top : ℤ) := by
  have hlt := P.zeta_strictAnti (Fin.castSucc_lt_last i)
  have hle := P.zeta_strictAnti.antitone (Fin.zero_le i.castSucc)
  have hrow := P.xi_sub_zeta (0 : Fin (n + 1))
  have hpos := P.r_pos (0 : Fin (n + 1))
  have htop := P.topVar_coe
  rw [← c.top_eq_profile P hP] at htop
  rw [P.zeta_last] at hlt ⊢
  omega

/-- Left profile jets below half-span recover all proper selected-core rows. -/
theorem selected_core_early_rows {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hcoeff : ∀ z, 0 ≤ z → 2 * z < K →
      (c.selectedCoreLeftProfile P hP).coeff z = (c.selectedCoreLeftProfile Q hQ).coeff z) :
    Finset.univ.image (fun i : Fin n => P.xi i.succ) =
      Finset.univ.image (fun j : Fin m => Q.xi j.succ) := by
  classical
  let left := fun i : Fin n => P.xi 0 - P.xi i.succ
  let right := fun j : Fin m => Q.xi 0 - Q.xi j.succ
  have hleft : Function.Injective left := by
    intro i j he
    apply Fin.strictMono_succ.injective
    apply P.xi_strictAnti.injective
    dsimp only [left] at he
    omega
  have hright : Function.Injective right := by
    intro i j he
    apply Fin.strictMono_succ.injective
    apply Q.xi_strictAnti.injective
    dsimp only [right] at he
    omega
  have hpvis (i : Fin n) : 2 * left i < K := by
    have h := c.selected_core_left_distances P hP i
    dsimp only [left]
    omega
  have hqvis (j : Fin m) : 2 * right j < K := by
    have h := c.selected_core_left_distances Q hQ j
    dsimp only [right]
    omega
  have hs := endpointProfile_visible_support_eq left right hleft hright
    (fun i => c.selectedCoreIncoming P hP () i) (fun j => c.selectedCoreIncoming Q hQ () j)
    (c.selected_core_incoming_ne_zero P hP) (c.selected_core_incoming_ne_zero Q hQ)
    (fun i => (c.selected_core_left_distances P hP i).1)
    (fun j => (c.selected_core_left_distances Q hQ j).1) (fun z => 2 * z < K) hcoeff
  rw [Finset.filter_true_of_mem (fun i _ => hpvis i),
    Finset.filter_true_of_mem (fun j _ => hqvis j)] at hs
  have hpmap (i : Fin n) : (c.top : ℤ) - left i = P.xi i.succ := by
    have htop := P.topVar_coe
    rw [← c.top_eq_profile P hP] at htop
    dsimp only [left]
    omega
  have hqmap (j : Fin m) : (c.top : ℤ) - right j = Q.xi j.succ := by
    have htop := Q.topVar_coe
    rw [← c.top_eq_profile Q hQ] at htop
    dsimp only [right]
    omega
  have hrows := congrArg (Finset.image (fun z : ℤ => (c.top : ℤ) - z)) hs
  simpa only [Finset.image_image, Function.comp_def, hpmap, hqmap] using hrows

/-- Right profile jets below half-span recover all proper selected-core columns. -/
theorem selected_core_early_cols {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hcoeff : ∀ z, 0 ≤ z → 2 * z < K →
      (c.selectedCoreRightProfile P hP).coeff z = (c.selectedCoreRightProfile Q hQ).coeff z) :
    Finset.univ.image (fun i : Fin n => P.zeta i.castSucc) =
      Finset.univ.image (fun j : Fin m => Q.zeta j.castSucc) := by
  classical
  let left := fun i : Fin n => P.zeta i.castSucc - P.zeta (Fin.last n)
  let right := fun j : Fin m => Q.zeta j.castSucc - Q.zeta (Fin.last m)
  have hleft : Function.Injective left := by
    intro i j he
    apply Fin.strictMono_castSucc.injective
    apply P.zeta_strictAnti.injective
    dsimp only [left] at he
    omega
  have hright : Function.Injective right := by
    intro i j he
    apply Fin.strictMono_castSucc.injective
    apply Q.zeta_strictAnti.injective
    dsimp only [right] at he
    omega
  have hpvis (i : Fin n) : 2 * left i < K := by
    have h := c.selected_core_right_distances P hP i
    dsimp only [left]
    omega
  have hqvis (j : Fin m) : 2 * right j < K := by
    have h := c.selected_core_right_distances Q hQ j
    dsimp only [right]
    omega
  have hs := endpointProfile_visible_support_eq left right hleft hright
    (fun i => c.selectedCoreOutgoing P hP i ()) (fun j => c.selectedCoreOutgoing Q hQ j ())
    (c.selected_core_outgoing_ne_zero P hP) (c.selected_core_outgoing_ne_zero Q hQ)
    (fun i => (c.selected_core_right_distances P hP i).1)
    (fun j => (c.selected_core_right_distances Q hQ j).1) (fun z => 2 * z < K) hcoeff
  rw [Finset.filter_true_of_mem (fun i _ => hpvis i),
    Finset.filter_true_of_mem (fun j _ => hqvis j)] at hs
  simpa only [left, right, P.zeta_last, Q.zeta_last, sub_zero] using hs

/-- The actual two early profiles recover both complete selected-core beta lists,
including the original top and bottom entries. No literal equality of the two
selected-core diagrams or independent profile coefficients is assumed. -/
theorem selected_core_early_beta_sets {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hleft : ∀ z, 0 ≤ z → 2 * z < K →
      (c.selectedCoreLeftProfile P hP).coeff z = (c.selectedCoreLeftProfile Q hQ).coeff z)
    (hright : ∀ z, 0 ≤ z → 2 * z < K →
      (c.selectedCoreRightProfile P hP).coeff z = (c.selectedCoreRightProfile Q hQ).coeff z) :
    Finset.univ.image P.xi = Finset.univ.image Q.xi ∧
      Finset.univ.image P.zeta = Finset.univ.image Q.zeta := by
  have hrows := c.selected_core_early_rows P Q hP hQ K hK hleft
  have hcols := c.selected_core_early_cols P Q hP hQ K hK hright
  have htopP := P.topVar_coe
  have htopQ := Q.topVar_coe
  rw [← c.top_eq_profile P hP] at htopP
  rw [← c.top_eq_profile Q hQ] at htopQ
  have htop : P.xi 0 = Q.xi 0 := htopP.symm.trans htopQ
  refine ⟨?_, ?_⟩
  · rw [image_fin_succ, image_fin_succ, hrows, htop]
  · rw [image_fin_castSucc, image_fin_castSucc, hcols, P.zeta_last, Q.zeta_last]

/-- Early endpoint jets recover the literal normalized selected core
(`lem:early-recovery`), not just its Schur class. Ordered beta uniqueness is
supplied by Mathlib after the actual nonzero profile coefficients recover both
finite beta sets. -/
theorem selected_core_early_literal {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hleft : ∀ z, 0 ≤ z → 2 * z < K →
      (c.selectedCoreLeftProfile P hP).coeff z = (c.selectedCoreLeftProfile Q hQ).coeff z)
    (hright : ∀ z, 0 ≤ z → 2 * z < K →
      (c.selectedCoreRightProfile P hP).coeff z = (c.selectedCoreRightProfile Q hQ).coeff z) :
    P.cells = Q.cells := by
  have hnm : n = m := (Profile.rows_eq_of_schur_eq (hP.symm.trans hQ)).1
  subst m
  obtain ⟨hrows, hcols⟩ := c.selected_core_early_beta_sets P Q hP hQ K hK hleft hright
  have hrowRange : Set.range P.xi = Set.range Q.xi := by
    have h := congrArg (fun s : Finset ℤ => (s : Set ℤ)) hrows
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h
  have hcolRange : Set.range P.zeta = Set.range Q.zeta := by
    have h := congrArg (fun s : Finset ℤ => (s : Set ℤ)) hcols
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h
  have hxi : P.xi = Q.xi :=
    (P.xi_strictAnti.range_inj_of_wellFoundedLT Q.xi_strictAnti).mp hrowRange
  have hzeta : P.zeta = Q.zeta :=
    (P.zeta_strictAnti.range_inj_of_wellFoundedLT Q.zeta_strictAnti).mp hcolRange
  have hprofile : P = Q := by
    apply Profile.ext
    · funext i
      have h := P.xi_sub_zeta i
      rw [hxi, hzeta] at h
      exact_mod_cast h.symm.trans (Q.xi_sub_zeta i)
    · funext i
      have h := P.xi_succ_sub_zeta_castSucc i
      rw [hxi, hzeta] at h
      exact_mod_cast h.symm.trans (Q.xi_succ_sub_zeta_castSucc i)
  exact congrArg Profile.cells hprofile

end SelectedCoordinate
end SkewCornerDescent.Matrix
