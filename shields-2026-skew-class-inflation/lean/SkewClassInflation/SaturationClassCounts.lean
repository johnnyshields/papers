/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationFullClass
import SkewClassInflation.SaturationInnerEdges
import SkewClassInflation.SaturationSymmetricPowers
import SkewClassInflation.SaturationColumnResidues

/-!
# Exact full-class cardinalities for general repeated inners

Formalizes `eq:saturation-cardinality` of
`shields-2026-skew-class-inflation.tex`.  Opposite source orientations
can intersect only when the original inner is symmetric.  In that case
its total power has a singleton class, so every full mate is recovered
without rotating the source family.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

/-- Opposite source orientations can agree only when the original inner is symmetric. -/
theorem diagram_eq_rotated_implies_palindrome {M N : ℕ}
    (α : Composition M) (β : Composition N) (hM : 0 < M) (hN : 0 < N)
    (he : A.diagram α hM = ConnectedProfile.rotate (A.diagram β hN)) :
    (List.ofFn A.r).reverse = List.ofFn A.r := by
  let D := A.diagram α hM
  let E := A.diagram β hN
  have hD : A.k ≤ D.1 := A.diagram_order_ge_inner α hM
  have hE : A.k ≤ E.1 := A.diagram_order_ge_inner β hN
  have hmirror (i : Fin A.k) : A.r i.castSucc = A.r ⟨A.k - i.val, by omega⟩ := by
    have hi := i.isLt
    have hmD : min i.val D.1 = i.val := Nat.min_eq_left (by omega)
    have hmE : min i.val E.1 = i.val := Nat.min_eq_left (by omega)
    have hh := congrArg (fun X : ConnectedProfile =>
      X.2.r ⟨min i.val X.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) he
    change D.2.r ⟨min i.val D.1, by omega⟩ =
      E.2.r (⟨min i.val E.1, by omega⟩ : Fin (E.1 + 1)).rev at hh
    have hleft := A.diagram_first_inner_rows α hM
      (⟨min i.val D.1, by omega⟩ : Fin (D.1 + 1))
      (by change min i.val D.1 < A.k; omega)
    have hleftIndex : (⟨min i.val D.1, by omega⟩ : Fin (A.k + 1)) = i.castSucc :=
      Fin.ext hmD
    have hleft' : D.2.r ⟨min i.val D.1, by omega⟩ = A.r i.castSucc :=
      hleft.trans (congrArg A.r hleftIndex)
    have hrightIndex : (⟨min i.val E.1, by omega⟩ : Fin (E.1 + 1)).rev =
        ⟨E.1 - i.val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, hmE]
      omega
    have hright : E.2.r (⟨min i.val E.1, by omega⟩ : Fin (E.1 + 1)).rev =
        A.r ⟨A.k - i.val, by omega⟩ := by
      rw [hrightIndex]
      exact A.diagram_last_inner_rows β hN i
    exact hleft'.symm.trans (hh.trans hright)
  rw [← word_ofFn_rev]
  congr 1
  funext j
  by_cases hj : j.val < A.k
  · let i : Fin A.k := ⟨j.val, hj⟩
    have hh := hmirror i
    have hij : i.castSucc = j := Fin.ext rfl
    have hrev : (⟨A.k - i.val, by omega⟩ : Fin (A.k + 1)) = j.rev := by
      apply Fin.ext
      simp only [Fin.val_rev]
      change A.k - j.val = A.k + 1 - (j.val + 1)
      omega
    rw [hij, hrev] at hh
    exact hh.symm
  · have heq : j = Fin.last A.k := Fin.ext (by
      change j.val = A.k
      have := j.isLt
      omega)
    subst j
    have hh := hmirror (⟨0, A.k_pos⟩ : Fin A.k)
    change A.r 0 = A.r (Fin.last A.k) at hh
    simpa only [Fin.rev_last] using hh

/-- Literal symmetry of the full original inner is exactly palindromicity of its row word. -/
theorem inner_symmetric_iff :
    A.profile.rotate = A.profile ↔ (List.ofFn A.r).reverse = List.ofFn A.r := by
  constructor
  · intro he
    have hh := congrArg Gluing.Profile.r he
    change (fun i => A.r i.rev) = A.r at hh
    have hw := congrArg List.ofFn hh
    rw [word_ofFn_rev] at hw
    exact hw
  · intro he
    apply Gluing.Profile.ext
    · change (fun i => A.r i.rev) = A.r
      apply List.ofFn_injective
      rw [word_ofFn_rev]
      exact he
    · rfl

/-- Without original inner symmetry, the two whole source-parameter images are disjoint. -/
theorem orientations_disjoint {M : ℕ} (α : Composition M) (hM : 0 < M)
    (hpal : (List.ofFn A.r).reverse ≠ List.ofFn A.r) :
    Disjoint ((fun β : Composition M => A.diagram β hM) '' ribbonClass α)
      ((fun β : Composition M => ConnectedProfile.rotate (A.diagram β hM)) '' ribbonClass α) := by
  apply Set.disjoint_left.mpr
  rintro H ⟨β, _, hβ⟩ ⟨γ, _, hγ⟩
  exact hpal (A.diagram_eq_rotated_implies_palindrome β γ hM hM (hβ.trans hγ.symm))

/-- Whole-source rotation preserves injectivity of the literal outer parameter. -/
theorem rotated_diagram_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun β : Composition M => ConnectedProfile.rotate (A.diagram β hM)) := by
  intro β γ he
  apply A.diagram_injective hM
  have hh := congrArg ConnectedProfile.rotate he
  simpa only [ConnectedProfile.rotate_rotate] using hh

/-- A symmetric original inner makes the actual total power invariant under global rotation. -/
theorem power_rotate_of_palindrome (hpal : (List.ofFn A.r).reverse = List.ofFn A.r)
    (M : ℕ) (hM : 0 < M) :
    ConnectedProfile.rotate (⟨M * A.k, A.power M hM⟩ : ConnectedProfile) =
      ⟨M * A.k, A.power M hM⟩ := by
  have hh : ConnectedProfile.rotate (⟨M * A.k, A.power M hM⟩ : ConnectedProfile) ∈
      ConnectedProfile.schurClass (⟨M * A.k, A.power M hM⟩ : ConnectedProfile) :=
    ConnectedProfile.schur_rotate _
  rw [A.power_full_class_of_palindromic_inner hpal M hM] at hh
  exact Set.mem_singleton_iff.mp hh

/-- For a symmetric inner, every full mate belongs to the unrotated parameter image.

**Differs from the paper's route.** The singleton total-power class and
the unrestricted positional inverse eliminate the second parameter image,
without first proving the literal reversal identity for every source. -/
theorem full_class_of_palindrome {M : ℕ} (α : Composition M) (hM : 2 ≤ M)
    (hpal : (List.ofFn A.r).reverse = List.ofFn A.r) :
    ConnectedProfile.schurClass (A.diagram α (by omega)) =
      (fun β : Composition M => A.diagram β (by omega)) '' ribbonClass α := by
  ext H
  constructor
  · intro hH
    obtain ⟨n, Q⟩ := H
    have he : Q.toBetaDiagram.schur = (A.diagram α (by omega)).2.toBetaDiagram.schur := by
      change profileSchur Q = profileSchur (A.diagram α (by omega)).2 at hH
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hH
    have hdata := A.source_mate_reduction α (by omega) Q he
    have hcore : (contractAllMinimum Q A.largeLabel : ConnectedProfile) =
        ⟨M * A.k, A.power M (by omega)⟩ := by
      rcases A.arbitrary_mate_total_core_rigidity α hM Q he with hh | hh
      · exact hh
      · exact hh.trans (A.power_rotate_of_palindrome hpal M (by omega))
    have hconst : eraseGenerator A.largeLabel Q.toBetaDiagram.schur =
        (A.powerFunctions α.blocks (fun _ h => α.blocks_pos h)).prod := by
      rw [he]
      exact A.diagram_constant_coefficient α (by omega)
    obtain ⟨β, hβ⟩ := A.oriented_profile_reconstruction (by omega) Q hdata.2.1 hdata.2.2.1
      _ (A.powerFunctions_are_actual _ _) hconst hcore
    refine ⟨β, ?_, hβ.symm⟩
    apply (A.diagram_schur_eq_iff_ribbon β α (by omega)).mp
    exact (congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.schur) hβ).symm.trans he
  · rintro ⟨β, hβ, rfl⟩
    have he := (A.diagram_schur_eq_iff_ribbon β α (by omega)).mpr hβ
    change profileSchur (A.diagram β (by omega)).2 = profileSchur (A.diagram α (by omega)).2
    simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he

/-- Every actual unrestricted general-source class is finite. -/
theorem full_class_finite {M : ℕ} (α : Composition M) (hM : 2 ≤ M) :
    (ConnectedProfile.schurClass (A.diagram α (by omega))).Finite := by
  rw [A.full_class α hM]
  exact ((Set.toFinite (ribbonClass α)).image _).union
    ((Set.toFinite (ribbonClass α)).image _)

open scoped Classical in
/-- Symmetric inners have one full parameter image; asymmetric inners have two. -/
theorem full_class_card {M : ℕ} (α : Composition M) (hM : 2 ≤ M) :
    (ConnectedProfile.schurClass (A.diagram α (by omega))).ncard =
      if A.profile.rotate = A.profile then (ribbonClass α).ncard
      else 2 * (ribbonClass α).ncard := by
  classical
  by_cases hsym : A.profile.rotate = A.profile
  · rw [ite_eq_left hsym, A.full_class_of_palindrome α hM ((A.inner_symmetric_iff).mp hsym),
      Set.ncard_image_of_injective _ (A.diagram_injective (by omega))]
  · have hpal : (List.ofFn A.r).reverse ≠ List.ofFn A.r :=
      fun h => hsym ((A.inner_symmetric_iff).mpr h)
    rw [ite_eq_right hsym, A.full_class α hM,
      Set.ncard_union_eq (A.orientations_disjoint α (by omega) hpal)
        ((Set.toFinite (ribbonClass α)).image _) ((Set.toFinite (ribbonClass α)).image _),
      Set.ncard_image_of_injective _ (A.diagram_injective (by omega)),
      Set.ncard_image_of_injective _ (A.rotated_diagram_injective (by omega))]
    omega

end SkewClassInflation.SaturationInner
