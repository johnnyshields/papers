/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationOverlapWords
import SkewClassInflation.OverlapSignedPeriods
import SkewClassInflation.RibbonReconstructionWords

/-!
# Complete unrestricted classes of repeated overlapped inners

Formalizes `lem:merged-block-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Every arbitrary connected mate
supplies its actual row count, constant gaps, and deflated ribbon equality.
Overlap reconstruction then identifies the complete profile up to rotation.
The one-copy boundary is deliberately excluded.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Every connected mate of a power with at least two copies is an actual source orientation. -/
theorem power_mate_eq_or_rotate (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.power m (by omega)).toBetaDiagram.schur) :
    (⟨n, Q⟩ : ConnectedProfile) = ⟨m * A.k, A.power m (by omega)⟩ ∨
      (⟨n, Q⟩ : ConnectedProfile) =
        ConnectedProfile.rotate ⟨m * A.k, A.power m (by omega)⟩ := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨hn, _, hgQ, hrQ⟩ := A.power_mate_reduction (a + 1) (by omega) Q he
  subst n
  let P := A.power (a + 1) (by omega)
  have hP : ∀ i, A.c < P.r i := A.powerRows_above_gap (a + 1)
  have hQ : ∀ i, A.c < Q.r i := fun i => A.c_lt_d.trans (hrQ i)
  let r := fun i => P.r i - A.c
  let s := fun i => Q.r i - A.c
  have hr : ∀ i, 0 < r i := fun i => Nat.sub_pos_of_lt (hP i)
  have hs : ∀ i, 0 < s i := fun i => Nat.sub_pos_of_lt (hQ i)
  have hrec : ribbonReconstructible (rowComposition r hr) := by
    apply ribbonReconstructible_of_blocks_eq (A.overlapWord.composition a)
      (rowComposition r hr) (A.power_deflated_word a).symm
    exact A.overlapWord.reconstructible a (by omega)
  have hw := ribbon_eq_reconstruct_of_reconstructible r s hr hs hrec
    (A.power_mate_ribbon (a + 1) (by omega) Q he).symm
  have hrestoreP : (List.ofFn r).map (fun x => x + A.c) = List.ofFn P.r := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact Nat.sub_add_cancel (hP i).le
  have hrestoreQ : (List.ofFn s).map (fun x => x + A.c) = List.ofFn Q.r := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact Nat.sub_add_cancel (hQ i).le
  rcases hw with hw | hw
  · have hv := congrArg (List.map (fun x : ℕ => x + A.c)) hw
    rw [hrestoreQ, hrestoreP] at hv
    apply Or.inl
    congr 1
    apply Gluing.Profile.ext
    · exact List.ofFn_injective hv
    · funext j
      exact hgQ j
  · have hv := congrArg (List.map (fun x : ℕ => x + A.c)) hw
    rw [hrestoreQ, List.map_reverse, hrestoreP, ← word_ofFn_rev] at hv
    apply Or.inr
    change (⟨(a + 1) * A.k, Q⟩ : ConnectedProfile) =
      ⟨(a + 1) * A.k, P.rotate⟩
    congr 1
    apply Gluing.Profile.ext
    · exact List.ofFn_injective hv
    · funext j
      exact hgQ j

/-- The entire connected Schur class of every repeated power is its rotation pair. -/
theorem power_full_class (m : ℕ) (hm : 2 ≤ m) :
    (ConnectedProfile.schurClass
      (⟨m * A.k, A.power m (by omega)⟩ : ConnectedProfile)) =
      {⟨m * A.k, A.power m (by omega)⟩,
        ConnectedProfile.rotate ⟨m * A.k, A.power m (by omega)⟩} := by
  ext H
  constructor
  · intro hH
    rcases H with ⟨n, Q⟩
    have he : Q.toBetaDiagram.schur = (A.power m (by omega)).toBetaDiagram.schur := by
      change profileSchur Q = profileSchur (A.power m (by omega)) at hH
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hH
    exact Set.mem_insert_iff.mpr ((A.power_mate_eq_or_rotate m hm Q he).imp_right
      Set.mem_singleton_iff.mpr)
  · intro hH
    rcases Set.mem_insert_iff.mp hH with he | he
    · subst H
      rfl
    · rw [Set.mem_singleton_iff] at he
      subst H
      exact ConnectedProfile.schur_rotate _

end SkewClassInflation.SaturationInner
