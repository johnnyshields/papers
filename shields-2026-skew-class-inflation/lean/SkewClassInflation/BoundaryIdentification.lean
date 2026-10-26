/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryLowestComponent

/-!
# Exact identification and separation at the first boundary

Formalizes the composition-recovery step in `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  The actual inflated full board
is identified with the restored parent by both complete beta supports and
its produced row count.  No core or lowest-component observation is taken
as a hypothesis.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

namespace ThinParameters

variable (B : ThinParameters)

/-- At the exact boundary, equal actual thin-family functions have the same entire composition. -/
theorem boundary_function_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun α : Composition M =>
      (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur) := by
  intro α β he
  apply compositionCore_schur_injective B.boundary hM
  have hc := congrArg (MvPolynomial.homogeneousComponent (M + 1)) he
  rw [B.boundary_lowest_component α hM, B.boundary_lowest_component β hM] at hc
  exact hc

/-- Lowering makes the exact boundary separation permanent at every greater integer inflation. -/
theorem superthreshold_function_injective {M : ℕ} (hM : 0 < M) (t : ℕ)
    (ht : B.boundary.p ≤ t) :
    Function.Injective (fun α : Composition M =>
      (ConnectedProfile.inflate t (B.diagram α hM)).schur) := by
  intro α β he
  have hp := ConnectedProfile.equality_at_earlier (B.diagram α hM) (B.diagram β hM) ht he
  apply B.boundary_function_injective hM
  change profileSchur (Profile.inflate B.boundary.p (B.diagram α hM).2) =
    profileSchur (Profile.inflate B.boundary.p (B.diagram β hM).2) at hp
  simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hp

/-- Distinct constructed outer words stay Schur-distinct at and above the threshold. -/
theorem superthreshold_functions_ne {M : ℕ} (α β : Composition M) (hM : 0 < M)
    (hαβ : α ≠ β) (t : ℕ) (ht : B.boundary.p ≤ t) :
    (ConnectedProfile.inflate t (B.diagram α hM)).schur ≠
      (ConnectedProfile.inflate t (B.diagram β hM)).schur :=
  fun he => hαβ (B.superthreshold_function_injective hM t ht he)

end ThinParameters
end SkewClassInflation
