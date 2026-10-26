/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinPositionalInverse
import SkewClassInflation.BoundaryIdentification

/-!
# Literal geometry of arbitrary thin mates

The arbitrary-mate and disjoint-orientation parts of
`thm:two-row-thin-class` in `shields-2026-skew-class-inflation.tex`.
Every reconstruction input is produced from the original Schur equality.
The parameter map is injective on literal diagrams, independently of
which compositions have equal ribbon functions.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The source chain always has the shorter endpoint first. -/
theorem chain_first (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l hl).2.r 0 = B.a := by
  cases l with
  | nil => rfl
  | cons b l =>
    let R := B.chain b (hl b List.mem_cons_self) l
      (fun k hk => hl k (List.mem_cons_of_mem _ hk))
    change Profile.joinRows (B.innerPower a ha) R.2 0 = B.a
    have h := Profile.joinRows_left (B.innerPower a ha) R.2 0
    exact h

/-- The final endpoint of the source chain is always the longer one. -/
theorem chain_last (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l hl).2.r (Fin.last (B.chain a ha l hl).1) = B.b := by
  induction l generalizing a with
  | nil =>
    change (B.innerPower a ha).r (Fin.last a) = B.b
    simp [innerPower, powerRows, Fin.val_last, Nat.ne_of_gt ha]
  | cons b l ih =>
    let R := B.chain b (hl b List.mem_cons_self) l
      (fun k hk => hl k (List.mem_cons_of_mem _ hk))
    change Profile.joinRows (B.innerPower a ha) R.2 (Fin.last (a + R.1 + 1)) = B.b
    have h := Profile.joinRows_right (B.innerPower a ha) R.2 (Fin.last R.1)
    have hi : (⟨a + 1 + (Fin.last R.1).val, by omega⟩ : Fin (a + R.1 + 2)) =
        Fin.last (a + R.1 + 1) := by apply Fin.ext; simp; omega
    rw [hi] at h
    exact h.trans (ih b _ _)

/-- Both literal exterior readings hold on the entire positive-composition domain. -/
theorem diagram_exteriors {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.r 0 = B.a ∧
      (B.diagram α hM).2.r (Fin.last (B.diagram α hM).1) = B.b := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · exact ⟨B.chain_first _ _ _ _, B.chain_last _ _ _ _⟩

/-- Every arbitrary connected mate is literally a constructed thin profile or its rotation. -/
theorem arbitrary_mate_geometry {M k : ℕ} (α : Composition M) (hM : 0 < M)
    (Q : Profile k)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    ∃ β : Composition M, (⟨k, Q⟩ : ConnectedProfile) = B.diagram β hM ∨
      (⟨k, Q⟩ : ConnectedProfile) = (B.diagram β hM).rotate := by
  obtain ⟨R, hRQ, hfirst, hR⟩ := B.arbitrary_mate_oriented α hM Q he
  have hn := Nat.succ.inj
    (R.toBetaDiagram.row_count_of_schur_eq (B.diagram α hM).2.toBetaDiagram hR)
  have hthick : Staircase.Thick R := by
    subst k
    exact GeneralHessenberg.hessenberg_thick _
      (hessenberg_of_equal_schur (B.diagram α hM).2.toBetaDiagram R.toBetaDiagram
        (B.diagram α hM).2.toBetaDiagram_connected R.toBetaDiagram_connected hR.symm
        (B.diagram_thick α hM).hessenberg)
  obtain ⟨β, hβ⟩ := B.oriented_profile_reconstruction hM R hthick hfirst
    (B.powerFunctions α.blocks (fun _ hm => α.blocks_pos hm))
    (B.powerFunctions_are_actual α.blocks (fun _ hm => α.blocks_pos hm))
    (B.arbitrary_mate_constant α hM R hR)
    (B.arbitrary_mate_total_contraction α hM R hR)
  refine ⟨β, ?_⟩
  rcases hRQ with rfl | rfl
  · exact Or.inl hβ
  · right
    have hh := congrArg ConnectedProfile.rotate hβ
    simpa only [ConnectedProfile.rotate, Gluing.Profile.rotate_rotate] using hh

/-- Literal source diagrams retain the full ordered outer composition. -/
theorem diagram_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun α : Composition M => B.diagram α hM) := by
  intro α β he
  apply B.boundary_function_injective hM
  exact congrArg
    (fun D : ConnectedProfile => (Profile.inflate B.boundary.p D.2).toBetaDiagram.schur) he

/-- A positive source orientation never equals any reversed source orientation. -/
theorem diagram_ne_rotated {M : ℕ} (α β : Composition M) (hM : 0 < M) :
    B.diagram α hM ≠ (B.diagram β hM).rotate := by
  intro he
  have hf := congrArg (fun D : ConnectedProfile => D.2.r 0) he
  change (B.diagram α hM).2.r 0 =
    (B.diagram β hM).2.r (0 : Fin ((B.diagram β hM).1 + 1)).rev at hf
  rw [Fin.rev_zero, (B.diagram_exteriors α hM).1, (B.diagram_exteriors β hM).2] at hf
  exact (Nat.ne_of_lt B.a_lt_b) hf

end SkewClassInflation.ThinParameters
