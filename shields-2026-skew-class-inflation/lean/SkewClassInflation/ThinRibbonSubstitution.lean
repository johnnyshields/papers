/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinPowerSection
import SkewClassInflation.ThinChainMerge
import SkewClassInflation.ZeroJoinRecurrence
import SkewClassInflation.RibbonPolynomials

/-!
# Ribbon polynomials and faithful thin substitution

Formalizes `eq:thin-substitution` in
`shields-2026-skew-class-inflation.tex`.  Ribbon polynomials use the
cut-and-near-concatenate recurrence in the independent complete
generators.  The actual thin-chain recurrence supplies their evaluation;
the explicit power section reflects equality.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

namespace ThinParameters

variable (B : ThinParameters)

/-- The full actual function obeys the cut-and-merge recurrence on its ordered block word. -/
theorem chain_schur_cons (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    (B.chain a ha (b :: l) (by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hb
      · exact hl k hk)).2.toBetaDiagram.schur =
      (B.innerPower a ha).toBetaDiagram.schur * (B.chain b hb l hl).2.toBetaDiagram.schur -
        (B.chain (a + b) (by omega) l hl).2.toBetaDiagram.schur := by
  let R := B.chain b hb l hl
  have hm := congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.schur)
    (B.merge_chain a b ha hb l hl)
  change (Profile.merge (B.innerPower a ha) R.2 0
    ((B.innerPower a ha).r_pos _) (R.2.r_pos _)).toBetaDiagram.schur = _ at hm
  change (Profile.zeroJoin (B.innerPower a ha) R.2).toBetaDiagram.schur = _
  rw [Profile.zeroJoin_schur _ _ (B.innerPower_thick a ha) (B.chain_thick b hb l hl), hm]

/-- Substitution by the actual power functions. -/
noncomputable def powerSubstitution : CompleteRing →ₐ[ℚ] CompleteRing :=
  MvPolynomial.aeval (fun m : ℕ+ => (B.innerPower m.val m.pos).toBetaDiagram.schur)

/-- Each positive complete generator evaluates to the corresponding actual power function. -/
theorem powerSubstitution_complete (a : ℕ) (ha : 0 < a) :
    B.powerSubstitution (complete a) = (B.innerPower a ha).toBetaDiagram.schur := by
  let j : ℕ+ := ⟨a, ha⟩
  have he : complete a = MvPolynomial.X j := by
    rw [complete_of_pos (by omega : (0 : ℤ) < a)]
    congr 1
  rw [he, powerSubstitution, MvPolynomial.aeval_X]
  rfl

/-- The actual ordered chain is the faithful evaluation of its ribbon polynomial. -/
theorem chain_substitution (a : ℕ) (ha : 0 < a) (l : List ℕ)
    (hl : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l hl).2.toBetaDiagram.schur = B.powerSubstitution (ribbonTail a l) := by
  induction l generalizing a with
  | nil => exact (B.powerSubstitution_complete a ha).symm
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    have ht : ∀ k ∈ l, 0 < k := fun k hk => hl k (List.mem_cons_of_mem _ hk)
    rw [B.chain_schur_cons a b ha hb l ht, ih b hb ht, ih (a + b) (by omega) ht,
      ribbonTail, map_sub, map_mul, B.powerSubstitution_complete a ha]

/-- The concrete diagram has precisely the ribbon substitution claimed by the manuscript. -/
theorem diagram_substitution {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.schur = B.powerSubstitution (ribbonWord α.blocks) := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    simp only [he, ribbonWord]
    exact B.chain_substitution _ _ _ _

/-- Equality of arbitrary constructed thin functions is exactly outer ribbon equivalence. -/
theorem diagram_schur_eq_iff {M : ℕ} (α β : Composition M) (hM : 0 < M) :
    (B.diagram α hM).2.toBetaDiagram.schur = (B.diagram β hM).2.toBetaDiagram.schur ↔
      ribbonWord α.blocks = ribbonWord β.blocks := by
  rw [B.diagram_substitution, B.diagram_substitution]
  exact B.power_substitution_injective.eq_iff

end ThinParameters
end SkewClassInflation
