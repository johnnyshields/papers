/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationChainMerge
import SkewClassInflation.SaturationCutCoefficients
import SkewClassInflation.RibbonDeterminants
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Localized ribbon substitution for actual general sources

The displayed identity `eq:saturation-substitution` in
`shields-2026-skew-class-inflation.tex`.  Every substituted polynomial
is the actual repeated-power determinant, and the denominator's nonvanishing
is proved in the fraction field of the full complete-generator ring.
Sorry-free.
-/

namespace SkewClassInflation

/-- The fraction field of the full independent complete-generator ring. -/
abbrev SaturationFractionField := FractionRing SkewJacobiNegative.CompleteRing

namespace SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- The actual source recurrence contracts the first larger seam in its literal position. -/
theorem chain_schur_recurrence (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (l : List ℕ) (hl : ∀ m ∈ b :: l, 0 < m) :
    (A.chain a ha (b :: l) hl).2.toBetaDiagram.schur =
      (A.power a ha).toBetaDiagram.schur *
        (A.chain b hb l (fun m hm => hl m (List.mem_cons_of_mem _ hm))).2.toBetaDiagram.schur -
      complete A.d *
        (A.chain (a + b) (by omega) l
          (fun m hm => hl m (List.mem_cons_of_mem _ hm))).2.toBetaDiagram.schur := by
  let htail : ∀ m ∈ l, 0 < m := fun m hm => hl m (List.mem_cons_of_mem _ hm)
  let Q := A.chain b hb l htail
  have hp : A.d < (A.power a ha).r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
  have hq : A.d < Q.2.r 0 := by
    rw [A.chain_first]
    have := A.first_bound
    omega
  have hJ : Staircase.Thick (Profile.join (A.power a ha) Q.2 A.d hp hq) :=
    A.chain_thick a ha (b :: l) hl
  have he := Profile.join_schur (A.power a ha) Q.2 A.d hp hq hJ
  have hm := congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.schur)
    (A.merge_power_chain a b ha hb l htail)
  rw [hm] at he
  exact he

/-- The distinguished seam generator remains nonzero in the genuine fraction field. -/
theorem large_generator_nonzero :
    algebraMap CompleteRing SaturationFractionField (complete A.d) ≠ 0 := by
  intro he
  apply (complete_ne_zero_iff (A.d : ℤ)).mpr (by positivity)
  apply IsFractionRing.injective CompleteRing SaturationFractionField
  simpa only [map_zero] using he

/-- Substitute each actual power polynomial divided by the distinguished seam generator. -/
noncomputable def localizedSubstitution : CompleteRing →+* SaturationFractionField :=
  MvPolynomial.eval₂Hom (algebraMap ℚ SaturationFractionField) (fun j : ℕ+ =>
    algebraMap CompleteRing SaturationFractionField (A.power j.val j.pos).toBetaDiagram.schur /
      algebraMap CompleteRing SaturationFractionField (complete A.d))

/-- Every positive ribbon generator is sent to the corresponding actual power ratio. -/
theorem localizedSubstitution_complete (a : ℕ) (ha : 0 < a) :
    A.localizedSubstitution (complete a) =
      algebraMap CompleteRing SaturationFractionField (A.power a ha).toBetaDiagram.schur /
        algebraMap CompleteRing SaturationFractionField (complete A.d) := by
  let j : ℕ+ := ⟨a, ha⟩
  have hc : complete (a : ℤ) = MvPolynomial.X j := complete_nat j
  rw [hc, localizedSubstitution, MvPolynomial.eval₂Hom_X']
  rfl

/-- The full arbitrary-inner chain has exactly the localized ribbon polynomial. -/
theorem chain_substitution (a : ℕ) (ha : 0 < a) (l : List ℕ)
    (hl : ∀ m ∈ l, 0 < m) :
    algebraMap CompleteRing SaturationFractionField
        (A.chain a ha l hl).2.toBetaDiagram.schur =
      algebraMap CompleteRing SaturationFractionField (complete A.d) ^ (l.length + 1) *
        A.localizedSubstitution (ribbonTail a l) := by
  induction l generalizing a with
  | nil =>
    change algebraMap CompleteRing SaturationFractionField (A.power a ha).toBetaDiagram.schur = _
    rw [ribbonTail, A.localizedSubstitution_complete a ha]
    simp only [List.length_nil, Nat.zero_add, pow_one]
    field_simp [A.large_generator_nonzero]
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    have htail : ∀ m ∈ l, 0 < m := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    rw [A.chain_schur_recurrence a b ha hb l hl, map_sub, map_mul, map_mul,
      ih b hb htail, ih (a + b) (by omega) htail,
      ribbonTail, map_sub, map_mul, A.localizedSubstitution_complete a ha]
    simp only [List.length_cons, pow_succ]
    field_simp [A.large_generator_nonzero]

/-- The exact displayed localized ribbon identity for every positive outer composition. -/
theorem diagram_substitution {M : ℕ} (α : Composition M) (hM : 0 < M) :
    algebraMap CompleteRing SaturationFractionField (A.diagram α hM).2.toBetaDiagram.schur =
      algebraMap CompleteRing SaturationFractionField (complete A.d) ^ α.length *
        A.localizedSubstitution (ribbonWord α.blocks) := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    have hh := A.chain_substitution a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun m hm => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hm))
    simpa only [Composition.length, he, List.length_cons, ribbonWord] using hh

/-- Every genuine outer ribbon equality gives equality of the corresponding full general sources. -/
theorem diagram_schur_eq_of_ribbon_eq {M : ℕ} (α β : Composition M) (hM : 0 < M)
    (he : ribbonWord α.blocks = ribbonWord β.blocks) :
    (A.diagram α hM).2.toBetaDiagram.schur = (A.diagram β hM).2.toBetaDiagram.schur := by
  have hlen := ribbonWord_eq_length α β hM hM he
  apply IsFractionRing.injective CompleteRing SaturationFractionField
  rw [A.diagram_substitution, A.diagram_substitution, hlen, he]

/-- Every prescribed ribbon mate and its global rotation belongs to the full connected class. -/
theorem prescribed_class_subset {M : ℕ} (α : Composition M) (hM : 0 < M) :
    {H : ConnectedProfile | ∃ β : Composition M,
      ribbonWord β.blocks = ribbonWord α.blocks ∧
        (H = A.diagram β hM ∨ H = (A.diagram β hM).rotate)} ⊆
      (A.diagram α hM).schurClass := by
  rintro H ⟨β, hβ, hH | hH⟩
  · subst H
    have he := A.diagram_schur_eq_of_ribbon_eq β α hM hβ
    simpa only [ConnectedProfile.schurClass, Set.mem_ofPred_eq, ConnectedProfile.schur,
      profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he
  · subst H
    change (A.diagram β hM).rotate.schur = (A.diagram α hM).schur
    rw [ConnectedProfile.schur_rotate]
    have he := A.diagram_schur_eq_of_ribbon_eq β α hM hβ
    simpa only [ConnectedProfile.schur, profileSchur_eq_inherited,
      Gluing.Profile.toBetaDiagram_schur] using he

end SaturationInner
end SkewClassInflation
