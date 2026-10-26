/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualSimultaneousRoots
import SkewCornerDescent.SimultaneousTopology
import SkewCornerDescent.RealResponseChambers

/-!
# Exposure supplied by complete original response elimination

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

A finite actual retained-response family is partitioned by its literal top indices.
Complete original-matrix elimination supplies every rational correction. Distinct
same-top residue classes then admit either prescribed real exposure sign.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Simultaneous off-anchor signs and regular pairwise separated anchor roots. -/
noncomputable def simultaneousActualChamber {ι : Type*} (N K : ℕ+) (top : ι → ℕ+)
    (p q : ι → OtherPolynomial N) (positive : Bool) : Set (ℕ → ℝ) :=
  simultaneousRealChamber K top
    (fun i => realResiduePolynomial N (p i)) (fun i => realResiduePolynomial N (q i)) positive

/-- Complete original matrices produce an open nonempty chamber of simultaneous root signs. -/
theorem originalResponses_simultaneous_chambers {ι : Type*} [Finite ι]
    (n : ι → ℕ) (P : ∀ i, Profile (n i))
    (b d : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (top : ι → ℕ+) (htop : ∀ i, c.top < top i)
    (hindices : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (b i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (d i))) = (top i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ))
    (K : ℕ+) (hanchor : ∃ i, top i = K)
    (hdistinct : ∀ i j, top i = K → top j = K → i ≠ j →
      c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) ≠
        c.regularResidue (c.originalLocalResponse (P j) (b j) (d j))) :
    ∃ p q : ι → OtherPolynomial c.top,
      (∀ i j, j ∈ (realResiduePolynomial c.top (p i)).vars → j < (top i : ℕ)) ∧
      (∀ i j, j ∈ (realResiduePolynomial c.top (q i)).vars → j < (c.top : ℕ)) ∧
      (∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨top i, ne_of_gt (htop i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i)) ∧
      ∀ positive : Bool,
        IsOpen (simultaneousActualChamber c.top K top p q positive) ∧
        (simultaneousActualChamber c.top K top p q positive).Nonempty := by
  classical
  obtain ⟨p, q, hp, hq, he, hwitness⟩ :=
    c.originalResponses_simultaneous_roots n P b d top htop hindices hmax
      K hanchor hdistinct
  refine ⟨p, q, hp, hq, he, ?_⟩
  intro positive
  obtain ⟨x, hinj, hreg, hs⟩ := hwitness positive
  let ap := fun a : {i : ι // top i = K} => realResiduePolynomial c.top (p a.val)
  let aq := fun a : {i : ι // top i = K} => realResiduePolynomial c.top (q a.val)
  let rp := fun i : {i : ι // top i ≠ K} => realResiduePolynomial c.top (p i.val)
  let rq := fun i : {i : ι // top i ≠ K} => realResiduePolynomial c.top (q i.val)
  have hsep : IsOpen {x : ℕ → ℝ | (∀ a, MvPolynomial.eval x (aq a) ≠ 0) ∧
      ∀ a b, a ≠ b → MvPolynomial.eval x (ap a * aq b - ap b * aq a) ≠ 0} :=
    rational_root_separation_open ap aq
  have hsign := simultaneous_root_signs_open (K : ℕ) ap aq
    (fun i : {i : ι // top i ≠ K} => (top i.val : ℕ)) rp rq positive
  have hopen : IsOpen (simultaneousActualChamber c.top K top p q positive) := by
    convert hsep.inter hsign using 1
    ext y
    change (_ ∧ _) ↔ ((_ ∧ _) ∧ _)
    aesop
  refine ⟨hopen, x, hreg, ?_, hs⟩
  intro a z haz
  apply (rational_roots_ne_iff ap aq a z x (hreg a) (hreg z)).mp
  exact fun hz => haz (hinj hz)

end SkewCornerDescent.Matrix.SelectedCoordinate
