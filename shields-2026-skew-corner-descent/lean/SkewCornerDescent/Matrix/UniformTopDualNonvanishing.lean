/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalActiveExtreme

/-!
# Dual nonvanishing for original responses with one top generator

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`).
For the uniform-top subcase, both signs use the same actual chamber point. Finite inactive
peeling identifies both distinct active extremes with the omitted class, a contradiction.
This module does not identify a literal chart with its completed response inventory.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- Two active classes of the same original top generator prevent simultaneous vanishing
of the complete short and full detectors. All inactive exposures are discharged by finite
peeling; the two active extremes are selected from the actual rational roots. -/
theorem uniformTop_original_dual_nonvanishing {α : Type*}
    [Fintype α] [DecidableEq α] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (hallTop : ∀ a, top a = K)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q false)
    (word : ZMod (r * d) → α) (k : ℕ)
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
      algebraMap (OtherPolynomial N) (OtherField N) (p a) /
        algebraMap (OtherPolynomial N) (OtherField N) (q a)
    ((s : OtherField N) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
      (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : OtherField N) *
          (response a)⁻¹) ≠ 0) ∨
    ((r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 (r * s - 1) 0 -
      (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : OtherField N) *
        (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) ≠ 0) := by
  classical
  dsimp only
  by_contra h
  obtain ⟨hshort, hfull⟩ := not_or.mp h
  have hshort := not_not.mp hshort
  have hfull := not_not.mp hfull
  let e := classDefect word 1 d s (r * s - 1) 0
  let active := {a : α // e a ≠ 0}
  obtain ⟨u, v, huv, heu, hev⟩ := htwo
  let _ : Nonempty active := ⟨⟨u, heu⟩⟩
  let roots := fun a : α => -MvPolynomial.eval x (realResiduePolynomial N (p a)) /
    MvPolynomial.eval x (realResiduePolynomial N (q a))
  have hinj : Function.Injective (fun a : active => roots a.val) := by
    intro a b hab
    have hi := simultaneousActualChamber_roots_injective N K top p q false x hx
    have heq : (⟨a.val, hallTop a.val⟩ : {a : α // top a = K}) =
        ⟨b.val, hallTop b.val⟩ := by
      apply hi
      simpa only [roots, rationalAnchorRoot, neg_div] using hab
    exact Subtype.ext (congrArg (fun z : {a : α // top a = K} => z.val) heq)
  obtain ⟨least, hleast⟩ := exists_least_anchor_label (fun a : active => roots a.val) hinj
  obtain ⟨greatest, hgreatest⟩ := exists_greatest_anchor_label
    (fun a : active => roots a.val) hinj
  have hxTrue : x ∈ simultaneousActualChamber N K top p q true := by
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro a i
    exact (i.property (hallTop i.val)).elim
  have hNtop : ∀ a, N ≤ top a := fun a => (hallTop a).symm ▸ hNK
  have hleastOmitted := originalChamber_active_extreme_is_omitted
    hr hd hs N K hNK top p q htop hNtop hp hq hq0 false x hx word k
    least.val (hallTop least.val) least.property (by
      intro b hb heb hne
      have hba : (⟨b, heb⟩ : active) ≠ least := fun hz => hne (congrArg Subtype.val hz)
      exact sub_neg.mpr (hleast ⟨b, heb⟩ hba)) hshort hfull
  have hgreatestOmitted := originalChamber_active_extreme_is_omitted
    hr hd hs N K hNK top p q htop hNtop hp hq hq0 true x hxTrue word k
    greatest.val (hallTop greatest.val) greatest.property (by
      intro b hb heb hne
      have hba : (⟨b, heb⟩ : active) ≠ greatest := fun hz => hne (congrArg Subtype.val hz)
      exact sub_pos.mpr (hgreatest ⟨b, heb⟩ hba)) hshort hfull
  have heq : least = greatest :=
    Subtype.ext (hleastOmitted.symm.trans hgreatestOmitted)
  have hother : ∃ a : active, a ≠ least := by
    by_cases hu : u = least.val
    · refine ⟨⟨v, hev⟩, ?_⟩
      intro hz
      exact huv (hu.trans (congrArg Subtype.val hz).symm)
    · exact ⟨⟨u, heu⟩, fun hz => hu (congrArg Subtype.val hz)⟩
  obtain ⟨a, ha⟩ := hother
  have hlo := hleast a ha
  have hhi := hgreatest a (heq ▸ ha)
  rw [← heq] at hhi
  exact (not_lt_of_gt hlo) hhi

end SkewCornerDescent.Matrix
