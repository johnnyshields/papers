/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.RemainingDetectorSlices
import SkewCornerDescent.Matrix.AnchorSliceOrder
import SkewCornerDescent.DualInventoryClosure
import SkewCornerDescent.InactiveWindowPeeling

/-!
# Exposed alternatives after finite inactive replacement

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The original dependent zero identities determine the next exposed class of an actual
remaining-family chamber. Previously removed masks retain every original word position.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- After any justified finite inactive replacement, the next produced anchor either has
an inactive periodic mask or is the omitted active class. Its defect and counts are not
assumed; they follow from the original complete detector identities. -/
theorem remainingActualChamber_dual_exposed_alternative {α : Type*}
    [Fintype α] [DecidableEq α] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0)
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive)
    (word : ZMod (r * d) → α) (k : ℕ)
    (he : ∀ a ∈ S, classDefect word 1 d s (r * s - 1) 0 a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) 1 (r * s) i =
      windowSum (classMask word a) 1 (r * s - 1) 0)
    (hshort :
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a)
      (s : OtherField N) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : OtherField N) *
            (response a)⁻¹) = 0)
    (hfull :
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a)
      (r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 (r * s - 1) 0 -
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : OtherField N) *
          (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) = 0) :
    ∃ a : {a : {a : α // a ∉ S} // top a.val = K},
      (∀ b, b ∉ S → top b = K → b ≠ a.val.val → responseSign positive
        ((-MvPolynomial.eval x (realResiduePolynomial N (p a.val.val)) /
            MvPolynomial.eval x (realResiduePolynomial N (q a.val.val))) -
          (-MvPolynomial.eval x (realResiduePolynomial N (p b)) /
            MvPolynomial.eval x (realResiduePolynomial N (q b))))) ∧
      ((classDefect word 1 d s (r * s - 1) 0 a.val.val = 0 ∧
        (∀ i, windowSum (classMask word a.val.val) 1 (r * s) i =
          windowSum (classMask word a.val.val) 1 (r * s - 1) 0) ∧
        Function.Periodic (classMask word a.val.val)
          ((Nat.gcd (r * s) (r * d) : ℕ) : ZMod (r * d)) ∧
        classMask word a.val.val ((r * s - 1 : ℕ) : ZMod (r * d)) = 0) ∨
      (classDefect word 1 d s (r * s - 1) 0 a.val.val ≠ 0 ∧
        word ((r * s - 1 : ℕ) : ZMod (r * d)) = a.val.val)) := by
  classical
  have hshortSlice := remainingActualChamber_shortDetector_zero S N K hNK top p q htop
    hNtop hp hq hq0 hanchor positive x hx word (classDefect word 1 d s (r * s - 1) 0)
    1 (r * s) (r * s - 1) 0 s (r * s) he hcount hshort
  have hfullSlice := remainingActualChamber_fullDetector_zero S N K hNK top p q htop
    hNtop hp hq hq0 hanchor positive x hx word (classDefect word 1 d s (r * s - 1) 0)
    (r * s) (r * s - 1) k (r * d * d) he hcount hfull
  obtain ⟨a, hroot, hsimple, hden, hsign⟩ := remainingActualChamber_exposed_slice
    S N K hNK top p q hp hq hanchor positive x hx
  let root := rationalAnchorRoot
    (fun a : {a : {a : α // a ∉ S} // top a.val = K} =>
      realResiduePolynomial N (p a.val.val))
    (fun a => realResiduePolynomial N (q a.val.val)) a x
  let num := fun Y => if Y ∈ S then Polynomial.C (if positive then 1 else -1)
    else coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q Y)
  let den := fun Y => if Y ∈ S then (1 : Polynomial ℝ)
    else coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q Y)
  have hresponse (Y : α) :
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y) =
      replaceResponses S (fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q Y)) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q Y)))
        (fun _ => RatFunc.C (if positive then 1 else -1)) Y := by
    by_cases hY : Y ∈ S <;> simp only [num, den, replaceResponses, hY,
      ite_true, ite_false, map_one, RatFunc.algebraMap_C, div_one]
  have horder : ∀ b, b ∉ S → top b = K → b ≠ a.val.val → responseSign positive
      ((-MvPolynomial.eval x (realResiduePolynomial N (p a.val.val)) /
          MvPolynomial.eval x (realResiduePolynomial N (q a.val.val))) -
        (-MvPolynomial.eval x (realResiduePolynomial N (p b)) /
          MvPolynomial.eval x (realResiduePolynomial N (q b)))) := by
    intro b hb htopb hba
    let b' : {a : {a : α // a ∉ S} // top a.val = K} := ⟨⟨b, hb⟩, htopb⟩
    have hsb := hsign b hba
    simp only [hb, ite_false] at hsb
    have h := anchor_slice_sign_implies_root_sign N K hNK
      (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val)
      (fun a j hj => hp a.val j hj) (fun a j hj => hq a.val j hj)
      a b' positive x (hx.1 b') (by
        simpa only [root, b', exposedResponseNumerator, exposedResponseLinearNumerator]
          using hsb)
    simpa only [rationalAnchorRoot, b', neg_div] using h
  refine ⟨a, horder, ?_⟩
  by_cases hea : classDefect word 1 d s (r * s - 1) 0 a.val.val = 0
  · refine Or.inl ⟨hea, ?_⟩
    apply inactive_short_detector_general_mask hr hd hs word a.val.val num den
      root (if positive then 1 else -1) hroot hsimple hden hsign hea
    simpa only [hresponse] using hshortSlice
  · refine Or.inr ⟨hea, ?_⟩
    apply exposed_dual_detector_omitted_class hr hd hs word a.val.val k num den root
      (if positive then 1 else -1) hroot hsimple hden hsign hea
    · simpa only [hresponse] using hshortSlice
    · simpa only [hresponse] using hfullSlice

end SkewCornerDescent.Matrix
