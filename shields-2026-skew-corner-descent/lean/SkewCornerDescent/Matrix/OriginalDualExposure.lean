/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalDetectorSlices
import SkewCornerDescent.DualInventoryClosure
import SkewCornerDescent.InactiveWindowPeeling

/-!
# Exposed alternatives from the original dependent detectors

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The actual chamber produces an exposed anchor. The original source identities imply either
an inactive periodic mask eligible for peeling or the unique omitted active class.
Every response retains its shared original generators. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- The original dependent detector identities decide the produced exposed anchor without
assuming its class defect, any pole order, or any window count. -/
theorem originalChamber_dual_exposed_alternative {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (hcoprime : Nat.Coprime d s)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hanchor : ∃ a, top a = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : ZMod (r * d) → α) (k : ℕ)
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
    ∃ a : {a : α // top a = K},
      (classDefect word 1 d s (r * s - 1) 0 a.val = 0 ∧
        (∀ i, windowSum (classMask word a.val) 1 (r * s) i =
          windowSum (classMask word a.val) 1 (r * s - 1) 0) ∧
        Function.Periodic (classMask word a.val) (r : ZMod (r * d)) ∧
        classMask word a.val ((r * s - 1 : ℕ) : ZMod (r * d)) = 0) ∨
      word ((r * s - 1 : ℕ) : ZMod (r * d)) = a.val := by
  classical
  have hshortSlice := originalChamber_shortDetector_zero_slice N K hNK top p q htop
    hp hq hanchor positive x hx word (classDefect word 1 d s (r * s - 1) 0)
    1 (r * s) (r * s - 1) 0 s (r * s) hshort
  have hfullSlice := originalChamber_fullDetector_zero_slice N K hNK top p q htop
    hp hq hanchor positive x hx word (classDefect word 1 d s (r * s - 1) 0)
    1 ((k - 1) * (r * d) + r * s) (r * d) (r * s - 1) k 0 (r * d * d) hfull
  obtain ⟨a, hroot, hsimple, hden, hsign⟩ := simultaneousActualChamber_exposed_slice
    N K hNK top p q hp hq hanchor positive x hx
  let root := rationalAnchorRoot
    (fun a : {a : α // top a = K} => realResiduePolynomial N (p a.val))
    (fun a => realResiduePolynomial N (q a.val)) a x
  let num := fun a => coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a)
  let den := fun a => coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a)
  refine ⟨a, ?_⟩
  by_cases he : classDefect word 1 d s (r * s - 1) 0 a.val = 0
  · exact Or.inl ⟨he, inactive_short_detector_mask hr hd hs hcoprime word a.val num den
      root (if positive then 1 else -1) hroot hsimple hden hsign he hshortSlice⟩
  · exact Or.inr (exposed_dual_detector_omitted_class hr hd hs word a.val k num den root
      (if positive then 1 else -1) hroot hsimple hden hsign he hshortSlice hfullSlice)

end SkewCornerDescent.Matrix
