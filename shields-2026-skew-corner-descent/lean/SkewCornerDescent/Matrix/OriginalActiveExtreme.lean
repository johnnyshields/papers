/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.RemainingDualExposure
import SkewCornerDescent.Matrix.RemainingActualChambers
import SkewCornerDescent.FiniteExposurePeeling

/-!
# Original active extremes after finite peeling

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The finite peeling induction is assembled from the original dependent detector identities.
Remaining chambers, regular slices and inactive count invariants are all produced internally.
The chosen active-root extremality is the input supplied by the active-label selection.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- An actual root extreme among the active top-generator classes is the omitted class.
Every inactive exposure and finite-step detector transfer is invoked in the proof. -/
theorem originalChamber_active_extreme_is_omitted {α : Type*}
    [Fintype α] [DecidableEq α] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : ZMod (r * d) → α) (k : ℕ) (target : α) (htarget : top target = K)
    (hactive : classDefect word 1 d s (r * s - 1) 0 target ≠ 0)
    (hextreme : ∀ b, top b = K → classDefect word 1 d s (r * s - 1) 0 b ≠ 0 →
      b ≠ target → responseSign positive
        ((-MvPolynomial.eval x (realResiduePolynomial N (p target)) /
            MvPolynomial.eval x (realResiduePolynomial N (q target))) -
          (-MvPolynomial.eval x (realResiduePolynomial N (p b)) /
            MvPolynomial.eval x (realResiduePolynomial N (q b)))))
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
    word ((r * s - 1 : ℕ) : ZMod (r * d)) = target := by
  apply finite_inactive_peeling_reaches_active_extreme
    (classDefect word 1 d s (r * s - 1) 0)
    (fun a => -MvPolynomial.eval x (realResiduePolynomial N (p a)) /
      MvPolynomial.eval x (realResiduePolynomial N (q a)))
    (fun a => top a = K)
    (fun a => ∀ i, windowSum (classMask word a) 1 (r * s) i =
      windowSum (classMask word a) 1 (r * s - 1) 0)
    positive target (word ((r * s - 1 : ℕ) : ZMod (r * d))) hactive htarget hextreme
  intro S he hcount ht
  have hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K := ⟨⟨target, ht⟩, htarget⟩
  have hxS := simultaneousActualChamber_restrict S N K top p q positive x hx
  obtain ⟨a, horder, halternative⟩ := remainingActualChamber_dual_exposed_alternative
    hr hd hs S N K hNK top p q htop hNtop hp hq hq0 hanchor positive x hxS
    word k he hcount hshort hfull
  refine ⟨a.val.val, a.val.property, a.property, horder, ?_⟩
  rcases halternative with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr h

end SkewCornerDescent.Matrix
