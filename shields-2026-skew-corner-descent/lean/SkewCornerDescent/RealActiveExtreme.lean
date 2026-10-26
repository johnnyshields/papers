/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealDualExposure
import SkewCornerDescent.FiniteExposurePeeling

/-!
# Real active extremes under complete detector vanishing

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-general`).
The finite induction invokes each regularity, specialization and exposure producer.
No source nonzero premise or inactive count identity remains a binder. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- Any active top-root extreme is the omitted class when both complete detectors vanish. -/
theorem realChamber_active_extreme_is_omitted {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ))
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K top p q positive)
    (word : ZMod (r * d) → α) (k : ℕ) (target : α) (htarget : top target = K)
    (hactive : classDefect word 1 d s (r * s - 1) 0 target ≠ 0)
    (hextreme : ∀ b, top b = K → classDefect word 1 d s (r * s - 1) 0 b ≠ 0 →
      b ≠ target → responseSign positive
        ((-eval x (p target) / eval x (q target)) - (-eval x (p b) / eval x (q b))))
    (hshort :
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      (s : F) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) = 0)
    (hfull :
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      (r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
          windowProduct (response ∘ word) 1 (r * s - 1) 0 -
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) = 0) :
    word ((r * s - 1 : ℕ) : ZMod (r * d)) = target := by
  obtain ⟨hqφ, hresponse⟩ := simultaneousRealChamber_source_regular φ hφ N K hNK
    top p q hp hq ⟨target, htarget⟩ positive x hx
  apply finite_inactive_peeling_reaches_active_extreme
    (classDefect word 1 d s (r * s - 1) 0)
    (fun a => -eval x (p a) / eval x (q a))
    (fun a => top a = K)
    (fun a => ∀ i, windowSum (classMask word a) 1 (r * s) i =
      windowSum (classMask word a) 1 (r * s - 1) 0)
    positive target (word ((r * s - 1 : ℕ) : ZMod (r * d))) hactive htarget hextreme
  intro S he hcount ht
  have hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K := ⟨⟨target, ht⟩, htarget⟩
  have hxS := simultaneousRealChamber_restrict S K top p q positive x hx
  obtain ⟨a, horder, halternative⟩ := remainingRealChamber_dual_exposed_alternative
    hr hd hs φ hφ S N K hNK top p q hp hq hqφ hresponse hanchor positive x hxS
    word k he hcount hshort hfull
  refine ⟨a.val.val, a.val.property, a.property, horder, ?_⟩
  rcases halternative with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr h

end SkewCornerDescent
