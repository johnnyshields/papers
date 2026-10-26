/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.TrueCapDualNonvanishing

/-!
# Dual detectors on a complete original matrix response family

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`).
Complete original Jacobi--Trudi matrices produce the faithful representatives and both
actual chambers. Original true caps then produce the common affine denominator and its
positive cap quotient. The active-class identities are the response classifier's output;
no representative family, chamber, cap sign or inactive exposure is assumed here.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Dual nonvanishing for unchanged complete original interval responses. The active
classification and cyclic word are retained explicitly; the literal-window inventory
must supply them when this declaration is used for the manuscript's original defect. -/
theorem originalMatrices_dual_nonvanishing {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (n : α → ℕ) (P : ∀ i, Profile (n i))
    (row col : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (top : α → ℕ+) (htop : ∀ i, c.top < top i)
    (hindices : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (row i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (col i))) = (top i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ))
    (K : ℕ+) (closure left right : α) (hclosure : top closure = K)
    (hleft : top left < K) (hright : top right < K)
    (word : ZMod (r * d) → α) (k : ℕ) (label : α → ℚ)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hdistinct : Function.Injective (fun a =>
      c.regularResidue (c.originalLocalResponse (P a) (row a) (col a))))
    (hsource : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let response := fun a => c.regularResidue (c.originalLocalResponse (P a) (row a) (col a))
      response a = response closure - (label a : OtherField c.top) *
        (response left * response right))
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let response := fun a => c.regularResidue (c.originalLocalResponse (P a) (row a) (col a))
    ((s : OtherField c.top) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
      (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : OtherField c.top) *
          (response a)⁻¹) ≠ 0) ∨
    ((r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 (r * s - 1) 0 -
      (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : OtherField c.top) *
        (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * (r * d) + r * s) i) ≠ 0) := by
  classical
  obtain ⟨p, q, hp, hq, he, hchambers⟩ :=
    c.originalResponses_simultaneous_chambers n P row col top htop hindices hmax K
      ⟨closure, hclosure⟩ (fun a b _ _ hab => fun heq => hab (hdistinct heq))
  obtain ⟨xn, hxn⟩ := (hchambers false).2
  obtain ⟨xp, hxp⟩ := (hchambers true).2
  have hq0 (i : α) : q i ≠ 0 := by
    intro hz
    by_cases hi : top i = K
    · have h := hxn.1 ⟨i, hi⟩
      dsimp only at h
      rw [hz, map_zero, map_zero] at h
      exact h rfl
    · have h := (hxn.2.2 ⟨closure, hclosure⟩ ⟨i, hi⟩).1
      dsimp only at h
      rw [hz, map_zero, map_zero] at h
      exact h rfl
  have hinj : Function.Injective (fun a => residueGenerator c.top ⟨top a, ne_of_gt (htop a)⟩ +
      algebraMap (OtherPolynomial c.top) (OtherField c.top) (p a) /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (q a)) := by
    intro a b hab
    apply hdistinct
    dsimp only at hab ⊢
    rw [he a, he b]
    exact hab
  have hactive (a : α) (ha : classDefect word 1 d s (r * s - 1) 0 a ≠ 0) :
      let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
      let response := fun a => residueGenerator c.top ⟨top a, ne_of_gt (htop a)⟩ +
        ι (p a) / ι (q a)
      response a = response closure - (label a : OtherField c.top) *
        (response left * response right) := by
    simpa only [he] using hsource a ha
  have h := trueCaps_original_dual_nonvanishing hr hd hs c.top K
    (by simpa only [hclosure] using (htop closure).le) top p q
    (fun a => ne_of_gt (htop a)) (fun a => (htop a).le) hp hq hq0 word k closure left right
    hclosure hleft hright label hactiveTop hinj hactive xn xp hxn hxp htwo
  have hefamily : (fun a => residueGenerator c.top ⟨top a, ne_of_gt (htop a)⟩ +
      algebraMap (OtherPolynomial c.top) (OtherField c.top) (p a) /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (q a)) =
      (fun a => c.regularResidue (c.originalLocalResponse (P a) (row a) (col a))) :=
    funext (fun a => (he a).symm)
  simpa only [hefamily, ← he] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
