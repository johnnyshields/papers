/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealTrueCapChambers

/-!
# Real dual nonvanishing with produced chambers and true caps

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-general`).
A faithful finite triangular response family supplies both simultaneous chambers.
The true lower caps produce the common positive scale; the active affine identities
then invoke the complete two-extreme peeling assembly. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- Distinct dependent triangular responses with two active affine classes have a nonzero
complete detector. Every chamber point, source regularity and positive cap product is
produced in the proof, including families with irrational real coefficients. -/
theorem realTrueCaps_dual_nonvanishing {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (htop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ)) (hq0 : ∀ a, q a ≠ 0)
    (closure left right : α) (hclosure : top closure = K)
    (hleft : top left < K) (hright : top right < K)
    (word : ZMod (r * d) → α) (l : ℕ) (label : α → ℝ)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hdistinct : Function.Injective (fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)))
    (hsource : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      response a = response closure - φ (C (label a)) * (response left * response right))
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
    ((s : F) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
      (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) ≠ 0) ∨
    ((r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (l - 1) *
        windowProduct (response ∘ word) 1 (r * s - 1) 0 -
      (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((l - 1) * (r * d) + r * s) i) ≠ 0) := by
  classical
  have hqφ (a : α) : φ (q a) ≠ 0 := (map_ne_zero_iff _ hφ).mpr (hq0 a)
  have hdiff : ∀ a b, top a = K → top b = K → a ≠ b →
      p a * q b - p b * q a ≠ 0 := by
    intro a b ha hb hab hz
    apply hab
    apply hdistinct
    have he := congrArg φ hz
    simp only [map_sub, map_mul, map_zero] at he
    dsimp only
    rw [ha, hb]
    congr 1
    apply (div_eq_div_iff (hqφ a) (hqφ b)).mpr
    exact sub_eq_zero.mp he
  obtain ⟨xn, hxn⟩ := (simultaneousRealChamber_open_nonempty N K hNK top p q
    htop hp hq hq0 hdiff false).2
  obtain ⟨xp, hxp⟩ := (simultaneousRealChamber_open_nonempty N K hNK top p q
    htop hp hq hq0 hdiff true).2
  let base := p closure * q left * q right
  let cap := (X (top left : ℕ) * q left + p left) *
    (X (top right : ℕ) * q right + p right) * q closure
  let scaleDen := q closure * q left * q right
  have hcaps (positive : Bool) (x : ℕ → ℝ)
      (hx : x ∈ simultaneousRealChamber K top p q positive) :
      eval x scaleDen ≠ 0 ∧ 0 < eval x cap / eval x scaleDen := by
    obtain ⟨hc, hl, hr, hpos⟩ := simultaneousRealChamber_true_cap_product N K hNK
      top p q htop hp hq closure left right hclosure hleft hright positive x hx
    refine ⟨by simpa only [scaleDen, map_mul] using mul_ne_zero (mul_ne_zero hc hl) hr, ?_⟩
    have heq : eval x cap / eval x scaleDen =
        rationalTriangularResponse (top left : ℕ) (p left) (q left) x *
          rationalTriangularResponse (top right : ℕ) (p right) (q right) x := by
      simp only [cap, scaleDen, map_mul, map_add, eval_X, rationalTriangularResponse]
      field_simp [hc, hl, hr]
    rw [heq]
    exact hpos
  have hn := hcaps false xn hxn
  have hp' := hcaps true xp hxp
  apply realActiveLabels_dual_nonvanishing hr hd hs φ hφ N K hNK top p q hp hq word l
    label base cap scaleDen hactiveTop
  · intro a b ha hb he
    apply hdistinct
    rw [hsource a ha, hsource b hb, he]
  · intro a ha
    have he := hsource a ha
    dsimp only at he
    rw [he]
    simp only [base, cap, scaleDen, map_mul, map_add]
    rw [hactiveTop a ha, hclosure]
    field_simp [hqφ closure, hqφ left, hqφ right]
  · exact hxn
  · exact hxp
  · exact hn.1
  · exact hp'.1
  · exact hn.2
  · exact hp'.2
  · exact htwo

end SkewCornerDescent
