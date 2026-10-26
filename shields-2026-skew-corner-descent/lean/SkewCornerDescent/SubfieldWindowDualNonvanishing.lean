/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealWindowDualNonvanishing
import SkewCornerDescent.SubfieldDualNonvanishing

/-!
# Literal dual inventories over real subfields

Formalizes the constant-field extension in `shields-2026-skew-corner-descent.tex`
(`thm:dual-general`). Faithful coefficient extension transports the actual cyclic
inventories, including every closure-word start. The real chamber and true-cap
normalization are produced by the real-coefficient theorem. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- A field homomorphism preserves the complete cyclic defect, including all wraps. -/
theorem map_windowDefect {α F G : Type*} [Fintype α] [Field F] [Field G]
    (ψ : F →+* G) {n : ℕ} [NeZero n] (f : ZMod n → F) (S : α → F)
    (e : α → ℤ) (b B j : ℕ) [NeZero B] :
    ψ (windowDefect f S e b B j) =
      windowDefect (ψ ∘ f) (ψ ∘ S) e b B j := by
  classical
  simp only [windowDefect, inverseWindowSum, windowProduct, map_sub, map_mul,
    map_natCast, map_intCast, map_sum, map_inv₀, map_prod, Function.comp_apply,
    closureWord, apply_ite]

/-- The literal dual-period conclusion holds over any constant field embedded in the
reals. No chamber, cap-sign, regularity, or inventory-clearing premise is left to supply. -/
theorem subfieldTrueCaps_windowDefect_nonvanishing {α c : Type*}
    [Fintype α] [DecidableEq α] [Field c]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (ρ : c →+* ℝ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ c)
    (htop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ)) (hq0 : ∀ a, q a ≠ 0)
    (closure left right : α) (hclosure : top closure = K)
    (hleft : top left < K) (hright : top right < K)
    (word : ZMod (r * d) → α) (label : α → c)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hdistinct : Function.Injective (fun a =>
      let φ := algebraMap (MvPolynomial ℕ c) (FractionRing (MvPolynomial ℕ c))
      φ (X (top a : ℕ)) + φ (p a) / φ (q a)))
    (hsource : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let φ := algebraMap (MvPolynomial ℕ c) (FractionRing (MvPolynomial ℕ c))
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      response a = response closure - φ (C (label a)) * (response left * response right))
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let φ := algebraMap (MvPolynomial ℕ c) (FractionRing (MvPolynomial ℕ c))
    let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
    let e := classDefect word 1 d s (r * s - 1) 0
    windowDefect (response ∘ word) response e (k * d + s)
        (k * (r * d) + r * s) (r * d) ≠ 0 ∨
      windowDefect (response ∘ word) response e (k * d + s)
        (k * (r * d) + r * s) (k * (r * d) + r * s) ≠ 0 := by
  classical
  let φ := algebraMap (MvPolynomial ℕ ℝ) (FractionRing (MvPolynomial ℕ ℝ))
  let ψ := realCoefficientExtension ρ
  have h := realTrueCaps_windowDefect_nonvanishing hr hd hs hsd hk φ
    (IsFractionRing.injective _ _) N K hNK top
    (fun a => MvPolynomial.map ρ (p a)) (fun a => MvPolynomial.map ρ (q a))
    htop
    (fun a j hj => hp a j (MvPolynomial.vars_map (p a) ρ hj))
    (fun a j hj => hq a j (MvPolynomial.vars_map (q a) ρ hj))
    (fun a => (map_ne_zero_iff _ (MvPolynomial.map_injective ρ ρ.injective)).mpr (hq0 a))
    closure left right hclosure hleft hright word (fun a => ρ (label a)) hactiveTop
    (by
      intro a b he
      apply hdistinct
      apply ψ.injective
      simpa only [ψ, map_add, map_div₀, realCoefficientExtension_polynomial,
        MvPolynomial.map_X] using he)
    (by
      intro a ha
      have he := congrArg ψ (hsource a ha)
      simpa only [ψ, map_add, map_sub, map_mul, map_div₀,
        realCoefficientExtension_polynomial, MvPolynomial.map_X,
        MvPolynomial.map_C] using he)
    htwo
  dsimp only
  by_contra hz
  obtain ⟨hn, hB⟩ := not_or.mp hz
  have hn := congrArg ψ (not_not.mp hn)
  have hB := congrArg ψ (not_not.mp hB)
  simp only [map_windowDefect, map_zero, Function.comp_def, ψ, map_add, map_div₀,
    realCoefficientExtension_polynomial, MvPolynomial.map_X] at hn hB
  exact h.elim (fun h => h hn) (fun h => h hB)

end SkewCornerDescent
