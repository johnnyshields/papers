/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.SubfieldDualNonvanishing
import SkewCornerDescent.CyclicWindowNonvanishing

/-!
# Literal dual inventories under the scalar exposure hypotheses

Formalizes `shields-2026-skew-corner-descent.tex` (`thm:dual-general`). The
hypotheses specify the dependent triangular responses, their two exposure
chambers, and the common positive affine scale. No actual corner realization,
coprimality, or geometric gap is required. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- The scalar exposure contract implies nonvanishing of the literal period/last-window
pair over every real subfield. Source units, class balance, and reversible clearing
are established internally from the supplied chambers and literal word. -/
theorem subfieldExposure_inventories_nonvanishing {α c : Type*}
    [Fintype α] [DecidableEq α] [Field c]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (ρ : c →+* ℝ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ c)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ))
    (word : ZMod (r * d) → α) (label : α → c)
    (base cap scaleDen : MvPolynomial ℕ c)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hlabels : ∀ a b, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0 → label a = label b → a = b)
    (hsourceAffine : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let φ := algebraMap (MvPolynomial ℕ c) (FractionRing (MvPolynomial ℕ c))
      φ (X (top a : ℕ)) + φ (p a) / φ (q a) =
        φ (X (top a : ℕ)) + φ base / φ scaleDen - φ (C (label a)) * (φ cap / φ scaleDen))
    (xnegative xpositive : ℕ → ℝ)
    (hxnegative : xnegative ∈ simultaneousRealChamber K top
      (fun a => MvPolynomial.map ρ (p a)) (fun a => MvPolynomial.map ρ (q a)) false)
    (hxpositive : xpositive ∈ simultaneousRealChamber K top
      (fun a => MvPolynomial.map ρ (p a)) (fun a => MvPolynomial.map ρ (q a)) true)
    (hscaleNegative : eval xnegative (MvPolynomial.map ρ scaleDen) ≠ 0)
    (hscalePositive : eval xpositive (MvPolynomial.map ρ scaleDen) ≠ 0)
    (hcapnegative : 0 < eval xnegative (MvPolynomial.map ρ cap) /
      eval xnegative (MvPolynomial.map ρ scaleDen))
    (hcappositive : 0 < eval xpositive (MvPolynomial.map ρ cap) /
      eval xpositive (MvPolynomial.map ρ scaleDen))
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let φ := algebraMap (MvPolynomial ℕ c) (FractionRing (MvPolynomial ℕ c))
    let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
    let e := classDefect word 1 d s (r * s - 1) 0
    windowDefect (response ∘ word) response e (k * d + s)
        (k * (r * d) + r * s) (r * d) ≠ 0 ∨
      lastWindowDefect (response ∘ word) response e (k * d + s)
        (k * (r * d) + r * s) ≠ 0 := by
  classical
  let _ : CharZero c := ρ.charZero
  let φ := algebraMap (MvPolynomial ℕ c) (FractionRing (MvPolynomial ℕ c))
  let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
  obtain ⟨u, v, huv, heu, hev⟩ := htwo
  have ⟨_, hreal⟩ := simultaneousRealChamber_source_regular
    (algebraMap (MvPolynomial ℕ ℝ) (FractionRing (MvPolynomial ℕ ℝ)))
    (IsFractionRing.injective _ _) N K hNK top
    (fun a => MvPolynomial.map ρ (p a)) (fun a => MvPolynomial.map ρ (q a))
    (fun a j hj => hp a j (MvPolynomial.vars_map (p a) ρ hj))
    (fun a j hj => hq a j (MvPolynomial.vars_map (q a) ρ hj))
    ⟨u, hactiveTop u heu⟩ false xnegative hxnegative
  have hreg (a : α) : response a ≠ 0 := by
    intro hz
    apply hreal a
    have he := congrArg (realCoefficientExtension ρ) hz
    simpa only [response, φ, map_add, map_div₀, map_zero,
      realCoefficientExtension_polynomial, MvPolynomial.map_X] using he
  have hcore := subfieldActiveLabels_dual_nonvanishing hr hd hs ρ N K hNK top p q
    hp hq word k label base cap scaleDen hactiveTop hlabels hsourceAffine
    xnegative xpositive hxnegative hxpositive hscaleNegative hscalePositive
    hcapnegative hcappositive ⟨u, v, huv, heu, hev⟩
  exact cleared_dual_implies_window_nonvanishing hr hs hsd hk word response hreg hcore

end SkewCornerDescent
