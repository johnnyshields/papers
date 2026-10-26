/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealActiveLabels
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Dual detector nonvanishing over real constant subfields

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-general`).
An embedding of the constant field into the reals induces a faithful coefficient
extension of its multivariate fraction field. The complete dependent expressions,
including their whole-cycle powers, are transferred before invoking real peeling.
Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- Faithful extension of a multivariate fraction field along a real constant embedding. -/
noncomputable def realCoefficientExtension {k : Type*} [Field k] (ρ : k →+* ℝ) :
    FractionRing (MvPolynomial ℕ k) →+* FractionRing (MvPolynomial ℕ ℝ) :=
  IsFractionRing.lift (K := FractionRing (MvPolynomial ℕ k))
    (g := (algebraMap (MvPolynomial ℕ ℝ) (FractionRing (MvPolynomial ℕ ℝ))).comp
      (MvPolynomial.map ρ))
    ((IsFractionRing.injective (MvPolynomial ℕ ℝ) (FractionRing (MvPolynomial ℕ ℝ))).comp
      (MvPolynomial.map_injective ρ ρ.injective))

/-- Coefficient extension agrees with the polynomial coefficient map. -/
@[simp] theorem realCoefficientExtension_polynomial {k : Type*} [Field k]
    (ρ : k →+* ℝ) (p : MvPolynomial ℕ k) :
    realCoefficientExtension ρ (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k)) p) =
      algebraMap (MvPolynomial ℕ ℝ) (FractionRing (MvPolynomial ℕ ℝ)) (MvPolynomial.map ρ p) := by
  simp only [realCoefficientExtension, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

/-- Dual nonvanishing holds over every constant field embedded into the reals, without
coprimality or a lower bound on the separation. The chamber and affine identities are
those of the same dependent family, not independently chosen response variables. -/
theorem subfieldActiveLabels_dual_nonvanishing {α k : Type*}
    [Fintype α] [DecidableEq α] [Field k] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s) (ρ : k →+* ℝ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ k)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ))
    (word : ZMod (r * d) → α) (l : ℕ) (label : α → k)
    (base cap scaleDen : MvPolynomial ℕ k)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hlabels : ∀ a b, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0 → label a = label b → a = b)
    (hsourceAffine : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let φ := algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))
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
    let φ := algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))
    let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
    ((s : FractionRing (MvPolynomial ℕ k)) *
      (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
      (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : FractionRing (MvPolynomial ℕ k)) *
          (response a)⁻¹) ≠ 0) ∨
    ((r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (l - 1) *
        windowProduct (response ∘ word) 1 (r * s - 1) 0 -
      (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : FractionRing (MvPolynomial ℕ k)) *
        (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((l - 1) * (r * d) + r * s) i) ≠ 0) := by
  classical
  let φ := algebraMap (MvPolynomial ℕ ℝ) (FractionRing (MvPolynomial ℕ ℝ))
  have h := realActiveLabels_dual_nonvanishing hr hd hs φ
    (IsFractionRing.injective _ _) N K hNK top
    (fun a => MvPolynomial.map ρ (p a)) (fun a => MvPolynomial.map ρ (q a))
    (fun a j hj => hp a j (MvPolynomial.vars_map (p a) ρ hj))
    (fun a j hj => hq a j (MvPolynomial.vars_map (q a) ρ hj))
    word l (fun a => ρ (label a))
    (MvPolynomial.map ρ base) (MvPolynomial.map ρ cap) (MvPolynomial.map ρ scaleDen)
    hactiveTop
    (by intro a b ha hb he; exact hlabels a b ha hb (ρ.injective he))
    (by
      intro a ha
      have he := congrArg (realCoefficientExtension ρ) (hsourceAffine a ha)
      simpa only [map_add, map_sub, map_mul, map_div₀, realCoefficientExtension_polynomial,
        MvPolynomial.map_X, MvPolynomial.map_C] using he)
    xnegative xpositive hxnegative hxpositive hscaleNegative hscalePositive
    hcapnegative hcappositive htwo
  dsimp only
  by_contra hz
  obtain ⟨hshort, hfull⟩ := not_or.mp hz
  have hshort := congrArg (realCoefficientExtension ρ) (not_not.mp hshort)
  have hfull := congrArg (realCoefficientExtension ρ) (not_not.mp hfull)
  simp only [map_sub, map_mul, map_sum, map_inv₀, map_pow, map_natCast, map_intCast,
    map_zero, windowProduct, map_prod, Function.comp_apply, map_add, map_div₀,
    realCoefficientExtension_polynomial, MvPolynomial.map_X] at hshort hfull
  exact h.elim (fun hn => hn hshort) (fun hn => hn hfull)

end SkewCornerDescent
