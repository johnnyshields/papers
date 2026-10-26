/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualCapFractions
import SkewCornerDescent.Matrix.ConstantActiveLabelDualNonvanishing

/-!
# Dual nonvanishing with the original true caps

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`).
The full source identities use the two original cap responses. The assembly produces
common affine representatives, regular cap denominators and positivity in both actual
chambers; finite inactive peeling supplies the two active exposure contradictions.
The literal chart's response classifier and detector interpretation remain the inputs
when applying this result to the manuscript's original defect. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- Two distinct active classes force nonvanishing of an original detector. Their labels
need not be supplied injective: full source-class separation produces injectivity.
Neither cap positivity nor a common affine denominator is a hypothesis. -/
theorem trueCaps_original_dual_nonvanishing {α : Type*}
    [Fintype α] [DecidableEq α] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0) (word : ZMod (r * d) → α) (k : ℕ)
    (closure left right : α) (hclosure : top closure = K)
    (hleft : top left < K) (hright : top right < K) (label : α → ℚ)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hdistinct : Function.Injective (fun a => residueGenerator N ⟨top a, htop a⟩ +
      algebraMap (OtherPolynomial N) (OtherField N) (p a) /
        algebraMap (OtherPolynomial N) (OtherField N) (q a)))
    (hsource : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let ι := algebraMap (OtherPolynomial N) (OtherField N)
      let response := fun a => residueGenerator N ⟨top a, htop a⟩ + ι (p a) / ι (q a)
      response a = response closure - (label a : OtherField N) *
        (response left * response right))
    (xnegative xpositive : ℕ → ℝ)
    (hxnegative : xnegative ∈ simultaneousActualChamber N K top p q false)
    (hxpositive : xpositive ∈ simultaneousActualChamber N K top p q true)
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
  let ι := algebraMap (OtherPolynomial N) (OtherField N)
  let cap := originalCapNumerator N top p q htop left right
  let capDen := originalCapDenominator N q left right
  let base := p closure * capDen
  let scaledCap := cap * q closure
  let scaleDen := capDen * q closure
  have hcap := originalCapFraction_eq N top p q htop left right (hq0 left) (hq0 right)
  have hnegative := simultaneousActualChamber_cap_fraction_pos N K hNK top p q htop
    hp hq left right hleft hright ⟨closure, hclosure⟩ false xnegative hxnegative
  have hpositive := simultaneousActualChamber_cap_fraction_pos N K hNK top p q htop
    hp hq left right hleft hright ⟨closure, hclosure⟩ true xpositive hxpositive
  have hqclosure : ι (q closure) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hq0 closure)
  have hcapDen : ι capDen ≠ 0 := by
    simp only [ι, capDen, originalCapDenominator, map_mul, map_pow]
    exact mul_ne_zero
      (pow_ne_zero 2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hq0 left)))
      (pow_ne_zero 2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hq0 right)))
  have haffine (a : α) (ha : classDefect word 1 d s (r * s - 1) 0 a ≠ 0) :
      residueGenerator N ⟨top a, htop a⟩ + ι (p a) / ι (q a) =
        residueGenerator N ⟨top a, htop a⟩ + ι base / ι scaleDen -
          (label a : OtherField N) * (ι scaledCap / ι scaleDen) := by
    have he := hsource a ha
    dsimp only at he hcap
    rw [← hcap] at he
    have hgen : residueGenerator N ⟨top closure, htop closure⟩ =
        residueGenerator N ⟨top a, htop a⟩ := by
      congr 1
      exact Subtype.ext (hclosure.trans (hactiveTop a ha).symm)
    rw [hgen] at he
    rw [he]
    simp only [base, scaleDen, scaledCap, map_mul]
    dsimp only [ι, cap, capDen] at hqclosure hcapDen ⊢
    field_simp [hqclosure, hcapDen]
  have hlabels (a b : α) (ha : classDefect word 1 d s (r * s - 1) 0 a ≠ 0)
      (hb : classDefect word 1 d s (r * s - 1) 0 b ≠ 0) (hab : label a = label b) : a = b := by
    apply hdistinct
    have he := hsource a ha
    have hf := hsource b hb
    dsimp only at he hf
    rw [hab] at he
    exact he.trans hf.symm
  have hscaled (positive : Bool) (x : ℕ → ℝ)
      (hx : x ∈ simultaneousActualChamber N K top p q positive)
      (hc : MvPolynomial.eval x (realResiduePolynomial N capDen) ≠ 0 ∧
        0 < MvPolynomial.eval x (realResiduePolynomial N cap) /
          MvPolynomial.eval x (realResiduePolynomial N capDen)) :
      MvPolynomial.eval x (realResiduePolynomial N scaleDen) ≠ 0 ∧
        0 < MvPolynomial.eval x (realResiduePolynomial N scaledCap) /
          MvPolynomial.eval x (realResiduePolynomial N scaleDen) := by
    have hqc := hx.1 ⟨closure, hclosure⟩
    constructor
    · simpa only [scaleDen, map_mul] using mul_ne_zero hc.1 hqc
    · simpa only [scaledCap, scaleDen, map_mul, mul_div_mul_right _ _ hqc] using hc.2
  have hn := hscaled false xnegative hxnegative hnegative
  have hp' := hscaled true xpositive hxpositive hpositive
  exact constantActiveLabels_original_dual_nonvanishing hr hd hs N K hNK
    top p q htop hNtop hp hq hq0 word k label base scaledCap scaleDen hactiveTop hlabels
    haffine xnegative xpositive hxnegative hxpositive hn.1 hp'.1 hn.2 hp'.2 htwo

end SkewCornerDescent.Matrix
