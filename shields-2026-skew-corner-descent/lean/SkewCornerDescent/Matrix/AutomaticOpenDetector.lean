/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ConstantActiveLabelDualNonvanishing

/-!
# Automatic short cancellation and full-period nonvanishing

Supports `shields-2026-skew-corner-descent.tex` (`cor:automatic-open`).
For multiplicity and positive remainder both one, the short detector cancels by the
complete literal class counts. The produced dual nonvanishing therefore belongs to
the full-period detector. Original normal coefficients still require the actual
span-bin transfer. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- Distinct active constant labels force the full-period detector to be nonzero in the
one-position short-remainder case. The short zero identity is proved internally from
literal counts, and all inactive exposures are supplied by the dual assembly. -/
theorem constantActiveLabels_automatic_full_nonvanishing {α : Type*}
    [Fintype α] [DecidableEq α] {d : ℕ} [NeZero (1 * d)] (hd : 0 < d)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0) (word : ZMod (1 * d) → α) (k : ℕ)
    (label : α → ℚ) (base cap scaleDen : OtherPolynomial N)
    (hactiveTop : ∀ a, classDefect word 1 d 1 0 0 a ≠ 0 → top a = K)
    (hlabels : ∀ a b, classDefect word 1 d 1 0 0 a ≠ 0 →
      classDefect word 1 d 1 0 0 b ≠ 0 → label a = label b → a = b)
    (hsourceAffine : ∀ a, classDefect word 1 d 1 0 0 a ≠ 0 →
      let ι := algebraMap (OtherPolynomial N) (OtherField N)
      residueGenerator N ⟨top a, htop a⟩ + ι (p a) / ι (q a) =
        residueGenerator N ⟨top a, htop a⟩ + ι base / ι scaleDen -
          (label a : OtherField N) * (ι cap / ι scaleDen))
    (xnegative xpositive : ℕ → ℝ)
    (hxnegative : xnegative ∈ simultaneousActualChamber N K top p q false)
    (hxpositive : xpositive ∈ simultaneousActualChamber N K top p q true)
    (hscaleNegative : MvPolynomial.eval xnegative (realResiduePolynomial N scaleDen) ≠ 0)
    (hscalePositive : MvPolynomial.eval xpositive (realResiduePolynomial N scaleDen) ≠ 0)
    (hcapnegative : 0 < MvPolynomial.eval xnegative (realResiduePolynomial N cap) /
      MvPolynomial.eval xnegative (realResiduePolynomial N scaleDen))
    (hcappositive : 0 < MvPolynomial.eval xpositive (realResiduePolynomial N cap) /
      MvPolynomial.eval xpositive (realResiduePolynomial N scaleDen))
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d 1 0 0 a ≠ 0 ∧
      classDefect word 1 d 1 0 0 b ≠ 0) :
    let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
      algebraMap (OtherPolynomial N) (OtherField N) (p a) /
        algebraMap (OtherPolynomial N) (OtherField N) (q a)
    ((d * d : ℕ) : OtherField N) *
        (windowProduct (response ∘ word) 1 d 0) ^ (k - 1) -
      (∑ a, (classDefect word 1 d 1 0 0 a : OtherField N) * (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * d + 1) i) ≠ 0 := by
  dsimp only
  have hdual := constantActiveLabels_original_dual_nonvanishing
    (r := 1) (s := 1) (by decide) hd (by decide) N K hNK top p q htop hNtop
    hp hq hq0 word k label base cap scaleDen hactiveTop hlabels hsourceAffine
    xnegative xpositive hxnegative hxpositive hscaleNegative hscalePositive
    hcapnegative hcappositive htwo
  dsimp only at hdual
  let response := fun a => residueGenerator N ⟨top a, htop a⟩ +
    algebraMap (OtherPolynomial N) (OtherField N) (p a) /
      algebraMap (OtherPolynomial N) (OtherField N) (q a)
  have hshort := one_position_short_detector_zero word response 1 d 0
  have hprefix : windowProduct (response ∘ word) 1 0 (0 : ZMod (1 * d)) = 1 := by
    simp only [windowProduct, Finset.range_zero, Finset.prod_empty]
  simp only [hprefix, inv_one, one_mul] at hshort
  dsimp only [response] at hshort hprefix
  simpa only [Nat.one_mul, Nat.sub_self, Nat.cast_one, one_mul, hprefix,
    inv_one, mul_one, hshort, ne_eq, not_true_eq_false, false_or] using hdual

end SkewCornerDescent.Matrix
