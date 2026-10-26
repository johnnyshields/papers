/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalActiveExtreme
import SkewCornerDescent.Matrix.OriginalActiveAffineRepresentatives

/-!
# Original dual nonvanishing with constant active labels

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`, `thm:dual-general`).
The active affine identities preserve the identities of both active extremes across two
actual chambers. Finite inactive peeling then forces both extremes into the omitted slot.
No coprimality is required: finite replacement uses the inactive constant-count
identity, while the mask's actual gcd period remains available separately.
The response classifier and literal-chart inventory must supply the affine identities and
the detector interpretation when this assembly is applied to the manuscript's chart.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows PhaseInventory
open scoped BigOperators

/-- Original dependent response detectors cannot both vanish when two active affine classes
have distinct rational labels and the cap product is positive in both actual chambers.
The only root-order input is the active affine identity; both extrema and every intervening
inactive exposure are produced inside this assembly. -/
theorem constantActiveLabels_original_dual_nonvanishing {α : Type*}
    [Fintype α] [DecidableEq α] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0) (word : ZMod (r * d) → α) (k : ℕ)
    (label : α → ℚ) (base cap scaleDen : OtherPolynomial N)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hlabels : ∀ a b, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0 → label a = label b → a = b)
    (hsourceAffine : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
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
  classical
  dsimp only
  by_contra h
  obtain ⟨hshort, hfull⟩ := not_or.mp h
  have hshort := not_not.mp hshort
  have hfull := not_not.mp hfull
  let e := classDefect word 1 d s (r * s - 1) 0
  let active := {a : α // e a ≠ 0}
  obtain ⟨u, v, huv, heu, hev⟩ := htwo
  let _ : Nonempty active := ⟨⟨u, heu⟩⟩
  have hscale0 : scaleDen ≠ 0 := by
    intro hz
    exact hscaleNegative (by rw [hz, map_zero, map_zero])
  have haffine (a : α) (ha : e a ≠ 0) :=
    original_active_affine_representative N (top a) (htop a) (p a) (q a)
      base cap scaleDen (label a) (hq0 a) hscale0 (hsourceAffine a ha)
  have hinj : Function.Injective (fun a : active => (label a.val : ℝ)) := by
    intro a b hab
    change (label a.val : ℝ) = (label b.val : ℝ) at hab
    apply Subtype.ext
    exact hlabels a.val b.val a.property b.property (by exact_mod_cast hab)
  obtain ⟨least, hleast⟩ := exists_least_anchor_label
    (fun a : active => (label a.val : ℝ)) hinj
  obtain ⟨greatest, hgreatest⟩ := exists_greatest_anchor_label
    (fun a : active => (label a.val : ℝ)) hinj
  have hleastOmitted := originalChamber_active_extreme_is_omitted
    hr hd hs N K hNK top p q htop hNtop hp hq hq0 false xnegative hxnegative
    word k least.val (hactiveTop least.val least.property) least.property (by
      intro b hb heb hne
      have hba : (⟨b, heb⟩ : active) ≠ least := fun hz => hne (congrArg Subtype.val hz)
      apply sub_neg.mpr
      apply actual_anchor_root_order_of_labels _ _ _ _ (realResiduePolynomial N base)
        (realResiduePolynomial N cap) (realResiduePolynomial N scaleDen)
        (label least.val) (label b)
        xnegative (haffine least.val least.property) (haffine b heb)
        (hxnegative.1 ⟨least.val, hactiveTop least.val least.property⟩)
        (hxnegative.1 ⟨b, hb⟩) hscaleNegative hcapnegative
      exact_mod_cast hleast ⟨b, heb⟩ hba) hshort hfull
  have hgreatestOmitted := originalChamber_active_extreme_is_omitted
    hr hd hs N K hNK top p q htop hNtop hp hq hq0 true xpositive hxpositive
    word k greatest.val (hactiveTop greatest.val greatest.property) greatest.property (by
      intro b hb heb hne
      have hba : (⟨b, heb⟩ : active) ≠ greatest := fun hz => hne (congrArg Subtype.val hz)
      apply sub_pos.mpr
      apply actual_anchor_root_order_of_labels _ _ _ _ (realResiduePolynomial N base)
        (realResiduePolynomial N cap) (realResiduePolynomial N scaleDen)
        (label b) (label greatest.val) xpositive (haffine b heb)
        (haffine greatest.val greatest.property)
        (hxpositive.1 ⟨b, hb⟩)
        (hxpositive.1 ⟨greatest.val, hactiveTop greatest.val greatest.property⟩)
        hscalePositive hcappositive
      exact_mod_cast hgreatest ⟨b, heb⟩ hba) hshort hfull
  have heq : least = greatest :=
    Subtype.ext (hleastOmitted.symm.trans hgreatestOmitted)
  have hother : ∃ a : active, a ≠ least := by
    by_cases hu : u = least.val
    · refine ⟨⟨v, hev⟩, ?_⟩
      intro hz
      exact huv (hu.trans (congrArg Subtype.val hz).symm)
    · exact ⟨⟨u, heu⟩, fun hz => hu (congrArg Subtype.val hz)⟩
  obtain ⟨a, ha⟩ := hother
  have hlo := hleast a ha
  have hhi := hgreatest a (heq ▸ ha)
  rw [← heq] at hhi
  exact (not_lt_of_gt hlo) hhi

end SkewCornerDescent.Matrix
