/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealActiveExtreme

/-!
# Dual nonvanishing for distinct real active labels

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-general`).
The same active label identities hold at both real chambers. The proof chooses the
least and greatest labels and invokes the complete finite peeling chain for each.
Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- Faithfulness turns a monic source affine identity into its cleared polynomial identity. -/
theorem real_source_affine_identity {F : Type*} [Field F]
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (K : ℕ+) (p q base cap scaleDen : MvPolynomial ℕ ℝ) (label : ℝ)
    (hq : φ q ≠ 0) (hscale : φ scaleDen ≠ 0)
    (hidentity : φ (X (K : ℕ)) + φ p / φ q =
      φ (X (K : ℕ)) + φ base / φ scaleDen - φ (C label) * (φ cap / φ scaleDen)) :
    p * scaleDen = (base - C label * cap) * q := by
  apply hφ
  simp only [map_mul, map_sub]
  have he : φ p / φ q = φ base / φ scaleDen - φ (C label) * (φ cap / φ scaleDen) := by
    linear_combination hidentity
  field_simp [hq, hscale] at he
  linear_combination he

/-- A real constant active label determines its actual root at every regular assignment. -/
theorem real_anchor_root_eq_affine_label
    (p q base cap scaleDen : MvPolynomial ℕ ℝ) (label : ℝ) (x : ℕ → ℝ)
    (hidentity : p * scaleDen = (base - C label * cap) * q)
    (hq : eval x q ≠ 0) (hscale : eval x scaleDen ≠ 0) :
    -eval x p / eval x q = label * (eval x cap / eval x scaleDen) -
      eval x base / eval x scaleDen := by
  have he := congrArg (eval x) hidentity
  simp only [map_mul, map_sub, eval_C] at he
  field_simp [hq, hscale]
  nlinarith [he]

/-- Positive cap products preserve the order of arbitrary real active labels. -/
theorem real_anchor_root_order_of_labels
    (pa qa pb qb base cap scaleDen : MvPolynomial ℕ ℝ) (la lb : ℝ) (x : ℕ → ℝ)
    (ha : pa * scaleDen = (base - C la * cap) * qa)
    (hb : pb * scaleDen = (base - C lb * cap) * qb)
    (hqa : eval x qa ≠ 0) (hqb : eval x qb ≠ 0) (hscale : eval x scaleDen ≠ 0)
    (hcap : 0 < eval x cap / eval x scaleDen) (hlab : la < lb) :
    -eval x pa / eval x qa < -eval x pb / eval x qb := by
  rw [real_anchor_root_eq_affine_label pa qa base cap scaleDen la x ha hqa hscale,
    real_anchor_root_eq_affine_label pb qb base cap scaleDen lb x hb hqb hscale]
  exact sub_lt_sub_right (mul_lt_mul_of_pos_right hlab hcap) _

/-- The two complete detectors cannot both vanish for distinct real active labels.
Source regularity and the two affine root orders are produced inside the proof. -/
theorem realActiveLabels_dual_nonvanishing {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] {r d s : ℕ} [NeZero (r * d)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ))
    (word : ZMod (r * d) → α) (k : ℕ) (label : α → ℝ)
    (base cap scaleDen : MvPolynomial ℕ ℝ)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hlabels : ∀ a b, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0 → label a = label b → a = b)
    (hsourceAffine : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      φ (X (top a : ℕ)) + φ (p a) / φ (q a) =
        φ (X (top a : ℕ)) + φ base / φ scaleDen - φ (C (label a)) * (φ cap / φ scaleDen))
    (xnegative xpositive : ℕ → ℝ)
    (hxnegative : xnegative ∈ simultaneousRealChamber K top p q false)
    (hxpositive : xpositive ∈ simultaneousRealChamber K top p q true)
    (hscaleNegative : eval xnegative scaleDen ≠ 0)
    (hscalePositive : eval xpositive scaleDen ≠ 0)
    (hcapnegative : 0 < eval xnegative cap / eval xnegative scaleDen)
    (hcappositive : 0 < eval xpositive cap / eval xpositive scaleDen)
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
    ((s : F) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
      (r * s : ℕ) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
        (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) ≠ 0) ∨
    ((r * d * d : ℕ) * (windowProduct (response ∘ word) 1 (r * d) 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 (r * s - 1) 0 -
      (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : F) * (response a)⁻¹) *
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
  obtain ⟨hqφ, _⟩ := simultaneousRealChamber_source_regular φ hφ N K hNK top p q hp hq
    ⟨u, hactiveTop u heu⟩ false xnegative hxnegative
  have hscale0 : scaleDen ≠ 0 := by
    intro hz
    exact hscaleNegative (by rw [hz, map_zero])
  have hscaleφ : φ scaleDen ≠ 0 := (map_ne_zero_iff _ hφ).mpr hscale0
  have haffine (a : α) (ha : e a ≠ 0) := real_source_affine_identity φ hφ
    (top a) (p a) (q a) base cap scaleDen (label a) (hqφ a) hscaleφ (hsourceAffine a ha)
  have hinj : Function.Injective (fun a : active => label a.val) := by
    intro a b hab
    exact Subtype.ext (hlabels a.val b.val a.property b.property hab)
  obtain ⟨least, hleast⟩ := exists_least_anchor_label (fun a : active => label a.val) hinj
  obtain ⟨greatest, hgreatest⟩ := exists_greatest_anchor_label (fun a : active => label a.val) hinj
  have hleastOmitted := realChamber_active_extreme_is_omitted
    hr hd hs φ hφ N K hNK top p q hp hq false xnegative hxnegative
    word k least.val (hactiveTop least.val least.property) least.property (by
      intro b hb heb hne
      have hba : (⟨b, heb⟩ : active) ≠ least := fun hz => hne (congrArg Subtype.val hz)
      apply sub_neg.mpr
      exact real_anchor_root_order_of_labels _ _ _ _ base cap scaleDen
        (label least.val) (label b) xnegative (haffine least.val least.property) (haffine b heb)
        (hxnegative.1 ⟨least.val, hactiveTop least.val least.property⟩)
        (hxnegative.1 ⟨b, hb⟩) hscaleNegative hcapnegative (hleast ⟨b, heb⟩ hba)) hshort hfull
  have hgreatestOmitted := realChamber_active_extreme_is_omitted
    hr hd hs φ hφ N K hNK top p q hp hq true xpositive hxpositive
    word k greatest.val (hactiveTop greatest.val greatest.property) greatest.property (by
      intro b hb heb hne
      have hba : (⟨b, heb⟩ : active) ≠ greatest := fun hz => hne (congrArg Subtype.val hz)
      apply sub_pos.mpr
      exact real_anchor_root_order_of_labels _ _ _ _ base cap scaleDen
        (label b) (label greatest.val) xpositive (haffine b heb)
        (haffine greatest.val greatest.property)
        (hxpositive.1 ⟨b, hb⟩)
        (hxpositive.1 ⟨greatest.val, hactiveTop greatest.val greatest.property⟩)
        hscalePositive hcappositive (hgreatest ⟨b, heb⟩ hba)) hshort hfull
  have heq : least = greatest := Subtype.ext (hleastOmitted.symm.trans hgreatestOmitted)
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

end SkewCornerDescent
