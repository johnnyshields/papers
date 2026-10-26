/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RationalExposure
import SkewCornerDescent.CoordinatePolynomials
import SkewCornerDescent.SimultaneousTopology
import SkewCornerDescent.SimultaneousChambers

/-!
# Simultaneous triangular-response chambers over real coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `thm:dual-general`).
The chamber and extreme-root construction use real coefficients directly. Finite
restriction preserves the assignment and all remaining anchor inequalities, without
requiring rational active labels. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

/-- Regular separated anchor roots and strict off-anchor signs at every anchor section. -/
noncomputable def simultaneousRealChamber {ι : Type*} (K : ℕ+) (top : ι → ℕ+)
    (p q : ι → MvPolynomial ℕ ℝ) (positive : Bool) : Set (ℕ → ℝ) :=
  {x | (∀ a : {i : ι // top i = K}, eval x (q a.val) ≠ 0) ∧
    (∀ a b : {i : ι // top i = K}, a ≠ b →
      eval x (p a.val * q b.val - p b.val * q a.val) ≠ 0) ∧
    ∀ a : {i : ι // top i = K}, ∀ i : {i : ι // top i ≠ K},
      let y := anchorAssignment (K : ℕ)
        (rationalAnchorRoot (fun a => p a.val) (fun a => q a.val)) a x
      eval y (q i.val) ≠ 0 ∧
        responseSign positive (rationalTriangularResponse (top i.val : ℕ) (p i.val) (q i.val) y)}

/-- Triangular real representatives with distinct same-top functions produce both nonempty
open simultaneous chambers. No density assumption on the constant subfield is needed. -/
theorem simultaneousRealChamber_open_nonempty {ι : Type*} [Finite ι]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → MvPolynomial ℕ ℝ)
    (htop : ∀ i, N ≤ top i)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ)) (hq0 : ∀ i, q i ≠ 0)
    (hdiff : ∀ a b, top a = K → top b = K → a ≠ b →
      p a * q b - p b * q a ≠ 0) (positive : Bool) :
    IsOpen (simultaneousRealChamber K top p q positive) ∧
      (simultaneousRealChamber K top p q positive).Nonempty := by
  classical
  let lo := {i : ι // top i < K}
  let hi := {i : ι // K < top i}
  let anchors := {i : ι // top i = K}
  let ap := fun a : anchors => p a.val
  let aq := fun a : anchors => q a.val
  have hap : ∀ a : anchors, ∀ j ∈ (ap a).vars, j < (K : ℕ) := by
    intro a j hj
    simpa only [ap, a.property] using hp a.val j hj
  obtain ⟨x, hinj, hreg, hsigned⟩ :=
    exists_simultaneous_rational_roots (lo := lo) (hi := hi) (α := anchors)
      (N : ℕ) (K : ℕ) hNK
      (fun i => (top i.val : ℕ)) (fun i => (top i.val : ℕ))
      (fun i => p i.val) (fun i => q i.val)
      (fun i => p i.val) (fun i => q i.val) ap aq
      (fun i => ⟨htop i.val, i.property⟩) (fun i => i.property)
      (fun i => hp i.val) (fun i => hq i.val) (fun i => hq0 i.val)
      (fun i => hp i.val) (fun i => hq i.val) (fun i => hq0 i.val)
      hap (fun i => hq i.val) (fun i => hq0 i.val)
      (fun a b hab => hdiff a.val b.val a.property b.property
        (fun he => hab (Subtype.ext he))) positive
  have hsep := rational_root_separation_open ap aq
  have hsign := simultaneous_root_signs_open (K : ℕ) ap aq
    (fun i : {i : ι // top i ≠ K} => (top i.val : ℕ))
    (fun i => p i.val) (fun i => q i.val) positive
  constructor
  · convert hsep.inter hsign using 1
    ext y
    change (_ ∧ _) ↔ ((_ ∧ _) ∧ _)
    aesop
  · refine ⟨x, hreg, ?_, ?_⟩
    · intro a b hab
      apply (rational_roots_ne_iff ap aq a b x (hreg a) (hreg b)).mp
      exact fun he => hab (hinj he)
    · intro a i
      rcases lt_or_gt_of_ne i.property with h | h
      · exact (hsigned a).1 ⟨i.val, h⟩
      · exact (hsigned a).2 ⟨i.val, h⟩

/-- Finite inactive removal preserves every remaining root and sign at the same point. -/
theorem simultaneousRealChamber_restrict {α : Type*}
    (S : Finset α) (K : ℕ+) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (positive : Bool) (x : ℕ → ℝ) (hx : x ∈ simultaneousRealChamber K top p q positive) :
    x ∈ simultaneousRealChamber K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive := by
  refine ⟨fun a => hx.1 ⟨a.val.val, a.property⟩, ?_, ?_⟩
  · intro a b hab
    apply hx.2.1 ⟨a.val.val, a.property⟩ ⟨b.val.val, b.property⟩
    intro he
    exact hab (Subtype.ext (Subtype.ext
      (congrArg (fun z : {i : α // top i = K} => z.val) he)))
  · intro a i
    exact hx.2.2 ⟨a.val.val, a.property⟩ ⟨i.val.val, i.property⟩

/-- Pairwise separated numerator cross-products make the actual anchor roots injective. -/
theorem simultaneousRealChamber_roots_injective {ι : Type*}
    (K : ℕ+) (top : ι → ℕ+) (p q : ι → MvPolynomial ℕ ℝ) (positive : Bool)
    (x : ℕ → ℝ) (hx : x ∈ simultaneousRealChamber K top p q positive) :
    Function.Injective (rationalAnchorRoot (fun a : {i : ι // top i = K} => p a.val)
      (fun a => q a.val) · x) := by
  intro a b hab
  by_contra hne
  exact ((rational_roots_ne_iff
    (fun a : {i : ι // top i = K} => p a.val) (fun a => q a.val)
    a b x (hx.1 a) (hx.1 b)).mpr (hx.2.1 a b hne)) hab

/-- A least or greatest remaining anchor zeros its own response and strictly signs all
other responses. Only triangular support and chamber membership are assumed. -/
theorem simultaneousRealChamber_exposed_extreme {ι : Type*} [Finite ι]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool)
    (x : ℕ → ℝ) (hx : x ∈ simultaneousRealChamber K top p q positive) :
    ∃ a : {i : ι // top i = K},
      let y := anchorAssignment (K : ℕ)
        (rationalAnchorRoot (fun a => p a.val) (fun a => q a.val)) a x
      rationalTriangularResponse (K : ℕ) (p a.val) (q a.val) y = 0 ∧
      (∀ i, eval y (q i) ≠ 0) ∧
      ∀ i, i ≠ a.val → responseSign positive
        (rationalTriangularResponse (top i : ℕ) (p i) (q i) y) := by
  classical
  let anchors := {i : ι // top i = K}
  obtain ⟨i0, hi0⟩ := hanchor
  let _ : Nonempty anchors := ⟨⟨i0, hi0⟩⟩
  let ap := fun a : anchors => p a.val
  let aq := fun a : anchors => q a.val
  have hap : ∀ a j, j ∈ (ap a).vars → j < (K : ℕ) := by
    intro a j hj
    simpa only [a.property] using hp a.val j hj
  have haq : ∀ a j, j ∈ (aq a).vars → j < (K : ℕ) :=
    fun a j hj => lt_of_lt_of_le (hq a.val j hj) hNK
  have hinj := simultaneousRealChamber_roots_injective K top p q positive x hx
  have hextreme : ∃ a : anchors, ∀ b, b ≠ a → responseSign positive
      (rationalAnchorRoot ap aq a x - rationalAnchorRoot ap aq b x) := by
    cases positive
    · obtain ⟨a, ha⟩ := exists_least_anchor_label _ hinj
      exact ⟨a, fun b hba => sub_neg.mpr (ha b hba)⟩
    · obtain ⟨a, ha⟩ := exists_greatest_anchor_label _ hinj
      exact ⟨a, fun b hba => sub_pos.mpr (ha b hba)⟩
  obtain ⟨a, ha⟩ := hextreme
  let y := anchorAssignment (K : ℕ) (rationalAnchorRoot ap aq) a x
  refine ⟨a, rational_anchor_response_zero (K : ℕ) ap aq hap haq a x, ?_, ?_⟩
  · intro i
    by_cases hi : top i = K
    · have hqi : eval y (q i) = eval x (q i) := by
        apply eval_polynomial_eq_of_agree_below _ (K : ℕ)
          (fun j hj => lt_of_lt_of_le (hq i j hj) hNK)
        intro j hj
        simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)]
      rw [hqi]
      exact hx.1 ⟨i, hi⟩
    · exact (hx.2.2 a ⟨i, hi⟩).1
  · intro i hia
    by_cases hi : top i = K
    · let b : anchors := ⟨i, hi⟩
      have hba : b ≠ a := fun he => hia (congrArg Subtype.val he)
      have hc := rational_correction_locality (K : ℕ) (ap b) (aq b) (hap b) (haq b)
        y x (by
          intro j hj
          simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)])
      change responseSign positive (y (top i : ℕ) + _ / _)
      rw [hi]
      change responseSign positive (y (K : ℕ) + eval y (ap b) / eval y (aq b))
      rw [hc]
      simpa only [y, anchorAssignment, Function.update_self, rationalAnchorRoot, sub_neg_eq_add]
        using ha b hba
    · exact (hx.2.2 a ⟨i, hi⟩).2

end SkewCornerDescent
