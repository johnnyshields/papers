/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.SymmetricUnits
import SkewCofactorIndependence.ResidueSpaces

/-!
# Exact symmetric first-variation kernel

The two kernel equalities and the exact dimension in
`prop:symmetric-unit-kernel`.  All coordinates belong to the actual
available-position set, and the relation map is the actual rational map
summing first-variation polynomials.  Midpoints have zero odd coordinate.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators

namespace BetaDiagram
variable {n : ℕ} (D : BetaDiagram (n + 1))

/-- Applying the actual available-position reflection twice is the identity. -/
theorem availableReflection_involutive (hn : D.Normalized) (hs : D.Symmetric) :
    Function.Involutive (D.availableReflection hn hs) := by
  intro z
  apply Subtype.ext
  simp only [availableReflection_val]
  omega

/-- Reflection does not change the polynomial attached to a coordinate. -/
theorem availableReflection_unit (hn : D.Normalized) (hs : D.Symmetric)
    (z : D.Available) :
    D.unitVariation (D.availableReflection hn hs z).val = D.unitVariation z.val :=
  D.symmetric_unitVariation hn hs z.val

/-- Fold a rational coefficient vector to representatives, counting a midpoint once. -/
def foldedUnitCoefficient (hn : D.Normalized) (hs : D.Symmetric)
    (c : D.Available → ℚ) (z : D.UnitRepresentative) : ℚ :=
  if 2 * z.val.val = D.unitSpan then c z.val
  else c z.val + c (D.availableReflection hn hs z.val)

set_option backward.isDefEq.respectTransparency false in
/-- Folding is an equality of the actual polynomial sums, not a rank surrogate. -/
theorem unitRelationMap_fold (hn : D.Normalized) (hs : D.Symmetric)
    (c : D.Available → ℚ) :
    D.unitRelationMap c = ∑ z : D.UnitRepresentative,
      D.foldedUnitCoefficient hn hs c z • D.unitVariation z.val.val := by
  classical
  let σ := D.availableReflection hn hs
  let low (z : D.Available) : Prop := 2 * z.val ≤ D.unitSpan
  let small (z : D.Available) : Prop := 2 * z.val < D.unitSpan
  have hinv := D.availableReflection_involutive hn hs
  have hunit := D.availableReflection_unit hn hs
  have hfold : (∑ z : D.UnitRepresentative,
      D.foldedUnitCoefficient hn hs c z • D.unitVariation z.val.val) =
      (∑ z : D.Available, if low z then c z • D.unitVariation z.val else 0) +
      ∑ z : D.Available,
        if small z then c (σ z) • D.unitVariation z.val else 0 := by
    rw [← unit_sum_subtype low]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hl : low z
    · by_cases hm : 2 * z.val = D.unitSpan
      · have hns : ¬ small z := by dsimp [small]; omega
        simp [hl, hns, foldedUnitCoefficient, hm]
      · have hsm : small z := by dsimp [low] at hl; dsimp [small]; omega
        simp [hl, hsm, foldedUnitCoefficient, hm, add_smul, σ]
    · have hns : ¬ small z := by dsimp [low] at hl; dsimp [small]; omega
      simp [hl, hns]
  have hupper : (∑ z : D.Available,
      if small z then c (σ z) • D.unitVariation z.val else 0) =
      ∑ z : D.Available, if ¬ low z then c z • D.unitVariation z.val else 0 := by
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro z _
    have hineq : small (σ z) ↔ ¬ low z := by
      dsimp [small, low, σ]
      omega
    have hσz : σ (σ z) = z := hinv z
    have hUz : D.unitVariation (σ z).val = D.unitVariation z.val := hunit z
    simp only [hineq, hσz, hUz]
  rw [hfold, hupper, ← Finset.sum_add_distrib]
  change (∑ z, c z • D.unitVariation z.val) = _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : low z <;> simp [hz]

/-- The concrete rational coordinate space defined by antisymmetry. -/
def antisymmetricUnitSpace (hn : D.Normalized) (hs : D.Symmetric) :
    Submodule ℚ (D.Available → ℚ) :=
  involutionOddSpace (D.availableReflection hn hs) (fun _ => True)

/-- Antisymmetry means exactly the coordinate equation in the manuscript. -/
theorem mem_antisymmetricUnitSpace_iff (hn : D.Normalized) (hs : D.Symmetric)
    (c : D.Available → ℚ) :
    c ∈ D.antisymmetricUnitSpace hn hs ↔
      ∀ z, c z + c (D.availableReflection hn hs z) = 0 := by
  change ((∀ z, c z + c (D.availableReflection hn hs z) = 0) ∧
    (∀ z, ¬ True → c z = 0)) ↔ _
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual relation kernel equals the entire antisymmetric coordinate space.
Representative independence is supplied by the private-generator induction. -/
theorem symmetric_unitKernel_eq (hd : D.Dense) (hn : D.Normalized)
    (hs : D.Symmetric) : D.unitKernel = D.antisymmetricUnitSpace hn hs := by
  classical
  ext c
  rw [D.mem_unitKernel_iff, D.mem_antisymmetricUnitSpace_iff hn hs]
  constructor
  · intro hc
    have hfold : (∑ z : D.UnitRepresentative,
        D.foldedUnitCoefficient hn hs c z • D.unitVariation z.val.val) = 0 := by
      rw [← D.unitRelationMap_fold hn hs]
      exact hc
    have hcoeff := Fintype.linearIndependent_iff.mp
      (symmetric_units_independent n D hd hn hs) _ hfold
    have hlow (z : D.Available) (hz : 2 * z.val ≤ D.unitSpan) :
        c z + c (D.availableReflection hn hs z) = 0 := by
      have hh := hcoeff ⟨z, hz⟩
      by_cases hm : 2 * z.val = D.unitSpan
      · have hfix := (D.availableReflection_fixed_iff hn hs z).2 hm
        simp only [foldedUnitCoefficient, hm, ite_true] at hh
        simp [hfix, hh]
      · simpa [foldedUnitCoefficient, hm] using hh
    intro z
    by_cases hz : 2 * z.val ≤ D.unitSpan
    · exact hlow z hz
    · have hzr : 2 * (D.availableReflection hn hs z).val ≤ D.unitSpan := by
        simp only [availableReflection_val]; omega
      have hh := hlow (D.availableReflection hn hs z) hzr
      rw [D.availableReflection_involutive hn hs z] at hh
      simpa [add_comm] using hh
  · intro hc
    change D.unitRelationMap c = 0
    rw [D.unitRelationMap_fold hn hs]
    apply Finset.sum_eq_zero
    intro z _
    have hh := hc z.val
    have hzero : D.foldedUnitCoefficient hn hs c z = 0 := by
      by_cases hm : 2 * z.val.val = D.unitSpan
      · have hfix := (D.availableReflection_fixed_iff hn hs z.val).2 hm
        rw [hfix] at hh
        simp only [foldedUnitCoefficient, hm, ite_true]
        linarith
      · simpa [foldedUnitCoefficient, hm] using hh
    simp [hzero]

/-- The exact coordinate criterion for an actual rational unit relation. -/
theorem mem_symmetric_unitKernel_iff (hd : D.Dense) (hn : D.Normalized)
    (hs : D.Symmetric) (c : D.Available → ℚ) :
    c ∈ D.unitKernel ↔ ∀ z, c z + c (D.availableReflection hn hs z) = 0 := by
  rw [D.symmetric_unitKernel_eq hd hn hs, D.mem_antisymmetricUnitSpace_iff hn hs]

/-- An available midpoint has coefficient zero in every actual unit relation. -/
theorem symmetric_unitKernel_midpoint_zero (hd : D.Dense) (hn : D.Normalized)
    (hs : D.Symmetric) (c : D.unitKernel) (z : D.Available)
    (hz : 2 * z.val = D.unitSpan) : (c : D.Available → ℚ) z = 0 := by
  have hh := (D.mem_symmetric_unitKernel_iff hd hn hs c.val).1 c.property z
  rw [(D.availableReflection_fixed_iff hn hs z).2 hz] at hh
  linarith

/-- Available positions have a faithful nonnegative integer index. -/
def unitPositionIndex (z : D.Available) : ℕ := z.val.toNat

/-- Positivity of all available positions makes this index injective. -/
theorem unitPositionIndex_injective (hn : D.Normalized) :
    Function.Injective D.unitPositionIndex := by
  intro z w he
  have hz := (D.mem_availablePositions_iff hn _).1 z.property
  have hw := (D.mem_availablePositions_iff hn _).1 w.property
  apply Subtype.ext
  dsimp [unitPositionIndex] at he
  omega

/-- Free representatives are the strictly lower endpoints of two-element orbits. -/
abbrev StrictUnitRepresentative := {z : D.Available // 2 * z.val < D.unitSpan}

/-- The generic odd-coordinate representatives are exactly the manuscript's `2z<N` positions. -/
def strictUnitRepresentativeEquiv (hn : D.Normalized) (hs : D.Symmetric) :
    D.StrictUnitRepresentative ≃ OrbitRepresentative (D.availableReflection hn hs)
      (fun _ => True) D.unitPositionIndex where
  toFun z := ⟨z.val, trivial, by
    have hz := (D.mem_availablePositions_iff hn _).1 z.val.property
    have hr := (D.mem_availablePositions_iff hn _).1
      (D.availableReflection hn hs z.val).property
    have hh := z.property
    simp only [unitPositionIndex, availableReflection_val]
    omega⟩
  invFun z := ⟨z.val, by
    have hz := (D.mem_availablePositions_iff hn _).1 z.val.property
    have hr := (D.mem_availablePositions_iff hn _).1
      (D.availableReflection hn hs z.val).property
    have hh := z.property.2
    simp only [unitPositionIndex, availableReflection_val] at hh
    omega⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- Coordinate differences on the actual restoration-position domain. -/
def unitCoordinateDifference (hn : D.Normalized) (hs : D.Symmetric)
    (z : D.Available) : D.Available → ℚ :=
  Pi.single z 1 - Pi.single (D.availableReflection hn hs z) 1

/-- Each concrete coordinate difference is antisymmetric. -/
theorem unitCoordinateDifference_mem (hn : D.Normalized) (hs : D.Symmetric)
    (z : D.Available) : D.unitCoordinateDifference hn hs z ∈
      D.antisymmetricUnitSpace hn hs := by
  classical
  rw [D.mem_antisymmetricUnitSpace_iff hn hs]
  intro w
  let σ := D.availableReflection hn hs
  have hσ : Function.Involutive σ := D.availableReflection_involutive hn hs
  have h₁ : σ w = z ↔ w = σ z := by
    constructor
    · intro h
      have hh : σ (σ w) = σ z := congrArg (fun x : D.Available => σ x) h
      rw [hσ w] at hh
      exact hh
    · intro h; rw [h, hσ z]
  have h₂ : σ w = σ z ↔ w = z := σ.injective.eq_iff
  simp only [unitCoordinateDifference, Pi.sub_apply, Pi.single_apply]
  change (if w = z then 1 else 0) - (if w = σ z then 1 else 0) +
    ((if σ w = z then 1 else 0) - (if σ w = σ z then 1 else 0)) = 0
  simp only [h₁, h₂]
  ring

/-- At a lower representative, a lower coordinate difference is its Kronecker coordinate. -/
theorem unitCoordinateDifference_representative (hn : D.Normalized)
    (hs : D.Symmetric) (z w : D.StrictUnitRepresentative) :
    D.unitCoordinateDifference hn hs z.val w.val = if z = w then 1 else 0 := by
  classical
  have hne : w.val ≠ D.availableReflection hn hs z.val := by
    intro he
    have hz := z.property
    have hw := w.property
    have hv := congrArg Subtype.val he
    simp only [availableReflection_val] at hv
    omega
  have he : w.val = z.val ↔ z = w := by
    constructor
    · intro h; exact (Subtype.ext h).symm
    · intro h; subst w; rfl
  simp only [unitCoordinateDifference, Pi.sub_apply, Pi.single_apply, hne, ite_false,
    sub_zero, he]
set_option backward.isDefEq.respectTransparency false in

/-- Antisymmetric functions have the exact coordinate-difference expansion. -/
theorem antisymmetric_unit_expansion (hn : D.Normalized) (hs : D.Symmetric)
    (c : D.antisymmetricUnitSpace hn hs) :
    (c : D.Available → ℚ) = ∑ z : D.StrictUnitRepresentative,
      c.val z.val • D.unitCoordinateDifference hn hs z.val := by
  classical
  let S := D.antisymmetricUnitSpace hn hs
  let f : D.Available → ℚ := ∑ z : D.StrictUnitRepresentative,
    c.val z.val • D.unitCoordinateDifference hn hs z.val
  have hf : f ∈ S := by
    apply Submodule.sum_mem
    intro z _
    exact S.smul_mem _ (D.unitCoordinateDifference_mem hn hs z.val)
  let e := D.strictUnitRepresentativeEquiv hn hs
  have he : c = (⟨f, hf⟩ : S) := by
    apply oddCoordinates_injective (D.availableReflection hn hs) (fun _ => True)
      D.unitPositionIndex (D.availableReflection_involutive hn hs)
      (fun _ => Iff.rfl) (D.unitPositionIndex_injective hn)
    funext r
    let w := e.symm r
    change c.val r.val = f r.val
    have hw : w.val = r.val := rfl
    rw [← hw]
    simp only [f, Finset.sum_apply, Pi.smul_apply,
      D.unitCoordinateDifference_representative hn hs]
    simp [smul_eq_mul]
  exact congrArg Subtype.val he

/-- The antisymmetric space is exactly the span of lower-endpoint coordinate differences. -/
theorem antisymmetricUnitSpace_eq_span (hn : D.Normalized) (hs : D.Symmetric) :
    D.antisymmetricUnitSpace hn hs = Submodule.span ℚ
      (Set.range (fun z : D.StrictUnitRepresentative =>
        D.unitCoordinateDifference hn hs z.val)) := by
  classical
  apply le_antisymm
  · intro c hc
    have he := D.antisymmetric_unit_expansion hn hs ⟨c, hc⟩
    change c = ∑ z : D.StrictUnitRepresentative,
      c z.val • D.unitCoordinateDifference hn hs z.val at he
    rw [he]
    apply Submodule.sum_mem
    intro z _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨z, rfl⟩
    exact D.unitCoordinateDifference_mem hn hs z.val

/-- The second exact kernel equality of `prop:symmetric-unit-kernel`, on actual coordinates. -/
theorem symmetric_unitKernel_eq_span (hd : D.Dense) (hn : D.Normalized)
    (hs : D.Symmetric) : D.unitKernel = Submodule.span ℚ
      (Set.range (fun z : D.StrictUnitRepresentative =>
        Pi.single z.val 1 - Pi.single (D.availableReflection hn hs z.val) 1)) := by
  rw [D.symmetric_unitKernel_eq hd hn hs, D.antisymmetricUnitSpace_eq_span hn hs]
  rfl

/-- Restriction parametrizes the actual kernel by the free two-element reflection orbits. -/
def symmetricUnitCoordinates (hd : D.Dense) (hn : D.Normalized) (hs : D.Symmetric) :
    D.unitKernel ≃ₗ[ℚ] (D.StrictUnitRepresentative → ℚ) :=
  (LinearEquiv.ofEq _ _ (D.symmetric_unitKernel_eq hd hn hs)).trans
    ((oddCoordinatesEquiv (D.availableReflection hn hs) (fun _ => True)
      D.unitPositionIndex (D.availableReflection_involutive hn hs)
      (fun _ => Iff.rfl) (D.unitPositionIndex_injective hn)).trans
      (LinearEquiv.funCongrLeft ℚ ℚ (D.strictUnitRepresentativeEquiv hn hs)))

/-- Available midpoints form a subsingleton, regardless of whether one is present. -/
theorem symmetric_available_fixed_card_le_one (hn : D.Normalized) (hs : D.Symmetric) :
    Fintype.card (SupportedFixed (D.availableReflection hn hs) (fun _ => True)) ≤ 1 := by
  classical
  apply Fintype.card_le_one_iff.2
  intro z w
  apply Subtype.ext
  apply Subtype.ext
  have hz := (D.availableReflection_fixed_iff hn hs z.val).1 z.property.2
  have hw := (D.availableReflection_fixed_iff hn hs w.val).1 w.property.2
  omega

/-- Each free rational coordinate corresponds to one two-element actual position orbit. -/
theorem symmetric_unitKernel_finrank_representatives (hd : D.Dense)
    (hn : D.Normalized) (hs : D.Symmetric) :
    Module.finrank ℚ D.unitKernel = Fintype.card D.StrictUnitRepresentative := by
  rw [(D.symmetricUnitCoordinates hd hn hs).finrank_eq]
  exact Module.finrank_pi ℚ

/-- Exact orbit-count identity for the actual first-variation kernel; a midpoint
contributes zero. -/
theorem symmetric_unitKernel_twice_finrank (hd : D.Dense) (hn : D.Normalized)
    (hs : D.Symmetric) :
    2 * Module.finrank ℚ D.unitKernel +
      Fintype.card (SupportedFixed (D.availableReflection hn hs) (fun _ => True)) =
      D.availablePositions.card := by
  classical
  rw [D.symmetric_unitKernel_finrank_representatives hd hn hs]
  let σ := D.availableReflection hn hs
  have hσ : Function.Involutive σ := D.availableReflection_involutive hn hs
  have hsplit := Fintype.card_congr (supportedSplit σ (fun _ => True))
  have hmove := Fintype.card_congr
    (movingEquiv σ (fun _ => True) D.unitPositionIndex hσ
      (fun _ => Iff.rfl) (D.unitPositionIndex_injective hn))
  have hrep := Fintype.card_congr (D.strictUnitRepresentativeEquiv hn hs)
  let e : {z : D.Available // True} ≃ D.Available :=
    { toFun := Subtype.val
      invFun := fun z => ⟨z, trivial⟩
      left_inv := fun z => by apply Subtype.ext; rfl
      right_inv := fun z => rfl }
  have htrue := Fintype.card_congr e
  simp only [Fintype.card_sum] at hsplit hmove
  simp only [← Nat.card_eq_fintype_card] at hsplit hmove hrep htrue ⊢
  have havailable : Nat.card D.Available = D.availablePositions.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  dsimp only [σ] at *
  omega

/-- The exact floor-half cardinality formula of `prop:symmetric-unit-kernel`. -/
theorem symmetric_unitKernel_finrank (hd : D.Dense) (hn : D.Normalized)
    (hs : D.Symmetric) :
    Module.finrank ℚ D.unitKernel = D.availablePositions.card / 2 := by
  have hh := D.symmetric_unitKernel_twice_finrank hd hn hs
  have hf := D.symmetric_available_fixed_card_le_one hn hs
  omega

end BetaDiagram
end SkewCofactorIndependence
