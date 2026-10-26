/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.SmallCoreWitnesses
import SkewCofactorIndependence.KernelNullity
import SkewCofactorIndependence.NonsymmetricCofactors
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The actual modulus-one dilation ray

The full determinant, unit kernel, cofactor independence, and residue basis
in `ex:dilation-ray` of `shields-2026-skew-cofactor-independence.tex`.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators

/-- The only available integer in the literal base diagram is three. -/
theorem dilationRayCore_available : dilationRayCore.availablePositions = {3} := by
  classical
  ext z
  rw [BetaDiagram.mem_availablePositions]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨h₀, h₄, hr, hc⟩
    have h₁ := hc 0
    have h₂ := hr 1
    norm_num [dilationRayCore] at h₀ h₄ h₁ h₂
    omega
  · rintro rfl
    refine ⟨by norm_num [dilationRayCore], by norm_num [dilationRayCore], ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [dilationRayCore]
    · intro j; fin_cases j <;> norm_num [dilationRayCore]

/-- Three is an actual coordinate of the unit relation space. -/
def dilationRayPosition : dilationRayCore.Available :=
  ⟨3, by rw [dilationRayCore_available]; simp⟩

/-- The available coordinate domain is a singleton, not an ambient interval. -/
theorem dilationRayCore_available_eq (z : dilationRayCore.Available) :
    z = dilationRayPosition := by
  apply Subtype.ext
  have hz : z.val = 3 := by
    simpa only [dilationRayCore_available, Finset.mem_singleton] using z.property
  exact hz

/-- An exact rational specialization distinguishes the two monomials in the unit. -/
theorem dilationRayCore_unit_three_ne_zero : dilationRayCore.unitVariation 3 ≠ 0 := by
  intro h
  let e : CompleteRing →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun k => if k = (3 : ℕ+) then 0 else 1)
  have he := congrArg e h
  rw [dilationRayCore_unit_three] at he
  norm_num [e, complete_of_pos (by norm_num : (0 : ℤ) < 1),
    complete_of_pos (by norm_num : (0 : ℤ) < 2),
    complete_of_pos (by norm_num : (0 : ℤ) < 3)] at he

/-- The actual rational first-variation kernel of the base diagram is zero. -/
theorem dilationRayCore_unitKernel : dilationRayCore.unitKernel = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro c hc
  change c = 0
  have hsum : dilationRayCore.unitRelationMap c =
      c dilationRayPosition • dilationRayCore.unitVariation 3 := by
    change (∑ z : dilationRayCore.Available, c z • dilationRayCore.unitVariation z.val) = _
    rw [Finset.sum_eq_single dilationRayPosition]
    · rfl
    · intro z hz hne
      exact (hne (dilationRayCore_available_eq z)).elim
    · simp
  have hzero : c dilationRayPosition = 0 := by
    have hh : c dilationRayPosition • dilationRayCore.unitVariation 3 = 0 :=
      hsum.symm.trans hc
    exact (smul_eq_zero.mp hh).resolve_right dilationRayCore_unit_three_ne_zero
  funext z
  rw [dilationRayCore_available_eq z, hzero]
  rfl

/-- The actual four signed generator cofactors are rationally independent. -/
theorem dilationRayCore_cofactors_independent :
    LinearIndependent ℚ (fun ij : Fin 2 × Fin 2 => dilationRayCore.cofactor ij.1 ij.2) :=
  dilationRayCore.nonsymmetric_cofactor_independent
    dilationRayCore_dense dilationRayCore_nonsymmetric

/-- The endpoint gcd is one because the column beta one is among its entries. -/
theorem dilationRayCore_endpointModulus : dilationRayCore.endpointModulus = 1 := by
  apply Nat.dvd_one.mp
  simpa [BetaDiagram.endpointPeriod, dilationRayCore] using
    dilationRayCore.endpointModulus_dvd (Sum.inr (0 : Fin 2))

@[simp] theorem dilationRayCore_span : dilationRayCore.span = 4 := by
  norm_num [BetaDiagram.span, dilationRayCore]

/-- No inherited summand survives anywhere along this ray. -/
theorem dilationRayCore_inheritedKernel (t : ℕ+) :
    dilationRayCore.inheritedKernel t = ⊥ := by
  simp [BetaDiagram.inheritedKernel, dilationRayCore_unitKernel]

/-- For every positive integer dilation the entire actual kernel is arithmetic. -/
theorem dilationRayCore_dilation_kernel (t : ℕ+) :
    (dilationRayCore.dilate t).unitKernel = dilationRayCore.arithmeticOffGrid t := by
  have h := dilationRayCore.dilation_kernel t (by omega)
    (dilationRayCore_dense.connected (by omega)) dilationRayCore_dense.zeroFree
    dilationRayCore_normalized dilationRayCore_cofactors_independent
  simpa [dilationRayCore_inheritedKernel] using h.1

/-- The floor nullity holds at every positive dilation, including one and two. -/
theorem dilationRayCore_dilation_nullity (t : ℕ+) :
    Module.finrank ℚ (dilationRayCore.dilate t).unitKernel = ((t : ℕ) - 1) / 2 := by
  have h := dilationRayCore.dilation_nullity_modulus_one t (by omega)
    (dilationRayCore_dense.connected (by omega)) dilationRayCore_dense.zeroFree
    dilationRayCore_normalized dilationRayCore_cofactors_independent
    dilationRayCore_endpointModulus
  have hk : Module.finrank ℚ ↥dilationRayCore.unitKernel = 0 := by
    rw [dilationRayCore_unitKernel]
    exact finrank_bot ℚ (dilationRayCore.Available → ℚ)
  rw [hk, Nat.sub_zero] at h
  exact h

/-- Every dilated matrix still has four rationally independent actual cofactors. -/
theorem dilationRayCore_dilation_cofactors_independent (t : ℕ+) :
    LinearIndependent ℚ (fun ij : Fin 2 × Fin 2 =>
      (dilationRayCore.dilate t).cofactor ij.1 ij.2) :=
  dilationRayCore.dilate_cofactors_independent t dilationRayCore_cofactors_independent

/-- The modulus of each residue-coordinate domain is strictly positive. -/
instance dilationRayResidueModulus_neZero (t : ℕ+) :
    NeZero ((t : ℕ) * dilationRayCore.endpointModulus) :=
  ⟨by rw [dilationRayCore_endpointModulus, mul_one]; exact t.ne_zero⟩

/-- With modulus one the lesser representative condition is exactly
`0 < r < t/2`, read without truncating a strict rational inequality. -/
theorem dilationRay_residue_representative_iff (t : ℕ+) (r : ZMod (t : ℕ)) :
    (¬ (t : ℕ) ∣ r.val ∧
      r.val < (residueReflection (t : ℕ) ((t : ℕ) * 4) r).val) ↔
      0 < r.val ∧ 2 * r.val < (t : ℕ) := by
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  have hv := ZMod.val_lt r
  have hd : (t : ℕ) ∣ r.val ↔ r.val = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hv]
  have hr : residueReflection (t : ℕ) ((t : ℕ) * 4) r = -r := by
    simp [residueReflection, Nat.cast_mul]
  rw [hd, hr]
  by_cases hz : r = 0
  · subst r; simp
  · let : NeZero r := ⟨hz⟩
    have hp : 0 < r.val := by
      have hn : r.val ≠ 0 := by
        intro he
        exact hz ((ZMod.val_injective (t : ℕ)) (by simpa only [ZMod.val_zero] using he))
      omega
    rw [ZMod.val_neg_of_ne_zero]
    omega

/-- Free residue coordinates: lesser representatives of the pairs `r,-r`,
excluding the grid class. -/
abbrev DilationRayResidue (t : ℕ+) :=
  OrbitRepresentative
    (residueReflection ((t : ℕ) * dilationRayCore.endpointModulus)
      ((t : ℕ) * dilationRayCore.span))
    (fun r => ¬ (t : ℕ) ∣ r.val) ZMod.val

/-- Restriction identifies the genuine residue functions with the genuine kernel. -/
def dilationRayKernelEquiv (t : ℕ+) :
    offGridResidueSpace (t : ℕ) dilationRayCore.endpointModulus dilationRayCore.span ≃ₗ[ℚ]
      (dilationRayCore.dilate t).unitKernel := by
  let F := (dilationRayCore.offGridRestriction t).codRestrict
    (dilationRayCore.dilate t).unitKernel (fun f =>
      dilationRayCore.arithmeticOffGrid_le_kernel t dilationRayCore_normalized
        dilationRayCore_dense.zeroFree
        (by rw [← dilationRayCore.offGridRestriction_range]; exact ⟨f, rfl⟩))
  apply LinearEquiv.ofBijective F
  constructor
  · intro f g h
    exact dilationRayCore.offGridRestriction_injective t (by omega)
      dilationRayCore_normalized (congrArg Subtype.val h)
  · rintro ⟨c, hc⟩
    rw [dilationRayCore_dilation_kernel, ← dilationRayCore.offGridRestriction_range] at hc
    obtain ⟨f, hf⟩ := hc
    exact ⟨f, Subtype.ext hf⟩

/-- The explicit free-residue coordinate system of the actual dilated kernel. -/
def dilationRayKernelCoordinates (t : ℕ+) :
    (dilationRayCore.dilate t).unitKernel ≃ₗ[ℚ] (DilationRayResidue t → ℚ) := by
  letI : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  letI : NeZero dilationRayCore.endpointModulus :=
    ⟨by rw [dilationRayCore_endpointModulus]; norm_num⟩
  exact (dilationRayKernelEquiv t).symm.trans
    (offGridCoordinates (t : ℕ) dilationRayCore.endpointModulus dilationRayCore.span)

/-- A genuine basis, rather than just a spanning family or nullity count. -/
def dilationRayKernelBasis (t : ℕ+) :
    Module.Basis (DilationRayResidue t) ℚ (dilationRayCore.dilate t).unitKernel :=
  Module.Basis.ofEquivFun (dilationRayKernelCoordinates t)

/-- Each basis vector is the difference of the two residue indicators,
restricted to the actual available positions. -/
theorem dilationRayKernelBasis_apply (t : ℕ+) (r : DilationRayResidue t)
    (w : (dilationRayCore.dilate t).Available) :
    (dilationRayKernelBasis t r).val w =
      (if (w.val : ZMod ((t : ℕ) * dilationRayCore.endpointModulus)) = r.val then 1 else 0) -
      (if (w.val : ZMod ((t : ℕ) * dilationRayCore.endpointModulus)) =
        residueReflection ((t : ℕ) * dilationRayCore.endpointModulus)
          ((t : ℕ) * dilationRayCore.span) r.val then 1 else 0) := by
  classical
  let : NeZero (t : ℕ) := ⟨t.ne_zero⟩
  let : NeZero dilationRayCore.endpointModulus :=
    ⟨by rw [dilationRayCore_endpointModulus]; norm_num⟩
  let σ := residueReflection ((t : ℕ) * dilationRayCore.endpointModulus)
    ((t : ℕ) * dilationRayCore.span)
  let P := fun q : ZMod ((t : ℕ) * dilationRayCore.endpointModulus) => ¬ (t : ℕ) ∣ q.val
  let x : ZMod ((t : ℕ) * dilationRayCore.endpointModulus) := w.val
  let φ : offGridResidueSpace (t : ℕ) dilationRayCore.endpointModulus dilationRayCore.span :=
    ⟨extendOdd σ P ZMod.val (Pi.single r 1),
      extendOdd_mem σ P ZMod.val (residueReflection_involutive _ _)
        (fun q => not_congr (reflection_grid_iff (t : ℕ)
          dilationRayCore.endpointModulus dilationRayCore.span q)) _⟩
  have hb : dilationRayKernelBasis t r = dilationRayKernelEquiv t φ := by
    apply (dilationRayKernelCoordinates t).injective
    rw [dilationRayKernelBasis, Module.Basis.coe_ofEquivFun,
      LinearEquiv.apply_symm_apply]
    change Pi.single r 1 = (offGridCoordinates (t : ℕ)
      dilationRayCore.endpointModulus dilationRayCore.span)
        ((dilationRayKernelEquiv t).symm (dilationRayKernelEquiv t φ))
    rw [LinearEquiv.symm_apply_apply]
    funext q
    exact (extendOdd_representative σ P ZMod.val (Pi.single r 1) q).symm
  rw [hb]
  change extendOdd σ P ZMod.val (Pi.single r 1) x =
    (if x = r.val then 1 else 0) - (if x = σ r.val then 1 else 0)
  have hinv : Function.Involutive σ := residueReflection_involutive _ _
  by_cases hx : P x ∧ x.val < (σ x).val
  · rw [extendOdd, dite_eq_left hx]
    have hn : x ≠ σ r.val := by
      intro he
      have hv : r.val.val < (σ r.val).val := r.property.2
      have hh := hx.2
      rw [he, hinv r.val] at hh
      omega
    have he : (⟨x, hx⟩ : DilationRayResidue t) = r ↔ x = r.val :=
      Subtype.ext_iff
    simp only [Pi.single_apply, he, ite_eq_right hn, sub_zero]
  · by_cases hy : P (σ x) ∧ (σ x).val < (σ (σ x)).val
    · rw [extendOdd, dite_eq_right hx, dite_eq_left hy]
      have hn : x ≠ r.val := by
        intro he
        apply hx
        rw [he]
        exact r.property
      have hePoint : σ x = r.val ↔ x = σ r.val := by
        constructor
        · intro h
          calc
            x = σ (σ x) := (hinv x).symm
            _ = σ r.val := congrArg σ h
        · intro h
          rw [h, hinv r.val]
      have he : (⟨σ x, hy⟩ : DilationRayResidue t) = r ↔ x = σ r.val := by
        rw [Subtype.ext_iff]
        exact hePoint
      simp only [Pi.single_apply, he, ite_eq_right hn, zero_sub]
    · rw [extendOdd, dite_eq_right hx, dite_eq_right hy]
      have hn : x ≠ r.val := by
        intro h
        apply hx
        rw [h]
        exact r.property
      have hm : x ≠ σ r.val := by
        intro he
        apply hy
        rw [he, hinv r.val]
        exact r.property
      simp [hn, hm]

/-- Every vector in the kernel, not only the displayed basis, vanishes on the grid. -/
theorem dilationRayCore_kernel_grid_zero (t : ℕ+)
    (c : (dilationRayCore.dilate t).Available → ℚ)
    (hc : c ∈ (dilationRayCore.dilate t).unitKernel)
    (w : (dilationRayCore.dilate t).Available) (hw : (t : ℤ) ∣ w.val) : c w = 0 := by
  rw [dilationRayCore_dilation_kernel] at hc
  exact dilationRayCore.arithmeticOffGrid_grid t (by omega) c hc w hw

end SkewCofactorIndependence
