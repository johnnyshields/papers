/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Odd residue spaces and dilation arithmetic

Rational odd functions in «Integral dilation» (`sec:dilation`), including the
space in `eq:offgrid-space` and the arithmetic in `cor:nullity-increment`.
The coordinate set consists of one actual representative of each two-element
reflection orbit.  Cardinalities are proved for the actual fixed-point sets.
-/

namespace SkewCofactorIndependence

attribute [local instance] Classical.propDecidable

section Involution

variable {α : Type*}

/-- Odd functions supported on a specified subset of an involution's domain. -/
def involutionOddSpace (σ : α → α) (P : α → Prop) : Submodule ℚ (α → ℚ) where
  carrier := {f | (∀ x, f x + f (σ x) = 0) ∧ (∀ x, ¬ P x → f x = 0)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x
      change (f x + g x) + (f (σ x) + g (σ x)) = 0
      linarith [hf.1 x, hg.1 x]
    · intro x hx
      simp [hf.2 x hx, hg.2 x hx]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x
      change c * f x + c * f (σ x) = 0
      rw [← mul_add, hf.1 x, mul_zero]
    · intro x hx
      simp [hf.2 x hx]

/-- The lesser endpoint of each nontrivial orbit, measured by an injective index. -/
abbrev OrbitRepresentative (σ : α → α) (P : α → Prop) (index : α → ℕ) :=
  {x : α // P x ∧ index x < index (σ x)}

/-- The actual supported fixed points. -/
abbrev SupportedFixed (σ : α → α) (P : α → Prop) :=
  {x : α // P x ∧ σ x = x}

/-- The actual supported nonfixed points. -/
abbrev SupportedMoving (σ : α → α) (P : α → Prop) :=
  {x : α // P x ∧ σ x ≠ x}

variable (σ : α → α) (P : α → Prop) (index : α → ℕ)
variable (hσ : Function.Involutive σ) (hP : ∀ x, P (σ x) ↔ P x)
variable (hindex : Function.Injective index)

/-- Extension from free orbit coordinates, zero on fixed points and outside support. -/
noncomputable def extendOdd (a : OrbitRepresentative σ P index → ℚ) (x : α) : ℚ :=
  if hx : P x ∧ index x < index (σ x) then a ⟨x, hx⟩
  else if hy : P (σ x) ∧ index (σ x) < index (σ (σ x)) then -a ⟨σ x, hy⟩
  else 0

/-- The extension satisfies both defining equations of the supported odd space. -/
theorem extendOdd_mem (hσ : Function.Involutive σ) (hP : ∀ x, P (σ x) ↔ P x)
    (a : OrbitRepresentative σ P index → ℚ) :
    extendOdd σ P index a ∈ involutionOddSpace σ P := by
  classical
  constructor
  · intro x
    by_cases hx : P x ∧ index x < index (σ x)
    · have hy : ¬ (P (σ x) ∧ index (σ x) < index x) := by omega
      simp [extendOdd, hσ x, hx, hy]
    · by_cases hy : P (σ x) ∧ index (σ x) < index x
      · simp [extendOdd, hσ x, hx, hy]
      · simp [extendOdd, hσ x, hx, hy]
  · intro x hx
    have hy : ¬ P (σ x) := fun hy => hx ((hP x).1 hy)
    simp [extendOdd, hx, hy]

/-- Restriction recovers the supplied free coordinates exactly. -/
theorem extendOdd_representative (a : OrbitRepresentative σ P index → ℚ)
    (r : OrbitRepresentative σ P index) : extendOdd σ P index a r = a r := by
  classical
  simp only [extendOdd, dite_eq_left r.property]

/-- Restriction to orbit representatives is a rational linear map. -/
def oddCoordinates : involutionOddSpace σ P →ₗ[ℚ]
    (OrbitRepresentative σ P index → ℚ) where
  toFun f r := (f : α → ℚ) r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every supported odd function is uniquely determined by its free coordinates. -/
theorem oddCoordinates_injective (hσ : Function.Involutive σ)
    (hP : ∀ x, P (σ x) ↔ P x) (hindex : Function.Injective index) :
    Function.Injective (oddCoordinates σ P index) := by
  intro f g h
  apply Subtype.ext
  funext x
  by_cases hx : P x
  · by_cases hfix : σ x = x
    · have hf := f.property.1 x
      have hg := g.property.1 x
      rw [hfix] at hf hg
      linarith
    · have hne : index x ≠ index (σ x) := by
        intro he
        exact hfix (hindex he.symm)
      rcases lt_or_gt_of_ne hne with hlo | hhi
      · have he := congrFun h ⟨x, hx, hlo⟩
        change (f : α → ℚ) x = (g : α → ℚ) x at he
        exact he
      · have hy : P (σ x) := (hP x).2 hx
        have hlo : index (σ x) < index (σ (σ x)) := by simpa [hσ x] using hhi
        have he := congrFun h ⟨σ x, hy, hlo⟩
        have hf := f.property.1 x
        have hg := g.property.1 x
        change (f : α → ℚ) (σ x) = (g : α → ℚ) (σ x) at he
        linarith
  · rw [f.property.2 x hx, g.property.2 x hx]

/-- Free coordinates may be prescribed arbitrarily. -/
theorem oddCoordinates_surjective (hσ : Function.Involutive σ)
    (hP : ∀ x, P (σ x) ↔ P x) :
    Function.Surjective (oddCoordinates σ P index) := by
  intro a
  refine ⟨⟨extendOdd σ P index a, extendOdd_mem σ P index hσ hP a⟩, ?_⟩
  funext r
  change extendOdd σ P index a r = a r
  exact extendOdd_representative σ P index a r

/-- Genuine linear parametrization by the two-element reflection orbits. -/
noncomputable def oddCoordinatesEquiv (hσ : Function.Involutive σ)
    (hP : ∀ x, P (σ x) ↔ P x) (hindex : Function.Injective index) :
    involutionOddSpace σ P ≃ₗ[ℚ]
    (OrbitRepresentative σ P index → ℚ) :=
  LinearEquiv.ofBijective (oddCoordinates σ P index)
    ⟨oddCoordinates_injective σ P index hσ hP hindex,
      oddCoordinates_surjective σ P index hσ hP⟩

/-- Supported points partition into fixed points and moving points. -/
noncomputable def supportedSplit :
    SupportedFixed σ P ⊕ SupportedMoving σ P ≃ {x : α // P x} where
  toFun := Sum.elim (fun x => ⟨x, x.property.1⟩) (fun x => ⟨x, x.property.1⟩)
  invFun x := if h : σ x = x then Sum.inl ⟨x, x.property, h⟩
    else Sum.inr ⟨x, x.property, h⟩
  left_inv := by
    intro x
    cases x with
    | inl x => simp [x.property.2]
    | inr x => simp [x.property.2]
  right_inv := by
    intro x
    dsimp only
    split_ifs <;> rfl

/-- Each actual moving point is one of the two endpoints of a representative's orbit. -/
noncomputable def movingEquiv : SupportedMoving σ P ≃
    OrbitRepresentative σ P index ⊕ OrbitRepresentative σ P index where
  toFun x :=
    if h : index x < index (σ x) then Sum.inl ⟨x, x.property.1, h⟩
    else Sum.inr ⟨σ x, (hP x).2 x.property.1, by
      have hne : index x ≠ index (σ x) := by
        intro he
        exact x.property.2 (hindex he.symm)
      simpa only [hσ x] using (show index (σ x) < index x by omega)⟩
  invFun := Sum.elim
    (fun r => ⟨r, r.property.1, by
      intro he
      have hh := r.property.2
      rw [he] at hh
      omega⟩)
    (fun r => ⟨σ r, (hP r).2 r.property.1, by
      intro he
      have hh := r.property.2
      rw [hσ r] at he
      rw [← he] at hh
      omega⟩)
  left_inv := by
    intro x
    dsimp only
    split_ifs with h
    · rfl
    · apply Subtype.ext
      exact hσ x
  right_inv := by
    intro x
    cases x with
    | inl r =>
      dsimp only
      split_ifs with h
      · rfl
      · exact False.elim (h r.property.2)
    | inr r =>
      dsimp only
      have hh : ¬ index (σ r) < index (σ (σ r)) := by
        rw [hσ r]
        exact not_lt_of_ge (Nat.le_of_lt r.property.2)
      split_ifs with h
      · exact False.elim (hh h)
      · congr 1
        apply Subtype.ext
        exact hσ r

variable [Fintype α]

/-- Dimension equals the number of freely assignable orbit representatives. -/
theorem finrank_involutionOddSpace (hσ : Function.Involutive σ)
    (hP : ∀ x, P (σ x) ↔ P x) (hindex : Function.Injective index) :
    Module.finrank ℚ (involutionOddSpace σ P) =
      Fintype.card (OrbitRepresentative σ P index) := by
  classical
  rw [(oddCoordinatesEquiv σ P index hσ hP hindex).finrank_eq]
  exact Module.finrank_pi ℚ

/-- Exact, subtraction-free orbit count; fixed points contribute no odd coordinate. -/
theorem two_finrank_add_fixed (index : α → ℕ) (hσ : Function.Involutive σ)
    (hP : ∀ x, P (σ x) ↔ P x) (hindex : Function.Injective index) :
    2 * Module.finrank ℚ (involutionOddSpace σ P) +
      Fintype.card (SupportedFixed σ P) = Fintype.card {x : α // P x} := by
  classical
  have hs := Fintype.card_congr (supportedSplit σ P)
  have hm := Fintype.card_congr (movingEquiv σ P index hσ hP hindex)
  simp only [Fintype.card_sum] at hs hm
  rw [finrank_involutionOddSpace σ P index hσ hP hindex]
  omega

end Involution

/-- The endpoint reflection on a finite residue group. -/
def residueReflection (q M : ℕ) (r : ZMod q) : ZMod q := (M : ZMod q) - r

@[simp]
theorem residueReflection_involutive (q M : ℕ) :
    Function.Involutive (residueReflection q M) := by
  intro r
  simp [residueReflection]

/-- Reflection fixed points are exactly the solutions of the congruence `2r = M`. -/
theorem residueReflection_fixed_iff (q M : ℕ) (r : ZMod q) :
    residueReflection q M r = r ↔ 2 * r = (M : ZMod q) := by
  unfold residueReflection
  constructor <;> intro h <;> linear_combination -h

/-- The actual reflection fixed-point set, not a numerical surrogate. -/
abbrev FixedResidue (q M : ℕ) := {r : ZMod q // residueReflection q M r = r}

/-- The fixed-point count in `cor:nullity-increment`. -/
noncomputable def fixedCount (q M : ℕ) [NeZero q] : ℕ :=
  Fintype.card (FixedResidue q M)

/-- The paper's cardinality description of `fixedCount`. -/
theorem fixedCount_eq_congruence_card (q M : ℕ) [NeZero q] :
    fixedCount q M = Fintype.card {r : ZMod q // 2 * r = (M : ZMod q)} := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquivRight
    (residueReflection_fixed_iff q M))

/-- Rational odd functions on the entire residue group. -/
def oddResidueSpace (q M : ℕ) : Submodule ℚ (ZMod q → ℚ) :=
  involutionOddSpace (residueReflection q M) (fun _ => True)

/-- The independent residue coordinates of an odd function. -/
abbrev ResidueRepresentative (q M : ℕ) :=
  OrbitRepresentative (residueReflection q M) (fun _ => True) ZMod.val

/-- Restriction to lesser residue representatives gives all free coordinates. -/
noncomputable def oddResidueCoordinates (q M : ℕ) [NeZero q] :
    oddResidueSpace q M ≃ₗ[ℚ] (ResidueRepresentative q M → ℚ) :=
  oddCoordinatesEquiv _ _ _ (residueReflection_involutive q M)
    (fun _ => Iff.rfl) (ZMod.val_injective q)

/-- The dimension/fixed-point identity for the full odd residue space. -/
theorem oddResidue_dimension (q M : ℕ) [NeZero q] :
    2 * Module.finrank ℚ (oddResidueSpace q M) + fixedCount q M = q := by
  classical
  have h := two_finrank_add_fixed (residueReflection q M) (fun _ => True)
    ZMod.val (residueReflection_involutive q M) (fun _ => Iff.rfl)
    (ZMod.val_injective q)
  rw [finrank_involutionOddSpace (residueReflection q M) (fun _ => True) ZMod.val
    (residueReflection_involutive q M) (fun _ => Iff.rfl) (ZMod.val_injective q)] at h
  have hr : Module.finrank ℚ (oddResidueSpace q M) =
      Fintype.card (ResidueRepresentative q M) := by
    rw [(oddResidueCoordinates q M).finrank_eq]
    exact Module.finrank_pi ℚ
  have hf : Fintype.card (SupportedFixed (residueReflection q M) (fun _ => True)) =
      fixedCount q M := by
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => by simp))
  have ha : Fintype.card {r : ZMod q // True} = q := by simp
  rw [Fintype.card_eq_nat_card] at hf ha
  rw [hr]
  simpa only [Fintype.card_eq_nat_card, ResidueRepresentative, hf, ha] using h

/-- The full odd-space dimension is half the number of nonfixed classes. -/
theorem oddResidue_dimension_quotient (q M : ℕ) [NeZero q] :
    Module.finrank ℚ (oddResidueSpace q M) = (q - fixedCount q M) / 2 := by
  have h := oddResidue_dimension q M
  omega

/-- Every freely assignable representative supplies one independent coordinate. -/
theorem oddResidue_dimension_representatives (q M : ℕ) [NeZero q] :
    Module.finrank ℚ (oddResidueSpace q M) = Fintype.card (ResidueRepresentative q M) := by
  rw [(oddResidueCoordinates q M).finrank_eq]
  exact Module.finrank_pi ℚ

/-- Oddness forces zero at every actual fixed point. -/
theorem oddResidue_fixed_zero (q M : ℕ) (f : oddResidueSpace q M)
    (r : ZMod q) (hr : residueReflection q M r = r) : (f : ZMod q → ℚ) r = 0 := by
  have h := f.property.1 r
  rw [hr] at h
  linarith

/-- The full residue space is defined by precisely the endpoint oddness equation. -/
theorem mem_oddResidueSpace_iff (q M : ℕ) (f : ZMod q → ℚ) :
    f ∈ oddResidueSpace q M ↔ ∀ r, f r + f ((M : ZMod q) - r) = 0 := by
  change ((∀ r, f r + f ((M : ZMod q) - r) = 0) ∧
    (∀ r : ZMod q, ¬ True → f r = 0)) ↔ _
  simp

/-- Multiplication by the dilation factor as an additive map of residue groups. -/
noncomputable def gridHom (t g : ℕ) : ZMod g →+ ZMod (t * g) :=
  ZMod.lift g ⟨
    { toFun := fun z : ℤ => (t : ZMod (t * g)) * (z : ZMod (t * g))
      map_zero' := by simp
      map_add' := by intro a b; simp [mul_add] },
    by
      change (t : ZMod (t * g)) * ((g : ℤ) : ZMod (t * g)) = 0
      rw [Int.cast_natCast, ← Nat.cast_mul, ZMod.natCast_self]⟩

/-- The grid map is integer multiplication on integer representatives. -/
@[simp]
theorem gridHom_intCast (t g : ℕ) (z : ℤ) :
    gridHom t g (z : ZMod g) = (t : ZMod (t * g)) * (z : ZMod (t * g)) := by
  simp [gridHom]

/-- The grid map is multiplication on natural representatives as well. -/
@[simp]
theorem gridHom_natCast (t g k : ℕ) :
    gridHom t g (k : ZMod g) = (t * k : ℕ) := by
  have h := gridHom_intCast t g (k : ℤ)
  simpa only [Int.cast_natCast, Nat.cast_mul] using h

/-- No wrap occurs when the least representative is multiplied by the dilation. -/
theorem gridHom_val (t g : ℕ) [NeZero t] [NeZero g] (r : ZMod g) :
    (gridHom t g r).val = t * r.val := by
  have ht : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  have hb : t * r.val < t * g := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt r) ht
  have he : gridHom t g r = ((t * r.val : ℕ) : ZMod (t * g)) := by
    calc
      gridHom t g r = gridHom t g (r.val : ZMod g) :=
        congrArg (gridHom t g) (ZMod.natCast_zmod_val r).symm
      _ = _ := gridHom_natCast t g r.val
  rw [he]
  exact ZMod.val_cast_of_lt hb

/-- The actual grid embedding is injective, including base modulus one. -/
theorem gridHom_injective (t g : ℕ) [NeZero t] [NeZero g] :
    Function.Injective (gridHom t g) := by
  intro r s h
  apply ZMod.val_injective g
  have hv := congrArg ZMod.val h
  rw [gridHom_val, gridHom_val] at hv
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne t)) hv

/-- Grid classes are exactly the residues with representatives divisible by `t`. -/
theorem gridHom_range_iff (t g : ℕ) [NeZero t] [NeZero g] (r : ZMod (t * g)) :
    (∃ s : ZMod g, gridHom t g s = r) ↔ t ∣ r.val := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [gridHom_val]
    exact dvd_mul_right t s.val
  · rintro ⟨k, hk⟩
    have ht : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
    have hb : k < g := by
      apply (Nat.mul_lt_mul_left ht).1
      rw [← hk]
      exact ZMod.val_lt r
    refine ⟨(k : ZMod g), ?_⟩
    apply ZMod.val_injective (t * g)
    rw [gridHom_val, ZMod.val_cast_of_lt hb, hk]

/-- Equivalence with the actual grid subset, proving its cardinality is `g`. -/
noncomputable def gridEquiv (t g : ℕ) [NeZero t] [NeZero g] :
    ZMod g ≃ {r : ZMod (t * g) // t ∣ r.val} :=
  Equiv.ofBijective
    (fun s => ⟨gridHom t g s, (gridHom_range_iff t g _).1 ⟨s, rfl⟩⟩)
    ⟨by
      intro r s h
      exact gridHom_injective t g (congrArg Subtype.val h),
      by
        intro r
        obtain ⟨s, hs⟩ := (gridHom_range_iff t g r).2 r.property
        exact ⟨s, Subtype.ext hs⟩⟩

/-- Dilation intertwines the endpoint reflections. -/
theorem gridHom_reflection (t g N : ℕ) (r : ZMod g) :
    gridHom t g (residueReflection g N r) =
      residueReflection (t * g) (t * N) (gridHom t g r) := by
  simp [residueReflection]

/-- Reflection preserves the grid, in both directions. -/
theorem reflection_grid_iff (t g N : ℕ) [NeZero t] [NeZero g]
    (r : ZMod (t * g)) :
    t ∣ (residueReflection (t * g) (t * N) r).val ↔ t ∣ r.val := by
  have forward : ∀ r : ZMod (t * g), t ∣ r.val →
      t ∣ (residueReflection (t * g) (t * N) r).val := by
    intro r hr
    obtain ⟨s, rfl⟩ := (gridHom_range_iff t g r).2 hr
    apply (gridHom_range_iff t g _).1
    exact ⟨residueReflection g N s, gridHom_reflection t g N s⟩
  constructor
  · intro hr
    simpa only [residueReflection_involutive (t * g) (t * N) r] using
      forward (residueReflection (t * g) (t * N) r) hr
  · exact forward r

/-- The grid fixed points are exactly the embedded fixed points of the base group. -/
noncomputable def gridFixedEquiv (t g N : ℕ) [NeZero t] [NeZero g] :
    FixedResidue g N ≃ SupportedFixed
      (residueReflection (t * g) (t * N)) (fun r => t ∣ r.val) :=
  Equiv.ofBijective
    (fun s => ⟨gridHom t g s, (gridHom_range_iff t g _).1 ⟨s, rfl⟩, by
      rw [← gridHom_reflection, s.property]⟩)
    ⟨by
      intro r s h
      apply Subtype.ext
      exact gridHom_injective t g (congrArg Subtype.val h),
      by
        intro r
        obtain ⟨s, hs⟩ := (gridHom_range_iff t g r).2 r.property.1
        have hf : residueReflection g N s = s := by
          apply gridHom_injective t g
          rw [gridHom_reflection, hs, r.property.2]
        exact ⟨⟨s, hf⟩, Subtype.ext hs⟩⟩

/-- Odd functions with zero values on every grid class, as in `eq:offgrid-space`. -/
def offGridResidueSpace (t g N : ℕ) : Submodule ℚ (ZMod (t * g) → ℚ) :=
  involutionOddSpace (residueReflection (t * g) (t * N)) (fun r => ¬ t ∣ r.val)

/-- Membership is exactly the two equations of `eq:offgrid-space`. -/
theorem mem_offGridResidueSpace_iff (t g N : ℕ) (f : ZMod (t * g) → ℚ) :
    f ∈ offGridResidueSpace t g N ↔
      (∀ r, f r + f (((t * N : ℕ) : ZMod (t * g)) - r) = 0) ∧
        (∀ r, t ∣ r.val → f r = 0) := by
  change ((∀ r, f r + f (((t * N : ℕ) : ZMod (t * g)) - r) = 0) ∧
    (∀ r : ZMod (t * g), ¬ ¬ (t ∣ r.val) → f r = 0)) ↔ _
  simp only [not_not]



/-- The free coordinates of the off-grid space are its two-element off-grid orbits. -/
noncomputable def offGridCoordinates (t g N : ℕ) [NeZero t] [NeZero g] :
    offGridResidueSpace t g N ≃ₗ[ℚ]
      (OrbitRepresentative (residueReflection (t * g) (t * N))
        (fun r => ¬ t ∣ r.val) ZMod.val → ℚ) :=
  oddCoordinatesEquiv _ _ _ (residueReflection_involutive _ _)
    (fun r => not_congr (reflection_grid_iff t g N r))
    (ZMod.val_injective (t * g))

/-- The actual off-grid subset has `(t-1)g` elements. -/
theorem offGrid_card (t g : ℕ) [NeZero t] [NeZero g] :
    Fintype.card {r : ZMod (t * g) // ¬ t ∣ r.val} = (t - 1) * g := by
  classical
  have hg : Fintype.card {r : ZMod (t * g) // t ∣ r.val} = g := by
    rw [← Fintype.card_congr (gridEquiv t g)]
    exact ZMod.card g
  rw [Fintype.card_subtype_compl, ZMod.card, hg]
  have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.2 (NeZero.ne t)
  have he : (t - 1) * g + g = t * g := by
    calc
      (t - 1) * g + g = (t - 1 + 1) * g := by ring
      _ = t * g := by rw [Nat.sub_add_cancel ht]
  omega

/-- A fixed-point set partitions into its grid and off-grid members. -/
theorem fixed_grid_partition (t g N : ℕ) [NeZero t] [NeZero g] :
    Fintype.card (SupportedFixed (residueReflection (t * g) (t * N))
      (fun r => ¬ t ∣ r.val)) + fixedCount g N = fixedCount (t * g) (t * N) := by
  classical
  let σ := residueReflection (t * g) (t * N)
  let e : SupportedFixed σ (fun r => t ∣ r.val) ⊕
      SupportedFixed σ (fun r => ¬ t ∣ r.val) ≃ FixedResidue (t * g) (t * N) :=
    { toFun := Sum.elim (fun r => ⟨r, r.property.2⟩) (fun r => ⟨r, r.property.2⟩)
      invFun := fun r => if h : t ∣ (r : ZMod (t * g)).val then
        Sum.inl ⟨r, h, r.property⟩ else Sum.inr ⟨r, h, r.property⟩
      left_inv := by
        intro r
        cases r with
        | inl r => simp [r.property.1]
        | inr r => simp [r.property.1]
      right_inv := by
        intro r
        dsimp only
        split_ifs <;> rfl }
  have he := Fintype.card_congr e
  have hg := Fintype.card_congr (gridFixedEquiv t g N)
  simp only [Fintype.card_sum] at he
  change fixedCount g N =
    Fintype.card (SupportedFixed (residueReflection (t * g) (t * N))
      (fun r => t ∣ r.val)) at hg
  change Fintype.card (SupportedFixed (residueReflection (t * g) (t * N))
      (fun r => t ∣ r.val)) +
    Fintype.card (SupportedFixed (residueReflection (t * g) (t * N))
      (fun r => ¬ t ∣ r.val)) = fixedCount (t * g) (t * N) at he
  rw [← hg] at he
  simpa only [Nat.add_comm] using he

/-- Subtraction-safe exact nullity arithmetic: twice the dimension plus the
dilated fixed-point count equals the off-grid count plus the base fixed count. -/
theorem offGrid_dimension_exact (t g N : ℕ) [NeZero t] [NeZero g] :
    2 * Module.finrank ℚ (offGridResidueSpace t g N) + fixedCount (t * g) (t * N) =
      (t - 1) * g + fixedCount g N := by
  classical
  have hd := two_finrank_add_fixed (residueReflection (t * g) (t * N))
    (fun r => ¬ t ∣ r.val) ZMod.val (residueReflection_involutive _ _)
    (fun r => not_congr (reflection_grid_iff t g N r))
    (ZMod.val_injective (t * g))
  rw [finrank_involutionOddSpace (residueReflection (t * g) (t * N))
    (fun r => ¬ t ∣ r.val) ZMod.val (residueReflection_involutive _ _)
    (fun r => not_congr (reflection_grid_iff t g N r)) (ZMod.val_injective (t * g))] at hd
  have hr : Module.finrank ℚ (offGridResidueSpace t g N) =
      Fintype.card (OrbitRepresentative (residueReflection (t * g) (t * N))
        (fun r => ¬ t ∣ r.val) ZMod.val) := by
    rw [(offGridCoordinates t g N).finrank_eq]
    exact Module.finrank_pi ℚ
  have hc := offGrid_card t g
  rw [Fintype.card_eq_nat_card] at hc
  simp only [Fintype.card_eq_nat_card, hc] at hd
  have hf := fixed_grid_partition t g N
  simp only [Fintype.card_eq_nat_card] at hf
  rw [hr]
  simp only [Fintype.card_eq_nat_card]
  omega

/-- The numerator in the natural-number version of the increment cannot underflow. -/
theorem offGrid_numerator_nonnegative (t g N : ℕ) [NeZero t] [NeZero g] :
    fixedCount (t * g) (t * N) ≤ (t - 1) * g + fixedCount g N := by
  have h := offGrid_dimension_exact t g N
  omega

/-- The exact quotient formula of `cor:nullity-increment`, with subtraction
performed after adding the base fixed-point count. -/
theorem offGrid_dimension (t g N : ℕ) [NeZero t] [NeZero g] :
    Module.finrank ℚ (offGridResidueSpace t g N) =
      ((t - 1) * g + fixedCount g N - fixedCount (t * g) (t * N)) / 2 := by
  have h := offGrid_dimension_exact t g N
  omega

/-- Translating by a solution identifies a reflection's fixed-point set with the
fixed-point set of negation. -/
noncomputable def fixedTranslationEquiv (q M : ℕ) (a : ZMod q)
    (ha : 2 * a = (M : ZMod q)) : FixedResidue q M ≃ FixedResidue q 0 where
  toFun r := ⟨(r : ZMod q) - a, by
    apply (residueReflection_fixed_iff q 0 _).2
    have hr := (residueReflection_fixed_iff q M r).1 r.property
    linear_combination hr - ha⟩
  invFun r := ⟨(r : ZMod q) + a, by
    apply (residueReflection_fixed_iff q M _).2
    have hr := (residueReflection_fixed_iff q 0 r).1 r.property
    linear_combination hr + ha⟩
  left_inv r := by apply Subtype.ext; simp
  right_inv r := by apply Subtype.ext; simp

/-- A nonempty reflection fiber has the same actual cardinality as negation's fiber. -/
theorem fixedCount_of_solution (q M : ℕ) [NeZero q] (a : ZMod q)
    (ha : 2 * a = (M : ZMod q)) : fixedCount q M = fixedCount q 0 :=
  Fintype.card_congr (fixedTranslationEquiv q M a ha)

/-- On an odd modulus, zero is the only fixed point of negation. -/
theorem fixedCount_zero_odd (q : ℕ) [NeZero q] (hq : q % 2 = 1) :
    fixedCount q 0 = 1 := by
  classical
  have he : Finset.univ.filter (fun r : ZMod q => residueReflection q 0 r = r) = {0} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      residueReflection, Nat.cast_zero, zero_sub, ZMod.neg_eq_self_iff]
    constructor
    · rintro (hr | hr)
      · exact hr
      · omega
    · exact Or.inl
  unfold fixedCount
  rw [Fintype.card_subtype, he]
  simp

/-- On a positive even modulus, the fixed points of negation are zero and the
half-modulus class; they are distinct, so the actual fixed-point count is two. -/
theorem fixedCount_zero_even (q : ℕ) [NeZero q] (hq : q % 2 = 0) :
    fixedCount q 0 = 2 := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hh : q / 2 < q := by omega
  have hv : ((q / 2 : ℕ) : ZMod q).val = q / 2 := ZMod.val_cast_of_lt hh
  have hn : ((q / 2 : ℕ) : ZMod q) ≠ 0 := by
    intro he
    have he' := congrArg ZMod.val he
    rw [hv, ZMod.val_zero] at he'
    omega
  have he : Finset.univ.filter (fun r : ZMod q => residueReflection q 0 r = r) =
      {0, ((q / 2 : ℕ) : ZMod q)} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, residueReflection, Nat.cast_zero, zero_sub,
      ZMod.neg_eq_self_iff]
    constructor
    · rintro (hr | hr)
      · exact Or.inl hr
      · right
        apply ZMod.val_injective q
        rw [hv]
        omega
    · rintro (hr | hr)
      · exact Or.inl hr
      · right
        rw [hr, hv]
        omega
  unfold fixedCount
  rw [Fintype.card_subtype, he]
  simp [Ne.symm hn]

/-- Every reflection on an odd modulus has exactly one fixed residue. -/
theorem fixedCount_odd (q M : ℕ) [NeZero q] (hq : q % 2 = 1) :
    fixedCount q M = 1 := by
  have hc : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.2 (by
    intro hd
    have he := Nat.mod_eq_zero_of_dvd hd
    omega)
  have hu : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).2 hc
  let a : ZMod q := (2 : ZMod q)⁻¹ * (M : ZMod q)
  have ha : 2 * a = (M : ZMod q) := by
    dsimp [a]
    rw [← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
  rw [fixedCount_of_solution q M a ha]
  exact fixedCount_zero_odd q hq

/-- Even endpoint sum on an even modulus gives two actual fixed residues. -/
theorem fixedCount_even_even (q M : ℕ) [NeZero q]
    (hq : q % 2 = 0) (hM : M % 2 = 0) : fixedCount q M = 2 := by
  have he : 2 * (M / 2) = M := by omega
  have ha : 2 * ((M / 2 : ℕ) : ZMod q) = (M : ZMod q) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ZMod q)) he
  rw [fixedCount_of_solution q M ((M / 2 : ℕ) : ZMod q) ha]
  exact fixedCount_zero_even q hq

/-- Odd endpoint sum on an even modulus gives no fixed residue. -/
theorem fixedCount_even_odd (q M : ℕ) [NeZero q]
    (hq : q % 2 = 0) (hM : M % 2 = 1) : fixedCount q M = 0 := by
  have hd : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq
  let π : ZMod q →+* ZMod 2 := ZMod.castHom hd (ZMod 2)
  have hz : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hnone : ∀ r : FixedResidue q M, False := by
    intro r
    have hr := (residueReflection_fixed_iff q M r).1 r.property
    have he := congrArg π hr
    have hm : (M : ZMod 2) = 0 := by
      simpa only [map_mul, map_ofNat, map_natCast, hz, zero_mul] using he.symm
    have hm' := Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff M 2).1 hm)
    omega
  let _ : IsEmpty (FixedResidue q M) := ⟨hnone⟩
  simp [fixedCount]

/-- Complete fixed-point count for every positive modulus and every endpoint sum. -/
theorem fixedCount_formula (q M : ℕ) [NeZero q] :
    fixedCount q M = if q % 2 = 0 then (if M % 2 = 0 then 2 else 0) else 1 := by
  by_cases hq : q % 2 = 0
  · rw [ite_eq_left hq]
    by_cases hM : M % 2 = 0
    · rw [ite_eq_left hM]
      exact fixedCount_even_even q M hq hM
    · rw [ite_eq_right hM]
      exact fixedCount_even_odd q M hq (by omega)
  · rw [ite_eq_right hq]
    exact fixedCount_odd q M (by omega)

/-- A multiple of the modulus has the same reflection as endpoint sum zero. -/
theorem fixedCount_multiple (q N : ℕ) [NeZero q] :
    fixedCount q (q * N) = fixedCount q 0 := by
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun r => by
    simp [residueReflection, Nat.cast_mul]))

/-- Modulus one has one fixed class for every endpoint sum. -/
@[simp]
theorem fixedCount_one (N : ℕ) : fixedCount 1 N = 1 :=
  fixedCount_odd 1 N (by decide)

/-- The modulus-one nullity increment is the floor of `(t-1)/2`, including
`t=1` and `t=2`, with no asymptotic or parity exclusions. -/
theorem offGrid_dimension_modulus_one (t N : ℕ) [NeZero t] :
    Module.finrank ℚ (offGridResidueSpace t 1 N) = (t - 1) / 2 := by
  have h := offGrid_dimension_exact t 1 N
  simp only [Nat.mul_one, fixedCount_one] at h
  rw [fixedCount_multiple, fixedCount_formula] at h
  have ht : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  split_ifs at h <;> omega

/-- At dilation one the off-grid subspace has dimension zero. -/
@[simp]
theorem offGrid_dimension_dilation_one (g N : ℕ) [NeZero g] :
    Module.finrank ℚ (offGridResidueSpace 1 g N) = 0 := by
  have h := offGrid_dimension_exact 1 g N
  simp only [Nat.one_mul, Nat.sub_self, Nat.zero_mul, zero_add] at h
  omega

/-- Finite dimensionality is inherited from the actual finite function space. -/
theorem oddResidue_finiteDimensional (q M : ℕ) [NeZero q] :
    FiniteDimensional ℚ (oddResidueSpace q M) := inferInstance

/-- The off-grid space is a genuine finite-dimensional rational subspace. -/
theorem offGrid_finiteDimensional (t g N : ℕ) [NeZero t] [NeZero g] :
    FiniteDimensional ℚ (offGridResidueSpace t g N) := inferInstance

end SkewCofactorIndependence
