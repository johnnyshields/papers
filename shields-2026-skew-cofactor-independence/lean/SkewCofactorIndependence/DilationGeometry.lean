/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.FirstVariations
import SkewCofactorIndependence.DilationAlgebra
import SkewCofactorIndependence.ResidueSpaces
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Dilation of beta geometry

Actual beta lists, signed cofactors, available positions, and endpoint modulus
in `eq:endpoint-modulus` and `thm:dilation`.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators
open StrictTriangularPaths
namespace BetaDiagram
variable {n : ℕ}

/-- Multiplication of both actual beta lists by a positive integer. -/
def dilate (D : BetaDiagram n) (t : ℕ+) : BetaDiagram n where
  row i := (t : ℕ) * D.row i
  col i := (t : ℕ) * D.col i
  row_strictAnti := fun i j hij => mul_lt_mul_of_pos_left
    (D.row_strictAnti hij) (by exact_mod_cast t.property)
  col_strictAnti := fun i j hij => mul_lt_mul_of_pos_left
    (D.col_strictAnti hij) (by exact_mod_cast t.property)
  row_nonempty i := mul_lt_mul_of_pos_left (D.row_nonempty i)
    (by exact_mod_cast t.property)

@[simp] theorem dilate_row (D : BetaDiagram n) (t : ℕ+) (i : Fin n) :
    (D.dilate t).row i = (t : ℕ) * D.row i := rfl
@[simp] theorem dilate_col (D : BetaDiagram n) (t : ℕ+) (i : Fin n) :
    (D.dilate t).col i = (t : ℕ) * D.col i := rfl

theorem Connected.dilate {D : BetaDiagram n} (hD : D.Connected) (t : ℕ+) :
    (D.dilate t).Connected :=
  ⟨hD.1, fun i hi => mul_le_mul_of_nonneg_left (hD.2 i hi)
    (by exact_mod_cast t.property.le)⟩

theorem ZeroFree.dilate {D : BetaDiagram n} (hD : D.ZeroFree) (t : ℕ+) :
    (D.dilate t).ZeroFree := by
  intro i j h
  exact hD i j (mul_left_cancel₀ (by exact_mod_cast t.ne_zero) h)

theorem Normalized.dilate {D : BetaDiagram n} (hD : D.Normalized) (t : ℕ+) :
    (D.dilate t).Normalized := by
  intro hn
  simp [hD hn]

theorem Dense.dilate {D : BetaDiagram n} (hD : D.Dense) (t : ℕ+) :
    (D.dilate t).Dense := fun i j => mul_lt_mul_of_pos_left (hD i j)
      (by exact_mod_cast t.property)

/-- Actual matrix entries commute with the complete-generator substitution. -/
theorem dilate_matrix (D : BetaDiagram n) (t : ℕ+) :
    (D.dilate t).matrix = D.matrix.map (dilation t) := by
  ext i j
  simp only [matrix, Matrix.of_apply, Matrix.map_apply, dilate_row, dilate_col]
  rw [dilation_complete, mul_sub]

theorem dilate_schur (D : BetaDiagram n) (t : ℕ+) :
    (D.dilate t).schur = dilation t D.schur := by
  rw [schur, dilate_matrix, ← dilation_det, schur]

theorem dilate_cofactor (D : BetaDiagram (n + 1)) (t : ℕ+)
    (i j : Fin (n + 1)) :
    (D.dilate t).cofactor i j = dilation t (D.cofactor i j) := by
  rw [cofactor_eq_adjugate, cofactor_eq_adjugate, dilate_matrix, dilation_cofactor]

/-- Rational independence of the actual signed cofactors survives every positive dilation. -/
theorem dilate_cofactors_independent (D : BetaDiagram (n + 1)) (t : ℕ+)
    (h : LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      D.cofactor ij.1 ij.2)) :
    LinearIndependent ℚ (fun ij : Fin (n + 1) × Fin (n + 1) =>
      (D.dilate t).cofactor ij.1 ij.2) := by
  simpa only [dilate_cofactor] using linearIndependent_dilation t h

/-- Strict positive returns, not index-zero matrix entries, commute with dilation. -/
theorem dilation_positiveGap (t : ℕ+) (a b : ℤ) :
    dilation t (positiveGap complete a b) =
      positiveGap complete ((t : ℕ) * a) ((t : ℕ) * b) := by
  have ht : (0 : ℤ) < (t : ℕ) := by exact_mod_cast t.property
  by_cases h : b < a
  · rw [positiveGap_of_lt complete h,
      positiveGap_of_lt complete (mul_lt_mul_of_pos_left h ht),
      dilation_complete, mul_sub]
  · rw [positiveGap_of_le complete (le_of_not_gt h), map_zero,
      positiveGap_of_le complete (mul_le_mul_of_nonneg_left (le_of_not_gt h) ht.le)]

/-- The unit at a grid position is the actual dilated base unit. -/
theorem dilate_unitVariation (D : BetaDiagram (n + 1)) (t : ℕ+) (z : ℤ) :
    (D.dilate t).unitVariation ((t : ℕ) * z) = dilation t (D.unitVariation z) := by
  simp only [unitVariation, map_sum, map_mul, dilate_cofactor,
    dilation_positiveGap, dilate_row, dilate_col]

/-- Membership in the exact finite available-position set. -/
theorem mem_availablePositions (D : BetaDiagram (n + 1)) (z : ℤ) :
    z ∈ D.availablePositions ↔
      D.col (Fin.last n) < z ∧ z < D.row 0 ∧
      (∀ i, z ≠ D.row i) ∧ (∀ j, z ≠ D.col j) := by
  classical
  simp [availablePositions, Finset.mem_Ioo, Finset.mem_image, eq_comm, and_assoc]

/-- A grid position is available exactly when its base position is available. -/
theorem dilate_available_iff (D : BetaDiagram (n + 1)) (t : ℕ+) (z : ℤ) :
    (t : ℕ) * z ∈ (D.dilate t).availablePositions ↔ z ∈ D.availablePositions := by
  have ht : (0 : ℤ) < (t : ℕ) := by exact_mod_cast t.property
  have he (a b : ℤ) : (t : ℕ) * a = (t : ℕ) * b ↔ a = b :=
    ⟨mul_left_cancel₀ (ne_of_gt ht), fun h => congrArg (fun x : ℤ => (t : ℤ) * x) h⟩
  have hl (a b : ℤ) : (t : ℕ) * a < (t : ℕ) * b ↔ a < b := by
    constructor <;> intro h <;> nlinarith
  simp only [mem_availablePositions, dilate_row, dilate_col, hl]
  constructor
  · rintro ⟨hlo, hhi, ha, hb⟩
    exact ⟨hlo, hhi, fun i h => ha i ((he _ _).2 h), fun j h => hb j ((he _ _).2 h)⟩
  · rintro ⟨hlo, hhi, ha, hb⟩
    exact ⟨hlo, hhi, fun i h => ha i ((he _ _).1 h), fun j h => hb j ((he _ _).1 h)⟩

/-- The actual embedding of the available base positions into the dilated grid. -/
def gridPosition (D : BetaDiagram (n + 1)) (t : ℕ+) :
    D.Available ↪ (D.dilate t).Available where
  toFun z := ⟨(t : ℕ) * z.val, (D.dilate_available_iff t z.val).2 z.property⟩
  inj' := by
    intro z w h
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast t.ne_zero) (congrArg Subtype.val h)

/-- Every available grid position has an available base preimage. -/
theorem gridPosition_range (D : BetaDiagram (n + 1)) (t : ℕ+)
    (w : (D.dilate t).Available) :
    (∃ z, D.gridPosition t z = w) ↔ (t : ℤ) ∣ w.val := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.val, rfl⟩
  · rintro ⟨z, hz⟩
    have hp : z ∈ D.availablePositions :=
      (D.dilate_available_iff t z).1 (hz ▸ w.property)
    exact ⟨⟨z, hp⟩, Subtype.ext hz.symm⟩

/-- Extension by zero along the actual grid-position embedding. -/
def gridLift (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.Available → ℚ) →ₗ[ℚ] ((D.dilate t).Available → ℚ) where
  toFun c w := if h : ∃ z, D.gridPosition t z = w then c (Classical.choose h) else 0
  map_add' c d := by funext w; dsimp; split_ifs <;> simp
  map_smul' a c := by funext w; dsimp; split_ifs <;> simp

@[simp] theorem gridLift_gridPosition (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : D.Available → ℚ) (z : D.Available) :
    D.gridLift t c (D.gridPosition t z) = c z := by
  classical
  have h : ∃ x, D.gridPosition t x = D.gridPosition t z := ⟨z, rfl⟩
  simp only [gridLift, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left h]
  congr 1
  exact (D.gridPosition t).injective (Classical.choose_spec h)

theorem gridLift_offGrid (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : D.Available → ℚ) (w : (D.dilate t).Available)
    (hw : ¬ (t : ℤ) ∣ w.val) : D.gridLift t c w = 0 := by
  have hn : ¬ ∃ z, D.gridPosition t z = w := by
    intro h
    exact hw ((D.gridPosition_range t w).1 h)
  change (if h : ∃ z, D.gridPosition t z = w then c (Classical.choose h) else 0) = 0
  rw [dite_eq_right hn]

theorem gridLift_injective (D : BetaDiagram (n + 1)) (t : ℕ+) :
    Function.Injective (D.gridLift t) := by
  intro c d h
  funext z
  simpa using congrFun h (D.gridPosition t z)

/-- Restriction to the inherited available grid. -/
def gridRestrict (D : BetaDiagram (n + 1)) (t : ℕ+) :
    ((D.dilate t).Available → ℚ) →ₗ[ℚ] (D.Available → ℚ) where
  toFun c z := c (D.gridPosition t z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem gridRestrict_gridLift (D : BetaDiagram (n + 1)) (t : ℕ+)
    (c : D.Available → ℚ) : D.gridRestrict t (D.gridLift t c) = c := by
  funext z
  exact D.gridLift_gridPosition t c z

/-- The top row beta of the nonempty actual list. -/
def span (D : BetaDiagram (n + 1)) : ℕ := (D.row 0).toNat

/-- The complete finite family used in the endpoint gcd. -/
def endpointPeriod (D : BetaDiagram (n + 1)) :
    Fin (n + 1) ⊕ Fin (n + 1) → ℕ :=
  Sum.elim (fun i => (D.row 0 - D.row i).natAbs) (fun j => (D.col j).natAbs)

/-- The manuscript's gcd of all row deficits and all column betas. -/
def endpointModulus (D : BetaDiagram (n + 1)) : ℕ :=
  Finset.univ.gcd D.endpointPeriod

theorem endpointModulus_dvd (D : BetaDiagram (n + 1))
    (i : Fin (n + 1) ⊕ Fin (n + 1)) :
    D.endpointModulus ∣ D.endpointPeriod i := Finset.gcd_dvd (Finset.mem_univ i)

/-- Normalization supplies nonnegative columns and strictly positive rows. -/
theorem normalized_bounds (D : BetaDiagram (n + 1)) (hD : D.Normalized) :
    (∀ i, 0 < D.row i ∧ D.row i ≤ D.row 0) ∧
      (∀ j, 0 ≤ D.col j ∧ D.col j < D.row 0) := by
  have hz : D.col (Fin.last n) = 0 := hD (by omega)
  have hc (j : Fin (n + 1)) : 0 ≤ D.col j := by
    rw [← hz]
    exact D.col_strictAnti.antitone (Fin.le_last j)
  constructor
  · intro i
    exact ⟨lt_of_le_of_lt (hc i) (D.row_nonempty i),
      D.row_strictAnti.antitone (Fin.zero_le i)⟩
  · intro j
    exact ⟨hc j, lt_of_lt_of_le (D.row_nonempty j)
      (D.row_strictAnti.antitone (Fin.zero_le j))⟩

@[simp] theorem span_intCast (D : BetaDiagram (n + 1)) (hD : D.Normalized) :
    (D.span : ℤ) = D.row 0 := by
  exact Int.toNat_of_nonneg ((D.normalized_bounds hD).1 0).1.le

/-- The two exterior periods are positive and fit inside the finite word. -/
theorem exterior_periods (D : BetaDiagram (n + 1)) (hn : 1 ≤ n)
    (hc : D.Connected) (hz : D.ZeroFree) (hD : D.Normalized) :
    let u := D.endpointPeriod (Sum.inl ⟨1, by omega⟩)
    let v := D.endpointPeriod (Sum.inr ⟨n - 1, by omega⟩)
    0 < u ∧ 0 < v ∧ u + v ≤ D.span - 1 ∧
      (∀ j, u + D.endpointPeriod (Sum.inr j) ≤ D.span - 1) ∧
      (∀ i, v + D.endpointPeriod (Sum.inl i) ≤ D.span - 1) := by
  have hb := D.normalized_bounds hD
  have hlast : D.col (Fin.last n) = 0 := hD (by omega)
  have hu := D.row_strictAnti
    (show (0 : Fin (n + 1)) < ⟨1, by omega⟩ by change (0 : ℕ) < 1; omega)
  have hv := D.col_strictAnti
    (show (⟨n - 1, by omega⟩ : Fin (n + 1)) < Fin.last n by
      change n - 1 < n; omega)
  have he₁ := hc.2 (0 : Fin (n + 1)) (by change 0 + 1 < n + 1; omega)
  have he₂ := hc.2 (⟨n - 1, by omega⟩ : Fin (n + 1)) (by
    change n - 1 + 1 < n + 1; omega)
  have hfirst : (⟨(0 : Fin (n + 1)).val + 1,
      by simp only [Fin.val_zero]; omega⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := Fin.ext rfl
  have hfinal : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    change n - 1 + 1 = n
    omega
  rw [hfirst] at he₁
  rw [hfinal] at he₂
  have he₁' : D.col 0 < D.row ⟨1, by omega⟩ :=
    lt_of_le_of_ne he₁ (Ne.symm (hz _ _))
  have he₂' : D.col ⟨n - 1, by omega⟩ < D.row (Fin.last n) :=
    lt_of_le_of_ne he₂ (Ne.symm (hz _ _))
  have habs₁ (i : Fin (n + 1)) :
      ((D.row 0 - D.row i).natAbs : ℤ) = D.row 0 - D.row i :=
    Int.natAbs_of_nonneg (sub_nonneg.mpr (hb.1 i).2)
  have habs₂ (j : Fin (n + 1)) : ((D.col j).natAbs : ℤ) = D.col j :=
    Int.natAbs_of_nonneg (hb.2 j).1
  have hN := D.span_intCast hD
  dsimp only [endpointPeriod, Sum.elim_inl, Sum.elim_inr]
  constructor
  · exact_mod_cast (show 0 < ((D.row 0 - D.row ⟨1, by omega⟩).natAbs : ℤ) by
      rw [habs₁]; omega)
  constructor
  · exact_mod_cast (show 0 < ((D.col ⟨n - 1, by omega⟩).natAbs : ℤ) by
      rw [habs₂]; omega)
  constructor
  · have ha := habs₁ ⟨1, by omega⟩
    have hb' := habs₂ ⟨n - 1, by omega⟩
    have hprev := D.col_strictAnti.antitone
      (Fin.zero_le (⟨n - 1, by omega⟩ : Fin (n + 1)))
    have hc' := (hb.2 0).2
    omega
  constructor
  · intro j
    have hj := D.col_strictAnti.antitone (Fin.zero_le j)
    have ha := habs₁ ⟨1, by omega⟩
    have hb' := habs₂ j
    omega
  · intro i
    have hi := D.row_strictAnti.antitone (Fin.le_last i)
    have ha := habs₁ i
    have hb' := habs₂ ⟨n - 1, by omega⟩
    omega

theorem endpointModulus_pos (D : BetaDiagram (n + 1)) (hn : 1 ≤ n) :
    0 < D.endpointModulus := by
  have hu := D.row_strictAnti
    (show (0 : Fin (n + 1)) < ⟨1, by omega⟩ by change (0 : ℕ) < 1; omega)
  have hd := D.endpointModulus_dvd (Sum.inl ⟨1, by omega⟩)
  by_contra h
  have he : D.endpointModulus = 0 := by omega
  rw [he, zero_dvd_iff] at hd
  simp only [endpointPeriod, Sum.elim_inl, Int.natAbs_eq_zero] at hd
  omega

/-- The positive gcd is strictly shorter than the normalized span. -/
theorem endpointModulus_lt_span (D : BetaDiagram (n + 1)) (hn : 1 ≤ n)
    (hD : D.Normalized) : D.endpointModulus < D.span := by
  have hb := D.normalized_bounds hD
  have hu := D.row_strictAnti
    (show (0 : Fin (n + 1)) < ⟨1, by omega⟩ by change (0 : ℕ) < 1; omega)
  have hd := D.endpointModulus_dvd (Sum.inl ⟨1, by omega⟩)
  have hp : 0 < (D.row 0 - D.row ⟨1, by omega⟩).natAbs := by
    rw [Int.natAbs_pos]; omega
  have hl := Nat.le_of_dvd hp hd
  have ha : ((D.row 0 - D.row ⟨1, by omega⟩).natAbs : ℤ) =
      D.row 0 - D.row ⟨1, by omega⟩ := Int.natAbs_of_nonneg (by omega)
  have hN := D.span_intCast hD
  have hrow := (hb.1 ⟨1, by omega⟩).1
  omega

@[simp] theorem dilate_endpointPeriod (D : BetaDiagram (n + 1)) (t : ℕ+)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) :
    (D.dilate t).endpointPeriod i = (t : ℕ) * D.endpointPeriod i := by
  cases i <;> simp [endpointPeriod, ← mul_sub, Int.natAbs_mul]

@[simp] theorem dilate_endpointModulus (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.dilate t).endpointModulus = (t : ℕ) * D.endpointModulus := by
  change (Finset.univ.gcd (fun i => (D.dilate t).endpointPeriod i) : ℕ) =
    (t : ℕ) * (Finset.univ.gcd D.endpointPeriod : ℕ)
  simp_rw [dilate_endpointPeriod]
  simpa using (Finset.gcd_mul_left (s := (Finset.univ :
    Finset (Fin (n + 1) ⊕ Fin (n + 1)))) (f := D.endpointPeriod) (a := (t : ℕ)))

@[simp] theorem dilate_span (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hD : D.Normalized) : (D.dilate t).span = (t : ℕ) * D.span := by
  apply Int.ofNat_inj.mp
  simp only [Nat.cast_mul, span_intCast _ (hD.dilate t), dilate_row, span_intCast _ hD]

/-- Common translation of the actual beta lists. -/
def translate (D : BetaDiagram n) (c : ℤ) : BetaDiagram n where
  row i := D.row i + c
  col i := D.col i + c
  row_strictAnti := fun i j h => by
    have he := D.row_strictAnti h
    change D.row j + c < D.row i + c
    omega
  col_strictAnti := fun i j h => by
    have he := D.col_strictAnti h
    change D.col j + c < D.col i + c
    omega
  row_nonempty i := by
    have he := D.row_nonempty i
    omega

/-- The normalized representative of an arbitrary nonempty beta core. -/
def normalizeBetas (D : BetaDiagram (n + 1)) : BetaDiagram (n + 1) :=
  D.translate (-D.col (Fin.last n))

theorem normalizeBetas_normalized (D : BetaDiagram (n + 1)) :
    D.normalizeBetas.Normalized := by
  intro hn
  have he : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    simp
  change D.col ⟨n + 1 - 1, by omega⟩ + -D.col (Fin.last n) = 0
  rw [he]
  simp

theorem normalizeBetas_connected (D : BetaDiagram (n + 1)) (hc : D.Connected) :
    D.normalizeBetas.Connected :=
  ⟨hc.1, fun i hi => by
    have he := hc.2 i hi
    change D.col i + -D.col (Fin.last n) ≤
      D.row ⟨i.val + 1, hi⟩ + -D.col (Fin.last n)
    omega⟩

theorem normalizeBetas_zeroFree (D : BetaDiagram (n + 1)) (hz : D.ZeroFree) :
    D.normalizeBetas.ZeroFree := by
  intro i j he
  exact hz i j (add_right_cancel he)

/-- The actual beta correspondence of two translated nonempty cores. -/
def translationPositions (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c) :
    D.Available ≃ E.Available where
  toFun z := ⟨z.val - c, by
    rw [mem_availablePositions]
    have hz := (D.mem_availablePositions z.val).1 z.property
    refine ⟨by rw [hc] at hz; omega, by rw [hr] at hz; omega, ?_, ?_⟩
    · intro i he
      exact hz.2.2.1 i (by rw [hr i]; omega)
    · intro j he
      exact hz.2.2.2 j (by rw [hc j]; omega)⟩
  invFun z := ⟨z.val + c, by
    rw [mem_availablePositions]
    have hz := (E.mem_availablePositions z.val).1 z.property
    refine ⟨by rw [hc]; omega, by rw [hr]; omega, ?_, ?_⟩
    · intro i he
      exact hz.2.2.1 i (by rw [hr i] at he; omega)
    · intro j he
      exact hz.2.2.2 j (by rw [hc j] at he; omega)⟩
  left_inv z := Subtype.ext (by simp)
  right_inv z := Subtype.ext (by simp)

/-- Coordinate transport along a genuine common beta translation. -/
def translationCoordinates (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c) :
    (D.Available → ℚ) ≃ₗ[ℚ] (E.Available → ℚ) where
  toFun f z := f ((D.translationPositions E c hr hc).symm z)
  invFun f z := f (D.translationPositions E c hr hc z)
  left_inv f := by funext z; simp
  right_inv f := by funext z; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Cofactors are unchanged by common translation of the actual beta lists. -/
theorem translation_cofactor (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c)
    (i j : Fin (n + 1)) : D.cofactor i j = E.cofactor i j := by
  have hm : D.matrix = E.matrix :=
    TranslationEquivalent.matrix_eq ⟨c, hr, hc⟩
  simp only [cofactor, hm]

/-- Strict return factors depend on differences and commute with common translation. -/
theorem positiveGap_translate (a b c : ℤ) :
    positiveGap complete (a + c) (b + c) = positiveGap complete a b := by
  by_cases h : b < a
  · have h' : b + c < a + c := by omega
    rw [positiveGap_of_lt complete h', positiveGap_of_lt complete h]
    congr 1
    ring
  · have h' : a + c ≤ b + c := by omega
    rw [positiveGap_of_le complete h', positiveGap_of_le complete (le_of_not_gt h)]

/-- Every actual unit translates with its insertion position. -/
theorem translation_unitVariation (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c)
    (z : ℤ) : D.unitVariation (z + c) = E.unitVariation z := by
  simp only [unitVariation, D.translation_cofactor E c hr hc, hr, hc,
    positiveGap_translate]

/-- Actual relation maps, not only determinants, are identified by translation. -/
theorem translation_relationMap (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c)
    (f : D.Available → ℚ) :
    E.unitRelationMap (D.translationCoordinates E c hr hc f) = D.unitRelationMap f := by
  classical
  let e := D.translationPositions E c hr hc
  change (∑ z : E.Available, D.translationCoordinates E c hr hc f z • E.unitVariation z.val) =
    ∑ z : D.Available, f z • D.unitVariation z.val
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro z hz
  have hp : (e z).val + c = z.val := by simp [e, translationPositions]
  rw [← D.translation_unitVariation E c hr hc, hp]
  change f (e.symm (e z)) • D.unitVariation z.val = f z • D.unitVariation z.val
  rw [e.symm_apply_apply]

/-- Actual kernel equivalence under common beta translation. -/
def translationKernelEquiv (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c) :
    D.unitKernel ≃ₗ[ℚ] E.unitKernel where
  toFun f := ⟨D.translationCoordinates E c hr hc f.val, by
    change E.unitRelationMap _ = 0
    rw [D.translation_relationMap E c hr hc]
    exact f.property⟩
  invFun f := ⟨(D.translationCoordinates E c hr hc).symm f.val, by
    have he := D.translation_relationMap E c hr hc
      ((D.translationCoordinates E c hr hc).symm f.val)
    rw [LinearEquiv.apply_symm_apply] at he
    change D.unitRelationMap ((D.translationCoordinates E c hr hc).symm f.val) = 0
    rw [← he]
    exact f.property⟩
  left_inv f := Subtype.ext (by simp)
  right_inv f := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The canonical normalization kernel equivalence points from normalized to original
coordinates. -/
def normalizationKernelEquiv (D : BetaDiagram (n + 1)) :
    D.normalizeBetas.unitKernel ≃ₗ[ℚ] D.unitKernel :=
  D.normalizeBetas.translationKernelEquiv D (-D.col (Fin.last n))
    (fun _ => rfl) (fun _ => rfl)

/-- Normalization after dilation is the same common translation by the dilated bottom column. -/
def dilatedNormalizationPositions (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.normalizeBetas.dilate t).Available ≃ (D.dilate t).Available :=
  (D.normalizeBetas.dilate t).translationPositions (D.dilate t)
    (-(t : ℕ) * D.col (Fin.last n))
    (fun i => by
      change (t : ℤ) * (D.row i + -D.col (Fin.last n)) =
        (t : ℤ) * D.row i + (-(t : ℤ)) * D.col (Fin.last n)
      ring)
    (fun j => by
      change (t : ℤ) * (D.col j + -D.col (Fin.last n)) =
        (t : ℤ) * D.col j + (-(t : ℤ)) * D.col (Fin.last n)
      ring)

/-- Transport available coordinates from the normalized dilation to the original dilation. -/
def dilatedNormalizationCoordinates (D : BetaDiagram (n + 1)) (t : ℕ+) :
    ((D.normalizeBetas.dilate t).Available → ℚ) ≃ₗ[ℚ] ((D.dilate t).Available → ℚ) :=
  (D.normalizeBetas.dilate t).translationCoordinates (D.dilate t)
    (-(t : ℕ) * D.col (Fin.last n))
    (fun i => by
      change (t : ℤ) * (D.row i + -D.col (Fin.last n)) =
        (t : ℤ) * D.row i + (-(t : ℤ)) * D.col (Fin.last n)
      ring)
    (fun j => by
      change (t : ℤ) * (D.col j + -D.col (Fin.last n)) =
        (t : ℤ) * D.col j + (-(t : ℤ)) * D.col (Fin.last n)
      ring)

/-- Transport the unit kernel from the normalized dilation to the original dilation. -/
def dilatedNormalizationKernelEquiv (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.normalizeBetas.dilate t).unitKernel ≃ₗ[ℚ] (D.dilate t).unitKernel :=
  (D.normalizeBetas.dilate t).translationKernelEquiv (D.dilate t)
    (-(t : ℕ) * D.col (Fin.last n))
    (fun i => by
      change (t : ℤ) * (D.row i + -D.col (Fin.last n)) =
        (t : ℤ) * D.row i + (-(t : ℤ)) * D.col (Fin.last n)
      ring)
    (fun j => by
      change (t : ℤ) * (D.col j + -D.col (Fin.last n)) =
        (t : ℤ) * D.col j + (-(t : ℤ)) * D.col (Fin.last n)
      ring)

theorem normalizeBetas_cofactor (D : BetaDiagram (n + 1)) (i j : Fin (n + 1)) :
    D.normalizeBetas.cofactor i j = D.cofactor i j :=
  D.normalizeBetas.translation_cofactor D (-D.col (Fin.last n))
    (fun _ => rfl) (fun _ => rfl) i j

/-- Translation transports the actual kernel as a submodule of the whole coordinate space. -/
theorem translation_unitKernel_map (D E : BetaDiagram (n + 1)) (c : ℤ)
    (hr : ∀ i, D.row i = E.row i + c) (hc : ∀ j, D.col j = E.col j + c) :
    D.unitKernel.map (D.translationCoordinates E c hr hc).toLinearMap = E.unitKernel := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    change E.unitRelationMap _ = 0
    exact (D.translation_relationMap E c hr hc g).trans hg
  · intro hf
    refine ⟨(D.translationCoordinates E c hr hc).symm f, ?_, by simp⟩
    have he := D.translation_relationMap E c hr hc
      ((D.translationCoordinates E c hr hc).symm f)
    rw [LinearEquiv.apply_symm_apply] at he
    change D.unitRelationMap _ = 0
    rw [← he]
    exact hf

theorem dilatedNormalization_kernel_map (D : BetaDiagram (n + 1)) (t : ℕ+) :
    (D.normalizeBetas.dilate t).unitKernel.map
      (D.dilatedNormalizationCoordinates t).toLinearMap = (D.dilate t).unitKernel :=
  (D.normalizeBetas.dilate t).translation_unitKernel_map (D.dilate t)
    (-(t : ℕ) * D.col (Fin.last n))
    (fun i => by
      change (t : ℤ) * (D.row i + -D.col (Fin.last n)) =
        (t : ℤ) * D.row i + (-(t : ℤ)) * D.col (Fin.last n)
      ring)
    (fun j => by
      change (t : ℤ) * (D.col j + -D.col (Fin.last n)) =
        (t : ℤ) * D.col j + (-(t : ℤ)) * D.col (Fin.last n)
      ring)

/-- Canonical coordinate transport from normalized beta lists to the original lists. -/
def normalizationCoordinates (D : BetaDiagram (n + 1)) :
    (D.normalizeBetas.Available → ℚ) ≃ₗ[ℚ] (D.Available → ℚ) :=
  D.normalizeBetas.translationCoordinates D (-D.col (Fin.last n))
    (fun _ => rfl) (fun _ => rfl)

/-- Identify normalized available positions with the original available positions. -/
def normalizationPositions (D : BetaDiagram (n + 1)) :
    D.normalizeBetas.Available ≃ D.Available :=
  D.normalizeBetas.translationPositions D (-D.col (Fin.last n))
    (fun _ => rfl) (fun _ => rfl)

theorem normalization_kernel_map (D : BetaDiagram (n + 1)) :
    D.normalizeBetas.unitKernel.map D.normalizationCoordinates.toLinearMap = D.unitKernel :=
  D.normalizeBetas.translation_unitKernel_map D (-D.col (Fin.last n))
    (fun _ => rfl) (fun _ => rfl)

end BetaDiagram
end SkewCofactorIndependence
