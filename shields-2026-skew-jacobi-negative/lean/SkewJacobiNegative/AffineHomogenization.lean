/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.RepresentationBridges
import SkewJacobiNegative.FirstVariations
import SkewJacobiNegative.Gluing.RowTransport

/-!
# Faithful affine passage to zero-free boards

The actual map `(X,Y) ↦ (2X+1,2Y)` in `lem:homogenization` and `eq:gamma`
of `shields-2026-skew-jacobi-negative.tex`.  Its equality transport uses the
proved fixed-degree homogeneous determinant, with the omitted unit factors
retained before substitution.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n m : ℕ}

/-- The literal affine map on the entire full-row board. -/
def gamma (D : BetaDiagram n) : BetaDiagram n where
  row i := 2 * D.row i + 1
  col i := 2 * D.col i
  row_strictAnti i j hij := by
    change 2 * D.row j + 1 < 2 * D.row i + 1
    have h := D.row_strictAnti hij
    omega
  col_strictAnti i j hij := by
    change 2 * D.col j < 2 * D.col i
    have h := D.col_strictAnti hij
    omega
  row_nonempty i := by
    change 2 * D.col i < 2 * D.row i + 1
    have h := D.row_nonempty i
    omega

/-- Opposite parity removes units without canceling or deleting any row. -/
theorem gamma_zeroFree (D : BetaDiagram n) : D.gamma.ZeroFree := by
  intro i j h
  change 2 * D.row i + 1 = 2 * D.col j at h
  omega

/-- Every negative position is preserved, including the distinction from original units. -/
theorem gamma_negative_iff (D : BetaDiagram n) (i j : Fin n) :
    D.gamma.row i < D.gamma.col j ↔ D.row i < D.col j := by
  change 2 * D.row i + 1 < 2 * D.col j ↔ D.row i < D.col j
  omega

/-- Connectedness is preserved in both directions under the actual affine coordinate map. -/
theorem gamma_connected_iff (D : BetaDiagram n) : D.gamma.Connected ↔ D.Connected := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro i hi
    have hh := h i hi
    change 2 * D.col i ≤ 2 * D.row ⟨i.val + 1, hi⟩ + 1 at hh
    omega
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro i hi
    have hh := h i hi
    change 2 * D.col i ≤ 2 * D.row ⟨i.val + 1, hi⟩ + 1
    omega

/-- Gamma commutes with the literal half-turn up to its common translation. -/
theorem gamma_rotation (D : BetaDiagram n) :
    D.rotate.gamma.TranslationEquivalent D.gamma.rotate := by
  refine ⟨1, ?_, ?_⟩ <;> intro i <;> simp only [gamma, rotate] <;> ring

/-- The normalized Gamma profile is exactly the inherited affine profile lift. -/
theorem gamma_toProfile (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    D.gamma.toProfile ((D.gamma_connected_iff).mpr hD) =
      (D.toProfile hD).lift Gluing.rowShiftTwoOne := by
  apply Gluing.Profile.eq_of_beta_eq
  · funext i
    rw [D.gamma.toProfile_xi, Gluing.Profile.xi_lift]
    simp only [D.toProfile_xi hD, Gluing.rowShiftTwoOne, gamma]
    ring
  · funext i
    rw [D.gamma.toProfile_zeta, Gluing.Profile.zeta_lift]
    simp only [D.toProfile_zeta hD, Gluing.rowShiftTwoOne, gamma]
    ring

/-- Equality is transported faithfully at the same full row count, with no zero-free premise. -/
theorem gamma_schur_eq_iff_same_order (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) :
    D.gamma.schur = E.gamma.schur ↔ D.schur = E.schur := by
  rw [← D.gamma.toProfile_schur ((D.gamma_connected_iff).mpr hD),
    ← E.gamma.toProfile_schur ((E.gamma_connected_iff).mpr hE),
    D.gamma_toProfile hD, E.gamma_toProfile hE,
    Gluing.Profile.schur_lift_eq_iff, D.toProfile_schur hD, E.toProfile_schur hE]

/-- Row count is produced from equality before the fixed-degree transport is applied. -/
theorem gamma_schur_eq_iff (D : BetaDiagram (n + 1)) (E : BetaDiagram (m + 1))
    (hD : D.Connected) (hE : E.Connected) :
    D.gamma.schur = E.gamma.schur ↔ D.schur = E.schur := by
  constructor
  · intro he
    have hn := D.gamma.row_count_of_schur_eq E.gamma he
    have hnm : n = m := Nat.succ.inj hn
    subst m
    exact (D.gamma_schur_eq_iff_same_order E hD hE).mp he
  · intro he
    have hn := D.row_count_of_schur_eq E he
    have hnm : n = m := Nat.succ.inj hn
    subst m
    exact (D.gamma_schur_eq_iff_same_order E hD hE).mpr he

/-- The actual affine map is injective on literal beta lists. -/
theorem gamma_injective : Function.Injective (@gamma n) := by
  intro D E he
  have hr : D.row = E.row := by
    funext i
    have h := congrArg (fun B : BetaDiagram n => B.row i) he
    change 2 * D.row i + 1 = 2 * E.row i + 1 at h
    omega
  have hc : D.col = E.col := by
    funext i
    have h := congrArg (fun B : BetaDiagram n => B.col i) he
    change 2 * D.col i = 2 * E.col i at h
    omega
  cases D
  cases E
  simp only [BetaDiagram.mk.injEq]
  exact ⟨hr, hc⟩

/-- Gamma is injective on translation classes, including the empty coordinate domain. -/
theorem gamma_translation_iff (D E : BetaDiagram n) :
    D.gamma.TranslationEquivalent E.gamma ↔ D.TranslationEquivalent E := by
  constructor
  · rintro ⟨c, hr, hc⟩
    by_cases hn : 0 < n
    · let t := D.col ⟨0, hn⟩ - E.col ⟨0, hn⟩
      have ht : c = 2 * t := by
        have h := hc ⟨0, hn⟩
        change 2 * D.col ⟨0, hn⟩ = 2 * E.col ⟨0, hn⟩ + c at h
        dsimp [t]
        omega
      refine ⟨t, ?_, ?_⟩
      · intro i
        have h := hr i
        change 2 * D.row i + 1 = 2 * E.row i + 1 + c at h
        omega
      · intro i
        have h := hc i
        change 2 * D.col i = 2 * E.col i + c at h
        omega
    · refine ⟨0, ?_, ?_⟩ <;> intro i <;> have := i.isLt <;> omega
  · rintro ⟨c, hr, hc⟩
    refine ⟨2 * c, ?_, ?_⟩
    · intro i
      change 2 * D.row i + 1 = 2 * E.row i + 1 + 2 * c
      rw [hr i]
      ring
    · intro i
      change 2 * D.col i = 2 * E.col i + 2 * c
      rw [hc i]
      ring

/-- Gamma preserves and reflects rotation classes without imposing a normalization. -/
theorem gamma_rotation_iff (D E : BetaDiagram n) :
    D.gamma.RotationEquivalent E.gamma ↔ D.RotationEquivalent E := by
  constructor
  · rintro ⟨c, hr, hc⟩
    by_cases hn : 0 < n
    · let t := D.row ⟨0, hn⟩ + E.col (⟨0, hn⟩ : Fin n).rev
      have ht : c = 2 * t + 1 := by
        have h := hr ⟨0, hn⟩
        change 2 * D.row ⟨0, hn⟩ + 1 = c - 2 * E.col (⟨0, hn⟩ : Fin n).rev at h
        dsimp [t]
        omega
      refine ⟨t, ?_, ?_⟩
      · intro i
        have h := hr i
        change 2 * D.row i + 1 = c - 2 * E.col i.rev at h
        omega
      · intro i
        have h := hc i
        change 2 * D.col i = c - (2 * E.row i.rev + 1) at h
        omega
    · refine ⟨0, ?_, ?_⟩ <;> intro i <;> have := i.isLt <;> omega
  · rintro ⟨c, hr, hc⟩
    refine ⟨2 * c + 1, ?_, ?_⟩
    · intro i
      change 2 * D.row i + 1 = 2 * c + 1 - 2 * E.col i.rev
      rw [hr i]
      ring
    · intro i
      change 2 * D.col i = 2 * c + 1 - (2 * E.row i.rev + 1)
      rw [hc i]
      ring

end SkewJacobiNegative.BetaDiagram
