-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/RowTransport.lean
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import GluingCore.Homogenization

/-!
# The row-inner transport

Formalizes `shields-2026-skew-factor-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
`lem:gluing-row-transport`.

For `q ≥ 2` and `0 ≤ w < q` the affine profile map `𝓛_{q,w}` (`Profile.lift`) is induced on skew
Schur functions by the substitution `h̃_j ↦ h̃_{qj+w}` of the homogenized ring (`rowSubst`).  We
prove:

* `Profile.schurHom_lift`, `Profile.schur_lift`: the homogenized Jacobi--Trudi determinant of
  `𝓛_{q,w} D` is the substitution of that of `D`, and specializing the unit variable gives
  `s_{𝓛 D} = subst (s_D)`;
* `rowSubst_injective`, `rowUnsubst_rowSubst`: the substitution is injective, with an explicit
  left inverse;
* `Profile.schur_lift_eq_iff`: for profiles with the same number of rows,
  `s_D = s_{D'} ↔ s_{𝓛 D} = s_{𝓛 D'}`;
* `Profile.negativePositions_lift`: `𝓛` preserves the set of positions `(i, j)` with
  `ξ_i - ζ_j < 0`; commutation with rotation is `Profile.lift_rotate`;
* `Profile.lift_bijOn_schurClass`: the full bijection of Schur classes, with the row
  invariants `ReinerRowInvariants` carried as an explicit hypothesis `hR`, discharged by
  `reinerRowInvariants` (`GluingCore.RowInvariants`).

Sorry-free.
-/

namespace GluingCore

open MvPolynomial

/-- The substitution `h̃_j ↦ h̃_{qj+w}`, `j ≥ 0`, on the homogenized ring. -/
noncomputable def rowSubst (s : RowShift) : HomLambda →ₐ[ℚ] HomLambda :=
  rename fun j : ℕ => s.q * j + s.w

/-- The explicit left inverse `h̃_k ↦ h̃_{(k - w) / q}` of `rowSubst`. -/
noncomputable def rowUnsubst (s : RowShift) : HomLambda →ₐ[ℚ] HomLambda :=
  rename fun k : ℕ => (k - s.w) / s.q

theorem rowSubst_injective (s : RowShift) : Function.Injective (rowSubst s) := by
  have hq : 0 < s.q := by have := s.two_le_q; omega
  refine rename_injective _ fun a b hab => ?_
  have hab' : s.q * a + s.w = s.q * b + s.w := hab
  exact Nat.eq_of_mul_eq_mul_left hq (by omega)

/-- The substitution has a left inverse. -/
theorem rowUnsubst_rowSubst (s : RowShift) (p : HomLambda) : rowUnsubst s (rowSubst s p) = p := by
  have hq : 0 < s.q := by have := s.two_le_q; omega
  simp only [rowUnsubst, rowSubst]
  rw [← AlgHom.comp_apply, rename_comp_rename]
  have : ((fun k : ℕ => (k - s.w) / s.q) ∘ fun j : ℕ => s.q * j + s.w) = id := by
    funext j
    change (s.q * j + s.w - s.w) / s.q = j
    rw [Nat.add_sub_cancel]
    exact Nat.mul_div_cancel_left j hq
  rw [this, rename_id]
  rfl

theorem rowSubst_hTilde (s : RowShift) (k : ℤ) :
    rowSubst s (hTilde k) = hTilde (s.q * k + s.w) := by
  have hw := s.w_lt_q
  have hq := s.two_le_q
  unfold hTilde rowSubst
  by_cases hk : k < 0
  · have : (s.q : ℤ) * k + s.w < 0 := by nlinarith
    simp [hk, this]
  · push Not at hk
    have h2 : ¬ ((s.q : ℤ) * k + s.w < 0) := by
      have : (0 : ℤ) ≤ s.q * k := by positivity
      omega
    obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp only [not_lt.mpr (Int.natCast_nonneg t), ite_false, h2, rename_X, Int.toNat_natCast]
    rw [show ((s.q : ℤ) * t + s.w).toNat = s.q * t + s.w by omega]

namespace Profile

variable {n : ℕ}

/-- **The substitution carries the homogenized skew Schur function of `D` to that of
`𝓛_{q,w} D`.** -/
theorem schurHom_lift (s : RowShift) (P : Profile n) :
    (P.lift s).schurHom = rowSubst s P.schurHom := by
  rw [schurHom, schurHom, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [rowSubst_hTilde, xi_lift, zeta_lift]
  rw [show (s.q : ℤ) * P.xi i + s.w - s.q * P.zeta j = s.q * (P.xi i - P.zeta j) + s.w by ring]

/-- `s_{𝓛_{q,w} D}` is the specialization of the substituted homogenized function of `D`. -/
theorem schur_lift (s : RowShift) (P : Profile n) :
    (P.lift s).schur = dehom (rowSubst s P.schurHom) := by
  rw [← dehom_schurHom, schurHom_lift]

/-- **Transport of equalities.**  For profiles with the same number of rows,
`s_D = s_{D'}` exactly when `s_{𝓛_{q,w} D} = s_{𝓛_{q,w} D'}`.  The forward direction uses the
substitution; the converse uses its left inverse (injectivity) and that both homogenized
functions are homogeneous of the same degree. -/
theorem schur_lift_eq_iff (s : RowShift) (P Q : Profile n) :
    (P.lift s).schur = (Q.lift s).schur ↔ P.schur = Q.schur := by
  rw [schur_eq_iff_schurHom_eq, schur_eq_iff_schurHom_eq, schurHom_lift, schurHom_lift]
  exact (rowSubst_injective s).eq_iff

/-- The positions `(i, j)` at which the Jacobi--Trudi index `ξ_i - ζ_j` is negative. -/
def negativePositions (P : Profile n) : Set (Fin (n + 1) × Fin (n + 1)) :=
  {p | P.xi p.1 - P.zeta p.2 < 0}

/-- **`𝓛_{q,w}` preserves the set of positions with negative Jacobi--Trudi index**, including
the positions where `ξ_i = ζ_j`. -/
theorem negativePositions_lift (s : RowShift) (P : Profile n) :
    (P.lift s).negativePositions = P.negativePositions := by
  have hw := s.w_lt_q
  have hq := s.two_le_q
  ext ⟨i, j⟩
  simp only [negativePositions, Set.mem_ofPred_eq, xi_lift, zeta_lift]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have : (0 : ℤ) ≤ s.q * (P.xi i - P.zeta j) := by positivity
    nlinarith
  · intro h
    nlinarith

/-- The set of profiles with `n + 1` rows and the skew Schur function of `D`: the part of the
Schur class of `D` with a fixed number of rows (the whole class is `GluingCore.schurClass`). -/
def schurFiber (D : Profile n) : Set (Profile n) := {P | P.schur = D.schur}

/-- **A profile with the function of `𝓛_{q,w} D` has the same number of rows as `D`**, given the
row invariants `hR : ReinerRowInvariants` (proved as `reinerRowInvariants`). -/
theorem rows_eq_of_schur_eq_lift (hR : ReinerRowInvariants) (s : RowShift) {m : ℕ}
    (D : Profile n) (H : Profile m) (h : H.schur = (D.lift s).schur) : m = n :=
  (hR m n H (D.lift s) h).1

/-- **The bijection of Schur classes** (`lem:gluing-row-transport`).  Given the row
invariants `ReinerRowInvariants` (carried as `hR`, proved as `reinerRowInvariants`), `𝓛_{q,w}`
bijects the profiles whose skew Schur function is `s_D` with those whose skew Schur function is
`s_{𝓛_{q,w} D}`.  By
`rows_eq_of_schur_eq_lift` the second set already contains only profiles with `n + 1` rows, so
it is all of the Schur class of `𝓛_{q,w} D`.  Injectivity of `𝓛` is unconditional; so is the
forward inclusion. -/
theorem lift_bijOn_schurClass (hR : ReinerRowInvariants) (s : RowShift) (D : Profile n) :
    Set.BijOn (lift s) (schurFiber D) (schurFiber (D.lift s)) := by
  refine ⟨fun P hP => ?_, (lift_injective s).injOn, fun H hH => ?_⟩
  · exact (schur_lift_eq_iff s P D).mpr hP
  · obtain ⟨-, hrows, hgaps⟩ := hR n n H (D.lift s) hH
    rw [rowMultiset_lift] at hrows
    rw [gapMultiset_lift] at hgaps
    have hres : H.HasResidue s := by
      have hq : 0 < s.q := by have := s.two_le_q; omega
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have : H.r i ∈ Multiset.map (fun x => s.q * x + s.w) D.rowMultiset := by
          rw [← hrows]; exact mem_rowMultiset.mpr ⟨i, rfl⟩
        obtain ⟨x, -, hx⟩ := Multiset.mem_map.mp this
        rw [← hx, Nat.mul_add_mod, Nat.mod_eq_of_lt s.w_lt_q]
      · have : H.g j ∈ Multiset.map (fun x => s.q * x + s.w) D.gapMultiset := by
          rw [← hgaps]; exact mem_gapMultiset.mpr ⟨j, rfl⟩
        obtain ⟨x, -, hx⟩ := Multiset.mem_map.mp this
        rw [← hx, Nat.mul_add_mod, Nat.mod_eq_of_lt s.w_lt_q]
    have hlen : ∀ i, s.q ≤ H.r i := fun i => by
      have : H.r i ∈ Multiset.map (fun x => s.q * x + s.w) D.rowMultiset := by
        rw [← hrows]; exact mem_rowMultiset.mpr ⟨i, rfl⟩
      obtain ⟨x, hx, hx'⟩ := Multiset.mem_map.mp this
      obtain ⟨j, rfl⟩ := mem_rowMultiset.mp hx
      have := D.r_pos j
      rw [← hx']
      nlinarith
    refine ⟨H.divide s hres hlen, ?_, lift_divide s H hres hlen⟩
    have h1 : ((H.divide s hres hlen).lift s).schur = (D.lift s).schur := by
      rw [lift_divide]; exact hH
    exact (schur_lift_eq_iff s _ D).mp h1

end Profile

/-- The parameters `q = 2`, `w = 1`. -/
def rowShiftTwoOne : RowShift where
  q := 2
  w := 1
  two_le_q := le_refl _
  w_lt_q := by norm_num

/-- The image of the hook `(2,1)` under `𝓛_{2,1}` has profile `(5, 3; 1)` and beta lists
`ξ = (7, 3)`, `ζ = (2, 0)`. -/
example : (hookProfile.lift rowShiftTwoOne).r 0 = 5 ∧ (hookProfile.lift rowShiftTwoOne).r 1 = 3 ∧
    (hookProfile.lift rowShiftTwoOne).g 0 = 1 ∧ (hookProfile.lift rowShiftTwoOne).xi 0 = 7 ∧
    (hookProfile.lift rowShiftTwoOne).xi 1 = 3 ∧ (hookProfile.lift rowShiftTwoOne).zeta 0 = 2 ∧
    (hookProfile.lift rowShiftTwoOne).zeta 1 = 0 := by
  decide

/-- The substitution at `q = 2`, `w = 1`, applied to `s_{(2,1)} = h₁ h₂ - h₃`, with the padding
`h̃₀ ↦ h̃₁`: `s_{𝓛_{2,1}(2,1)} = h₃ h₅ - h₇ h₁`. -/
theorem schur_lift_hook :
    (hookProfile.lift rowShiftTwoOne).schur = X 3 * X 5 - X 7 * X 1 := by
  have h1 : (hookProfile.lift rowShiftTwoOne).xi 0 = 7 := by decide
  have h2 : (hookProfile.lift rowShiftTwoOne).xi 1 = 3 := by decide
  have h3 : (hookProfile.lift rowShiftTwoOne).zeta 0 = 2 := by decide
  have h4 : (hookProfile.lift rowShiftTwoOne).zeta 1 = 0 := by decide
  have e1 : hh 1 = X 1 := by simpa using hh_pnat 1
  have e3 : hh 3 = X 3 := by simpa using hh_pnat 3
  have e5 : hh 5 = X 5 := by simpa using hh_pnat 5
  have e7 : hh 7 = X 7 := by simpa using hh_pnat 7
  rw [Profile.schur, Matrix.det_fin_two]
  simp [h1, h2, h3, h4, e1, e3, e5, e7]
  ring

end GluingCore
