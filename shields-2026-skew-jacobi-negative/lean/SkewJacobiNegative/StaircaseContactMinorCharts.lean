/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseFivePlacements

/-!
# Actual beta charts for the contact families

The beta-coordinate and classification steps of
`cor:staircase-contact-minors` in
`shields-2026-skew-jacobi-negative.tex`.  The charts use decreasing beta
order and include the original zero-gap boundary.  Contact means equality
with an upper interval index, not with an arbitrary matrix entry.
-/

namespace SkewJacobiNegative.StaircaseContactMinors

open Gluing StaircaseFiveFamilies StaircaseFivePlacements

/-- The common decreasing row-beta list, with `q = X.a + X.d` and
`sigma = X.b`. -/
def commonContactRows (X : ContactParameters) : Fin 5 → ℤ :=
  ![X.a + X.d + 4 * X.b, X.a + X.d + 3 * X.b,
    X.a + X.d + 2 * X.b, X.a + X.d + X.b, X.a + X.d]

/-- The decreasing column betas of the rotated first A1 representative. -/
def a1ContactColumnsF (X : ContactParameters) : Fin 5 → ℤ :=
  ![3 * X.b, X.a + 2 * X.b, X.a + X.b, X.a, 0]

/-- The decreasing column betas of the rotated second A1 representative. -/
def a1ContactColumnsH (X : ContactParameters) : Fin 5 → ℤ :=
  ![X.a + 3 * X.b, X.a + 2 * X.b, X.b, X.a, 0]

/-- The decreasing column betas of the rotated first A2 representative. -/
def a2ContactColumnsF (X : ContactParameters) : Fin 5 → ℤ :=
  ![3 * X.b, 2 * X.b, X.a + X.b, X.a, 0]

/-- The decreasing column betas of the rotated second A2 representative. -/
def a2ContactColumnsH (X : ContactParameters) : Fin 5 → ℤ :=
  ![X.a + 3 * X.b, 2 * X.b, X.b, X.a, 0]

/-- The actual A1 profiles give the stated normalized beta chart, including
`X.d = 0`. -/
theorem a1_rotated_chart (X : ContactParameters) :
    (m3F X).rotate.xi = commonContactRows X ∧
      (m3F X).rotate.zeta = a1ContactColumnsF X ∧
      (m3H X).rotate.xi = commonContactRows X ∧
      (m3H X).rotate.zeta = a1ContactColumnsH X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i; fin_cases i
  all_goals
    simp [Profile.xi, Profile.zeta, Profile.rotate, Fin.sum_univ_succ,
      m3F, m3H, commonContactRows, a1ContactColumnsF, a1ContactColumnsH,
      Fin.rev] <;> ring

/-- The actual A2 profiles give the stated normalized beta chart, including
`X.d = 0`. -/
theorem a2_rotated_chart (X : ContactParameters) :
    (m4F X).rotate.xi = commonContactRows X ∧
      (m4F X).rotate.zeta = a2ContactColumnsF X ∧
      (m4H X).rotate.xi = commonContactRows X ∧
      (m4H X).rotate.zeta = a2ContactColumnsH X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext i; fin_cases i
  all_goals
    simp [Profile.xi, Profile.zeta, Profile.rotate, Fin.sum_univ_succ,
      m4F, m4H, commonContactRows, a2ContactColumnsF, a2ContactColumnsH,
      Fin.rev] <;> ring

/-- A gap equals an upper interval index.  Lower gap entries are excluded. -/
def HasIntervalContact (P : Profile 4) : Prop :=
  ∃ k : Fin 4, ∃ i j : Fin 5,
    i ≤ j ∧ (P.g k : ℤ) = P.xi i - P.zeta j

private theorem no_interval_contact_of_separated (P : Profile 4)
    (hsep : ∀ (k : Fin 4) (i : Fin 5), (P.g k : ℤ) < (P.r i : ℤ)) :
    ¬ HasIntervalContact P := by
  rintro ⟨k, i, j, hij, he⟩
  have hz := P.zeta_strictAnti.antitone hij
  have hr := P.xi_sub_zeta i
  have hg := hsep k i
  omega

/-- No member of an actual thick B class has an upper-interval contact.
Every row exceeds `z + w`, every gap is at most `z + w`, and rotation
preserves these bounds. -/
theorem no_interval_contact_B {P : Profile 4} {X : BParameters}
    (h : BMember P X) : ¬ HasIntervalContact P := by
  have hz := X.z_pos
  have hw := X.w_pos
  have hp := X.p_gt
  have hm := X.m_gt
  have hrows : ∀ i : Fin 5,
      X.z + X.w < (X.F.r i : ℤ) ∧ X.z + X.w < (X.H.r i : ℤ) := by
    intro i
    constructor <;> fin_cases i <;>
      simp [BParameters.F, BParameters.H, bProfileF, bProfileH] <;> omega
  have hgaps : ∀ k : Fin 4,
      (X.F.g k : ℤ) ≤ X.z + X.w ∧ (X.H.g k : ℤ) ≤ X.z + X.w := by
    intro k
    constructor <;> fin_cases k <;>
      simp [BParameters.F, BParameters.H, bProfileF, bProfileH] <;> omega
  have hF : ∀ (k : Fin 4) (i : Fin 5), (X.F.g k : ℤ) < (X.F.r i : ℤ) := by
    intro k i
    have := (hrows i).1
    have := (hgaps k).1
    omega
  have hH : ∀ (k : Fin 4) (i : Fin 5), (X.H.g k : ℤ) < (X.H.r i : ℤ) := by
    intro k i
    have := (hrows i).2
    have := (hgaps k).2
    omega
  rcases h with rfl | rfl | rfl | rfl
  · exact no_interval_contact_of_separated X.F hF
  · exact no_interval_contact_of_separated X.F.rotate (fun k i => hF k.rev i.rev)
  · exact no_interval_contact_of_separated X.H hH
  · exact no_interval_contact_of_separated X.H.rotate (fun k i => hH k.rev i.rev)

/-- Every nonrotation interior family is separated from all upper-interval contacts. -/
theorem b_relation_separated {P Q : Profile 4} (h : BRelation P Q) :
    ¬ HasIntervalContact P ∧ ¬ HasIntervalContact Q := by
  obtain ⟨X, hP, hQ⟩ := h
  exact ⟨no_interval_contact_B hP, no_interval_contact_B hQ⟩

/-- A genuine nonrotation equality with an upper-interval contact belongs to
one of the actual contact families.  The family parameters are produced by
the full thick five-row classification. -/
theorem classify_contact_equality (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hgap : ∀ j, 0 < P.g j)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur)
    (hne : P ≠ Q) (hnrot : P ≠ Q.rotate)
    (hc : HasIntervalContact P ∨ HasIntervalContact Q) :
    ContactRelation false P Q ∨ ContactRelation true P Q := by
  rcases (thick_five_full_class P Q hP hQ hgap).mp he with
    h | h | h | h | ⟨X, hPX, hQX⟩
  · exact False.elim (hne h)
  · exact False.elim (hnrot h)
  · exact Or.inl h
  · exact Or.inr h
  · rcases hc with hc | hc
    · exact False.elim (no_interval_contact_B hPX hc)
    · exact False.elim (no_interval_contact_B hQX hc)

end SkewJacobiNegative.StaircaseContactMinors
