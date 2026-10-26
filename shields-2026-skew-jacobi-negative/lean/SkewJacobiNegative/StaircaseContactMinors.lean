/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseContactMinorQuotients
import SkewJacobiNegative.StaircaseContactMinorCharts

/-!
# Actual reduced Toeplitz minors of contact families

The beta charts, coefficient quotient, and determinant reductions for
`cor:staircase-contact-minors` in `shields-2026-skew-jacobi-negative.tex`.
No complete generator is specialized to zero in this correspondence.
-/
namespace SkewJacobiNegative.StaircaseContactMinors
open Gluing StaircaseFiveFamilies StaircaseFivePlacements

/-- The actual localized Jacobi–Trudi matrix in the common row-beta chart. -/
noncomputable def localChartMatrix (X : ContactParameters) (cols : Fin 5 → ℤ) :
    Matrix (Fin 5) (Fin 5) (ContactLocalization X) :=
  fun i j => algebraMap CompleteRing (ContactLocalization X)
    (complete (commonContactRows X i-cols j))

private theorem map_complete_negative (X : ContactParameters) (k : ℤ) (hk : k<0) :
    algebraMap CompleteRing (ContactLocalization X) (complete k)=0 :=
  (congrArg (algebraMap CompleteRing (ContactLocalization X)) (complete_of_neg hk)).trans
    (map_zero _)

private theorem a1F_chart_matrix (X : ContactParameters) :
    localChartMatrix X (a1ContactColumnsF X)=a1MatrixF (contactU X) (contactV X) := by
  have ha := X.a_pos
  have hd := X.d_nonneg
  have hb := X.b_gt
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [localChartMatrix,commonContactRows,a1ContactColumnsF,a1MatrixF,contactU,contactV]
  all_goals first
    | (apply congrArg (algebraMap CompleteRing (ContactLocalization X));
       apply congrArg complete; ring)
    | (apply map_complete_negative X; omega)

private theorem a1H_chart_matrix (X : ContactParameters) :
    localChartMatrix X (a1ContactColumnsH X)=a1MatrixH (contactU X) (contactV X) := by
  have ha := X.a_pos
  have hd := X.d_nonneg
  have hb := X.b_gt
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [localChartMatrix,commonContactRows,a1ContactColumnsH,a1MatrixH,contactU,contactV]
  all_goals first
    | (apply congrArg (algebraMap CompleteRing (ContactLocalization X));
       apply congrArg complete; ring)
    | (apply map_complete_negative X; omega)

private theorem a2F_chart_matrix (X : ContactParameters) :
    localChartMatrix X (a2ContactColumnsF X)=a2MatrixF (contactU X) (contactV X) := by
  have ha := X.a_pos
  have hd := X.d_nonneg
  have hb := X.b_gt
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [localChartMatrix,commonContactRows,a2ContactColumnsF,a2MatrixF,contactU,contactV]
  all_goals first
    | (apply congrArg (algebraMap CompleteRing (ContactLocalization X));
       apply congrArg complete; ring)
    | (apply map_complete_negative X; omega)

private theorem a2H_chart_matrix (X : ContactParameters) :
    localChartMatrix X (a2ContactColumnsH X)=a2MatrixH (contactU X) (contactV X) := by
  have ha := X.a_pos
  have hd := X.d_nonneg
  have hb := X.b_gt
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [localChartMatrix,commonContactRows,a2ContactColumnsH,a2MatrixH,contactU,contactV]
  all_goals first
    | (apply congrArg (algebraMap CompleteRing (ContactLocalization X));
       apply congrArg complete; ring)
    | (apply map_complete_negative X; omega)

private theorem mapped_chart_schur (X : ContactParameters) (P : Profile 4)
    (cols : Fin 5 → ℤ) (hr : P.xi = commonContactRows X) (hc : P.zeta = cols) :
    algebraMap CompleteRing (ContactLocalization X) P.toBetaDiagram.schur =
      (localChartMatrix X cols).det := by
  rw [BetaDiagram.schur, RingHom.map_det]
  congr 1
  ext i j
  change algebraMap CompleteRing (ContactLocalization X)
    (complete (P.xi i - P.zeta j)) = _
  rw [hr, hc]
  rfl

/-- The first actual A1 Schur determinant is the negative reduced Toeplitz minor. -/
theorem a1F_schur_reduction (X : ContactParameters) :
    algebraMap CompleteRing (ContactLocalization X) (m3F X).toBetaDiagram.schur =
      -(contactU X 0)^5 * (a1MinorF (contactCoefficients X)).det := by
  have h := mapped_chart_schur X (m3F X).rotate _
    (a1_rotated_chart X).1 (a1_rotated_chart X).2.1
  rw [Profile.toBetaDiagram_schur, Profile.schur_rotate,
    ← Profile.toBetaDiagram_schur] at h
  rw [h, a1F_chart_matrix, ← contact_convolution, a1_matrixF_reduction]

/-- The second actual A1 Schur determinant is the paired negative minor. -/
theorem a1H_schur_reduction (X : ContactParameters) :
    algebraMap CompleteRing (ContactLocalization X) (m3H X).toBetaDiagram.schur =
      -(contactU X 0)^5 * (a1MinorH (contactCoefficients X)).det := by
  have h := mapped_chart_schur X (m3H X).rotate _
    (a1_rotated_chart X).2.2.1 (a1_rotated_chart X).2.2.2
  rw [Profile.toBetaDiagram_schur, Profile.schur_rotate,
    ← Profile.toBetaDiagram_schur] at h
  rw [h, a1H_chart_matrix, ← contact_convolution, a1_matrixH_reduction]

/-- The first actual A2 Schur determinant is the positive reduced Toeplitz minor. -/
theorem a2F_schur_reduction (X : ContactParameters) :
    algebraMap CompleteRing (ContactLocalization X) (m4F X).toBetaDiagram.schur =
      (contactU X 0)^5 * (a2MinorF (contactCoefficients X)).det := by
  have h := mapped_chart_schur X (m4F X).rotate _
    (a2_rotated_chart X).1 (a2_rotated_chart X).2.1
  rw [Profile.toBetaDiagram_schur, Profile.schur_rotate,
    ← Profile.toBetaDiagram_schur] at h
  rw [h, a2F_chart_matrix, ← contact_convolution, a2_matrixF_reduction]

/-- The second actual A2 Schur determinant is the paired positive minor. -/
theorem a2H_schur_reduction (X : ContactParameters) :
    algebraMap CompleteRing (ContactLocalization X) (m4H X).toBetaDiagram.schur =
      (contactU X 0)^5 * (a2MinorH (contactCoefficients X)).det := by
  have h := mapped_chart_schur X (m4H X).rotate _
    (a2_rotated_chart X).2.2.1 (a2_rotated_chart X).2.2.2
  rw [Profile.toBetaDiagram_schur, Profile.schur_rotate,
    ← Profile.toBetaDiagram_schur] at h
  rw [h, a2H_chart_matrix, ← contact_convolution, a2_matrixH_reduction]

/-- The lower triangular Toeplitz matrix of the quotient coefficients. -/
def quotientToeplitz {R : Type*} [Zero R] (c : Fin 5 → R) :
    Matrix (Fin 5) (Fin 5) R :=
  fun i j => if h : j.val ≤ i.val then c ⟨i.val-j.val, by omega⟩ else 0

/-- The four reduced matrices are actual complementary Toeplitz submatrices. -/
theorem toeplitz_submatrices {R : Type*} [CommRing R] (c : Fin 5 → R) :
    a1MinorF c = (quotientToeplitz c).submatrix ![1,2,4] ![0,1,2] ∧
    a1MinorH c = (quotientToeplitz c).submatrix ![2,3,4] ![0,2,3] ∧
    a2MinorF c = (quotientToeplitz c).submatrix ![1,4] ![0,1] ∧
    a2MinorH c = (quotientToeplitz c).submatrix ![3,4] ![0,3] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Strictly positive gaps place a contact class inside the thick parameter domain. -/
theorem contact_member_d_pos {second : Bool} {P : Profile 4} {X : ContactParameters}
    (hgap : ∀ j, 0 < P.g j) (hm : ContactMember second P X) : 0 < X.d := by
  cases second <;> simp only [ContactMember, Bool.false_eq_true, if_false, if_true] at hm
  all_goals rcases hm with rfl | rfl | rfl | rfl
  all_goals
    first
    | (have h := hgap 0
       simpa [m3F, m3H, m4F, m4H, profile] using h)
    | (have h := hgap 3
       simpa [Profile.rotate, Fin.rev, m3F, m3H, m4F, m4H, profile] using h)

/-- Every member of an A1 class has the same actual localized Schur reduction. -/
theorem a1_member_reduction {P : Profile 4} {X : ContactParameters}
    (hm : ContactMember false P X) :
    algebraMap CompleteRing (ContactLocalization X) P.toBetaDiagram.schur =
      -(contactU X 0)^5 * (a1MinorF (contactCoefficients X)).det := by
  simp only [ContactMember, Bool.false_eq_true, if_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact a1F_schur_reduction X
  · simpa only [Profile.toBetaDiagram_schur, Profile.schur_rotate] using
      a1F_schur_reduction X
  · rw [a1H_schur_reduction, a1_minor_eq]
  · simpa only [Profile.toBetaDiagram_schur, Profile.schur_rotate, a1_minor_eq] using
      a1H_schur_reduction X

/-- Every member of an A2 class has the same actual localized Schur reduction. -/
theorem a2_member_reduction {P : Profile 4} {X : ContactParameters}
    (hm : ContactMember true P X) :
    algebraMap CompleteRing (ContactLocalization X) P.toBetaDiagram.schur =
      (contactU X 0)^5 * (a2MinorF (contactCoefficients X)).det := by
  simp only [ContactMember, if_true] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact a2F_schur_reduction X
  · simpa only [Profile.toBetaDiagram_schur, Profile.schur_rotate] using
      a2F_schur_reduction X
  · rw [a2H_schur_reduction, a2_minor_eq]
  · simpa only [Profile.toBetaDiagram_schur, Profile.schur_rotate, a2_minor_eq] using
      a2H_schur_reduction X

/-- Every genuine thick contact equality produces one of the two stated pairs
of reduced Toeplitz minors, with its actual localization and Schur determinants. -/
theorem contact_minor_correspondence (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hgap : ∀ j, 0 < P.g j)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur)
    (hne : P ≠ Q) (hnrot : P ≠ Q.rotate)
    (hc : HasIntervalContact P ∨ HasIntervalContact Q) :
    (∃ X : ContactParameters, 0 < X.d ∧
      ContactMember false P X ∧ ContactMember false Q X ∧
      algebraMap CompleteRing (ContactLocalization X) P.toBetaDiagram.schur =
        -(contactU X 0)^5 * (a1MinorF (contactCoefficients X)).det ∧
      algebraMap CompleteRing (ContactLocalization X) Q.toBetaDiagram.schur =
        -(contactU X 0)^5 * (a1MinorH (contactCoefficients X)).det ∧
      (a1MinorF (contactCoefficients X)).det = (a1MinorH (contactCoefficients X)).det) ∨
    (∃ X : ContactParameters, 0 < X.d ∧
      ContactMember true P X ∧ ContactMember true Q X ∧
      algebraMap CompleteRing (ContactLocalization X) P.toBetaDiagram.schur =
        (contactU X 0)^5 * (a2MinorF (contactCoefficients X)).det ∧
      algebraMap CompleteRing (ContactLocalization X) Q.toBetaDiagram.schur =
        (contactU X 0)^5 * (a2MinorH (contactCoefficients X)).det ∧
      (a2MinorF (contactCoefficients X)).det = (a2MinorH (contactCoefficients X)).det) := by
  rcases classify_contact_equality P Q hP hQ hgap he hne hnrot hc with
    ⟨X, hPX, hQX⟩ | ⟨X, hPX, hQX⟩
  · exact Or.inl ⟨X, contact_member_d_pos hgap hPX, hPX, hQX,
      a1_member_reduction hPX, (a1_member_reduction hQX).trans
        (congrArg (fun t => -(contactU X 0)^5*t) (a1_minor_eq _)),
      a1_minor_eq _⟩
  · exact Or.inr ⟨X, contact_member_d_pos hgap hPX, hPX, hQX,
      a2_member_reduction hPX, (a2_member_reduction hQX).trans
        (congrArg (fun t => (contactU X 0)^5*t) (a2_minor_eq _)),
      a2_minor_eq _⟩

end SkewJacobiNegative.StaircaseContactMinors
