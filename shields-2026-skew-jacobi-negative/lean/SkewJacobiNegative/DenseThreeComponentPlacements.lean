/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.ThreeComponentContexts
import SkewJacobiNegative.DenseFourRemainder
import SkewJacobiNegative.FourRowBorders

/-!
# Dense four-row cores in three-component parents

Actual connected intermediates, strict first markers, and arbitrary-mate
component recovery for `lem:three-component-forms` and
`eq:auxiliary-parent-functions` in `shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative.BetaDiagram
set_option backward.isDefEq.respectTransparency false

theorem extendTop_schur_parameter_congr {n : ℕ} (Q : BetaDiagram (n+2))
    {t u : ℤ} (he : t = u) (ht : 0 < t) (hu : 0 < u) :
    (Q.extendTop t ht).schur = (Q.extendTop u hu).schur := by
  cases he
  rfl

theorem extendBottom_schur_parameter_congr {n : ℕ} (Q : BetaDiagram (n+2))
    {t u : ℤ} (he : t = u) (ht : 0 < t) (hu : 0 < u) :
    (Q.extendBottom t ht).schur = (Q.extendBottom u hu).schur := by
  cases he
  rfl

theorem endpointDifference_parameter_congr {n : ℕ} (Q : BetaDiagram (n+2))
    {t u : ℤ} (he : t = u) (ht : 0 < t) (hu : 0 < u) :
    Q.endpointDifference t ht = Q.endpointDifference u hu := by
  cases he
  rfl

theorem positiveBorder_tied_first_derivative_of_eq {n : ℕ}
    (Q : BetaDiagram (n+2)) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (he : u = v) :
    MvPolynomial.pderiv (Q.positiveBorder u v hu hv).borderSecondGenerator
      (Q.positiveBorder u v hu hv).schur =
        (-1 : CompleteRing)^(n+1) *
          ((Q.extendTop u hu).schur + (Q.extendBottom v hv).schur) := by
  cases he
  exact SkewJacobiNegative.FourRowBorders.BetaDiagram.positiveBorder_tied_first_derivative Q u hu

theorem borderDifference_eq_zero_of_eq {n : ℕ} (Q : BetaDiagram (n+2))
    {u v : ℤ} (he : u = v) (hu : 0 < u) (hv : 0 < v) :
    Q.borderDifference u v hu hv = 0 := by
  cases he
  simp only [borderDifference, sub_self]

/-- The actual two-row diagram whose determinant is `A_L`. -/
def threeComponentA (P : ThreeComponentParameters) : BetaDiagram 2 where
  row := ![P.m + P.left + P.u, P.m + P.left]
  col := ![P.m + P.left - P.ell, 0]
  row_strictAnti := by
    intro i j hij
    have hu := P.u_pos
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  col_strictAnti := by
    intro i j hij
    have hm := P.m_pos
    have hg := P.g₁_pos
    fin_cases i <;> fin_cases j <;>
      simp [ThreeComponentParameters.left] at hij ⊢ <;> omega
  row_nonempty := by
    intro i
    have hu := P.u_pos
    have hℓ := P.ell_pos
    have hm := P.m_pos
    have hL := P.left_pos
    fin_cases i <;> simp <;> omega

theorem threeComponentA_dense (P : ThreeComponentParameters) : (threeComponentA P).Dense := by
  intro i j
  have hu := P.u_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hL := P.left_pos
  fin_cases i <;> fin_cases j <;> simp [threeComponentA] <;> omega


theorem threeComponentA_largestLabel (P : ThreeComponentParameters) :
    (threeComponentA P).largestLabel = P.m + P.left + P.u := by
  simp [largestLabel, threeComponentA, Fin.cons, Fin.cases, Fin.induction,
    Fin.induction.go]
/-- The polynomial called `A_L` is not supplied as an irreducibility premise. -/
theorem threeComponentA_schur (P : ThreeComponentParameters) :
    (threeComponentA P).schur =
      complete (P.ell + P.u) * complete (P.m + P.left) -
        complete P.ell * complete (P.m + P.left + P.u) := by
  simp only [schur, Matrix.det_fin_two, matrix, Matrix.of_apply, threeComponentA]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
  have h₁ : P.m + P.left + P.u - (P.m + P.left - P.ell) = P.ell + P.u := by ring
  have h₂ : P.m + P.left - (P.m + P.left - P.ell) = P.ell := by ring
  rw [h₁, h₂]
  ring

theorem threeComponentA_irreducible (P : ThreeComponentParameters) :
    Irreducible (threeComponentA P).schur :=
  (threeComponentA P).schur_irreducible ((threeComponentA_dense P).connected (by omega))

theorem threeComponentA_complete_not_dvd (P : ThreeComponentParameters)
    (s : ℤ) (hs : 0 < s) : ¬ complete s ∣ (threeComponentA P).schur :=
  (threeComponentA P).complete_not_dvd_connected
    ((threeComponentA_dense P).connected (by omega)) s hs

/-- The five-row intermediate retains the exact ordered lists of `eq:intermediate-U`. -/
theorem threeComponentU_lists (Q : BetaDiagram 4) (ell x u : ℤ)
    (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).row =
      ![Q.row 0 + x + u, Q.row 0 + x, Q.row 1, Q.row 2, Q.row 3] ∧
    (Q.threeComponentU ell x u hℓ hx hu).col =
      ![Q.row 0 + x - ell, Q.col 0, Q.col 1, Q.col 2, Q.col 3] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [threeComponentU, extendTop, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

/-- Its connectedness is derived from the genuine dense core. -/
theorem dense_threeComponentU_connected (Q : BetaDiagram 4) (hD : Q.Dense)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).Connected :=
  Q.threeComponentU_connected (Q.positiveCorner_of_nonnegative hD.nonnegative)
    ell x u hℓ hx hu

/-- The only negative entries of the dense-core intermediate form its true first-column strip. -/
theorem dense_threeComponentU_negative_iff (Q : BetaDiagram 4) (hD : Q.Dense)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u)
    (i j : Fin 5) :
    (Q.threeComponentU ell x u hℓ hx hu).row i <
        (Q.threeComponentU ell x u hℓ hx hu).col j ↔ 2 ≤ i.val ∧ j = 0 := by
  cases j using Fin.cases with
  | zero =>
    cases i using Fin.cases with
    | zero => simp [threeComponentU]; omega
    | succ i =>
      cases i using Fin.cases with
      | zero => simp [threeComponentU, extendTop]; omega
      | succ i =>
        have hr := Q.row_strictAnti.antitone (Fin.zero_le i.succ)
        simp only [threeComponentU, Fin.cons_succ, Fin.cons_zero, extendTop,
          Fin.succ_ne_zero, if_false, Fin.val_succ, and_true]
        omega
  | succ j =>
    have hn : j.succ ≠ 0 := Fin.succ_ne_zero j
    cases i using Fin.cases with
    | zero =>
      have h := hD 0 j
      simp only [threeComponentU, Fin.cons_zero, Fin.cons_succ, hn, and_false,
        Fin.val_zero, Fin.val_succ]
      exact iff_false_intro (by omega)
    | succ i =>
      have h := (Q.extendTop_dense hD x (by omega)) i j
      simp only [threeComponentU, Fin.cons_succ, hn, and_false]
      exact iff_false_intro (not_lt_of_ge h.le)

/-- A concrete board equality, not a negative-partition assumption. -/
theorem dense_threeComponentU_negativeSites (Q : BetaDiagram 4) (hD : Q.Dense)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    negativeSites (Q.threeComponentU ell x u hℓ hx hu) =
      {(2, 0), (3, 0), (4, 0)} := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [negativeSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Q.dense_threeComponentU_negative_iff hD ell x u hℓ hx hu]
  fin_cases i <;> fin_cases j <;> simp

/-- The dense intermediate has exactly three negative indices. -/
theorem dense_threeComponentU_negativeCount (Q : BetaDiagram 4) (hD : Q.Dense)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    negativeCount (Q.threeComponentU ell x u hℓ hx hu) = 3 := by
  rw [negativeCount, Q.dense_threeComponentU_negativeSites hD ell x u hℓ hx hu]
  decide

/-- The strict top first marker in `eq:first-marker-table`, extracted after corner erasure. -/
theorem threeEndContext_top_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (huv : P.u < P.v) :
    let B := (Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.threeEndContext P).schur) =
        -(complete (P.ell + P.u) * complete P.m * Q.schur) := by
  dsimp only
  simp only [threeEndContext, singletonContext, shifted_schur]
  change MvPolynomial.pderiv _ (eraseGenerator _
    ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).schur) = _
  rw [positiveBorder_top_coefficient _ _ _ _ _ huv,
    threeEndCore_extendTop_schur]
  norm_num

theorem threeMiddleContext_top_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (huv : P.u < P.v) :
    let B := (Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.threeMiddleContext P).schur) =
        -(complete (P.ell + P.u) * complete P.m * Q.schur) := by
  dsimp only
  simp only [threeMiddleContext, singletonContext, shifted_schur]
  change MvPolynomial.pderiv _ (eraseGenerator _
    ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).schur) = _
  rw [positiveBorder_top_coefficient _ _ _ _ _ huv,
    threeMiddleCore_extendTop_schur]
  norm_num

/-- The strict bottom end marker retains the actual bottom endpoint function. -/
theorem threeEndContext_bottom_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (hvu : P.v < P.u) :
    let B := (Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.threeEndContext P).schur) =
        -(complete P.ell * complete P.m * (Q.extendBottom P.v P.v_pos).schur) := by
  dsimp only
  simp only [threeEndContext, singletonContext, shifted_schur]
  change MvPolynomial.pderiv _ (eraseGenerator _
    ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).schur) = _
  rw [positiveBorder_bottom_coefficient _ _ _ _ _ hvu,
    threeEndCore_extendBottom_schur]
  norm_num

theorem threeMiddleContext_bottom_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (hvu : P.v < P.u) :
    let B := (Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.threeMiddleContext P).schur) =
        -(complete P.ell * complete (P.m + P.v) * Q.schur) := by
  dsimp only
  simp only [threeMiddleContext, singletonContext, shifted_schur]
  change MvPolynomial.pderiv _ (eraseGenerator _
    ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).schur) = _
  rw [positiveBorder_bottom_coefficient _ _ _ _ _ hvu,
    threeMiddleCore_extendBottom_schur]
  norm_num

/-- Factor recovery already fixes every arbitrary mate component geometrically,
with both singleton copies retained when their lengths coincide. -/
theorem dense_three_context_mate_component_motions (Q : BetaDiagram 4)
    (hD : Q.Dense) (P : ThreeComponentParameters) (middle : Bool)
    {k : ℕ} (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = 7,
      let F := E.castOrder hrow
      ∃ hP : F.PositiveCorner, F.ZeroFree ∧
        ∀ K : ComponentDecomposition (F.cornerDiagram hP),
          K.components.length = 3 ∧
          Multiset.Rel (fun X Y : Σ a : ℕ, BetaDiagram a => X.2.MotionEquivalent Y.2)
            (([⟨1, singletonDiagram P.ell P.ell_pos⟩,
              ⟨1, singletonDiagram P.m P.m_pos⟩, ⟨4, Q⟩] :
                List (Σ a : ℕ, BetaDiagram a)) : Multiset _)
            (K.components : Multiset _) := by
  obtain ⟨hrow, hP, hZ, hK⟩ := Q.three_context_mate_components
    (hD.connected (by omega)) hD.zeroFree P middle E hE he
  refine ⟨hrow, hP, hZ, ?_⟩
  intro K
  have hrel := hK K
  have hcard := Multiset.card_eq_card_of_rel hrel
  refine ⟨by simpa using hcard.symm, ?_⟩
  apply hrel.mono
  intro X hX Y hY hXY
  have hXC : X.2.RotationRigid := by
    have hm : X ∈ [⟨1, singletonDiagram P.ell P.ell_pos⟩,
        ⟨1, singletonDiagram P.m P.m_pos⟩, ⟨4, Q⟩] := by simpa using hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact singletonDiagram_rigid P.ell P.ell_pos
    · exact singletonDiagram_rigid P.m P.m_pos
    · exact Q.rotationRigid_of_nonnegative (hD.connected (by omega)) hD.nonnegative
  exact hXC Y.1 Y.2 (K.components_connected Y (by simpa using hY)) hXY.symm

/-- `lem:three-component-forms`: every arbitrary mate has true end/middle beta lists,
a core equal to the source up to motion, and either singleton order. -/
theorem dense_three_context_arbitrary_mate_recovery (Q : BetaDiagram 4)
    (hD : Q.Dense) (P : ThreeComponentParameters) (middle : Bool)
    {k : ℕ} (E : BetaDiagram k) (hE : E.Connected)
    (he : (if middle then Q.threeMiddleContext P else Q.threeEndContext P).schur = E.schur) :
    ∃ hrow : k = 7,
      let F := E.castOrder hrow
      ∃ (R : BetaDiagram 4) (T : ThreeComponentParameters),
        R.Normalized ∧ Q.MotionEquivalent R ∧
        ((P.ell = T.ell ∧ P.m = T.m) ∨ (P.ell = T.m ∧ P.m = T.ell)) ∧
        (F.TranslationEquivalent (R.threeEndContext T) ∨
          F.TranslationEquivalent (R.threeMiddleContext T) ∨
          F.rotate.TranslationEquivalent (R.threeEndContext T)) := by
  obtain ⟨hrow,R,T,hRN,hRC,hfun,hpair,hform⟩ :=
    Q.three_context_arbitrary_mate_recovery (hD.connected (by omega)) hD.zeroFree
      P middle E hE he
  have hR := Q.rotationRigid_of_nonnegative (hD.connected (by omega)) hD.nonnegative
  exact ⟨hrow,R,T,hRN,hR 4 R hRC hfun.symm,hpair,hform⟩

/-- The full fixed-parameter end orientation difference of `eq:end-orientation`. -/
theorem threeEndContext_orientation_difference (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur - (Q.rotate.threeEndContext P).schur =
      (threeComponentA P).schur * Q.borderDifference P.right P.v P.right_pos P.v_pos -
      complete P.m * complete (P.ell+P.u) *
        Q.borderDifference (P.left+P.right) P.v
          (by have := P.left_pos; have := P.right_pos; omega) P.v_pos +
      complete P.ell * complete P.m *
        Q.borderDifference (P.left+P.right+P.u) P.v
          (by have := P.left_pos; have := P.right_pos; have := P.u_pos; omega) P.v_pos := by
  rw [threeEndContext_schur,threeEndContext_schur,
    positiveBorder_rotate_schur,positiveBorder_rotate_schur,positiveBorder_rotate_schur,
    threeComponentA_schur]
  unfold borderDifference
  ring

/-- The full middle orientation difference before the leader/tie extraction. -/
theorem threeMiddleContext_orientation_difference (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    (Q.threeMiddleContext P).schur - (Q.rotate.threeMiddleContext P).schur =
      complete (P.ell+P.u) * complete (P.m+P.v) *
        Q.borderDifference P.left P.right P.left_pos P.right_pos -
      complete P.ell * complete (P.m+P.v) *
        Q.borderDifference (P.left+P.u) P.right
          (by have := P.left_pos; have := P.u_pos; omega) P.right_pos -
      complete (P.ell+P.u) * complete P.m *
        Q.borderDifference P.left (P.right+P.v) P.left_pos
          (by have := P.right_pos; have := P.v_pos; omega) +
      complete P.ell * complete P.m *
        Q.borderDifference (P.left+P.u) (P.right+P.v)
          (by have := P.left_pos; have := P.u_pos; omega)
          (by have := P.right_pos; have := P.v_pos; omega) := by
  rw [threeMiddleContext_schur,threeMiddleContext_schur,
    positiveBorder_rotate_schur,positiveBorder_rotate_schur,
    positiveBorder_rotate_schur,positiveBorder_rotate_schur]
  unfold borderDifference
  ring

/-- Highest-label response of a coordinate times an actual endpoint difference. -/
theorem endpoint_coordinate_response (Q : BetaDiagram 4) (r t : ℤ) (ht : 0 < t)
    (w : ℕ+) (hw : Q.endpointKappa+t ≤ (w.val : ℤ)) :
    MvPolynomial.pderiv w (complete r * Q.endpointDifference t ht) =
      (if r = (w.val : ℤ) then Q.endpointDifference t ht else 0) +
      complete r * (if (w.val : ℤ) = Q.endpointKappa+t then Q.endpointCoefficient else 0) := by
  have hD : MvPolynomial.pderiv w (Q.endpointDifference t ht) =
      if (w.val : ℤ) = Q.endpointKappa+t then Q.endpointCoefficient else 0 := by
    split_ifs with he
    · exact Q.pderiv_endpointDifference_at t ht w he
    · exact Q.pderiv_endpointDifference_above t ht w (by omega)
  rw [MvPolynomial.pderiv_mul,pderiv_complete_label,hD]
  split_ifs <;> simp_all <;> ring

theorem endpointCoefficient_response_zero (Q : BetaDiagram 4) (t : ℤ) (ht : 0 < t)
    (w : ℕ+) (hw : Q.endpointKappa+t ≤ (w.val : ℤ)) :
    MvPolynomial.pderiv w Q.endpointCoefficient = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  have hh := Q.endpointCoefficient_labels t ht w h
  omega

/-- The actual endpoint function cannot vanish when its fixed coefficient is nonzero. -/
theorem endpointDifference_ne_zero_of_coefficient (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0) (t : ℤ) (ht : 0 < t) :
    Q.endpointDifference t ht ≠ 0 := by
  intro h
  have hd := congrArg (MvPolynomial.pderiv (Q.endpointGenerator t ht)) h
  rw [endpointDifference_pderiv,map_zero] at hd
  exact hc hd

theorem complete_scalar_pair_ne_zero (m a : ℤ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (c : CompleteRing) (hc : c ≠ 0) :
    complete m * (complete a * c) ≠ 0 :=
  mul_ne_zero ((complete_ne_zero_iff m).mpr hm)
    (mul_ne_zero ((complete_ne_zero_iff a).mpr ha) hc)

theorem cross_second_scalar_rearrange (l m a c d f B T H : CompleteRing)
    (hz : -(l*m*B)+(a*c-l*d)*f-(-(l*d*f)+m*(a*T-l*H)) = 0) :
    a*c*f = m*(a*T+l*B-l*H) := by
  linear_combination hz

theorem cross_second_scalar_residual (l a c d f B T H : CompleteRing)
    (hz : -(l*a*B)+(a*c-l*d)*f-(-(l*d*f)+a*(a*T-l*H)) = 0) :
    a*(a*T-c*f-l*(H-B)) = 0 := by
  linear_combination -hz

theorem cross_second_scalar_rotated (l a c d f T H : CompleteRing)
    (hz : -(l*a*H)+(a*c-l*d)*f-(-(l*d*f)+a*(a*T-l*H)) = 0) :
    a*(a*T) = a*(c*f) := by
  linear_combination -hz

/-- For the nonrotation middle tie with larger left separation, the true leader
and lower term exclude the coefficient cancellation in `eq:middle-final-tie`. -/
theorem middle_final_tie_nonzero_of_left_gt (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0)
    (hlower : ∀ (t : ℤ) (ht : 0 < t),
      Q.endpointDifference t ht ≠ complete (Q.endpointKappa+t)*Q.endpointCoefficient)
    (P : ThreeComponentParameters) (hLR : P.right < P.left)
    (htie : P.left+P.u = P.right+P.v) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference P.left P.left_pos -
      complete P.ell * complete (P.m+P.v) *
        Q.endpointDifference P.right P.right_pos ≠ 0 := by
  let p := Q.endpointKappa+P.left
  let q := Q.endpointKappa+P.right
  let a := P.ell+P.u
  let b := P.m+P.v
  have hκ := Q.endpointKappa_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hℓp : P.ell < p := by dsimp [p]; unfold ThreeComponentParameters.left; omega
  have hmq : P.m < q := by dsimp [q]; unfold ThreeComponentParameters.right; omega
  have hqp : q < p := by dsimp [p,q]; omega
  have hap : P.ell < a := by dsimp [a]; omega
  have hmb : P.m < b := by dsimp [b]; omega
  have hD₁ := Q.endpointDifference_ne_zero_of_coefficient hc P.left P.left_pos
  have hD₂ := Q.endpointDifference_ne_zero_of_coefficient hc P.right P.right_pos
  let T := complete P.m * complete a * Q.endpointDifference P.left P.left_pos -
    complete P.ell * complete b * Q.endpointDifference P.right P.right_pos
  have hresponse : ∀ (w : ℕ+), p ≤ (w.val : ℤ) → a ≤ (w.val : ℤ) →
      b ≤ (w.val : ℤ) →
      MvPolynomial.pderiv w T =
        complete P.m *
          ((if a = (w.val : ℤ) then Q.endpointDifference P.left P.left_pos else 0) +
            complete a * (if (w.val : ℤ) = p then Q.endpointCoefficient else 0)) -
        complete P.ell *
          (if b = (w.val : ℤ) then Q.endpointDifference P.right P.right_pos else 0) := by
    intro w hp ha hb
    have heℓ := pderiv_complete_label w P.ell
    rw [if_neg (by omega)] at heℓ
    have hem := pderiv_complete_label w P.m
    rw [if_neg (by omega)] at hem
    have hLeft := Q.endpoint_coordinate_response a P.left P.left_pos w
      (by dsimp [p] at hp; exact hp)
    have hRight := Q.endpoint_coordinate_response b P.right P.right_pos w
      (by dsimp [p,q] at hqp; omega)
    rw [if_neg (show (w.val : ℤ) ≠ Q.endpointKappa+P.right by
      dsimp [p,q] at *; omega),mul_zero,add_zero] at hRight
    dsimp only [T]
    rw [mul_assoc (complete P.m),mul_assoc (complete P.ell)]
    rw [map_sub,MvPolynomial.pderiv_mul,hem,zero_mul,zero_add,hLeft,
      MvPolynomial.pderiv_mul,heℓ,zero_mul,zero_add,hRight]
  intro hzero
  change T = 0 at hzero
  by_cases hab : a = b
  · have hinner : complete P.m * Q.endpointDifference P.left P.left_pos -
        complete P.ell * Q.endpointDifference P.right P.right_pos = 0 := by
      apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr (by dsimp [a]; omega))
      rw [mul_zero]
      calc
        complete a * _ = T := by dsimp [T]; rw [hab]; ring
        _ = 0 := hzero
    let w : ℕ+ := ⟨p.toNat, by dsimp [p]; have := P.left_pos; omega⟩
    have hw : (w.val : ℤ) = p := by dsimp [w]; omega
    have hd := congrArg (MvPolynomial.pderiv w) hinner
    rw [map_sub,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
      pderiv_complete_label,pderiv_complete_label,
      if_neg (by omega),if_neg (by omega),zero_mul,zero_mul,zero_add,zero_add,
      Q.pderiv_endpointDifference_at _ _ w (by dsimp [p] at hw; exact hw),
      Q.pderiv_endpointDifference_above _ _ w (by dsimp [p,q] at *; omega),
      mul_zero,sub_zero,map_zero] at hd
    exact mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le) hc hd
  · by_cases hap' : a = p
    · by_cases hbp : b ≤ p
      · let w : ℕ+ := ⟨p.toNat, by dsimp [p]; have := P.left_pos; omega⟩
        have hw : (w.val : ℤ) = p := by dsimp [w]; omega
        have hr := hresponse w hw.ge (by omega) (by omega)
        rw [if_pos (by omega),if_pos hw,if_neg (by omega)] at hr
        have hd := congrArg (MvPolynomial.pderiv w ∘ MvPolynomial.pderiv w) hzero
        simp only [Function.comp_apply,map_zero] at hd
        have hdm : MvPolynomial.pderiv w (complete P.m) = 0 := by
          rw [pderiv_complete_label,if_neg (by omega)]
        have hdℓ : MvPolynomial.pderiv w (complete P.ell) = 0 := by
          rw [pderiv_complete_label,if_neg (by omega)]
        have hda : MvPolynomial.pderiv w (complete a) = 1 := by
          rw [pderiv_complete_label,if_pos (by omega)]
        have hdc := Q.endpointCoefficient_response_zero P.left P.left_pos w
          (by dsimp [p] at hw; exact hw.ge)
        have hDL := Q.pderiv_endpointDifference_at P.left P.left_pos w
          (by dsimp [p] at hw; exact hw)
        rw [hr] at hd
        simp only [map_sub,map_add,MvPolynomial.pderiv_mul,hdm,hdℓ,hda,hdc,hDL,
          map_zero,zero_mul,mul_zero,zero_add,add_zero,one_mul,sub_zero] at hd
        have hn : complete P.m*(Q.endpointCoefficient+Q.endpointCoefficient) ≠ 0 := by
          rw [← two_mul]
          exact mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le)
            (mul_ne_zero (by norm_num) hc)
        exact hn hd
      · let w : ℕ+ := ⟨b.toNat, by dsimp [b]; omega⟩
        have hw : (w.val : ℤ) = b := by dsimp [w]; omega
        have hd := congrArg (MvPolynomial.pderiv w) hzero
        rw [hresponse w (by omega) (by omega) hw.ge,if_neg (by omega),
          if_neg (by omega),if_pos hw.symm] at hd
        simp only [mul_zero, zero_add, zero_sub, map_zero] at hd
        exact (neg_ne_zero.mpr
          (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hD₂)) hd
    · by_cases hbp' : b = p
      · by_cases haplt : a < p
        · let w : ℕ+ := ⟨p.toNat, by dsimp [p]; have := P.left_pos; omega⟩
          have hw : (w.val : ℤ) = p := by dsimp [w]; omega
          have hd := congrArg (MvPolynomial.pderiv w) hzero
          rw [hresponse w hw.ge (by omega) (by omega),if_neg (by omega),
            if_pos hw,if_pos (by omega),zero_add,map_zero] at hd
          by_cases haq : a = q
          · have heℓm : P.ell = P.m := by
              dsimp [a,b,p,q] at *
              omega
            rw [heℓm] at hd
            have hr : complete a*Q.endpointCoefficient =
                Q.endpointDifference P.right P.right_pos := by
              apply (sub_eq_zero.mp ·)
              apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr hm.le)
              rw [mul_zero]
              simpa only [mul_sub,mul_assoc] using hd
            exact hlower P.right P.right_pos (by simpa only [haq,q] using hr.symm)
          · let zval := max a q
            let z : ℕ+ := ⟨zval.toNat, by dsimp [zval,q]; have := P.right_pos; omega⟩
            have hz : (z.val : ℤ) = zval := by dsimp [z]; omega
            have hza : a ≤ (z.val : ℤ) := by rw [hz]; exact le_max_left _ _
            have hzq : q ≤ (z.val : ℤ) := by rw [hz]; exact le_max_right _ _
            have hdm : MvPolynomial.pderiv z (complete P.m) = 0 := by
              rw [pderiv_complete_label,if_neg (by omega)]
            have hdℓ : MvPolynomial.pderiv z (complete P.ell) = 0 := by
              rw [pderiv_complete_label,if_neg (by omega)]
            have hdc : MvPolynomial.pderiv z Q.endpointCoefficient = 0 :=
              Q.endpointCoefficient_response_zero P.right P.right_pos z
                (by dsimp [q] at hzq; exact hzq)
            have hd' := congrArg (MvPolynomial.pderiv z) hd
            simp only [map_sub,MvPolynomial.pderiv_mul,hdm,hdℓ,hdc,
              zero_mul,mul_zero,zero_add,add_zero,pderiv_complete_label] at hd'
            rcases lt_or_gt_of_ne haq with haq | haq
            · have hzv : (z.val : ℤ) = q := by dsimp [zval] at hz; rw [max_eq_right haq.le] at hz; exact hz
              rw [if_neg (by omega),zero_mul,
                Q.pderiv_endpointDifference_at P.right P.right_pos z
                  (by dsimp [q] at hzv; exact hzv),
                mul_zero,zero_sub,map_zero] at hd'
              exact (neg_ne_zero.mpr
                (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hc)) hd'
            · have hzv : (z.val : ℤ) = a := by dsimp [zval] at hz; rw [max_eq_left haq.le] at hz; exact hz
              rw [if_pos hzv.symm,one_mul,
                Q.pderiv_endpointDifference_above P.right P.right_pos z
                  (by dsimp [q] at *; omega),
                mul_zero,sub_zero,map_zero] at hd'
              exact mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le) hc hd'
        · let w : ℕ+ := ⟨a.toNat, by dsimp [a]; omega⟩
          have hw : (w.val : ℤ) = a := by dsimp [w]; omega
          have hd := congrArg (MvPolynomial.pderiv w) hzero
          rw [hresponse w (by omega) hw.ge (by omega),if_pos hw.symm,
            if_neg (by omega),if_neg (by omega)] at hd
          simp only [mul_zero, add_zero, sub_zero, map_zero] at hd
          exact mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le) hD₁ hd
      · rcases lt_or_gt_of_ne hap' with hap' | hap'
        · rcases lt_or_gt_of_ne hbp' with hbp' | hbp'
          · let w : ℕ+ := ⟨p.toNat, by dsimp [p]; have := P.left_pos; omega⟩
            have hw : (w.val : ℤ) = p := by dsimp [w]; omega
            have hd := congrArg (MvPolynomial.pderiv w) hzero
            rw [hresponse w hw.ge (by omega) (by omega),if_neg (by omega),
              if_pos hw,if_neg (by omega)] at hd
            simp only [zero_add, mul_zero, sub_zero, map_zero] at hd
            have ha : 0 ≤ a := by dsimp only [a]; omega
            exact complete_scalar_pair_ne_zero P.m a hm.le ha Q.endpointCoefficient hc hd
          · rcases lt_or_gt_of_ne hab with hab | hab
            · let w : ℕ+ := ⟨b.toNat, by dsimp [b]; omega⟩
              have hw : (w.val : ℤ) = b := by dsimp [w]; omega
              have hd := congrArg (MvPolynomial.pderiv w) hzero
              rw [hresponse w (by omega) (by omega) hw.ge,if_neg (by omega),
                if_neg (by omega),if_pos hw.symm] at hd
              simp only [mul_zero, zero_add, zero_sub, map_zero] at hd
              exact (neg_ne_zero.mpr
                (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hD₂)) hd
            · omega
        · rcases lt_or_gt_of_ne hab with hab | hab
          · let w : ℕ+ := ⟨b.toNat, by dsimp [b]; omega⟩
            have hw : (w.val : ℤ) = b := by dsimp [w]; omega
            have hd := congrArg (MvPolynomial.pderiv w) hzero
            rw [hresponse w (by omega) (by omega) hw.ge,if_neg (by omega),
              if_neg (by omega),if_pos hw.symm] at hd
            simp only [mul_zero, zero_add, zero_sub, map_zero] at hd
            exact (neg_ne_zero.mpr
              (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hD₂)) hd
          · let w : ℕ+ := ⟨a.toNat, by dsimp [a]; omega⟩
            have hw : (w.val : ℤ) = a := by dsimp [w]; omega
            have hd := congrArg (MvPolynomial.pderiv w) hzero
            rw [hresponse w (by omega) hw.ge (by omega),if_pos hw.symm,
              if_neg (by omega),if_neg (by omega)] at hd
            simp only [mul_zero, add_zero, sub_zero, map_zero] at hd
            exact mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le) hD₁ hd

/-- The final middle orientation coefficient is nonzero except at the actual
whole-parent rotation configuration.  Singleton lengths may coincide. -/
theorem middle_final_tie_nonzero (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0)
    (hlower : ∀ (t : ℤ) (ht : 0 < t),
      Q.endpointDifference t ht ≠ complete (Q.endpointKappa+t)*Q.endpointCoefficient)
    (P : ThreeComponentParameters) (htie : P.left+P.u = P.right+P.v)
    (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference P.left P.left_pos -
      complete P.ell * complete (P.m+P.v) *
        Q.endpointDifference P.right P.right_pos ≠ 0 := by
  rcases lt_trichotomy P.left P.right with hLR | hLR | hLR
  · let T : ThreeComponentParameters :=
      { ell := P.m, m := P.ell, g₁ := P.g₂, g₂ := P.g₁,
        u := P.v, v := P.u, ell_pos := P.m_pos, m_pos := P.ell_pos,
        g₁_pos := P.g₂_pos, g₂_pos := P.g₁_pos, u_pos := P.v_pos, v_pos := P.u_pos }
    have ht : T.left+T.u = T.right+T.v := by
      change P.right+P.v = P.left+P.u
      exact htie.symm
    have hr : T.right < T.left := hLR
    have hn := Q.middle_final_tie_nonzero_of_left_gt hc hlower T hr ht
    intro he
    apply hn
    change complete P.ell * complete (P.m+P.v) *
        Q.endpointDifference P.right P.right_pos -
      complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference P.left P.left_pos = 0
    exact sub_eq_zero.mpr (sub_eq_zero.mp he).symm
  · have huv : P.u = P.v := by omega
    have hℓm : P.ell ≠ P.m := by tauto
    have hp : complete P.m * complete (P.ell+P.u) -
        complete P.ell * complete (P.m+P.u) ≠ 0 := by
      intro he
      have hpair := singleton_pair_recovery P.m (P.ell+P.u) P.ell (P.m+P.u)
        P.m_pos (by have := P.ell_pos; have := P.u_pos; omega) P.ell_pos
        (by have := P.m_pos; have := P.u_pos; omega) (sub_eq_zero.mp he)
      rcases hpair with ⟨h,_⟩ | ⟨h,_⟩
      · exact hℓm h.symm
      · have hu := P.u_pos
        omega
    have hd := Q.endpointDifference_ne_zero_of_coefficient hc P.left P.left_pos
    intro he
    apply mul_ne_zero hp hd
    calc
      _ = complete P.m * complete (P.ell+P.u) *
            Q.endpointDifference P.left P.left_pos -
          complete P.ell * complete (P.m+P.v) *
            Q.endpointDifference P.right P.right_pos := by
              rw [Q.endpointDifference_parameter_congr hLR.symm P.right_pos P.left_pos, ← huv]
              ring
      _ = 0 := he
  · exact Q.middle_final_tie_nonzero_of_left_gt hc hlower P hLR htie

/-- The dense-core source supplies the true leader and lower term, not assumptions about a mate. -/
theorem dense_middle_final_tie_nonzero (Q : BetaDiagram 4) (hD : Q.Dense)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters)
    (htie : P.left+P.u = P.right+P.v) (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference P.left P.left_pos -
      complete P.ell * complete (P.m+P.v) *
        Q.endpointDifference P.right P.right_pos ≠ 0 :=
  Q.middle_final_tie_nonzero (Q.endpointCoefficient_ne_zero_dense hD hS)
    (Q.dense_four_lower_part hD hS) P htie hnonrot

/-- The final end-orientation tie has a nonzero true highest response.
No inequality between the singleton lengths is required. -/
theorem end_orientation_tie_nonzero (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0) (P : ThreeComponentParameters) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference (P.left+P.right) (by
          have := P.left_pos; have := P.right_pos; omega) -
      (threeComponentA P).schur * Q.endpointDifference P.right P.right_pos ≠ 0 := by
  let p := Q.endpointKappa+P.left+P.right
  let q := Q.endpointKappa+P.right
  let z := P.m+P.left+P.u
  let a := P.ell+P.u
  have hκ := Q.endpointKappa_pos
  have hu := P.u_pos
  have hg := P.g₁_pos
  have hm := P.m_pos
  have hℓ := P.ell_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hqp : q < p := by dsimp [p,q]; omega
  have haz : a < z := by dsimp [a,z]; unfold ThreeComponentParameters.left; omega
  have hmz : P.m < z := by dsimp [z]; omega
  have hℓz : P.ell < z := by dsimp [z]; unfold ThreeComponentParameters.left; omega
  let T := complete P.m * complete a *
      Q.endpointDifference (P.left+P.right) (by omega) -
    (threeComponentA P).schur * Q.endpointDifference P.right P.right_pos
  have hresponse : ∀ (w : ℕ+), p ≤ (w.val : ℤ) → z ≤ (w.val : ℤ) →
      MvPolynomial.pderiv w T =
        complete P.m * complete a *
          (if (w.val : ℤ) = p then Q.endpointCoefficient else 0) +
        complete P.ell *
          (if z = (w.val : ℤ) then Q.endpointDifference P.right P.right_pos else 0) := by
    intro w hp hz
    have hm0 : MvPolynomial.pderiv w (complete P.m) = 0 := by
      rw [pderiv_complete_label,if_neg (by omega)]
    have ha0 : MvPolynomial.pderiv w (complete a) = 0 := by
      rw [pderiv_complete_label,if_neg (by omega)]
    have hℓ0 : MvPolynomial.pderiv w (complete P.ell) = 0 := by
      rw [pderiv_complete_label,if_neg (by omega)]
    have hdR := Q.pderiv_endpointDifference_above P.right P.right_pos w
      (by dsimp [p,q] at *; omega)
    have hdL : MvPolynomial.pderiv w
        (Q.endpointDifference (P.left+P.right) (by omega)) =
          if (w.val : ℤ) = p then Q.endpointCoefficient else 0 := by
      split_ifs with he
      · exact Q.pderiv_endpointDifference_at _ _ w (by dsimp [p] at he; omega)
      · exact Q.pderiv_endpointDifference_above _ _ w (by dsimp [p] at *; omega)
    have hA : MvPolynomial.pderiv w (threeComponentA P).schur =
        -(complete P.ell * (if z = (w.val : ℤ) then 1 else 0)) := by
      rw [threeComponentA_schur,map_sub,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
        pderiv_complete_label,pderiv_complete_label,pderiv_complete_label,pderiv_complete_label]
      rw [if_neg (by dsimp [a] at haz; omega),if_neg (by dsimp [z] at hz; omega),
        if_neg (by omega)]
      simp only [zero_mul,mul_zero,add_zero,zero_add,zero_sub,z]
    dsimp only [T]
    simp only [map_sub,MvPolynomial.pderiv_mul,hm0,ha0,hdR,hdL,hA,
      zero_mul,mul_zero,zero_add,add_zero]
    split_ifs <;> ring
  intro hzero
  change T = 0 at hzero
  rcases lt_trichotomy p z with hpz | hpz | hpz
  · let w : ℕ+ := ⟨z.toNat, by dsimp [z]; omega⟩
    have hw : (w.val : ℤ) = z := by dsimp [w]; omega
    have hd := congrArg (MvPolynomial.pderiv w) hzero
    rw [hresponse w (by omega) hw.ge,if_neg (by omega),if_pos hw.symm,
      mul_zero,zero_add,map_zero] at hd
    exact mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le)
      (Q.endpointDifference_ne_zero_of_coefficient hc P.right P.right_pos) hd
  · let w : ℕ+ := ⟨p.toNat, by dsimp [p]; omega⟩
    have hw : (w.val : ℤ) = p := by dsimp [w]; omega
    have hd := congrArg (MvPolynomial.pderiv w) hzero
    rw [hresponse w hw.ge (by omega),if_pos hw,if_pos (by omega),map_zero] at hd
    have hmq : P.m < q := by dsimp [p,z,q] at *; omega
    let k := max a q
    let e : ℕ+ := ⟨k.toNat, by dsimp [k,q]; have := le_max_right a q; omega⟩
    have he : (e.val : ℤ) = k := by dsimp [e]; omega
    have hea : a ≤ (e.val : ℤ) := by rw [he]; exact le_max_left _ _
    have heq : q ≤ (e.val : ℤ) := by rw [he]; exact le_max_right _ _
    have hem : MvPolynomial.pderiv e (complete P.m) = 0 := by
      rw [pderiv_complete_label,if_neg (by omega)]
    have heℓ : MvPolynomial.pderiv e (complete P.ell) = 0 := by
      rw [pderiv_complete_label,if_neg (by dsimp [a] at hea; omega)]
    have hec := Q.endpointCoefficient_response_zero P.right P.right_pos e
      (by dsimp [q] at heq; exact heq)
    have hd' := congrArg (MvPolynomial.pderiv e) hd
    simp only [map_add, MvPolynomial.pderiv_mul, hem, heℓ, hec,
      zero_mul, mul_zero, zero_add, add_zero, pderiv_complete_label, map_zero] at hd'
    rcases lt_trichotomy a q with haq | haq | haq
    · have hev : (e.val : ℤ) = q := by dsimp [k] at he; rw [max_eq_right haq.le] at he; exact he
      rw [if_neg (by omega),mul_zero,zero_mul,zero_add,
        Q.pderiv_endpointDifference_at _ _ e (by dsimp [q] at hev; exact hev)] at hd'
      exact mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hc hd'
    · have hev : (e.val : ℤ) = q := by dsimp [k] at he; rw [haq,max_self] at he; exact he
      have hℓm : P.ell = P.m := by dsimp [p,z,a,q] at *; omega
      rw [if_pos (by omega),mul_one,
        Q.pderiv_endpointDifference_at _ _ e (by dsimp [q] at hev; exact hev),
        ← hℓm] at hd'
      have hn : complete P.ell*Q.endpointCoefficient+
          complete P.ell*Q.endpointCoefficient ≠ 0 := by
        rw [← two_mul]
        exact mul_ne_zero (by norm_num)
          (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hc)
      exact hn hd'
    · have hev : (e.val : ℤ) = a := by dsimp [k] at he; rw [max_eq_left haq.le] at he; exact he
      rw [if_pos hev.symm,mul_one,
        Q.pderiv_endpointDifference_above _ _ e (by dsimp [q] at *; omega),
        mul_zero,add_zero] at hd'
      exact mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le) hc hd'
  · let w : ℕ+ := ⟨p.toNat, by dsimp [p]; omega⟩
    have hw : (w.val : ℤ) = p := by dsimp [w]; omega
    have hd := congrArg (MvPolynomial.pderiv w) hzero
    rw [hresponse w hw.ge (by omega),if_pos hw,if_neg (by omega),mul_zero,add_zero,map_zero] at hd
    exact mul_ne_zero (mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le)
      ((complete_ne_zero_iff _).mpr (by dsimp [a]; omega))) hc hd

theorem dense_end_orientation_tie_nonzero (Q : BetaDiagram 4) (hD : Q.Dense)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters) :
    complete P.m * complete (P.ell+P.u) *
        Q.endpointDifference (P.left+P.right) (by
          have := P.left_pos; have := P.right_pos; omega) -
      (threeComponentA P).schur * Q.endpointDifference P.right P.right_pos ≠ 0 :=
  Q.end_orientation_tie_nonzero (Q.endpointCoefficient_ne_zero_dense hD hS) P

/-- Different connected row orders cannot divide one another's actual Schur functions. -/
theorem connected_schur_not_dvd_of_order_ne {n k : ℕ}
    (D : BetaDiagram n) (E : BetaDiagram k) (hD : D.Connected) (hE : E.Connected)
    (hn : n ≠ k) : ¬ D.schur ∣ E.schur := by
  intro h
  have he := D.schur_eq_of_connected_dvd E hD hE h
  exact hn (D.row_count_of_schur_eq E he)

/-- The source core does not divide either genuinely shifted endpoint function. -/
theorem connected_schur_not_dvd_bottom_endpoint (Q : BetaDiagram 4)
    (hC : Q.Connected) (t : ℤ) (ht : 0 < t) :
    ¬ Q.schur ∣ (Q.extendBottom t ht).schur := by
  intro h
  have hE := Q.extendBottom_connected hC t ht
  have he := Q.schur_eq_of_connected_dvd (Q.extendBottom t ht) hC hE h
  have hl := Q.largestLabel_eq_of_schur_eq (Q.extendBottom t ht) hC hE he
  rw [border_extendBottom_largestLabel] at hl
  omega

theorem connected_four_schur_not_dvd_complete (Q : BetaDiagram 4) (hC : Q.Connected)
    (s : ℤ) (hs : 0 < s) : ¬ Q.schur ∣ complete s := by
  simpa only [singletonDiagram_schur] using
    connected_schur_not_dvd_of_order_ne Q (singletonDiagram s hs) hC
      (singletonDiagram_connected s hs) (by omega)

/-- The strict end bottom marker is not divisible by the four-row core.
This holds for either source negative pattern. -/
theorem three_end_bottom_marker_not_dvd_core (Q : BetaDiagram 4)
    (hC : Q.Connected) (P : ThreeComponentParameters) :
    ¬ Q.schur ∣ -(complete P.ell * complete P.m *
      (Q.extendBottom P.v P.v_pos).schur) := by
  intro h
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hC)
  have h' := dvd_neg.mp h
  rcases hprime.dvd_mul.mp h' with h' | h'
  · rcases hprime.dvd_mul.mp h' with h' | h'
    · exact Q.connected_four_schur_not_dvd_complete hC P.ell P.ell_pos h'
    · exact Q.connected_four_schur_not_dvd_complete hC P.m P.m_pos h'
  · exact Q.connected_schur_not_dvd_bottom_endpoint hC P.v P.v_pos h'

/-- The strict middle intermediate marker is not divisible by the four-row core. -/
theorem three_middle_intermediate_marker_not_dvd_core (Q : BetaDiagram 4)
    (hC : Q.Connected) (hP : Q.PositiveCorner) (P : ThreeComponentParameters) :
    ¬ Q.schur ∣ complete P.m *
      (Q.threeComponentU P.ell P.left P.u P.ell_pos
        (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  intro h
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp (Q.schur_irreducible hC)
  rcases hprime.dvd_mul.mp h with h | h
  · exact Q.connected_four_schur_not_dvd_complete hC P.m P.m_pos h
  · exact connected_schur_not_dvd_of_order_ne Q
      (Q.threeComponentU P.ell P.left P.u P.ell_pos
        (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos)
      hC (Q.threeComponentU_connected hP _ _ _ _ _ _) (by omega) h

/-- The end tied third marker is not divisible by the core. -/
theorem three_end_tied_marker_not_dvd_core (Q : BetaDiagram 4)
    (hC : Q.Connected) (P : ThreeComponentParameters) :
    ¬ Q.schur ∣
      -(complete P.ell * complete P.m * (Q.extendBottom P.v P.v_pos).schur) +
        (threeComponentA P).schur * Q.schur := by
  intro h
  apply Q.three_end_bottom_marker_not_dvd_core hC P
  have hd := dvd_sub h (dvd_mul_left Q.schur (threeComponentA P).schur)
  simpa only [add_sub_cancel_right] using hd

/-- The same tied end marker is not divisible by its second singleton. -/
theorem three_end_tied_marker_not_dvd_second_singleton (Q : BetaDiagram 4)
    (hC : Q.Connected) (P : ThreeComponentParameters) :
    ¬ complete P.m ∣
      -(complete P.ell * complete P.m * (Q.extendBottom P.v P.v_pos).schur) +
        (threeComponentA P).schur * Q.schur := by
  have hn : ¬ complete P.m ∣ (threeComponentA P).schur * Q.schur := by
    intro h
    rcases (complete_prime P.m P.m_pos).dvd_mul.mp h with h | h
    · exact threeComponentA_complete_not_dvd P P.m P.m_pos h
    · exact Q.complete_not_dvd_connected hC P.m P.m_pos h
  have hd : complete P.m ∣
      -(complete P.ell * complete P.m * (Q.extendBottom P.v P.v_pos).schur) := by
    refine ⟨-(complete P.ell * (Q.extendBottom P.v P.v_pos).schur),?_⟩
    ring
  intro h
  apply hn
  have hh := dvd_sub h hd
  simpa only [add_sub_cancel_left] using hh

/-- The middle tied third marker is not divisible by the core. -/
theorem three_middle_tied_marker_not_dvd_core (Q : BetaDiagram 4)
    (hC : Q.Connected) (hP : Q.PositiveCorner) (P : ThreeComponentParameters) :
    ¬ Q.schur ∣
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  intro h
  apply Q.three_middle_intermediate_marker_not_dvd_core hC hP P
  have hd : Q.schur ∣ -(complete P.ell * complete (P.m+P.v) * Q.schur) :=
    dvd_neg.mpr (dvd_mul_left _ _)
  have hh := dvd_sub h hd
  simpa only [add_sub_cancel_left] using hh

/-- A connected nonlinear core cannot absorb a changed singleton coordinate. -/
theorem changed_singleton_product_ne (Q : BetaDiagram 4) (hC : Q.Connected)
    (F : CompleteRing) (s t : ℤ) (hs : 0 < s) (ht : 0 < t) (hne : s ≠ t) :
    complete s * F ≠ complete t * Q.schur := by
  intro he
  have hd : complete s ∣ complete t * Q.schur := by
    rw [← he]
    exact dvd_mul_right _ _
  rcases (complete_prime s hs).dvd_mul.mp hd with h | h
  · exact hne ((complete_dvd_complete_iff s t hs ht).mp h)
  · exact Q.complete_not_dvd_connected hC s hs h

/-- The first cross-placement tie cannot cancel, for either core orientation.
The resonance premise is supplied by the dense or one-negative source theorem. -/
theorem three_cross_first_tie_exclusion (Q : BetaDiagram 4)
    (hC : Q.Connected) (hP : Q.PositiveCorner) (P : ThreeComponentParameters)
    (htie : P.v = P.left+P.u)
    (hres : complete (P.ell+P.u) * (Q.extendTop P.left P.left_pos).schur -
      complete (P.ell+P.v) * Q.schur -
      complete P.ell * Q.endpointDifference P.v P.v_pos ≠ 0)
    (R : BetaDiagram 4) (hR : R = Q ∨ R = Q.rotate) :
    -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) ≠
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  let U := Q.threeComponentU P.ell P.left P.u P.ell_pos
    (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
  have hU : ¬ complete P.ell ∣ U.schur :=
    Q.threeComponentU_complete_not_dvd hP P.ell P.left P.u P.ell P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos P.ell_pos
  intro he
  have hd₁ : complete P.ell ∣
      -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) := by
    refine ⟨-(complete P.m * (R.extendBottom P.v P.v_pos).schur),?_⟩
    ring
  have hd₂ : complete P.ell ∣ -(complete P.ell * complete (P.m+P.v) * Q.schur) := by
    refine ⟨-(complete (P.m+P.v) * Q.schur),?_⟩
    ring
  have hdU : complete P.ell ∣ complete P.m * U.schur := by
    rw [he] at hd₁
    have h := dvd_sub hd₁ hd₂
    simpa only [add_sub_cancel_left] using h
  have hℓm : P.ell = P.m := by
    rcases (complete_prime P.ell P.ell_pos).dvd_mul.mp hdU with h | h
    · exact (complete_dvd_complete_iff P.ell P.m P.ell_pos P.m_pos).mp h
    · exact False.elim (hU h)
  have hz := sub_eq_zero.mpr he
  rw [threeComponentU_schur] at hz
  rcases hR with rfl | rfl
  · apply hres
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
    rw [mul_zero]
    unfold endpointDifference
    rw [extendBottom_schur_parameter_congr _ htie P.v_pos
      (by have := P.left_pos; have := P.u_pos; omega)] at hz ⊢
    rw [extendTop_schur_parameter_congr _ htie P.v_pos
      (by have := P.left_pos; have := P.u_pos; omega)] at ⊢
    rw [htie] at hz ⊢
    simp only [hℓm] at hz ⊢
    linear_combination -hz
  · rw [rotate_extendBottom_schur] at hz
    have hfun : complete (P.ell+P.u) * (Q.extendTop P.left P.left_pos).schur =
        complete (P.ell+P.v) * Q.schur := by
      apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
      rw [Q.extendTop_schur_parameter_congr htie P.v_pos
        (by have := P.left_pos; have := P.u_pos; omega)] at hz
      rw [htie] at hz ⊢
      simp only [hℓm] at hz ⊢
      linear_combination -hz
    exact Q.changed_singleton_product_ne hC _ _ _
      (by have := P.ell_pos; have := P.u_pos; omega)
      (by have := P.ell_pos; have := P.v_pos; omega)
      (by have := P.left_pos; omega) hfun

/-- Dense cores supply the first cross-placement resonance directly. -/
theorem dense_three_cross_first_tie_exclusion (Q : BetaDiagram 4) (hD : Q.Dense)
    (P : ThreeComponentParameters) (htie : P.v = P.left+P.u)
    (R : BetaDiagram 4) (hR : R = Q ∨ R = Q.rotate) :
    -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) ≠
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  apply Q.three_cross_first_tie_exclusion (hD.connected (by omega))
    (Q.positiveCorner_of_nonnegative hD.nonnegative) P htie
  · have h := Q.dense_cross_resonance_one hD P.ell P.left P.u P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
    simpa only [← htie] using h
  · exact hR

/-- The second cross-placement tie also forces and then excludes its singleton resonance. -/
theorem three_cross_second_tie_exclusion (Q : BetaDiagram 4)
    (hC : Q.Connected) (P : ThreeComponentParameters) (htie : P.v = P.left+P.u)
    (hres : complete (P.ell+P.u) * (Q.extendTop P.left P.left_pos).schur -
      complete (P.ell+P.v) * Q.schur -
      complete P.ell * Q.endpointDifference P.v P.v_pos ≠ 0)
    (R : BetaDiagram 4) (hR : R = Q ∨ R = Q.rotate) :
    -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) +
        (threeComponentA P).schur * Q.schur ≠
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  intro he
  have hz := sub_eq_zero.mpr he
  rw [threeComponentA_schur,threeComponentU_schur] at hz
  have hd : complete P.m ∣
      complete (P.ell+P.u) * complete (P.m+P.left) * Q.schur := by
    refine ⟨complete (P.ell+P.u) * (Q.extendTop P.left P.left_pos).schur +
      complete P.ell * (R.extendBottom P.v P.v_pos).schur -
      complete P.ell * (Q.extendTop (P.left+P.u) (by
        have := P.left_pos; have := P.u_pos; omega)).schur,?_⟩
    rw [R.extendBottom_schur_parameter_congr htie P.v_pos
      (by have := P.left_pos; have := P.u_pos; omega)] at hz ⊢
    rw [htie] at hz
    have hi : P.m + (P.left + P.u) = P.m + P.left + P.u := by ring
    rw [hi] at hz
    exact cross_second_scalar_rearrange _ _ _ _ _ _ _ _ _ hz
  have hmshift : P.m = P.ell+P.u := by
    have hprime := complete_prime P.m P.m_pos
    rcases hprime.dvd_mul.mp hd with h | h
    · rcases hprime.dvd_mul.mp h with h | h
      · exact (complete_dvd_complete_iff P.m (P.ell+P.u) P.m_pos
          (by have := P.ell_pos; have := P.u_pos; omega)).mp h
      · have he := (complete_dvd_complete_iff P.m (P.m+P.left) P.m_pos
          (by have := P.m_pos; have := P.left_pos; omega)).mp h
        have hL := P.left_pos
        omega
    · exact False.elim (Q.complete_not_dvd_connected hC P.m P.m_pos h)
  rcases hR with rfl | rfl
  · apply hres
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
    rw [mul_zero]
    unfold endpointDifference
    rw [extendBottom_schur_parameter_congr _ htie P.v_pos
      (by have := P.left_pos; have := P.u_pos; omega)] at hz ⊢
    rw [extendTop_schur_parameter_congr _ htie P.v_pos
      (by have := P.left_pos; have := P.u_pos; omega)] at ⊢
    rw [htie,hmshift] at hz ⊢
    have hi : P.ell + P.u + P.left = P.ell + P.left + P.u := by ring
    have hj : P.ell + P.u + (P.left + P.u) = P.ell + P.u + P.left + P.u := by ring
    rw [hi] at hz
    simp only [hj, hi] at hz ⊢
    have hk : complete (P.ell + (P.left + P.u)) =
        complete (P.ell + P.left + P.u) := congrArg complete (by ring)
    rw [hk]
    exact cross_second_scalar_residual _ _ _ _ _ _ _ _ hz
  · rw [rotate_extendBottom_schur] at hz
    have hfun : complete (P.ell+P.u) * (Q.extendTop P.left P.left_pos).schur =
        complete (P.ell+P.v) * Q.schur := by
      apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr P.m_pos.le)
      rw [Q.extendTop_schur_parameter_congr htie P.v_pos
        (by have := P.left_pos; have := P.u_pos; omega)] at hz
      rw [htie,hmshift] at hz ⊢
      have hi : P.ell + P.u + P.left = P.ell + P.left + P.u := by ring
      rw [hi] at hz
      have hj : P.ell + P.u + (P.left + P.u) = P.ell + P.left + P.u + P.u := by ring
      have hk : P.ell + P.u + P.left + P.u = P.ell + P.left + P.u + P.u := by ring
      simp only [hj, hk] at hz ⊢
      have hc : complete (P.ell + (P.left + P.u)) =
          complete (P.ell + P.left + P.u) := congrArg complete (by ring)
      rw [hc]
      exact cross_second_scalar_rotated _ _ _ _ _ _ _ hz
    exact Q.changed_singleton_product_ne hC _ _ _
      (by have := P.ell_pos; have := P.u_pos; omega)
      (by have := P.ell_pos; have := P.v_pos; omega)
      (by have := P.left_pos; omega) hfun

theorem dense_three_cross_second_tie_exclusion (Q : BetaDiagram 4) (hD : Q.Dense)
    (P : ThreeComponentParameters) (htie : P.v = P.left+P.u)
    (R : BetaDiagram 4) (hR : R = Q ∨ R = Q.rotate) :
    -(complete P.ell * complete P.m * (R.extendBottom P.v P.v_pos).schur) +
        (threeComponentA P).schur * Q.schur ≠
      -(complete P.ell * complete (P.m+P.v) * Q.schur) +
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur := by
  apply Q.three_cross_second_tie_exclusion (hD.connected (by omega)) P htie
  · have h := Q.dense_cross_resonance_one hD P.ell P.left P.u P.ell_pos
      (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos
    simpa only [← htie] using h
  · exact hR

/-- The actual dense-core U intermediate satisfies the proved source column class,
against arbitrary connected mates and without requiring normalization. -/
theorem dense_threeComponentU_rotationRigid (Q : BetaDiagram 4)
    (hD : Q.Dense)
    (ell x u : ℤ) (hℓ : 0 < ell) (hx : ell < x) (hu : 0 < u) :
    (Q.threeComponentU ell x u hℓ hx hu).RotationRigid := by
  apply (Q.threeComponentU ell x u hℓ hx hu).column_rigidity
    (Q.dense_threeComponentU_connected hD ell x u hℓ hx hu)
  left
  change Q.col 0 ≤ Q.row 3
  exact (hD 3 0).le

/-- The second-label derivative is unchanged by removal of the strictly larger corner variable. -/
theorem positiveBorder_second_derivative_erased {n : ℕ} (D : BetaDiagram (n + 2))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    let B := D.positiveBorder u v hu hv
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator B.schur) =
      MvPolynomial.pderiv B.borderSecondGenerator B.schur := by
  dsimp only
  let B := D.positiveBorder u v hu hv
  have hk : D.largestLabel < (B.borderSecondGenerator.val : ℤ) := by
    rw [borderSecondGenerator_int,positiveBorder_secondLabel]
    have hm₁ := min_le_left u v
    have hm₂ := min_le_right u v
    omega
  have hcore : MvPolynomial.pderiv B.borderSecondGenerator
      ((-1 : CompleteRing)^(n+2)*D.schur) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro h
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h | h
    · have hh := MvPolynomial.vars_pow (-1 : CompleteRing) (n+2) h
      simpa using hh
    · have hh := D.vars_le_largestLabel B.borderSecondGenerator h
      omega
  have hne : B.borderSecondGenerator ≠ B.borderLargestGenerator := by
    intro he
    have hh := congrArg (fun w : ℕ+ => (w.val : ℤ)) he
    rw [borderSecondGenerator_int,borderLargestGenerator_int,
      positiveBorder_secondLabel,positiveBorder_largestLabel] at hh
    have hm : 0 < min u v := lt_min hu hv
    omega
  have hx : MvPolynomial.pderiv B.borderSecondGenerator
      (MvPolynomial.X B.borderLargestGenerator : CompleteRing) = 0 := by
    rw [MvPolynomial.pderiv_X_of_ne hne.symm]
  rw [positiveBorder_erased_corner,positiveBorder_corner_split,map_add,
    MvPolynomial.pderiv_mul,hcore,hx]
  simp only [zero_mul,mul_zero,zero_add,add_zero]

/-- The tied end marker in `eq:first-marker-table`, with the corner genuinely removed. -/
theorem threeEndContext_tied_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (huv : P.u = P.v) :
    let B := (Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.threeEndContext P).schur) =
      -(complete P.m * (complete (P.ell+P.u)*Q.schur+
        complete P.ell*(Q.extendBottom P.u P.u_pos).schur)) := by
  dsimp only
  simp only [threeEndContext,singletonContext,shifted_schur]
  change MvPolynomial.pderiv _ (eraseGenerator _
    ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).schur) = _
  rw [positiveBorder_second_derivative_erased,
    positiveBorder_tied_first_derivative_of_eq _ _ _ _ _ huv,
    threeEndCore_extendTop_schur, threeEndCore_extendBottom_schur,
    Q.extendBottom_schur_parameter_congr huv.symm P.v_pos P.u_pos]
  norm_num
  ring

theorem threeMiddleContext_tied_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters)
    (huv : P.u = P.v) :
    let B := (Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos
    MvPolynomial.pderiv B.borderSecondGenerator
      (eraseGenerator B.borderLargestGenerator (Q.threeMiddleContext P).schur) =
      -(Q.schur * (complete P.m*complete (P.ell+P.u)+
        complete P.ell*complete (P.m+P.u))) := by
  dsimp only
  simp only [threeMiddleContext,singletonContext,shifted_schur]
  change MvPolynomial.pderiv _ (eraseGenerator _
    ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).schur) = _
  rw [positiveBorder_second_derivative_erased,
    positiveBorder_tied_first_derivative_of_eq _ _ _ _ _ huv,
    threeMiddleCore_extendTop_schur, threeMiddleCore_extendBottom_schur]
  simp only [← huv]
  norm_num
  ring

/-- A same-sign pair of positive coordinate monomials cannot cancel, even when their indices coincide. -/
theorem complete_pair_sum_ne_zero (a b c d : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    complete a*complete b+complete c*complete d ≠ 0 := by
  let ev : CompleteRing →+* ℚ := MvPolynomial.eval (fun _ => (1 : ℚ))
  intro h
  have he := congrArg ev h
  simp [ev,complete_of_pos ha,complete_of_pos hb,complete_of_pos hc,
    complete_of_pos hd] at he

/-- Every genuine first marker is nonzero in all three margin regimes. -/
theorem three_context_first_marker_ne_zero (Q : BetaDiagram 4) (hC : Q.Connected)
    (P : ThreeComponentParameters) (middle : Bool) :
    let D := if middle then Q.threeMiddleContext P else Q.threeEndContext P
    MvPolynomial.pderiv D.borderSecondGenerator
      (eraseGenerator D.borderLargestGenerator D.schur) ≠ 0 := by
  dsimp only
  cases middle with
  | false =>
    simp only [Bool.false_eq_true,if_false]
    have heq :
        MvPolynomial.pderiv (Q.threeEndContext P).borderSecondGenerator
          (eraseGenerator (Q.threeEndContext P).borderLargestGenerator
            (Q.threeEndContext P).schur) =
        MvPolynomial.pderiv
          ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderSecondGenerator
          (eraseGenerator
            ((Q.threeEndCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderLargestGenerator
            (Q.threeEndContext P).schur) := by
      simp only [threeEndContext,singletonContext,shifted_borderLargestGenerator,
        shifted_borderSecondGenerator,threeEndCore]
    rw [heq]
    rcases lt_trichotomy P.u P.v with h | h | h
    · rw [threeEndContext_top_marker _ _ h]
      exact neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff _).mpr (by have := P.ell_pos; have := P.u_pos; omega))
          ((complete_ne_zero_iff _).mpr P.m_pos.le)) Q.schur_ne_zero)
    · rw [threeEndContext_tied_marker _ _ h]
      have hn := Q.singleton_tied_marker_divisibility hC P.ell P.u P.ell_pos P.u_pos
      exact neg_ne_zero.mpr
        (mul_ne_zero ((complete_ne_zero_iff _).mpr P.m_pos.le) hn.2.2)
    · rw [threeEndContext_bottom_marker _ _ h]
      exact neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
          ((complete_ne_zero_iff _).mpr P.m_pos.le))
        (Q.extendBottom P.v P.v_pos).schur_ne_zero)
  | true =>
    simp only [if_true]
    have heq :
        MvPolynomial.pderiv (Q.threeMiddleContext P).borderSecondGenerator
          (eraseGenerator (Q.threeMiddleContext P).borderLargestGenerator
            (Q.threeMiddleContext P).schur) =
        MvPolynomial.pderiv
          ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderSecondGenerator
          (eraseGenerator
            ((Q.threeMiddleCore P).positiveBorder P.u P.v P.u_pos P.v_pos).borderLargestGenerator
            (Q.threeMiddleContext P).schur) := by
      simp only [threeMiddleContext,singletonContext,shifted_borderLargestGenerator,
        shifted_borderSecondGenerator,threeMiddleCore]
    rw [heq]
    rcases lt_trichotomy P.u P.v with h | h | h
    · rw [threeMiddleContext_top_marker _ _ h]
      exact neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff _).mpr (by have := P.ell_pos; have := P.u_pos; omega))
          ((complete_ne_zero_iff _).mpr P.m_pos.le)) Q.schur_ne_zero)
    · rw [threeMiddleContext_tied_marker _ _ h]
      exact neg_ne_zero.mpr (mul_ne_zero Q.schur_ne_zero
        (complete_pair_sum_ne_zero _ _ _ _ P.m_pos
          (by have := P.ell_pos; have := P.u_pos; omega) P.ell_pos
          (by have := P.m_pos; have := P.u_pos; omega)))
    · rw [threeMiddleContext_bottom_marker _ _ h]
      exact neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero ((complete_ne_zero_iff _).mpr P.ell_pos.le)
          ((complete_ne_zero_iff _).mpr (by have := P.m_pos; have := P.v_pos; omega)))
        Q.schur_ne_zero)

/-- Full polynomial equality recovers the smaller exterior margin for either placement,
without assuming equal singleton order or a common negative pattern. -/
theorem three_context_min_margin_recovery (Q R : BetaDiagram 4)
    (hQ : Q.Connected) (hR : R.Connected)
    (P T : ThreeComponentParameters) (middle₁ middle₂ : Bool)
    (he : (if middle₁ then Q.threeMiddleContext P else Q.threeEndContext P).schur =
      (if middle₂ then R.threeMiddleContext T else R.threeEndContext T).schur) :
    min P.u P.v = min T.u T.v := by
  let D := if middle₁ then Q.threeMiddleContext P else Q.threeEndContext P
  let E := if middle₂ then R.threeMiddleContext T else R.threeEndContext T
  have hD : D.Connected := by
    cases middle₁ <;> simp only [D,Bool.false_eq_true,if_false,if_true]
    · exact Q.threeEndContext_connected P
    · exact Q.threeMiddleContext_connected P
  have hE : E.Connected := by
    cases middle₂ <;> simp only [E,Bool.false_eq_true,if_false,if_true]
    · exact R.threeEndContext_connected T
    · exact R.threeMiddleContext_connected T
  have hl := D.largestLabel_eq_of_schur_eq E hD hE he
  have hgen : D.borderLargestGenerator = E.borderLargestGenerator := by
    apply Subtype.ext
    simp only [borderLargestGenerator,hl]
  have hd : D.borderSecondGenerator ∈
      (eraseGenerator D.borderLargestGenerator D.schur).vars := by
    by_contra hn
    exact Q.three_context_first_marker_ne_zero hQ P middle₁
      (MvPolynomial.pderiv_eq_zero_of_notMem_vars hn)
  have hf : E.borderSecondGenerator ∈
      (eraseGenerator E.borderLargestGenerator E.schur).vars := by
    by_contra hn
    exact R.three_context_first_marker_ne_zero hR T middle₂
      (MvPolynomial.pderiv_eq_zero_of_notMem_vars hn)
  have hde : D.secondLabel ≤ E.secondLabel := by
    rw [he,hgen] at hd
    simpa only [borderSecondGenerator_int] using E.vars_le_secondLabel D.borderSecondGenerator hd
  have hed : E.secondLabel ≤ D.secondLabel := by
    rw [← he,← hgen] at hf
    simpa only [borderSecondGenerator_int] using D.vars_le_secondLabel E.borderSecondGenerator hf
  have hs := le_antisymm hde hed
  have hDm : min D.topMargin D.bottomMargin = min P.u P.v := by
    cases middle₁ <;> simp [D,threeEndContext,threeMiddleContext,singletonContext]
  have hEm : min E.topMargin E.bottomMargin = min T.u T.v := by
    cases middle₂ <;> simp [E,threeEndContext,threeMiddleContext,singletonContext]
  unfold secondLabel at hs
  rw [hDm,hEm,hl] at hs
  omega

/-- The full private corner split for a true four-row core, with its positive parity. -/
theorem four_border_corner_split (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) :
    let B := Q.positiveBorder w v hw hv
    B.schur = Q.schur*complete (Q.largestLabel+w+v)+B.cornerResidual := by
  dsimp only
  have h := Q.positiveBorder_corner_split w v hw hv
  dsimp only at h
  have hg : MvPolynomial.X (Q.positiveBorder w v hw hv).borderLargestGenerator =
      complete (Q.largestLabel+w+v) := by
    have hp : 0 < Q.largestLabel+w+v := by have := Q.largestLabel_pos; omega
    rw [complete_of_pos hp]
    congr 1
    apply Subtype.ext
    apply Int.ofNat.inj
    change ((Q.positiveBorder w v hw hv).borderLargestGenerator.val : ℤ) =
      ((Q.largestLabel+w+v).toNat : ℤ)
    rw [borderLargestGenerator_int, positiveBorder_largestLabel,
      Int.toNat_of_nonneg hp.le]
  rw [hg] at h
  norm_num at h
  exact h

theorem four_border_secondLabel (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) :
    (Q.positiveBorder w v hw hv).secondLabel =
      max (Q.largestLabel+w) (Q.largestLabel+v) := by
  rw [positiveBorder_secondLabel]
  omega

/-- Above its second geometric level the true corner residual has derivative zero. -/
theorem four_border_residual_above (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (k : ℕ+)
    (hk : max (Q.largestLabel+w) (Q.largestLabel+v) < (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.positiveBorder w v hw hv).cornerResidual = 0 := by
  rw [← positiveBorder_erased_corner]
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  have hb := (Q.positiveBorder w v hw hv).vars_le_secondLabel k h
  rw [four_border_secondLabel] at hb
  omega

/-- Highest-label extraction for the full actual bordered function. -/
theorem four_border_largest_response (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (k : ℕ+)
    (hk : Q.largestLabel+w+v ≤ (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.positiveBorder w v hw hv).schur =
      if (k.val : ℤ) = Q.largestLabel+w+v then Q.schur else 0 := by
  split_ifs with he
  · rw [(Q.positiveBorder w v hw hv).pderiv_schur_at k
      (by rw [positiveBorder_largestLabel]; exact he)]
    norm_num [cornerCoefficient]
  · exact (Q.positiveBorder w v hw hv).pderiv_schur_above k
      (by rw [positiveBorder_largestLabel]; omega)

theorem four_border_residual_bottom (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (hvw : v < w) (k : ℕ+)
    (hk : (k.val : ℤ) = Q.largestLabel+w) :
    MvPolynomial.pderiv k (Q.positiveBorder w v hw hv).cornerResidual =
      -(Q.extendBottom v hv).schur := by
  have hg : k = (Q.positiveBorder w v hw hv).borderSecondGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) =
      ((Q.positiveBorder w v hw hv).borderSecondGenerator.val : ℤ)
    rw [borderSecondGenerator_int,four_border_secondLabel,max_eq_left (by omega)]
    exact hk
  rw [hg,← positiveBorder_erased_corner,positiveBorder_bottom_coefficient _ _ _ _ _ hvw]
  norm_num

theorem four_border_residual_top (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (hwv : w < v) (k : ℕ+)
    (hk : (k.val : ℤ) = Q.largestLabel+v) :
    MvPolynomial.pderiv k (Q.positiveBorder w v hw hv).cornerResidual =
      -(Q.extendTop w hw).schur := by
  have hg : k = (Q.positiveBorder w v hw hv).borderSecondGenerator := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) =
      ((Q.positiveBorder w v hw hv).borderSecondGenerator.val : ℤ)
    rw [borderSecondGenerator_int,four_border_secondLabel,max_eq_right (by omega)]
    exact hk
  rw [hg,← positiveBorder_erased_corner,positiveBorder_top_coefficient _ _ _ _ _ hwv]
  norm_num

/-- The actual two common largest terms removed before the third-marker comparison. -/
noncomputable def threeSharedLeadingPart (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    CompleteRing :=
  Q.schur *
    (complete P.ell*complete P.m*complete (Q.largestLabel+P.left+P.right+P.u+P.v) -
      complete P.m*complete (P.ell+P.u)*complete (Q.largestLabel+P.left+P.right+P.v))

def threeThirdIndex (Q : BetaDiagram 4) (P : ThreeComponentParameters) : ℤ :=
  max (Q.largestLabel+P.left+P.right+P.u) (Q.largestLabel+P.right+P.v)

theorem threeThirdIndex_pos (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    0 < Q.threeThirdIndex P := by
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have h := le_max_left (Q.largestLabel+P.left+P.right+P.u)
    (Q.largestLabel+P.right+P.v)
  unfold threeThirdIndex
  omega

def threeThirdGenerator (Q : BetaDiagram 4) (P : ThreeComponentParameters) : ℕ+ :=
  ⟨(Q.threeThirdIndex P).toNat,by have := Q.threeThirdIndex_pos P; omega⟩

@[simp] theorem threeThirdGenerator_int (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    ((Q.threeThirdGenerator P).val : ℤ) = Q.threeThirdIndex P := by
  change ((Q.threeThirdIndex P).toNat : ℤ) = Q.threeThirdIndex P
  exact Int.toNat_of_nonneg (Q.threeThirdIndex_pos P).le

/-- The actual bottom intermediate inherits arbitrary-mate rigidity by whole-diagram rotation. -/
theorem dense_threeComponentZ_rotationRigid (Q : BetaDiagram 4)
    (hD : Q.Dense)
    (m y v : ℤ) (hm : 0 < m) (hy : m < y) (hv : 0 < v) :
    (Q.threeComponentZ m y v hm hy hv).RotationRigid := by
  have hDR : Q.rotate.Dense := by
    intro i j
    have h := hD j.rev i.rev
    change -Q.row j.rev < -Q.col i.rev
    omega
  have hU := Q.rotate.dense_threeComponentU_rotationRigid hDR m y v hm hy hv
  exact (Q.rotate.threeComponentU m y v hm hy hv).rotate.rotationRigid_shifted
    ((Q.rotate.threeComponentU m y v hm hy hv).rotationRigid_rotate hU)
    (y+v-Q.col 3)

/-- The actual end third marker, with both contributions retained at equality of levels. -/
theorem threeEndContext_third_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    let k := Q.threeThirdGenerator P
    MvPolynomial.pderiv k ((Q.threeEndContext P).schur-Q.threeSharedLeadingPart P) =
      (if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u then
        -(complete P.ell*complete P.m*(Q.extendBottom P.v P.v_pos).schur) else 0) +
      (if (k.val : ℤ) = Q.largestLabel+P.right+P.v then
        (threeComponentA P).schur*Q.schur else 0) := by
  dsimp only
  let k := Q.threeThirdGenerator P
  have hk₁ : Q.largestLabel+P.left+P.right+P.u ≤ (k.val : ℤ) := by
    change _ ≤ ((Q.threeThirdGenerator P).val : ℤ)
    rw [threeThirdGenerator_int,threeThirdIndex]
    exact le_max_left _ _
  have hk₂ : Q.largestLabel+P.right+P.v ≤ (k.val : ℤ) := by
    change _ ≤ ((Q.threeThirdGenerator P).val : ℤ)
    rw [threeThirdGenerator_int,threeThirdIndex]
    exact le_max_right _ _
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hLR : 0 < P.left+P.right := by omega
  have hLRu : 0 < P.left+P.right+P.u := by omega
  let B₂ := Q.positiveBorder (P.left+P.right) P.v hLR P.v_pos
  let B₃ := Q.positiveBorder (P.left+P.right+P.u) P.v hLRu P.v_pos
  have hpoly : (Q.threeEndContext P).schur-Q.threeSharedLeadingPart P =
      (threeComponentA P).schur*(Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur -
      complete P.m*complete (P.ell+P.u)*B₂.cornerResidual +
      complete P.ell*complete P.m*B₃.cornerResidual := by
    rw [threeEndContext_schur,← threeComponentA_schur,
      Q.four_border_corner_split (P.left+P.right) P.v hLR P.v_pos,
      Q.four_border_corner_split (P.left+P.right+P.u) P.v hLRu P.v_pos]
    dsimp only [threeSharedLeadingPart,B₂,B₃]
    simp only [add_assoc]
    ring
  have hPhi : MvPolynomial.pderiv k
      (Q.positiveBorder P.right P.v P.right_pos P.v_pos).schur =
        if (k.val : ℤ) = Q.largestLabel+P.right+P.v then Q.schur else 0 :=
    Q.four_border_largest_response P.right P.v P.right_pos P.v_pos k hk₂
  have hB₂ : MvPolynomial.pderiv k B₂.cornerResidual = 0 := by
    apply Q.four_border_residual_above _ _ _ _ k
    apply max_lt
    · omega
    · omega
  have hB₃ : MvPolynomial.pderiv k B₃.cornerResidual =
      if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u then
        -(Q.extendBottom P.v P.v_pos).schur else 0 := by
    split_ifs with he
    · have hmargin : P.v < P.left+P.right+P.u := by omega
      exact Q.four_border_residual_bottom _ _ _ _ hmargin k
        (by simpa only [add_assoc] using he)
    · apply Q.four_border_residual_above _ _ _ _ k
      apply max_lt
      · omega
      · omega
  have hA : MvPolynomial.pderiv k (threeComponentA P).schur = 0 := by
    apply (threeComponentA P).pderiv_schur_above k
    rw [threeComponentA_largestLabel]
    unfold ThreeComponentParameters.right at hk₁
    omega
  have heℓ : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have hem : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.right at hk₁; omega)]
  have hea : MvPolynomial.pderiv k (complete (P.ell+P.u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  rw [hpoly]
  dsimp only [k] at hA heℓ hem hea hPhi hB₂ hB₃
  simp only [map_add,map_sub,MvPolynomial.pderiv_mul,hA,heℓ,hem,hea,hPhi,hB₂,hB₃,
    zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  split_ifs <;> ring

/-- The actual middle third marker.  The five-row determinant is the genuine U intermediate. -/
theorem threeMiddleContext_third_marker (Q : BetaDiagram 4) (P : ThreeComponentParameters) :
    let k := Q.threeThirdGenerator P
    MvPolynomial.pderiv k ((Q.threeMiddleContext P).schur-Q.threeSharedLeadingPart P) =
      (if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u then
        -(complete P.ell*complete (P.m+P.v)*Q.schur) else 0) +
      (if (k.val : ℤ) = Q.largestLabel+P.right+P.v then
        complete P.m *
          (Q.threeComponentU P.ell P.left P.u P.ell_pos
            (by have := P.g₁_pos; unfold ThreeComponentParameters.left; omega) P.u_pos).schur
        else 0) := by
  dsimp only
  let k := Q.threeThirdGenerator P
  have hk₁ : Q.largestLabel+P.left+P.right+P.u ≤ (k.val : ℤ) := by
    change _ ≤ ((Q.threeThirdGenerator P).val : ℤ)
    rw [threeThirdGenerator_int,threeThirdIndex]
    exact le_max_left _ _
  have hk₂ : Q.largestLabel+P.right+P.v ≤ (k.val : ℤ) := by
    change _ ≤ ((Q.threeThirdGenerator P).val : ℤ)
    rw [threeThirdGenerator_int,threeThirdIndex]
    exact le_max_right _ _
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hℓ := P.ell_pos
  have hm := P.m_pos
  have hLu : 0 < P.left+P.u := by omega
  have hRv : 0 < P.right+P.v := by omega
  let B₃ := Q.positiveBorder P.left (P.right+P.v) P.left_pos hRv
  let B₄ := Q.positiveBorder (P.left+P.u) (P.right+P.v) hLu hRv
  have hpoly : (Q.threeMiddleContext P).schur-Q.threeSharedLeadingPart P =
      complete (P.ell+P.u)*complete (P.m+P.v) *
        (Q.positiveBorder P.left P.right P.left_pos P.right_pos).schur -
      complete P.ell*complete (P.m+P.v) *
        (Q.positiveBorder (P.left+P.u) P.right hLu P.right_pos).schur -
      complete (P.ell+P.u)*complete P.m*B₃.cornerResidual +
      complete P.ell*complete P.m*B₄.cornerResidual := by
    rw [threeMiddleContext_schur,
      Q.four_border_corner_split P.left (P.right+P.v) P.left_pos hRv,
      Q.four_border_corner_split (P.left+P.u) (P.right+P.v) hLu hRv]
    dsimp only [threeSharedLeadingPart,B₃,B₄]
    have hN₄ : Q.largestLabel+(P.left+P.u)+(P.right+P.v) =
        Q.largestLabel+P.left+P.right+P.u+P.v := by ring
    rw [hN₄]
    simp only [add_assoc]
    ring
  have hPhi₁ : MvPolynomial.pderiv k
      (Q.positiveBorder P.left P.right P.left_pos P.right_pos).schur = 0 := by
    apply (Q.positiveBorder P.left P.right P.left_pos P.right_pos).pderiv_schur_above k
    rw [positiveBorder_largestLabel]
    omega
  have hPhi₂ : MvPolynomial.pderiv k
      (Q.positiveBorder (P.left+P.u) P.right hLu P.right_pos).schur =
        if (k.val : ℤ) = Q.largestLabel+P.left+P.right+P.u then Q.schur else 0 := by
    have h := Q.four_border_largest_response (P.left+P.u) P.right hLu P.right_pos k
      (by omega)
    have hi : Q.largestLabel+(P.left+P.u)+P.right =
        Q.largestLabel+P.left+P.right+P.u := by ring
    simpa only [hi] using h
  have hB₃ : MvPolynomial.pderiv k B₃.cornerResidual =
      if (k.val : ℤ) = Q.largestLabel+P.right+P.v then
        -(Q.extendTop P.left P.left_pos).schur else 0 := by
    split_ifs with he
    · have hmargin : P.left < P.right+P.v := by omega
      exact Q.four_border_residual_top _ _ _ _ hmargin k
        (by simpa only [add_assoc] using he)
    · apply Q.four_border_residual_above _ _ _ _ k
      apply max_lt <;> omega
  have hB₄ : MvPolynomial.pderiv k B₄.cornerResidual =
      if (k.val : ℤ) = Q.largestLabel+P.right+P.v then
        -(Q.extendTop (P.left+P.u) hLu).schur else 0 := by
    split_ifs with he
    · have hmargin : P.left+P.u < P.right+P.v := by omega
      exact Q.four_border_residual_top _ _ _ _ hmargin k
        (by simpa only [add_assoc] using he)
    · apply Q.four_border_residual_above _ _ _ _ k
      apply max_lt <;> omega
  have heℓ : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have hem : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.right at hk₁; omega)]
  have hea : MvPolynomial.pderiv k (complete (P.ell+P.u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hk₁; omega)]
  have heb : MvPolynomial.pderiv k (complete (P.m+P.v)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.right at hk₂; omega)]
  rw [hpoly,threeComponentU_schur]
  dsimp only [k] at heℓ hem hea heb hPhi₁ hPhi₂ hB₃ hB₄
  simp only [map_add,map_sub,MvPolynomial.pderiv_mul,heℓ,hem,hea,heb,
    hPhi₁,hPhi₂,hB₃,hB₄,zero_mul,mul_zero,zero_add,add_zero,zero_sub]
  split_ifs <;> ring

theorem four_borderDifference_above (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (k : ℕ+)
    (hk : Q.largestLabel+max w v < (k.val : ℤ)) :
    MvPolynomial.pderiv k (Q.borderDifference w v hw hv) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  have hh := Q.borderDifference_vars_le w v hw hv k h
  omega

theorem four_borderDifference_at_gt (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (h : v < w) (k : ℕ+)
    (hk : (k.val : ℤ) = Q.largestLabel+w) :
    MvPolynomial.pderiv k (Q.borderDifference w v hw hv) = Q.endpointDifference v hv := by
  have hg : ((Q.borderDifferenceGenerator w v hw hv).val : ℤ) =
      Q.largestLabel+max w v := by
    have hS := Q.largestLabel_pos
    have hm := le_max_left w v
    change ((Q.largestLabel+max w v).toNat : ℤ) = Q.largestLabel+max w v
    rw [Int.toNat_of_nonneg (by omega)]
  have he : k = Q.borderDifferenceGenerator w v hw hv := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) = ((Q.borderDifferenceGenerator w v hw hv).val : ℤ)
    rw [hg,max_eq_left h.le]
    exact hk
  rw [he,borderDifference_coefficient_of_gt _ _ _ _ _ h]
  norm_num

theorem four_borderDifference_at_lt (Q : BetaDiagram 4) (w v : ℤ)
    (hw : 0 < w) (hv : 0 < v) (h : w < v) (k : ℕ+)
    (hk : (k.val : ℤ) = Q.largestLabel+v) :
    MvPolynomial.pderiv k (Q.borderDifference w v hw hv) = -Q.endpointDifference w hw := by
  have hg : ((Q.borderDifferenceGenerator w v hw hv).val : ℤ) =
      Q.largestLabel+max w v := by
    have hS := Q.largestLabel_pos
    have hm := le_max_right w v
    change ((Q.largestLabel+max w v).toNat : ℤ) = Q.largestLabel+max w v
    rw [Int.toNat_of_nonneg (by omega)]
  have he : k = Q.borderDifferenceGenerator w v hw hv := by
    apply Subtype.ext
    apply Int.ofNat.inj
    change (k.val : ℤ) = ((Q.borderDifferenceGenerator w v hw hv).val : ℤ)
    rw [hg,max_eq_right h.le]
    exact hk
  rw [he,borderDifference_coefficient_of_lt _ _ _ _ _ h]
  norm_num

/-- The true endpoint leader prohibits every fixed-parameter end core reversal,
including its equal-level comparison. -/
theorem threeEndContext_orientation_ne_of_coefficient (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0) (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur ≠ (Q.rotate.threeEndContext P).schur := by
  have hS := Q.largestLabel_pos
  have hκ := Q.endpointKappa_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hm := P.m_pos
  have hℓ := P.ell_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  let w₀ := P.left+P.right+P.u
  have hw₀ : 0 < w₀ := by dsimp [w₀]; omega
  have hLR : 0 < P.left+P.right := by omega
  let k : ℕ+ := ⟨(Q.largestLabel+max w₀ P.v).toNat,by have := le_max_left w₀ P.v; omega⟩
  have hk : (k.val : ℤ) = Q.largestLabel+max w₀ P.v := by dsimp [k]; omega
  have hkw : Q.largestLabel+w₀ ≤ (k.val : ℤ) := by rw [hk]; have := le_max_left w₀ P.v; omega
  have hA := (threeComponentA P).pderiv_schur_above k
    (by rw [threeComponentA_largestLabel];
        dsimp [w₀] at hkw; unfold ThreeComponentParameters.right at hkw; omega)
  have hm0 : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label,if_neg (by dsimp [w₀] at hkw; unfold ThreeComponentParameters.right at hkw; omega)]
  have hℓ0 : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label,if_neg (by dsimp [w₀] at hkw; unfold ThreeComponentParameters.left at hkw; omega)]
  have ha0 : MvPolynomial.pderiv k (complete (P.ell+P.u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by dsimp [w₀] at hkw; unfold ThreeComponentParameters.left at hkw; omega)]
  intro he
  have hz := sub_eq_zero.mpr he
  rw [threeEndContext_orientation_difference] at hz
  have hd := congrArg (MvPolynomial.pderiv k) hz
  simp only [map_add,map_sub,MvPolynomial.pderiv_mul,hA,hm0,hℓ0,ha0,
    zero_mul,mul_zero,zero_add,add_zero,map_zero] at hd
  rcases lt_trichotomy P.v w₀ with h | h | h
  · have hkv : (k.val : ℤ) = Q.largestLabel+w₀ := by rw [max_eq_left h.le] at hk; exact hk
    have hD₁ := Q.four_borderDifference_above P.right P.v P.right_pos P.v_pos k
      (by dsimp [w₀] at *; omega)
    have hD₂ := Q.four_borderDifference_above (P.left+P.right) P.v hLR P.v_pos k
      (by dsimp [w₀] at *; omega)
    have hD₃ := Q.four_borderDifference_at_gt w₀ P.v hw₀ P.v_pos h k hkv
    rw [hD₁,hD₂,hD₃,mul_zero,mul_zero,sub_zero,zero_add] at hd
    exact mul_ne_zero (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le)
      ((complete_ne_zero_iff _).mpr hm.le))
      (Q.endpointDifference_ne_zero_of_coefficient hc P.v P.v_pos) hd
  · have hkv : (k.val : ℤ) = Q.largestLabel+P.v := by rw [← h,max_self] at hk; exact hk
    have hD₁ := Q.four_borderDifference_at_lt P.right P.v P.right_pos P.v_pos
      (by dsimp [w₀] at h; omega) k hkv
    have hD₂ := Q.four_borderDifference_at_lt (P.left+P.right) P.v hLR P.v_pos
      (by dsimp [w₀] at h; omega) k hkv
    have hD₃ : MvPolynomial.pderiv k (Q.borderDifference w₀ P.v hw₀ P.v_pos) = 0 := by
      rw [Q.borderDifference_eq_zero_of_eq h.symm hw₀ P.v_pos, map_zero]
    rw [hD₁,hD₂,hD₃,mul_zero,add_zero] at hd
    apply Q.end_orientation_tie_nonzero hc P
    linear_combination hd
  · have hkv : (k.val : ℤ) = Q.largestLabel+P.v := by rw [max_eq_right h.le] at hk; exact hk
    have hD₁ := Q.four_borderDifference_at_lt P.right P.v P.right_pos P.v_pos
      (by dsimp [w₀] at h; omega) k hkv
    have hD₂ := Q.four_borderDifference_at_lt (P.left+P.right) P.v hLR P.v_pos
      (by dsimp [w₀] at h; omega) k hkv
    have hD₃ := Q.four_borderDifference_at_lt w₀ P.v hw₀ P.v_pos h k hkv
    rw [hD₁,hD₂,hD₃] at hd
    let t : ℕ+ := ⟨(Q.endpointKappa+w₀).toNat,by omega⟩
    have ht : (t.val : ℤ) = Q.endpointKappa+w₀ := by dsimp [t]; omega
    have hAt := (threeComponentA P).pderiv_schur_above t
      (by rw [threeComponentA_largestLabel];
          dsimp [w₀] at ht; unfold ThreeComponentParameters.right at ht; omega)
    have hmt : MvPolynomial.pderiv t (complete P.m) = 0 := by
      rw [pderiv_complete_label,if_neg (by dsimp [w₀] at ht; unfold ThreeComponentParameters.right at ht; omega)]
    have hℓt : MvPolynomial.pderiv t (complete P.ell) = 0 := by
      rw [pderiv_complete_label,if_neg (by dsimp [w₀] at ht; unfold ThreeComponentParameters.left at ht; omega)]
    have hat : MvPolynomial.pderiv t (complete (P.ell+P.u)) = 0 := by
      rw [pderiv_complete_label,if_neg (by dsimp [w₀] at ht; unfold ThreeComponentParameters.left at ht; omega)]
    have h₁ := Q.pderiv_endpointDifference_above P.right P.right_pos t
      (by dsimp [w₀] at ht; omega)
    have h₂ := Q.pderiv_endpointDifference_above (P.left+P.right) hLR t
      (by dsimp [w₀] at ht; omega)
    have h₃ := Q.pderiv_endpointDifference_at w₀ hw₀ t ht
    have hd' := congrArg (MvPolynomial.pderiv t) hd
    simp only [map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,
      hAt,hmt,hℓt,hat,h₁,h₂,h₃,zero_mul,mul_zero,neg_zero,zero_add,add_zero,zero_sub,map_zero] at hd'
    have hn := mul_ne_zero (mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le)
      ((complete_ne_zero_iff _).mpr hm.le)) hc
    apply neg_ne_zero.mpr hn
    linear_combination hd'

theorem dense_threeEndContext_orientation_ne (Q : BetaDiagram 4) (hD : Q.Dense)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters) :
    (Q.threeEndContext P).schur ≠ (Q.rotate.threeEndContext P).schur :=
  Q.threeEndContext_orientation_ne_of_coefficient (Q.endpointCoefficient_ne_zero_dense hD hS) P

/-- A singleton endpoint response retains a private top at the larger shift. -/
theorem endpoint_shift_response_ne_zero (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0) (s x u : ℤ)
    (hs : 0 < s) (hx : s < x) (hu : 0 < u) :
    complete (s+u)*Q.endpointDifference x (by omega) -
      complete s*Q.endpointDifference (x+u) (by omega) ≠ 0 := by
  have hκ := Q.endpointKappa_pos
  let k : ℕ+ := ⟨(Q.endpointKappa+x+u).toNat,by omega⟩
  have hk : (k.val : ℤ) = Q.endpointKappa+x+u := by dsimp [k]; omega
  have h₁ := Q.pderiv_endpointDifference_above x (by omega) k (by omega)
  have h₂ := Q.pderiv_endpointDifference_at (x+u) (by omega) k (by omega)
  have hs0 : MvPolynomial.pderiv k (complete s) = 0 := by
    rw [pderiv_complete_label,if_neg (by omega)]
  have hsu0 : MvPolynomial.pderiv k (complete (s+u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by omega)]
  intro he
  have hd := congrArg (MvPolynomial.pderiv k) he
  simp only [map_sub,MvPolynomial.pderiv_mul,hs0,hsu0,h₁,h₂,
    zero_mul,mul_zero,zero_add,add_zero,zero_sub,map_zero] at hd
  exact (neg_ne_zero.mpr (mul_ne_zero ((complete_ne_zero_iff _).mpr hs.le) hc)) hd

/-- Fixed-parameter middle core reversal is impossible outside whole-parent rotation.
All strict and tied exterior levels, including equal singleton lengths, are retained. -/
theorem threeMiddleContext_orientation_ne_of_coefficient (Q : BetaDiagram 4)
    (hc : Q.endpointCoefficient ≠ 0)
    (hlower : ∀ (t : ℤ) (ht : 0 < t),
      Q.endpointDifference t ht ≠ complete (Q.endpointKappa+t)*Q.endpointCoefficient)
    (P : ThreeComponentParameters)
    (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m ∨ P.u ≠ P.v) :
    (Q.threeMiddleContext P).schur ≠ (Q.rotate.threeMiddleContext P).schur := by
  have hS := Q.largestLabel_pos
  have hL := P.left_pos
  have hR := P.right_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hm := P.m_pos
  have hℓ := P.ell_pos
  have hg₁ := P.g₁_pos
  have hg₂ := P.g₂_pos
  have hLu : 0 < P.left+P.u := by omega
  have hRv : 0 < P.right+P.v := by omega
  let k : ℕ+ := ⟨(Q.largestLabel+max (P.left+P.u) (P.right+P.v)).toNat,by
    have := le_max_left (P.left+P.u) (P.right+P.v); omega⟩
  have hk : (k.val : ℤ) = Q.largestLabel+max (P.left+P.u) (P.right+P.v) := by
    dsimp [k]
    omega
  have hkl : Q.largestLabel+P.left+P.u ≤ (k.val : ℤ) := by
    rw [hk]; have := le_max_left (P.left+P.u) (P.right+P.v); omega
  have hkr : Q.largestLabel+P.right+P.v ≤ (k.val : ℤ) := by
    rw [hk]; have := le_max_right (P.left+P.u) (P.right+P.v); omega
  have hℓ0 : MvPolynomial.pderiv k (complete P.ell) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hkl; omega)]
  have hm0 : MvPolynomial.pderiv k (complete P.m) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.right at hkr; omega)]
  have ha0 : MvPolynomial.pderiv k (complete (P.ell+P.u)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.left at hkl; omega)]
  have hb0 : MvPolynomial.pderiv k (complete (P.m+P.v)) = 0 := by
    rw [pderiv_complete_label,if_neg (by unfold ThreeComponentParameters.right at hkr; omega)]
  have hD₁ := Q.four_borderDifference_above P.left P.right P.left_pos P.right_pos k
    (by omega)
  intro he
  have hz := sub_eq_zero.mpr he
  rw [threeMiddleContext_orientation_difference] at hz
  have hd := congrArg (MvPolynomial.pderiv k) hz
  simp only [map_add,map_sub,MvPolynomial.pderiv_mul,hℓ0,hm0,ha0,hb0,hD₁,
    zero_mul,mul_zero,zero_add,add_zero,zero_sub,map_zero] at hd
  rcases lt_trichotomy (P.left+P.u) (P.right+P.v) with h | h | h
  · have hkv : (k.val : ℤ) = Q.largestLabel+(P.right+P.v) := by
      rw [max_eq_right h.le] at hk
      exact hk
    have hD₂ := Q.four_borderDifference_above (P.left+P.u) P.right hLu P.right_pos k
      (by omega)
    have hD₃ := Q.four_borderDifference_at_lt P.left (P.right+P.v) P.left_pos hRv
      (by omega) k hkv
    have hD₄ := Q.four_borderDifference_at_lt (P.left+P.u) (P.right+P.v) hLu hRv h k hkv
    rw [hD₂,hD₃,hD₄] at hd
    simp only [mul_zero, neg_zero, zero_sub] at hd
    have hn := Q.endpoint_shift_response_ne_zero hc P.ell P.left P.u P.ell_pos
      (by unfold ThreeComponentParameters.left; omega) P.u_pos
    apply mul_ne_zero ((complete_ne_zero_iff _).mpr hm.le) hn
    linear_combination hd
  · have hkv : (k.val : ℤ) = Q.largestLabel+(P.right+P.v) := by
      rw [h,max_self] at hk
      exact hk
    have hD₂ := Q.four_borderDifference_at_gt (P.left+P.u) P.right hLu P.right_pos
      (by omega) k (by omega)
    have hD₃ := Q.four_borderDifference_at_lt P.left (P.right+P.v) P.left_pos hRv
      (by omega) k hkv
    have hD₄ : MvPolynomial.pderiv k
        (Q.borderDifference (P.left+P.u) (P.right+P.v) hLu hRv) = 0 := by
      rw [Q.borderDifference_eq_zero_of_eq h hLu hRv, map_zero]
    rw [hD₂,hD₃,hD₄,mul_zero,add_zero] at hd
    have hn : P.left ≠ P.right ∨ P.ell ≠ P.m := by
      by_cases hLR : P.left = P.right
      · have huv : P.u = P.v := by omega
        exact Or.inr (by tauto)
      · exact Or.inl hLR
    apply Q.middle_final_tie_nonzero hc hlower P h hn
    linear_combination hd
  · have hkv : (k.val : ℤ) = Q.largestLabel+(P.left+P.u) := by
      rw [max_eq_left h.le] at hk
      exact hk
    have hD₂ := Q.four_borderDifference_at_gt (P.left+P.u) P.right hLu P.right_pos
      (by omega) k hkv
    have hD₃ := Q.four_borderDifference_above P.left (P.right+P.v) P.left_pos hRv k
      (by omega)
    have hD₄ := Q.four_borderDifference_at_gt (P.left+P.u) (P.right+P.v) hLu hRv h k hkv
    rw [hD₂,hD₃,hD₄,mul_zero,sub_zero] at hd
    have hn := Q.endpoint_shift_response_ne_zero hc P.m P.right P.v P.m_pos
      (by unfold ThreeComponentParameters.right; omega) P.v_pos
    apply mul_ne_zero ((complete_ne_zero_iff _).mpr hℓ.le) hn
    linear_combination -hd

theorem dense_threeMiddleContext_orientation_ne (Q : BetaDiagram 4) (hD : Q.Dense)
    (hS : ¬ Q.Symmetric) (P : ThreeComponentParameters)
    (hnonrot : P.left ≠ P.right ∨ P.ell ≠ P.m ∨ P.u ≠ P.v) :
    (Q.threeMiddleContext P).schur ≠ (Q.rotate.threeMiddleContext P).schur :=
  Q.threeMiddleContext_orientation_ne_of_coefficient
    (Q.endpointCoefficient_ne_zero_dense hD hS) (Q.dense_four_lower_part hD hS) P hnonrot

end SkewJacobiNegative.BetaDiagram
