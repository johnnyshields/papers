import SkewJacobiNegative.FiveExceptionalFamilies
import SkewJacobiNegative.FiveNormalForms
import SkewJacobiNegative.Gluing.RowInvariants
import SkewJacobiNegative.HomogeneousIrreducibility
import SkewJacobiNegative.SmallRowRigidity
import SkewJacobiNegative.FiveMarkers
import SkewJacobiNegative.NegativeInvariants
import SkewJacobiNegative.SchurClasses

/-!
# Five-negative same-opening and mixed-opening classification

Actual homogeneous determinants give the comparisons in
`prop:five-same-opening`, `prop:five-mixed-opening`, and `thm:five-base`.
The index-zero generator is retained, and normal-form parameters and the
exceptional beta lists are reconstructed from actual Schur equality.
-/

namespace SkewJacobiNegative
namespace FiveExceptional

theorem rotationEquivalent_symm {D E : BetaDiagram 5}
    (h : D.RotationEquivalent E) : E.RotationEquivalent D := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    have h := hc i.rev
    simp only [Fin.rev_rev] at h
    omega
  · intro i
    have h := hr i.rev
    simp only [Fin.rev_rev] at h
    omega

theorem eq_rotate_implies_rotation {D E : BetaDiagram 5} (h : D = E.rotate) :
    D.RotationEquivalent E := by
  refine ⟨0, ?_, ?_⟩
  · intro i
    have hi := congrArg (fun T : BetaDiagram 5 => T.row i) h
    simpa [BetaDiagram.rotate] using hi
  · intro i
    have hi := congrArg (fun T : BetaDiagram 5 => T.col i) h
    simpa [BetaDiagram.rotate] using hi

theorem F_not_translation_H (P Q : Parameters) (s t : Bool) :
    ¬ (F P s).TranslationEquivalent (H Q t) := by
  rintro ⟨c, hr, hc⟩
  have hlast := hc 4
  have h0 := hr 4
  have h1 := hr 3
  have hcol := hc 1
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  norm_num [F, H, rows, fCols, hCols] at hlast h0 h1 hcol
  omega

theorem F_ne_rotate_F (P Q : Parameters) (s t : Bool) :
    F P s ≠ (F Q t).rotate :=
  fun h => F_not_rotation_F P Q s t (eq_rotate_implies_rotation h)

theorem F_ne_rotate_H (P Q : Parameters) (s t : Bool) :
    F P s ≠ (H Q t).rotate :=
  fun h => F_not_rotation_H P Q s t (eq_rotate_implies_rotation h)

theorem H_ne_rotate_F (P Q : Parameters) (s t : Bool) :
    H P s ≠ (F Q t).rotate :=
  fun h => F_not_rotation_H Q P t s
    (rotationEquivalent_symm (eq_rotate_implies_rotation h))

theorem H_ne_rotate_H (P Q : Parameters) (s t : Bool) :
    H P s ≠ (H Q t).rotate :=
  fun h => H_not_rotation_H P Q s t (eq_rotate_implies_rotation h)

/-- The six pairwise inequalities for the source quartet. -/
theorem quartet_distinct (P : Parameters) (s : Bool) :
    F P s ≠ (F P s).rotate ∧ F P s ≠ H P s ∧
    F P s ≠ (H P s).rotate ∧ (F P s).rotate ≠ H P s ∧
    (F P s).rotate ≠ (H P s).rotate ∧ H P s ≠ (H P s).rotate := by
  refine ⟨F_ne_rotate_F P P s s, F_ne_H P s s,
    F_ne_rotate_H P P s s, ?_, ?_, H_ne_rotate_H P P s s⟩
  · exact fun h => H_ne_rotate_F P P s s h.symm
  · intro h
    have hc := congrArg (fun T : BetaDiagram 5 => T.row 3) h
    have := P.q_pos
    have := P.q_le_b
    have := P.b_lt_g
    norm_num [BetaDiagram.rotate, F, H, rows, fCols, hCols, Fin.rev] at hc
    omega

end FiveExceptional

namespace FiveNegative

/-- Schur equality reads the full row and overlap multisets without ordering assumptions. -/
theorem profile_readings (P Q : Gluing.Profile 4)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    P.rowMultiset = Q.rowMultiset ∧ P.gapMultiset = Q.gapMultiset := by
  have hp : P.schur = Q.schur := by
    simpa only [Gluing.Profile.toBetaDiagram_schur] using he
  exact ⟨(Gluing.Profile.rows_eq_of_schur_eq hp).2,
    Gluing.Profile.gaps_eq_of_schur_eq hp⟩

theorem middle_middle_readings (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (he : (M t ht).schur = (M s hs).schur) :
    (mProfile t ht).rowMultiset = (mProfile s hs).rowMultiset ∧
    (mProfile t ht).gapMultiset = (mProfile s hs).gapMultiset :=
  profile_readings _ _ he

theorem end_end_readings (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : (E t ht).schur = (E s hs).schur) :
    (eProfile t ht).rowMultiset = (eProfile s hs).rowMultiset ∧
    (eProfile t ht).gapMultiset = (eProfile s hs).gapMultiset :=
  profile_readings _ _ he

theorem mixed_readings (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur = (E s hs).schur) :
    (mProfile t ht).rowMultiset = (eProfile s hs).rowMultiset ∧
    (mProfile t ht).gapMultiset = (eProfile s hs).gapMultiset :=
  profile_readings _ _ he

/-- The homogeneous complementary polynomial retains every index-zero variable. -/
noncomputable def homCorner (D : BetaDiagram 5) : Gluing.HomLambda :=
  (D.homMatrix.submatrix Fin.succ Fin.castSucc).det

theorem homOddRename_homCorner (D : BetaDiagram 5) :
    homOddRename (homCorner D) = D.gamma.cornerPolynomial := by
  unfold homCorner BetaDiagram.cornerPolynomial BetaDiagram.cornerBoard
  rw [AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change homOddRename (Gluing.hTilde (D.row i.succ - D.col j.castSucc)) =
    complete (D.gamma.row i.succ - D.gamma.col j.castSucc)
  rw [homOddRename_hTilde]
  congr 1
  simp [BetaDiagram.gamma]
  ring

/-- Equality really produces the complete homogeneous first cofactor. -/
theorem homCorner_eq_of_schur_eq (D E : BetaDiagram 5)
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    homCorner D = homCorner E := by
  have hg : D.gamma.schur = E.gamma.schur := by
    rw [D.gamma_schur_encoding, E.gamma_schur_encoding, he]
  have hc := D.gamma.cornerPolynomial_eq_of_schur_eq E.gamma
    ((D.gamma_connected_iff).mpr hD) ((E.gamma_connected_iff).mpr hE) hg
  have hm : homOddRename (homCorner D) = homOddRename (homCorner E) := by
    simpa only [homOddRename_homCorner] using hc
  simpa only [homOddRetraction_rename] using congrArg homOddRetraction hm
/-- Coordinate factors are read before comparing the quadratic factors. -/
theorem coordinate_pair_reading (a p c d : ℕ) (A B : Gluing.HomLambda)
    (hB : ∀ j, ¬ (MvPolynomial.X j : Gluing.HomLambda) ∣ B)
    (he : MvPolynomial.X a * MvPolynomial.X p * A =
      MvPolynomial.X c * MvPolynomial.X d * B) :
    ((a = c ∧ p = d) ∨ (a = d ∧ p = c)) ∧ A = B := by
  have ha : (MvPolynomial.X a : Gluing.HomLambda) ∣
      MvPolynomial.X c * MvPolynomial.X d * B := by
    rw [← he]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have ha' : a = c ∨ a = d := by
    rw [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_mul_iff,
      MvPolynomial.X_dvd_X, MvPolynomial.X_dvd_X] at ha
    have hnot := hB a
    tauto
  have solve (a p c d : ℕ)
      (ha : a = c)
      (he : MvPolynomial.X a * MvPolynomial.X p * A =
        MvPolynomial.X c * MvPolynomial.X d * B) :
      p = d ∧ A = B := by
    subst c
    have hcancel : MvPolynomial.X p * A = MvPolynomial.X d * B := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero a)
      simpa only [mul_assoc] using he
    have hp : (MvPolynomial.X p : Gluing.HomLambda) ∣ MvPolynomial.X d * B := by
      rw [← hcancel]
      exact dvd_mul_right _ _
    have hpd : p = d := by
      rw [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X] at hp
      exact hp.resolve_right (hB p)
    subst d
    exact ⟨rfl, mul_left_cancel₀ (MvPolynomial.X_ne_zero p) hcancel⟩
  rcases ha' with ha | ha
  · obtain ⟨hp, hab⟩ := solve a p c d ha he
    exact ⟨Or.inl ⟨ha, hp⟩, hab⟩
  · have he' : MvPolynomial.X a * MvPolynomial.X p * A =
        MvPolynomial.X d * MvPolynomial.X c * B := by
      simpa only [mul_comm (MvPolynomial.X c) (MvPolynomial.X d)] using he
    obtain ⟨hp, hab⟩ := solve a p d c ha he'
    exact ⟨Or.inr ⟨ha, hp⟩, hab⟩

/-- The marker product determines the unordered endpoints and the actual quadratic. -/
theorem first_marker_reading (t s : Parameters)
    (hsu : s.tau < s.u) (hsv : s.tau < s.v)
    (he : MvPolynomial.X t.a * MvPolynomial.X t.p * B t.u t.v t.tau =
      MvPolynomial.X s.a * MvPolynomial.X s.p * B s.u s.v s.tau) :
    ((t.a = s.a ∧ t.p = s.p) ∨ (t.a = s.p ∧ t.p = s.a)) ∧
      B t.u t.v t.tau = B s.u s.v s.tau :=
  coordinate_pair_reading _ _ _ _ _ _
    (fun j => B_coordinate_not_dvd _ _ _ j hsu hsv) he

/-- A quadratic equality reads the opening label and both unordered core lengths. -/
theorem quadratic_parameter_reading (u v tau U V T : ℕ)
    (hu : tau < u) (hv : tau < v) (hU : T < U) (hV : T < V)
    (he : B u v tau = B U V T) :
    tau = T ∧ ((u = U ∧ v = V) ∨ (u = V ∧ v = U)) := by
  let D := quadraticDiagram u v tau hu hv
  let E := quadraticDiagram U V T hU hV
  have heh : D.homSchur = E.homSchur := by
    dsimp [D, E]
    rw [quadratic_homSchur, quadratic_homSchur]
    simpa only [B_eq_F] using he
  have hes : D.schur = E.schur := (D.homSchur_eq_iff E).mp heh
  rcases D.small_rows_rigidity_same_order E
    (quadratic_connected u v tau hu hv) (quadratic_connected U V T hU hV)
    (by omega) hes with h | h
  · obtain ⟨c, hr, hc⟩ := h
    have hr0 := hr 0
    have hr1 := hr 1
    have hc0 := hc 0
    have hc1 := hc 1
    norm_num [D, E, quadraticDiagram] at hr0 hr1 hc0 hc1
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  · obtain ⟨c, hr, hc⟩ := h
    have hr0 := hr 0
    have hr1 := hr 1
    have hc0 := hc 0
    have hc1 := hc 1
    norm_num [D, E, quadraticDiagram, Fin.rev] at hr0 hr1 hc0 hc1
    exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩

/-- All first-marker parameters are produced from its polynomial equality. -/
theorem complete_first_marker_reading (t s : Parameters)
    (htu : t.tau < t.u) (htv : t.tau < t.v)
    (hsu : s.tau < s.u) (hsv : s.tau < s.v)
    (he : MvPolynomial.X t.a * MvPolynomial.X t.p * B t.u t.v t.tau =
      MvPolynomial.X s.a * MvPolynomial.X s.p * B s.u s.v s.tau) :
    ((t.a = s.a ∧ t.p = s.p) ∨ (t.a = s.p ∧ t.p = s.a)) ∧
      t.tau = s.tau ∧
      ((t.u = s.u ∧ t.v = s.v) ∨ (t.u = s.v ∧ t.v = s.u)) := by
  obtain ⟨hend, hB⟩ := first_marker_reading t s hsu hsv he
  exact ⟨hend, quadratic_parameter_reading _ _ _ _ _ _ htu htv hsu hsv hB⟩


/-- In the strict corner regime, both marker products orient the endpoint pair. -/
theorem strict_two_marker_reading (t s : Parameters)
    (htu : t.tau < t.u) (htv : t.tau < t.v) (htb : t.p < t.b)
    (hsu : s.tau < s.u) (hsv : s.tau < s.v) (hsb : s.p < s.b)
    (hfirst : MvPolynomial.X t.a * MvPolynomial.X t.p * B t.u t.v t.tau =
      MvPolynomial.X s.a * MvPolynomial.X s.p * B s.u s.v s.tau)
    (hsecond : MvPolynomial.X t.a * MvPolynomial.X t.b * B t.u t.v t.tau =
      MvPolynomial.X s.a * MvPolynomial.X s.b * B s.u s.v s.tau) :
    t.a = s.a ∧ t.b = s.b ∧ t.p = s.p ∧ t.tau = s.tau ∧
      ((t.u = s.u ∧ t.v = s.v) ∨ (t.u = s.v ∧ t.v = s.u)) := by
  obtain ⟨hp, htau, hcore⟩ :=
    complete_first_marker_reading t s htu htv hsu hsv hfirst
  obtain ⟨hb, hB⟩ := coordinate_pair_reading t.a t.b s.a s.b
    (B t.u t.v t.tau) (B s.u s.v s.tau)
    (fun j => B_coordinate_not_dvd _ _ _ j hsu hsv) hsecond
  rcases hp with hp | hp <;> rcases hb with hb | hb
  all_goals exact ⟨by omega, by omega, by omega, htau, hcore⟩

theorem homCofactor_corner (D : BetaDiagram 5) :
    homCofactor D 0 4 = homCorner D := by
  change (-1 : Gluing.HomLambda) ^ 4 *
    (D.homMatrix.submatrix Fin.succ (Fin.last 4).succAbove).det = homCorner D
  rw [Fin.succAbove_last]
  norm_num [homCorner]

theorem middle_first_marker_eq (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (he : (M t ht).schur = (M s hs).schur) : C15 t = C15 s := by
  rw [← M_C15 t ht, ← M_C15 s hs, homCofactor_corner, homCofactor_corner]
  exact homCorner_eq_of_schur_eq _ _ (M_connected t ht) (M_connected s hs) he

theorem end_first_marker_eq (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : (E t ht).schur = (E s hs).schur) : C15 t = C15 s := by
  rw [← E_C15 t ht, ← E_C15 s hs, homCofactor_corner, homCofactor_corner]
  exact homCorner_eq_of_schur_eq _ _ (E_connected t ht) (E_connected s hs) he

theorem mixed_first_marker_eq (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur = (E s hs).schur) : C15 t = C15 s := by
  rw [← M_C15 t ht, ← E_C15 s hs, homCofactor_corner, homCofactor_corner]
  exact homCorner_eq_of_schur_eq _ _ (M_connected t ht) (E_connected s hs) he

/-- First-marker invariants of unrestricted mixed Schur equality. -/
theorem mixed_first_reading (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur = (E s hs).schur) :
    ((t.a = s.a ∧ t.p = s.p) ∨ (t.a = s.p ∧ t.p = s.a)) ∧
      t.tau = s.tau ∧
      ((t.u = s.u ∧ t.v = s.v) ∨ (t.u = s.v ∧ t.v = s.u)) := by
  exact complete_first_marker_reading t s ht.1 ht.2.1 hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)

/-- First-marker invariants of unrestricted middle-opening Schur equality. -/
theorem middle_first_reading (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (he : (M t ht).schur = (M s hs).schur) :
    ((t.a = s.a ∧ t.p = s.p) ∨ (t.a = s.p ∧ t.p = s.a)) ∧
      t.tau = s.tau ∧
      ((t.u = s.u ∧ t.v = s.v) ∨ (t.u = s.v ∧ t.v = s.u)) := by
  exact complete_first_marker_reading t s ht.1 ht.2.1 hs.1 hs.2.1
    (middle_first_marker_eq t s ht hs he)

/-- First-marker invariants of unrestricted end-opening Schur equality. -/
theorem end_first_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : (E t ht).schur = (E s hs).schur) :
    ((t.a = s.a ∧ t.p = s.p) ∨ (t.a = s.p ∧ t.p = s.a)) ∧
      t.tau = s.tau ∧
      ((t.u = s.u ∧ t.v = s.v) ∨ (t.u = s.v ∧ t.v = s.u)) := by
  exact complete_first_marker_reading t s ht.1 ht.2.1 hs.1 hs.2.1
    (end_first_marker_eq t s ht hs he)

/-- A coordinate-free factor cannot absorb an unmatched coordinate. -/
theorem coordinate_single_reading (i j : ℕ) (A B : Gluing.HomLambda)
    (hB : ¬ (MvPolynomial.X i : Gluing.HomLambda) ∣ B)
    (he : MvPolynomial.X i * A = MvPolynomial.X j * B) :
    i = j ∧ A = B := by
  have hi : (MvPolynomial.X i : Gluing.HomLambda) ∣ MvPolynomial.X j * B := by
    rw [← he]
    exact dvd_mul_right _ _
  rw [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X] at hi
  have hij := hi.resolve_right hB
  subst j
  exact ⟨rfl, mul_left_cancel₀ (MvPolynomial.X_ne_zero i) he⟩

/-- The top-only mixed contact is impossible, including coincident coordinate labels. -/
theorem mixed_top_contact_ne (t s : Parameters) (hs : ValidE s) :
    MvPolynomial.X t.a * G t.u t.tau t.b t.p t.c ≠
      B s.u s.v s.tau * T s.b s.p s.c := by
  intro he
  have ha : (MvPolynomial.X t.a : Gluing.HomLambda) ∣
      B s.u s.v s.tau * T s.b s.p s.c := by
    rw [← he]
    exact dvd_mul_right _ _
  rw [MvPolynomial.X_dvd_mul_iff] at ha
  rcases ha with ha | ha
  · exact B_coordinate_not_dvd _ _ _ t.a hs.1 hs.2.1 ha
  · exact T_coordinate_not_dvd _ _ _ t.a hs.2.2.1 (by
      have hc := hs.2.2.2.2.2
      omega) ha

/-- A right-only mixed contact would identify the forbidden middle endpoint lengths. -/
theorem mixed_right_contact_ne (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ha : t.a = s.a) (hp : t.p = s.p) :
    MvPolynomial.X t.x * MvPolynomial.X t.p * B t.u t.v t.tau ≠
      MvPolynomial.X s.a * MvPolynomial.X s.p * F s.v s.x s.tau := by
  intro he
  have he' : MvPolynomial.X t.x * B t.u t.v t.tau =
      MvPolynomial.X s.a * F s.v s.x s.tau := by
    apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.p)
    rw [← hp] at he
    convert he using 1 <;> ring
  have hcoord : ¬ (MvPolynomial.X t.x : Gluing.HomLambda) ∣ F s.v s.x s.tau :=
    F_coordinate_not_dvd _ _ _ t.x hs.2.1 (by
      have hu := hs.1
      have hx := hs.2.2.2.1
      omega)
  have hxa := (coordinate_single_reading _ _ _ _ hcoord he').1
  have hax := ht.2.2.2.1
  omega

/-- The two-row upper block used in the middle-opening remainder. -/
noncomputable def upperQuadratic (t : Parameters) (z : ℕ) : Gluing.HomLambda :=
  MvPolynomial.X t.x * MvPolynomial.X z -
    MvPolynomial.X t.a * MvPolynomial.X (z + t.x - t.a)

/-- The four disjoint corner contributions subtracted in same-opening comparisons. -/
noncomputable def middleCornerPart (t : Parameters) : Gluing.HomLambda :=
  B t.u t.v t.tau *
    (MvPolynomial.X t.a * MvPolynomial.X t.p * MvPolynomial.X (m t) -
      MvPolynomial.X t.a * MvPolynomial.X t.b *
        MvPolynomial.X (t.x+t.y+t.c-t.a-t.tau) -
      MvPolynomial.X t.x * MvPolynomial.X t.p *
        MvPolynomial.X (t.y+t.c+t.b-t.tau-t.p) +
      MvPolynomial.X t.x * MvPolynomial.X t.b *
        MvPolynomial.X (t.y+t.c-t.tau))

/-- The collected remainder in `eq:five-middle-remainder`. -/
noncomputable def middleRemainder (t : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.L * upperQuadratic t t.y * T t.b t.p t.c -
    MvPolynomial.X t.v * upperQuadratic t t.y *
      T t.b t.p (t.c+t.u-t.tau) -
    MvPolynomial.X t.u * upperQuadratic t (t.y+t.v-t.tau) * T t.b t.p t.c +
    MvPolynomial.X t.tau * upperQuadratic t (t.y+t.v-t.tau) *
      T t.b t.p (t.c+t.u-t.tau)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact polynomial subtraction is valid before any label ordering or contact split. -/
theorem middle_remainder_expansion (t : Parameters) (ht : ValidM t) :
    (M t ht).homSchur = middleCornerPart t + middleRemainder t := by
  have ht' := ht
  obtain ⟨hu,hv,hb,hx,hy,hc⟩ := ht'
  have h1 : t.y+t.x-t.a = t.x+t.y-t.a := by omega
  have h2 : t.y+t.v-t.tau+t.x-t.a = t.x+t.y+t.v-t.a-t.tau := by omega
  have h3 : t.c+(t.b-t.p) = t.c+t.q := rfl
  have h4 : t.c+t.u-t.tau = t.u+t.c-t.tau := by omega
  have h6 : t.u+t.c-t.tau+(t.b-t.p) = t.u+t.c+t.b-t.tau-t.p := by omega
  have h5 : t.c+t.u-t.tau+(t.b-t.p) = t.u+t.c+t.b-t.tau-t.p := by omega
  rw [BetaDiagram.homSchur, M_homMatrix t ht]
  norm_num [mMatrix, middleCornerPart, middleRemainder, upperQuadratic,
    T, B, Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.sum_univ_succ, Fin.succAbove, h1, h2, h3, h4, h5, h6]
  simp only [Parameters.L,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  ring

noncomputable def endA0 (t : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.x * MvPolynomial.X t.L -
    MvPolynomial.X t.u * MvPolynomial.X (t.x+t.v-t.tau)

/-- The connected upper three-row factor in `eq:five-end-block`. -/
noncomputable def endJ (t : Parameters) (z : ℕ) : Gluing.HomLambda :=
  endA0 t * MvPolynomial.X z -
    F t.v t.x t.tau * MvPolynomial.X (z+t.u-t.tau) +
    B t.u t.v t.tau * MvPolynomial.X (t.x+z-t.tau)

noncomputable def endCornerPart (t : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.a *
    (B t.u t.v t.tau *
      (MvPolynomial.X t.p * MvPolynomial.X (m t) -
        MvPolynomial.X t.b * MvPolynomial.X (t.x+t.y+t.c-t.tau-t.a)) -
      F t.v t.x t.tau *
      (MvPolynomial.X t.p * MvPolynomial.X (t.u+t.y+t.c+t.b-t.tau-t.a-t.p) -
        MvPolynomial.X t.b * MvPolynomial.X (t.u+t.y+t.c-t.tau-t.a)) +
      endA0 t *
      (MvPolynomial.X t.p * MvPolynomial.X (t.y+t.c+t.b-t.a-t.p) -
        MvPolynomial.X t.b * MvPolynomial.X (t.y+t.c-t.a)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The joint-anchor identity is an identity of the actual end-opening determinant. -/
theorem end_block_expansion (t : Parameters) (ht : ValidE t) :
    (E t ht).homSchur = endJ t t.y * T t.b t.p t.c + endCornerPart t := by
  have h1 : t.y+t.u-t.tau = t.u+t.y-t.tau := by omega
  have h2 : t.c+(t.b-t.p) = t.c+t.q := rfl
  rw [BetaDiagram.homSchur, E_homMatrix]
  norm_num [eMatrix, endJ, endA0, endCornerPart, T, B, F,
    Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.sum_univ_succ, Fin.succAbove, h1, h2]
  simp only [Parameters.L,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  ring

/-- The upper connected three-row profile of an end-opening board. -/
def endUpperProfile (t : Parameters) (ht : ValidE t) (z : ℕ) (hz : t.v < z) :
    Gluing.Profile 2 where
  r := ![t.x, t.L, z]
  g := ![t.u, t.v]
  r_pos := by
    have hu := ht.1
    have hv := ht.2.1
    have hx := ht.2.2.2.1
    intro i
    fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_castSucc := by
    have hu := ht.1
    have hv := ht.2.1
    have hx := ht.2.2.2.1
    intro i
    fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_succ := by
    have hu := ht.1
    have hv := ht.2.1
    intro i
    fin_cases i <;> simp [Parameters.L] <;> omega

/-- The `J` factor is the actual homogeneous three-row determinant, also at `tau = 0`. -/
theorem endJ_eq_homSchur (t : Parameters) (ht : ValidE t) (z : ℕ) (hz : t.v < z) :
    endJ t z = (endUpperProfile t ht z hz).toBetaDiagram.homSchur := by
  have hu := ht.1
  have hv := ht.2.1
  have hx := ht.2.2.2.1
  have hX {w : ℤ} {k : ℕ} (h : w=(k : ℤ)) :
      Gluing.hTilde w=(MvPolynomial.X k : Gluing.HomLambda) := by
    rw [h,Gluing.hTilde,if_neg (show ¬(k : ℤ)<0 by omega),Int.toNat_natCast]
  have hm : (endUpperProfile t ht z hz).toBetaDiagram.homMatrix =
      !![MvPolynomial.X t.x,MvPolynomial.X (t.x+t.v-t.tau),MvPolynomial.X (t.x+z-t.tau);
        MvPolynomial.X t.u,MvPolynomial.X t.L,MvPolynomial.X (t.u+z-t.tau);
        MvPolynomial.X t.tau,MvPolynomial.X t.v,MvPolynomial.X z] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [BetaDiagram.homMatrix,Gluing.Profile.toBetaDiagram,endUpperProfile,
        Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ] <;>
      apply hX <;> (dsimp only [Parameters.L] at * <;> omega)
  rw [BetaDiagram.homSchur, hm, Matrix.det_fin_three]
  have hshift : z+t.u-t.tau=t.u+z-t.tau := by omega
  norm_num [endJ,endA0,F,B,Parameters.L,hshift,Matrix.of_apply]
  simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  ring

theorem endJ_irreducible (t : Parameters) (ht : ValidE t) (z : ℕ) (hz : t.v < z) :
    Irreducible (endJ t z) := by
  rw [endJ_eq_homSchur t ht z hz]
  exact ((endUpperProfile t ht z hz).toBetaDiagram).homSchur_irreducible
    (Gluing.Profile.toBetaDiagram_connected _)

theorem endJ_coordinate_not_dvd (t : Parameters) (ht : ValidE t)
    (z : ℕ) (hz : t.v < z) (j : ℕ) :
    ¬ (MvPolynomial.X j : Gluing.HomLambda) ∣ endJ t z := by
  rw [endJ_eq_homSchur t ht z hz]
  exact homSchur_coordinate_not_dvd _ (Gluing.Profile.toBetaDiagram_connected _) j

/-- The coefficient-one square-weight initial form fixes every scalar associate. -/
theorem schur_scalar_normalization {n k : ℕ} (D : BetaDiagram n) (E : BetaDiagram k)
    (r : ℚ) (hr : r ≠ 0)
    (he : D.schur = MvPolynomial.C r * E.schur) : r = 1 := by
  classical
  have hC : Base.initialForm Base.squareWeight.generatorWeight
      (MvPolynomial.C r : CompleteRing) = MvPolynomial.C r := by
    exact Base.initialForm_eq_of_homogeneous (MvPolynomial.C_ne_zero.mpr hr)
      (MvPolynomial.isWeightedHomogeneous_C _ _)
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [D.square_initialForm, Base.initialForm_mul
    (MvPolynomial.C_ne_zero.mpr hr) E.schur_ne_zero, hC, E.square_initialForm] at hi
  let ev : CompleteRing →ₐ[ℚ] ℚ := MvPolynomial.aeval fun _ => 1
  have hD (i : Fin n) : ev (complete (D.row i - D.col i)) = 1 := by
    have hpos : 0<D.row i-D.col i := sub_pos.mpr (D.row_nonempty i)
    let j : ℕ+ := ⟨(D.row i-D.col i).toNat,by omega⟩
    have hX : complete (D.row i-D.col i)=(MvPolynomial.X j : CompleteRing) :=
      complete_of_pos hpos
    rw [hX]
    exact MvPolynomial.aeval_X (R := ℚ) (fun _ : ℕ+ => (1 : ℚ)) j
  have hE (i : Fin k) : ev (complete (E.row i - E.col i)) = 1 := by
    have hpos : 0<E.row i-E.col i := sub_pos.mpr (E.row_nonempty i)
    let j : ℕ+ := ⟨(E.row i-E.col i).toNat,by omega⟩
    have hX : complete (E.row i-E.col i)=(MvPolynomial.X j : CompleteRing) :=
      complete_of_pos hpos
    rw [hX]
    exact MvPolynomial.aeval_X (R := ℚ) (fun _ : ℕ+ => (1 : ℚ)) j
  have hh := congrArg ev hi
  have hCr : ev (MvPolynomial.C r)=r := by
    calc
      ev (MvPolynomial.C r)=algebraMap ℚ ℚ r :=
        MvPolynomial.aeval_C (fun _ : ℕ+ => (1 : ℚ)) r
      _=r := rfl
  simp only [map_mul,map_prod,hD,hE,Finset.prod_const_one,hCr,mul_one] at hh
  exact hh.symm

theorem homSchur_scalar_normalization {n k : ℕ} (D : BetaDiagram n) (E : BetaDiagram k)
    (r : ℚ) (hr : r ≠ 0)
    (he : D.homSchur = MvPolynomial.C r * E.homSchur) : r = 1 := by
  have hC : homOddRename (MvPolynomial.C r) = MvPolynomial.C r := by
    simp [homOddRename]
  have hg : D.gamma.schur = MvPolynomial.C r * E.gamma.schur := by
    simpa only [map_mul, BetaDiagram.homOddRename_homSchur, hC] using
      congrArg homOddRename he
  exact schur_scalar_normalization D.gamma E.gamma r hr hg

/-- Associated homogeneous skew Schur determinants are equal, not merely proportional. -/
theorem homSchur_eq_of_associated {n k : ℕ} (D : BetaDiagram n) (E : BetaDiagram k)
    (he : Associated D.homSchur E.homSchur) : D.homSchur = E.homSchur := by
  obtain ⟨u, hu⟩ := he
  obtain ⟨r, hr, hur⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hr0 : r ≠ 0 := hr.ne_zero
  have hscale : E.homSchur = MvPolynomial.C r * D.homSchur := by
    rw [← hu, hur]
    ring
  have hr1 := homSchur_scalar_normalization E D r hr0 hscale
  simpa [hr1] using hscale.symm

/-- Connected factors of different row degrees cannot be confused in a product. -/
theorem unequal_order_factor_reading {n k : ℕ}
    (D A : BetaDiagram n) (E B : BetaDiagram k)
    (hD : D.Connected) (hA : A.Connected) (hE : E.Connected) (hB : B.Connected)
    (hnk : n ≠ k)
    (he : D.homSchur * E.homSchur = A.homSchur * B.homSchur) :
    D.homSchur = A.homSchur ∧ E.homSchur = B.homSchur := by
  have hdirr := D.homSchur_irreducible hD
  have hairr := A.homSchur_irreducible hA
  have hbirr := B.homSchur_irreducible hB
  have hdvd : D.homSchur ∣ A.homSchur * B.homSchur := by
    rw [← he]
    exact dvd_mul_right _ _
  rcases hdirr.prime.dvd_mul.mp hdvd with ha | hb
  · have hda := homSchur_eq_of_associated D A (hdirr.associated_of_dvd hairr ha)
    refine ⟨hda, ?_⟩
    rw [hda] at he
    exact mul_left_cancel₀ hairr.ne_zero he
  · have hdb := homSchur_eq_of_associated D B (hdirr.associated_of_dvd hbirr hb)
    have hdeg := congrArg MvPolynomial.totalDegree hdb
    rw [D.homSchur_totalDegree, B.homSchur_totalDegree] at hdeg
    exact (hnk hdeg).elim

/-- The end-opening joint-anchor product separates its cubic and quadratic factors. -/
theorem end_product_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : endJ t t.y * T t.b t.p t.c = endJ s s.y * T s.b s.p s.c) :
    endJ t t.y = endJ s s.y ∧ T t.b t.p t.c = T s.b s.p s.c := by
  have hty : t.v < t.y := by have := ht.2.2.2.2.1; omega
  have hsy : s.v < s.y := by have := hs.2.2.2.2.1; omega
  have htc : t.p < t.c := by have := ht.2.2.2.2.2; omega
  have hsc : s.p < s.c := by have := hs.2.2.2.2.2; omega
  let D := (endUpperProfile t ht t.y hty).toBetaDiagram
  let A := (endUpperProfile s hs s.y hsy).toBetaDiagram
  let E := quadraticDiagram t.b t.c t.p ht.2.2.1 htc
  let B' := quadraticDiagram s.b s.c s.p hs.2.2.1 hsc
  have hJt : D.homSchur = endJ t t.y := (endJ_eq_homSchur t ht t.y hty).symm
  have hJs : A.homSchur = endJ s s.y := (endJ_eq_homSchur s hs s.y hsy).symm
  have hTt : E.homSchur = T t.b t.p t.c := by
    rw [quadratic_homSchur, ← T_eq_F t.b t.p t.c ht.2.2.1]
  have hTs : B'.homSchur = T s.b s.p s.c := by
    rw [quadratic_homSchur, ← T_eq_F s.b s.p s.c hs.2.2.1]
  have hh : D.homSchur * E.homSchur = A.homSchur * B'.homSchur := by
    simpa only [hJt, hJs, hTt, hTs] using he
  have hread := unequal_order_factor_reading D A E B'
    (Gluing.Profile.toBetaDiagram_connected _)
    (Gluing.Profile.toBetaDiagram_connected _)
    (quadratic_connected _ _ _ _ _) (quadratic_connected _ _ _ _ _) (by omega) hh
  simpa only [hJt, hJs, hTt, hTs] using hread

/-- Fixing the endpoint pair makes the remaining quadratic factor injective. -/
theorem T_injective (b p c d : ℕ) (hb : p < b) (hc : p < c) (hd : p < d)
    (he : T b p c = T b p d) : c = d := by
  have heB : B b c p = B b d p := by
    rw [B_eq_F, B_eq_F, ← T_eq_F b p c hb, ← T_eq_F b p d hb]
    exact he
  have hr := (quadratic_parameter_reading b c p b d p hb hc hb hd heB).2
  rcases hr with h | h <;> omega

/-- Fixing both joint anchors gives literal end-opening parameter rigidity. -/
theorem end_joint_anchor (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hx : t.x = s.x) (hu : t.u = s.u) (hv : t.v = s.v)
    (htau : t.tau = s.tau) (hm : m t = m s)
    (ha : t.a = s.a) (hb : t.b = s.b) (hp : t.p = s.p)
    (he : (E t ht).schur = (E s hs).schur) : t = s := by
  have hty := ht.2.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have htu := ht.1
  have hsu := hs.1
  have htv := ht.2.1
  have hsv := hs.2.1
  have htb := ht.2.2.1
  have hsb := hs.2.2.1
  have hsum : t.y+t.c=s.y+s.c := by
    dsimp [m] at hm
    omega
  have h1 : t.x+t.y+t.c-t.tau-t.a=s.x+s.y+s.c-s.tau-s.a := by omega
  have h2 : t.u+t.y+t.c+t.b-t.tau-t.a-t.p =
      s.u+s.y+s.c+s.b-s.tau-s.a-s.p := by omega
  have h3 : t.u+t.y+t.c-t.tau-t.a=s.u+s.y+s.c-s.tau-s.a := by omega
  have h4 : t.y+t.c+t.b-t.a-t.p=s.y+s.c+s.b-s.a-s.p := by omega
  have h5 : t.y+t.c-t.a=s.y+s.c-s.a := by omega
  have hcorner : endCornerPart t = endCornerPart s := by
    unfold endCornerPart
    rw [h1, h2, h3, h4, h5, hm]
    simp only [endA0, B, F, Parameters.L, hx, hu, hv, htau, ha, hb, hp]
  have heh := ((E t ht).homSchur_eq_iff (E s hs)).mpr he
  rw [end_block_expansion t ht, end_block_expansion s hs, hcorner] at heh
  have hprod := add_right_cancel heh
  have hT := (end_product_reading t s ht hs hprod).2
  have htc : t.p < t.c := by have := ht.2.2.2.2.2; omega
  have hsc : t.p < s.c := by have := hs.2.2.2.2.2; omega
  have hc : t.c = s.c := by
    rw [← hb, ← hp] at hT
    exact T_injective t.b t.p t.c s.c htb htc hsc hT
  have hy : t.y = s.y := by omega
  cases t
  cases s
  simp_all

def middleTopCandidate (t : Parameters) : ℕ := t.x+t.y+t.v-t.a-t.tau
def middleRightCandidate (t : Parameters) : ℕ := t.y+t.c+t.b-t.tau-t.p

/-- The actual middle determinant after its two common top-row corners are removed. -/
noncomputable def middleTail (t : Parameters) : Gluing.HomLambda :=
  middleRemainder t + B t.u t.v t.tau *
    (-MvPolynomial.X t.x * MvPolynomial.X t.p *
      MvPolynomial.X (middleRightCandidate t) +
      MvPolynomial.X t.x * MvPolynomial.X t.b *
        MvPolynomial.X (t.y+t.c-t.tau))

theorem middle_tail_split (t : Parameters) (ht : ValidM t) :
    (M t ht).homSchur =
      MvPolynomial.X t.a * B t.u t.v t.tau *
        (MvPolynomial.X t.p * MvPolynomial.X (m t) -
          MvPolynomial.X t.b * MvPolynomial.X (t.x+t.y+t.c-t.a-t.tau)) +
      middleTail t := by
  rw [middle_remainder_expansion]
  unfold middleCornerPart middleTail middleRightCandidate
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The complete largest-label derivative of the middle comparison tail. -/
theorem middle_tail_coefficient (t : Parameters) (ht : ValidM t) (j : ℕ)
    (hR : middleTopCandidate t ≤ j) (hZ : middleRightCandidate t ≤ j) :
    MvPolynomial.pderiv j (middleTail t) =
      (if j = middleTopCandidate t then
        MvPolynomial.X t.a * G t.u t.tau t.b t.p t.c else 0) -
      (if j = middleRightCandidate t then
        MvPolynomial.X t.x * MvPolynomial.X t.p * B t.u t.v t.tau else 0) := by
  rcases ht with ⟨hu,hv,hb,hx,hy,hc⟩
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have h1 : t.y+t.v-t.tau+t.x-t.a=middleTopCandidate t := by
    dsimp [middleTopCandidate]
    omega
  have h2 : t.c+t.u-t.tau+(t.b-t.p)<j := by
    dsimp [middleRightCandidate] at hZ
    omega
  have h3 : t.y+t.x-t.a<j := by
    dsimp [middleTopCandidate] at hR
    omega
  have h4 : t.y+t.v-t.tau<j := by
    dsimp [middleTopCandidate] at hR
    omega
  have h5 : t.c+(t.b-t.p)<j := by
    dsimp [middleRightCandidate] at hZ
    omega
  have h6 : t.c+t.u-t.tau<j := by omega
  have h7 : t.y+t.c-t.tau<j := by
    dsimp [middleRightCandidate] at hZ
    omega
  have h8 : t.L<j := by dsimp [middleTopCandidate] at hR; omega
  have h9 : t.x<j := by dsimp [middleTopCandidate] at hR; omega
  have h10 : t.y<j := by omega
  have h11 : t.c<j := by omega
  have h12 : t.b<j := by dsimp [middleRightCandidate] at hZ; omega
  have h13 : t.a<j := by omega
  have h14 : t.u<j := by omega
  have h15 : t.v<j := by omega
  have h16 : t.tau<j := by omega
  have h17 : t.p<j := by omega
  simp only [middleTail, middleRemainder, upperQuadratic, T, B, G, h1,
    map_add, map_sub, MvPolynomial.pderiv_mul, map_neg]
  simp only [MvPolynomial.pderiv_X_of_ne (ne_of_lt h2),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h3),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h4),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h5),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h6),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h7),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h8),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h9),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h10),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h11),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h12),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h13),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h14),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h15),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h16),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h17)]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> try omega
  all_goals ring

def endTopCandidate (t : Parameters) : ℕ := t.x+t.y-t.tau
def endRightCandidate (t : Parameters) : ℕ := t.u+t.y+t.c+t.b-t.tau-t.a-t.p

noncomputable def endTail (t : Parameters) : Gluing.HomLambda :=
  endJ t t.y * T t.b t.p t.c + MvPolynomial.X t.a *
    (-F t.v t.x t.tau *
      (MvPolynomial.X t.p * MvPolynomial.X (endRightCandidate t) -
        MvPolynomial.X t.b * MvPolynomial.X (t.u+t.y+t.c-t.tau-t.a)) +
      endA0 t *
      (MvPolynomial.X t.p * MvPolynomial.X (t.y+t.c+t.b-t.a-t.p) -
        MvPolynomial.X t.b * MvPolynomial.X (t.y+t.c-t.a)))

theorem end_tail_split (t : Parameters) (ht : ValidE t) :
    (E t ht).homSchur =
      MvPolynomial.X t.a * B t.u t.v t.tau *
        (MvPolynomial.X t.p * MvPolynomial.X (m t) -
          MvPolynomial.X t.b * MvPolynomial.X (t.x+t.y+t.c-t.tau-t.a)) +
      endTail t := by
  rw [end_block_expansion]
  unfold endCornerPart endTail endRightCandidate
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The complete largest-label derivative of the oriented end comparison tail. -/
theorem end_tail_coefficient (t : Parameters) (ht : ValidE t) (j : ℕ)
    (hR : endTopCandidate t ≤ j) (hZ : endRightCandidate t ≤ j) :
    MvPolynomial.pderiv j (endTail t) =
      (if j = endTopCandidate t then B t.u t.v t.tau * T t.b t.p t.c else 0) -
      (if j = endRightCandidate t then
        MvPolynomial.X t.a * MvPolynomial.X t.p * F t.v t.x t.tau else 0) := by
  rcases ht with ⟨hu,hv,hb,hx,hy,hc⟩
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have h1 : t.x+t.y-t.tau=endTopCandidate t := rfl
  have h2 : t.x+t.v-t.tau<j := by dsimp [endTopCandidate] at hR; omega
  have h3 : t.y+t.u-t.tau<j := by dsimp [endTopCandidate] at hR; omega
  have h4 : t.c+(t.b-t.p)<j := by dsimp [endRightCandidate] at hZ; omega
  have h5 : t.u+t.y+t.c-t.tau-t.a<j := by dsimp [endRightCandidate] at hZ; omega
  have h6 : t.y+t.c+t.b-t.a-t.p<j := by dsimp [endRightCandidate] at hZ; omega
  have h7 : t.y+t.c-t.a<j := by omega
  have h8 : t.L<j := by dsimp [endTopCandidate] at hR; omega
  have h9 : t.x<j := by dsimp [endTopCandidate] at hR; omega
  have h10 : t.y<j := by dsimp [endTopCandidate] at hR; omega
  have h11 : t.c<j := by omega
  have h12 : t.b<j := by dsimp [endRightCandidate] at hZ; omega
  have h13 : t.a<j := by omega
  have h14 : t.u<j := by omega
  have h15 : t.v<j := by omega
  have h16 : t.tau<j := by omega
  have h17 : t.p<j := by omega
  simp only [endTail, endJ, endA0, T, B, F, h1,
    map_add, map_sub, MvPolynomial.pderiv_mul, map_neg]
  simp only [MvPolynomial.pderiv_X_of_ne (ne_of_lt h2),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h3),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h4),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h5),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h6),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h7),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h8),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h9),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h10),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h11),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h12),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h13),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h14),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h15),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h16),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt h17)]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> try omega
  all_goals ring

/-- Once the two actual corner anchors agree, equality gives equality of the full tails. -/
theorem mixed_tail_eq (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (htau : t.tau=s.tau)
    (hB : B t.u t.v t.tau=B s.u s.v s.tau) (hm : m t=m s)
    (he : (M t ht).schur=(E s hs).schur) : middleTail t=endTail s := by
  have hty := ht.2.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have htu := ht.1
  have hsu := hs.1
  have htv := ht.2.1
  have hsv := hs.2.1
  have htb := ht.2.2.1
  have hsb := hs.2.2.1
  have htx := ht.2.2.2.1
  have hsx := hs.2.2.2.1
  have hindex : t.x+t.y+t.c-t.a-t.tau=s.x+s.y+s.c-s.tau-s.a := by
    dsimp [m] at hm
    omega
  have hh := ((M t ht).homSchur_eq_iff (E s hs)).mpr he
  rw [middle_tail_split t ht, end_tail_split s hs] at hh
  rw [hindex, ha, hb, hp, hB, hm] at hh
  exact add_left_cancel hh

/-- The four candidate indices are compared jointly, including all multiple contacts. -/
def mixedContactLabel (t s : Parameters) : ℕ :=
  max (max (middleTopCandidate t) (endTopCandidate s))
    (max (middleRightCandidate t) (endRightCandidate s))

noncomputable def mixedContactCoefficient (t s : Parameters) : Gluing.HomLambda :=
  (if mixedContactLabel t s=middleTopCandidate t then
    MvPolynomial.X t.a * G t.u t.tau t.b t.p t.c else 0) -
  (if mixedContactLabel t s=endTopCandidate s then
    B s.u s.v s.tau * T s.b s.p s.c else 0) -
  (if mixedContactLabel t s=middleRightCandidate t then
    MvPolynomial.X t.x * MvPolynomial.X t.p * B t.u t.v t.tau else 0) +
  (if mixedContactLabel t s=endRightCandidate s then
    MvPolynomial.X s.a * MvPolynomial.X s.p * F s.v s.x s.tau else 0)

/-- `eq:five-mixed-coefficient` follows from actual polynomial equality, not a supplied identity. -/
theorem mixed_contact_zero (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (htau : t.tau=s.tau)
    (hB : B t.u t.v t.tau=B s.u s.v s.tau) (hm : m t=m s)
    (he : (M t ht).schur=(E s hs).schur) : mixedContactCoefficient t s=0 := by
  have htail := mixed_tail_eq t s ht hs ha hb hp htau hB hm he
  have hd := congrArg (MvPolynomial.pderiv (mixedContactLabel t s)) htail
  have hR : middleTopCandidate t ≤ mixedContactLabel t s := by
    unfold mixedContactLabel
    omega
  have hZ : middleRightCandidate t ≤ mixedContactLabel t s := by
    unfold mixedContactLabel
    omega
  have hR' : endTopCandidate s ≤ mixedContactLabel t s := by
    unfold mixedContactLabel
    omega
  have hZ' : endRightCandidate s ≤ mixedContactLabel t s := by
    unfold mixedContactLabel
    omega
  rw [middle_tail_coefficient t ht _ hR hZ, end_tail_coefficient s hs _ hR' hZ'] at hd
  unfold mixedContactCoefficient
  linear_combination hd

/-- A maximal mixed contact always involves a top position and a right position. -/
theorem mixed_contact_active (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ha : t.a=s.a) (hp : t.p=s.p)
    (hK : mixedContactCoefficient t s=0) :
    (mixedContactLabel t s=middleTopCandidate t ∨
      mixedContactLabel t s=endTopCandidate s) ∧
    (mixedContactLabel t s=middleRightCandidate t ∨
      mixedContactLabel t s=endRightCandidate s) := by
  have hsome : mixedContactLabel t s=middleTopCandidate t ∨
      mixedContactLabel t s=endTopCandidate s ∨
      mixedContactLabel t s=middleRightCandidate t ∨
      mixedContactLabel t s=endRightCandidate s := by
    unfold mixedContactLabel
    omega
  have hMtop : MvPolynomial.X t.a * G t.u t.tau t.b t.p t.c ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero _) (M_G_irreducible t ht).ne_zero
  have hEtop : B s.u s.v s.tau * T s.b s.p s.c ≠ 0 := by
    apply mul_ne_zero (B_irreducible _ _ _ hs.1 hs.2.1).ne_zero
    exact (T_irreducible _ _ _ hs.2.2.1 (by
      have := hs.2.2.2.2.2
      omega)).ne_zero
  have hMright : MvPolynomial.X t.x * MvPolynomial.X t.p * B t.u t.v t.tau ≠ 0 :=
    mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
      (B_irreducible _ _ _ ht.1 ht.2.1).ne_zero
  have hEright : MvPolynomial.X s.a * MvPolynomial.X s.p * F s.v s.x s.tau ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
    exact (F_irreducible _ _ _ hs.2.1 (by
      have hu := hs.1
      have hx := hs.2.2.2.1
      omega)).ne_zero
  constructor
  · by_contra h
    have hR : mixedContactLabel t s ≠ middleTopCandidate t := by tauto
    have hR' : mixedContactLabel t s ≠ endTopCandidate s := by tauto
    simp only [mixedContactCoefficient,if_neg hR,if_neg hR'] at hK
    by_cases hZ : mixedContactLabel t s=middleRightCandidate t <;>
      by_cases hZ' : mixedContactLabel t s=endRightCandidate s
    · simp only [if_pos hZ,if_pos hZ'] at hK
      exact mixed_right_contact_ne t s ht hs ha hp (by linear_combination -hK)
    · simp only [if_pos hZ,if_neg hZ'] at hK
      exact hMright (by linear_combination -hK)
    · simp only [if_neg hZ,if_pos hZ'] at hK
      exact hEright (by linear_combination hK)
    · tauto
  · by_contra h
    have hZ : mixedContactLabel t s ≠ middleRightCandidate t := by tauto
    have hZ' : mixedContactLabel t s ≠ endRightCandidate s := by tauto
    simp only [mixedContactCoefficient,if_neg hZ,if_neg hZ'] at hK
    by_cases hR : mixedContactLabel t s=middleTopCandidate t <;>
      by_cases hR' : mixedContactLabel t s=endTopCandidate s
    · simp only [if_pos hR,if_pos hR'] at hK
      exact mixed_top_contact_ne t s hs (by linear_combination hK)
    · simp only [if_pos hR,if_neg hR'] at hK
      exact hMtop (by linear_combination hK)
    · simp only [if_neg hR,if_pos hR'] at hK
      exact hEtop (by linear_combination -hK)
    · tauto

/-- Exact division by a coordinate with its zero-coordinate specialization as remainder. -/
theorem coordinate_quotient_remainder (j : ℕ) (f : Gluing.HomLambda) :
    ∃ q, f = MvPolynomial.X j * q + eraseOne j f := by
  induction f using MvPolynomial.induction_on with
  | C r =>
      refine ⟨0, ?_⟩
      simp [eraseOne]
  | add f g ihf ihg =>
      obtain ⟨q, hq⟩ := ihf
      obtain ⟨r, hr⟩ := ihg
      refine ⟨q+r, ?_⟩
      calc
        f+g=(MvPolynomial.X j*q+eraseOne j f)+(MvPolynomial.X j*r+eraseOne j g) :=
          congrArg₂ (fun a b : Gluing.HomLambda => a+b) hq hr
        _=MvPolynomial.X j*(q+r)+eraseOne j (f+g) := by
          rw [map_add]
          ring
  | mul_X f k ih =>
      obtain ⟨q, hq⟩ := ih
      by_cases hk : k=j
      · subst k
        refine ⟨f, ?_⟩
        have hkill : eraseOne j (MvPolynomial.X j)=0 := by simp [eraseOne_X]
        simp only [map_mul,hkill,mul_zero,add_zero]
        ring
      · refine ⟨q * MvPolynomial.X k, ?_⟩
        have hkeep : eraseOne j (MvPolynomial.X k)=MvPolynomial.X k := by
          simp [eraseOne_X,hk]
        calc
          f*MvPolynomial.X k=(MvPolynomial.X j*q+eraseOne j f)*MvPolynomial.X k :=
            congrArg (fun a : Gluing.HomLambda => a*MvPolynomial.X k) hq
          _=MvPolynomial.X j*(q*MvPolynomial.X k)+eraseOne j (f*MvPolynomial.X k) := by
            rw [map_mul,hkeep]
            ring

theorem eraseOne_eq_zero_iff_coordinate_dvd (j : ℕ) (f : Gluing.HomLambda) :
    eraseOne j f=0 ↔ (MvPolynomial.X j : Gluing.HomLambda) ∣ f := by
  constructor
  · intro hf
    obtain ⟨q, hq⟩ := coordinate_quotient_remainder j f
    exact ⟨q, by simpa [hf] using hq⟩
  · rintro ⟨q, rfl⟩
    simp

/-- Every coordinate-free factor survives every coordinate erasure. -/
theorem eraseOne_ne_zero_of_coordinate_not_dvd (j : ℕ) (f : Gluing.HomLambda)
    (hf : ¬ (MvPolynomial.X j : Gluing.HomLambda) ∣ f) : eraseOne j f ≠ 0 :=
  fun he => hf ((eraseOne_eq_zero_iff_coordinate_dvd j f).mp he)

private theorem eraseOne_contact_balance (j : ℕ)
    (A B C D : Gluing.HomLambda) (c d : Prop) [Decidable c] [Decidable d]
    (hC : eraseOne j C=0) (hD : eraseOne j D=0)
    (h : A-B-(if c then C else 0)+(if d then D else 0)=0) :
    eraseOne j A=eraseOne j B := by
  have hc : eraseOne j (if c then C else 0)=0 := by
    by_cases hc : c
    · rw [if_pos hc]
      exact hC
    · rw [if_neg hc,map_zero]
  have hd : eraseOne j (if d then D else 0)=0 := by
    by_cases hd : d
    · rw [if_pos hd]
      exact hD
    · rw [if_neg hd,map_zero]
  have hh:=congrArg (eraseOne j) h
  rw [map_add,map_sub,map_sub,hc,hd,map_zero,sub_zero,add_zero] at hh
  exact sub_eq_zero.mp hh

/-- The end-only active top contact is excluded by a genuine coordinate specialization. -/
theorem mixed_end_top_only_impossible (t s : Parameters) (hs : ValidE s)
    (hp : t.p=s.p)
    (hR : mixedContactLabel t s ≠ middleTopCandidate t)
    (hR' : mixedContactLabel t s = endTopCandidate s)
    (hK : mixedContactCoefficient t s=0) : False := by
  have hBne := eraseOne_ne_zero_of_coordinate_not_dvd s.p (B s.u s.v s.tau)
    (B_coordinate_not_dvd _ _ _ s.p hs.1 hs.2.1)
  have hbp : s.b ≠ s.p := by have := hs.2.2.1; omega
  have hcp : s.c ≠ s.p := by have := hs.2.2.2.2.2; omega
  have hM : eraseOne s.p (MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau)=0 := by
    rw [hp]
    simp only [map_mul,eraseOne_X,if_pos rfl,ite_true,mul_zero,zero_mul]
  have hE : eraseOne s.p (MvPolynomial.X s.a*MvPolynomial.X s.p*F s.v s.x s.tau)=0 := by
    simp only [map_mul,eraseOne_X,if_pos rfl,ite_true,mul_zero,zero_mul]
  have hT : eraseOne s.p (T s.b s.p s.c)=MvPolynomial.X s.b*MvPolynomial.X s.c := by
    simp only [T,map_sub,map_mul,eraseOne_X,if_neg hbp,if_neg hcp,
      if_pos rfl,ite_true,zero_mul,sub_zero]
  simp only [mixedContactCoefficient,if_neg hR,if_pos hR'] at hK
  have hh:=eraseOne_contact_balance s.p
    0 (B s.u s.v s.tau*T s.b s.p s.c)
    (MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau)
    (MvPolynomial.X s.a*MvPolynomial.X s.p*F s.v s.x s.tau)
    (mixedContactLabel t s=middleRightCandidate t)
    (mixedContactLabel t s=endRightCandidate s) hM hE hK
  rw [map_zero,map_mul,hT] at hh
  exact (mul_ne_zero hBne
    (mul_ne_zero (MvPolynomial.X_ne_zero s.b) (MvPolynomial.X_ne_zero s.c))) hh.symm

/-- If only the middle top position is active, its endpoint is the lower unit label. -/
theorem mixed_middle_top_only_endpoint (t s : Parameters) (ht : ValidM t)
    (hp : t.p=s.p)
    (hR : mixedContactLabel t s = middleTopCandidate t)
    (hR' : mixedContactLabel t s ≠ endTopCandidate s)
    (hK : mixedContactCoefficient t s=0) : t.a=t.p := by
  have hGne := eraseOne_ne_zero_of_coordinate_not_dvd t.p
    (G t.u t.tau t.b t.p t.c) (M_G_coordinate_not_dvd t ht t.p)
  have hM : eraseOne t.p (MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau)=0 := by
    simp only [map_mul,eraseOne_X,if_pos rfl,ite_true,mul_zero,zero_mul]
  have hE : eraseOne t.p (MvPolynomial.X s.a*MvPolynomial.X s.p*F s.v s.x s.tau)=0 := by
    rw [← hp]
    simp only [map_mul,eraseOne_X,if_pos rfl,ite_true,mul_zero,zero_mul]
  simp only [mixedContactCoefficient,if_pos hR,if_neg hR'] at hK
  have hh:=eraseOne_contact_balance t.p
    (MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c) 0
    (MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau)
    (MvPolynomial.X s.a*MvPolynomial.X s.p*F s.v s.x s.tau)
    (mixedContactLabel t s=middleRightCandidate t)
    (mixedContactLabel t s=endRightCandidate s) hM hE hK
  by_contra ha
  have hkeep : eraseOne t.p (MvPolynomial.X t.a)=MvPolynomial.X t.a := by
    rw [eraseOne_X,if_neg ha]
  rw [map_zero,map_mul,hkeep] at hh
  exact (mul_ne_zero (MvPolynomial.X_ne_zero t.a) hGne) hh

/-- The tied top indices determine the previously free bottom row of the end opening. -/
theorem mixed_tied_top_row (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (htau : t.tau=s.tau)
    (hm : m t=m s) (hR : middleTopCandidate t=endTopCandidate s) :
    s.c+t.v=t.c+t.a := by
  have hty := ht.2.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have htu := ht.1
  have hsu := hs.1
  have htv := ht.2.1
  have hsv := hs.2.1
  have htb := ht.2.2.1
  have hsb := hs.2.2.1
  have htx := ht.2.2.2.1
  have hsx := hs.2.2.2.1
  dsimp [m] at hm
  dsimp [middleTopCandidate, endTopCandidate] at hR
  omega

/-- The four-term divisibility obstruction at a double top contact. -/
theorem mixed_double_top_divisibility (t s : Parameters) (ht : ValidM t)
    (hb : t.b=s.b) (hp : t.p=s.p)
    (hB : B t.u t.v t.tau=B s.u s.v s.tau)
    (hR : mixedContactLabel t s=middleTopCandidate t)
    (hR' : mixedContactLabel t s=endTopCandidate s)
    (hK : mixedContactCoefficient t s=0) :
    (MvPolynomial.X t.p : Gluing.HomLambda) ∣
      MvPolynomial.X t.a * F t.u t.c t.tau -
        MvPolynomial.X s.c * B t.u t.v t.tau := by
  have hbp : t.b ≠ t.p := by have := ht.2.2.1; omega
  simp only [mixedContactCoefficient,if_pos hR,if_pos hR'] at hK
  rw [← hp,← hb,← hB] at hK
  have hM : eraseOne t.p (MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau)=0 := by
    simp only [map_mul,eraseOne_X,if_pos rfl,ite_true,mul_zero,zero_mul]
  have hE : eraseOne t.p (MvPolynomial.X s.a*MvPolynomial.X t.p*F s.v s.x s.tau)=0 := by
    simp only [map_mul,eraseOne_X,if_pos rfl,ite_true,mul_zero,zero_mul]
  have hh:=eraseOne_contact_balance t.p
    (MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c)
    (B t.u t.v t.tau*T t.b t.p s.c)
    (MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau)
    (MvPolynomial.X s.a*MvPolynomial.X t.p*F s.v s.x s.tau)
    (mixedContactLabel t s=middleRightCandidate t)
    (mixedContactLabel t s=endRightCandidate s) hM hE hK
  have hG : eraseOne t.p (G t.u t.tau t.b t.p t.c) =
      MvPolynomial.X t.b*eraseOne t.p (F t.u t.c t.tau) := by
    simp only [G,T,F,map_sub,map_mul,eraseOne_X,if_pos rfl,ite_true,
      if_neg hbp,zero_mul,mul_zero,sub_zero]
    ring
  have hT : eraseOne t.p (T t.b t.p s.c) =
      MvPolynomial.X t.b*eraseOne t.p (MvPolynomial.X s.c) := by
    simp only [T,map_sub,map_mul,eraseOne_X,if_pos rfl,ite_true,
      if_neg hbp,zero_mul,sub_zero]
  have hA : eraseOne t.p (MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c) =
      eraseOne t.p (MvPolynomial.X t.a) *
        (MvPolynomial.X t.b*eraseOne t.p (F t.u t.c t.tau)) := by
    rw [map_mul,hG]
  have hBT : eraseOne t.p (B t.u t.v t.tau*T t.b t.p s.c) =
      eraseOne t.p (B t.u t.v t.tau) *
        (MvPolynomial.X t.b*eraseOne t.p (MvPolynomial.X s.c)) := by
    rw [map_mul,hT]
  rw [hA,hBT] at hh
  have hres : MvPolynomial.X t.b *
      eraseOne t.p (MvPolynomial.X t.a*F t.u t.c t.tau -
        MvPolynomial.X s.c*B t.u t.v t.tau)=0 := by
    rw [map_sub,
      map_mul (eraseOne t.p) (MvPolynomial.X t.a) (F t.u t.c t.tau),
      map_mul (eraseOne t.p) (MvPolynomial.X s.c) (B t.u t.v t.tau)]
    linear_combination hh
  have hz := (mul_eq_zero.mp hres).resolve_left (MvPolynomial.X_ne_zero _)
  exact (eraseOne_eq_zero_iff_coordinate_dvd _ _).mp hz

theorem variable_product_reading (a b c d : ℕ)
    (he : (MvPolynomial.X a : Gluing.HomLambda) * MvPolynomial.X b =
      MvPolynomial.X c * MvPolynomial.X d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hunit (j : ℕ) : ¬ (MvPolynomial.X j : Gluing.HomLambda) ∣ 1 := by
    rintro ⟨q, hq⟩
    have hh := congrArg (MvPolynomial.aeval (fun _ : ℕ => (0 : ℚ))) hq
    simp at hh
  exact (coordinate_pair_reading a b c d 1 1 hunit (by simpa using he)).1

/-- Specializing the tied-top obstruction gives exactly the two possible parameter regimes. -/
theorem double_top_regimes (t : Parameters) (ht : ValidM t) (d : ℕ)
    (hd : t.a+t.p<d)
    (hdiv : (MvPolynomial.X t.p : Gluing.HomLambda) ∣
      MvPolynomial.X t.a * F t.u t.c t.tau -
        MvPolynomial.X d * B t.u t.v t.tau) :
    (t.a=t.v ∧ t.tau=t.p ∧ d=t.c) ∨
      (t.p=t.u ∧ t.a=t.L ∧ d=t.c+t.u-t.tau) := by
  rcases ht with ⟨hu,hv,hb,hx,hy,hc⟩
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hLu : t.u<t.L := by omega
  have hLv : t.v<t.L := by omega
  have hcp : t.c ≠ t.p := by omega
  have hdp : d ≠ t.p := by omega
  have hshift : t.c+t.u-t.tau ≠ t.p := by omega
  have hz := (eraseOne_eq_zero_iff_coordinate_dvd _ _).mpr hdiv
  have hap : t.a ≠ t.p := by
    intro ha
    have hBne := eraseOne_ne_zero_of_coordinate_not_dvd t.p (B t.u t.v t.tau)
      (B_coordinate_not_dvd _ _ _ t.p hu hv)
    simp [ha, hdp, hBne] at hz
  by_cases htau : t.p=t.tau
  · have hup : t.u ≠ t.p := by omega
    have hvp : t.v ≠ t.p := by omega
    have hh := hz
    simp [F, B, ← htau, hap, hcp, hdp, hup, hvp] at hh
    have hm : (MvPolynomial.X t.a : Gluing.HomLambda) * MvPolynomial.X t.c =
        MvPolynomial.X d * MvPolynomial.X t.v := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.u)
      linear_combination hh
    have hr := variable_product_reading _ _ _ _ hm
    rcases hr with hr | hr
    · omega
    · exact Or.inl ⟨hr.1, htau.symm, hr.2.symm⟩
  · by_cases hpu : t.p=t.u
    · have htp : t.tau ≠ t.p := by omega
      have hLp : t.u+t.v-t.tau ≠ t.p := by
        change t.L ≠ t.p
        omega
      have hkillu : eraseOne t.p (MvPolynomial.X t.u)=0 := by
        rw [← hpu,eraseOne_X,if_pos rfl]
      have hkeep (k : ℕ) (hk : k ≠ t.p) :
          eraseOne t.p (MvPolynomial.X k)=MvPolynomial.X k := by
        rw [eraseOne_X,if_neg hk]
      have hh := hz
      simp only [F,B,map_sub,map_mul,hkeep t.a hap,hkeep t.c hcp,hkeep d hdp,
        hkeep t.tau htp,hkeep (t.c+t.u-t.tau) hshift,
        hkeep (t.u+t.v-t.tau) hLp,hkillu,zero_mul,mul_zero,sub_zero,zero_sub] at hh
      change MvPolynomial.X t.a *
          -(MvPolynomial.X t.tau*MvPolynomial.X (t.c+t.u-t.tau)) -
        MvPolynomial.X d * -(MvPolynomial.X t.tau*MvPolynomial.X t.L)=0 at hh
      have hm : (MvPolynomial.X t.a : Gluing.HomLambda) *
          MvPolynomial.X (t.c+t.u-t.tau) =
          MvPolynomial.X d * MvPolynomial.X t.L := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.tau)
        linear_combination -hh
      have hr := variable_product_reading _ _ _ _ hm
      rcases hr with hr | hr
      · omega
      · exact Or.inr ⟨hpu, hr.1, hr.2.symm⟩
    · have htp : t.tau ≠ t.p := Ne.symm htau
      have hup : t.u ≠ t.p := Ne.symm hpu
      let ev : Gluing.HomLambda →ₐ[ℚ] ℚ :=
        MvPolynomial.aeval fun k => if k=t.p then 0 else 1
      have hev : ev (MvPolynomial.X t.a * F t.u t.c t.tau -
          MvPolynomial.X d * B t.u t.v t.tau)=0 := by
        obtain ⟨q, hq⟩ := hdiv
        rw [hq, map_mul]
        simp [ev]
      by_cases hpv : t.p=t.v
      · have hLp : t.u+t.v-t.tau ≠ t.p := by omega
        simp [ev,F,B,← hpv,hap,hcp,hdp,hshift,htp,hup,hLp] at hev <;> omega
      · have hvp : t.v ≠ t.p := Ne.symm hpv
        by_cases hpL : t.p=t.L
        · simp [ev, F, B, show t.u+t.v-t.tau=t.L from rfl, ← hpL,
            hap, hcp, hdp, hshift, htp, hup, hvp] at hev
        · have hLp : t.u+t.v-t.tau ≠ t.p := by
            change t.L ≠ t.p
            exact Ne.symm hpL
          have hh := hz
          simp [F, B, hap, hcp, hdp, hshift, htp, hup, hvp, hLp] at hh
          have hm : MvPolynomial.X t.a * F t.u t.c t.tau =
              MvPolynomial.X d * B t.u t.v t.tau := by
            simp only [F, B]
            linear_combination hh
          have had := (coordinate_single_reading _ _ _ _
            (B_coordinate_not_dvd _ _ _ t.a hu hv) hm).1
          omega

theorem maximal_variable_unique (f g : Gluing.HomLambda) (r s : ℕ)
    (hf : r ∈ f.vars ∧ ∀ k, k ∈ f.vars → k ≤ r)
    (hg : s ∈ g.vars ∧ ∀ k, k ∈ g.vars → k ≤ s)
    (he : f = g) : r = s := by
  have hfr : r∈g.vars := by simpa only [he] using hf.1
  have hgs : s∈f.vars := by simpa only [he] using hg.1
  exact Nat.le_antisymm (hg.2 _ hfr) (hf.2 _ hgs)

/-- Both actual greatest labels and both collected marker coefficients are invariant. -/
theorem mixed_marker_readings (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur=(E s hs).schur) :
    m t=m s ∧ NM t=NE s ∧ secondM t=secondE s := by
  have heh := ((M t ht).homSchur_eq_iff (E s hs)).mpr he
  have hm := maximal_variable_unique _ _ _ _ (M_largest_variable t ht)
    (E_largest_variable s hs) heh
  have heEr : eraseOne (m t) (M t ht).homSchur =
      eraseOne (m s) (E s hs).homSchur := by
    rw [← hm]
    exact congrArg (eraseOne (m t)) heh
  have hn := maximal_variable_unique _ _ _ _ (M_next_variable t ht)
    (E_next_variable s hs) heEr
  have hc := congrArg (MvPolynomial.pderiv (NM t)) heEr
  rw [M_second_coefficient, hn, E_second_coefficient] at hc
  exact ⟨hm, hn, hc⟩

/-- A mixed equality forces the end opening into its strict lower-corner regime. -/
theorem mixed_end_strict (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur=(E s hs).schur) : s.q<deltaE s := by
  have hsecond := (mixed_marker_readings t s ht hs he).2.2
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  have hdvd : B s.u s.v s.tau ∣ secondE s := by
    rw [← hsecond, secondM_factor, hB]
    exact dvd_mul_right _ _
  rcases lt_trichotomy s.q (deltaE s) with hr | hr | hr
  · exact hr
  · have heq : secondE s = -(MvPolynomial.X s.a * endTieParenthesis s) := by
      rw [secondE_tied s hr]
      unfold C14 C25E endTieParenthesis
      ring
    rw [heq, dvd_neg] at hdvd
    rcases (B_irreducible _ _ _ hs.1 hs.2.1).prime.dvd_mul.mp hdvd with h | h
    · exact (B_not_dvd_X _ _ _ _ hs.1 hs.2.1 h).elim
    · exact (endTie_B_not_dvd s hs h).elim
  · rw [secondE_strict_delta s hr, C25E, dvd_neg] at hdvd
    rcases (B_irreducible _ _ _ hs.1 hs.2.1).prime.dvd_mul.mp hdvd with h | h
    · rcases (B_irreducible _ _ _ hs.1 hs.2.1).prime.dvd_mul.mp h with h | h
      · exact (B_not_dvd_X _ _ _ _ hs.1 hs.2.1 h).elim
      · exact (B_not_dvd_X _ _ _ _ hs.1 hs.2.1 h).elim
    · exact (B_not_dvd_F _ _ _ _ hs.1 hs.2.1 hs.2.2.2.1 h).elim

/-- A mixed equality cannot have a tied middle corner. -/
theorem mixed_middle_untied (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur=(E s hs).schur) : t.q ≠ deltaM t := by
  have hsecond := (mixed_marker_readings t s ht hs he).2.2
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  rw [secondM_factor, secondE_strict_q s (mixed_end_strict t s ht hs he), C14] at hsecond
  rw [hB] at hsecond
  have hquot : middleSecondQuotient t =
      -(MvPolynomial.X s.a * MvPolynomial.X s.b) := by
    apply mul_left_cancel₀ (B_irreducible _ _ _ ht.1 ht.2.1).ne_zero
    rw [hB]
    convert hsecond using 1 <;> ring
  have hev := congrArg (MvPolynomial.eval (fun _ : ℕ => (1 : ℚ))) hquot
  rw [middleSecondQuotient_eval_one] at hev
  intro hr
  norm_num [hr] at hev

/-- In the oriented strict regime, shared endpoints are derived from equality. -/
theorem mixed_strict_endpoint_reading (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur) :
    t.a=s.a ∧ t.b=s.b ∧ t.p=s.p ∧ t.tau=s.tau ∧
      ((t.u=s.u ∧ t.v=s.v) ∨ (t.u=s.v ∧ t.v=s.u)) := by
  have hfirst := mixed_first_marker_eq t s ht hs he
  have hsecond := (mixed_marker_readings t s ht hs he).2.2
  rw [secondM_strict_q t hr, secondE_strict_q s (mixed_end_strict t s ht hs he)] at hsecond
  have hsecond' : MvPolynomial.X t.a * MvPolynomial.X t.b * B t.u t.v t.tau =
      MvPolynomial.X s.a * MvPolynomial.X s.b * B s.u s.v s.tau := by
    simpa only [C14, neg_inj] using hsecond
  exact strict_two_marker_reading t s ht.1 ht.2.1 ht.2.2.1
    hs.1 hs.2.1 hs.2.2.1 hfirst hsecond'

/-- The full collected contact equation follows for arbitrary strict-oriented mixed mates. -/
theorem mixed_strict_contact_zero (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur) :
    mixedContactCoefficient t s=0 := by
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  have hm := (mixed_marker_readings t s ht hs he).1
  exact mixed_contact_zero t s ht hs ha hb hp htau hB hm he

/-- The three source contact regimes, with no shared parameters postulated. -/
theorem mixed_strict_contact_regimes (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur) :
    (endTopCandidate s < middleTopCandidate t ∧ t.a=t.p) ∨
    (middleTopCandidate t=endTopCandidate s ∧ t.a=t.v ∧ t.tau=t.p ∧ s.c=t.c) ∨
    (middleTopCandidate t=endTopCandidate s ∧ t.p=t.u ∧ t.a=t.L ∧
      s.c=t.c+t.u-t.tau) := by
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  have hK := mixed_strict_contact_zero t s ht hs hr he
  have hactive := mixed_contact_active t s ht hs ha hp hK
  have hR : mixedContactLabel t s=middleTopCandidate t := by
    rcases hactive.1 with hR | hR'
    · exact hR
    · by_contra hn
      exact mixed_end_top_only_impossible t s hs hp hn hR' hK
  by_cases hR' : mixedContactLabel t s=endTopCandidate s
  · have hdiv := mixed_double_top_divisibility t s ht hb hp hB hR hR' hK
    have hd : t.a+t.p<s.c := by
      have hc := hs.2.2.2.2.2
      omega
    rcases double_top_regimes t ht s.c hd hdiv with h | h
    · exact Or.inr (Or.inl ⟨by omega,h.1,h.2.1,h.2.2⟩)
    · exact Or.inr (Or.inr ⟨by omega,h.1,h.2.1,h.2.2⟩)
  · have hap := mixed_middle_top_only_endpoint t s ht hp hR hR' hK
    have hle : endTopCandidate s ≤ mixedContactLabel t s := by
      unfold mixedContactLabel
      omega
    exact Or.inl ⟨by omega,hap⟩

noncomputable def tripleProduct (v : Fin 3 → ℕ) : Gluing.HomLambda :=
  MvPolynomial.X (v 0) * MvPolynomial.X (v 1) * MvPolynomial.X (v 2)

theorem tripleProduct_vec (a b c : ℕ) :
    tripleProduct ![a,b,c]=MvPolynomial.X a*MvPolynomial.X b*MvPolynomial.X c := rfl

noncomputable def tripleExponent (v : Fin 3 → ℕ) : ℕ →₀ ℕ :=
  Finsupp.single (v 0) 1 + Finsupp.single (v 1) 1 + Finsupp.single (v 2) 1

theorem tripleProduct_monomial (v : Fin 3 → ℕ) :
    tripleProduct v = MvPolynomial.monomial (tripleExponent v) 1 := by
  simp [tripleProduct, tripleExponent, MvPolynomial.X]

/-- Positive monomial sums cannot cancel a source term absent on the other side. -/
theorem positive_three_match (a b c d e f : Fin 3 → ℕ)
    (he : tripleProduct a+tripleProduct b+tripleProduct c =
      tripleProduct d+tripleProduct e+tripleProduct f) :
    tripleProduct a=tripleProduct d ∨ tripleProduct a=tripleProduct e ∨
      tripleProduct a=tripleProduct f := by
  have hc := congrArg (fun f : Gluing.HomLambda => f.coeff (tripleExponent a)) he
  simp only [MvPolynomial.coeff_add, tripleProduct_monomial,
    MvPolynomial.coeff_monomial] at hc
  have hx : tripleExponent a=tripleExponent d ∨
      tripleExponent a=tripleExponent e ∨ tripleExponent a=tripleExponent f := by
    by_contra hn
    have hd : tripleExponent d ≠ tripleExponent a := fun h => hn (Or.inl h.symm)
    have he : tripleExponent e ≠ tripleExponent a := fun h => hn (Or.inr (Or.inl h.symm))
    have hf : tripleExponent f ≠ tripleExponent a := fun h => hn (Or.inr (Or.inr h.symm))
    simp only [if_pos rfl, if_neg hd, if_neg he, if_neg hf] at hc
    split_ifs at hc <;> norm_num at hc
  rcases hx with h | h | h
  · exact Or.inl (by rw [tripleProduct_monomial, tripleProduct_monomial, h])
  · exact Or.inr (Or.inl (by rw [tripleProduct_monomial, tripleProduct_monomial, h]))
  · exact Or.inr (Or.inr (by rw [tripleProduct_monomial, tripleProduct_monomial, h]))

theorem positive_two_match (a b c d : Fin 3 → ℕ)
    (he : tripleProduct a+tripleProduct b=tripleProduct c+tripleProduct d) :
    tripleProduct a=tripleProduct c ∨ tripleProduct a=tripleProduct d := by
  have hc := congrArg (fun f : Gluing.HomLambda => f.coeff (tripleExponent a)) he
  simp only [MvPolynomial.coeff_add, tripleProduct_monomial,
    MvPolynomial.coeff_monomial] at hc
  have hx : tripleExponent a=tripleExponent c ∨ tripleExponent a=tripleExponent d := by
    by_contra hn
    have h1 : tripleExponent c ≠ tripleExponent a := fun h => hn (Or.inl h.symm)
    have h2 : tripleExponent d ≠ tripleExponent a := fun h => hn (Or.inr h.symm)
    simp only [if_pos rfl, if_neg h1, if_neg h2] at hc
    split_ifs at hc <;> norm_num at hc
  rcases hx with h | h
  · exact Or.inl (by rw [tripleProduct_monomial, tripleProduct_monomial, h])
  · exact Or.inr (by rw [tripleProduct_monomial, tripleProduct_monomial, h])

/-- Positive-monomial comparison closes Regime I without omitting the small-core case. -/
theorem regimeI_six_term (u v tau b p c x : ℕ)
    (hu : tau<u) (hv : tau<v) (hb : p<b) (hc : v+p<c)
    (hx : x=c+b-v)
    (he : (MvPolynomial.X b : Gluing.HomLambda)*MvPolynomial.X u*MvPolynomial.X c -
      MvPolynomial.X b*MvPolynomial.X tau*MvPolynomial.X (c+u-tau) -
      MvPolynomial.X x*MvPolynomial.X u*MvPolynomial.X v +
      MvPolynomial.X x*MvPolynomial.X tau*MvPolynomial.X (u+v-tau) +
      MvPolynomial.X p*MvPolynomial.X v*MvPolynomial.X (x+u-p) -
      MvPolynomial.X p*MvPolynomial.X u*MvPolynomial.X (x+v-p)=0) :
    b=v ∧ tau=p ∧ c=u ∧ x=u := by
  have hxb : b<x := by omega
  have hcp : p<c := by omega
  have hct : tau<c := by omega
  have hsum :
      tripleProduct ![b,u,c]+tripleProduct ![x,tau,u+v-tau]+
        tripleProduct ![p,v,x+u-p] =
      tripleProduct ![b,tau,c+u-tau]+tripleProduct ![x,u,v]+
        tripleProduct ![p,u,x+v-p] := by
    simp only [tripleProduct_vec]
    linear_combination he
  have hmatch := positive_three_match _ _ _ _ _ _ hsum
  have hbx : b=v ∧ x=c := by
    rcases hmatch with hm | hm | hm
    · have hm' : (MvPolynomial.X u : Gluing.HomLambda)*MvPolynomial.X c =
          MvPolynomial.X tau*MvPolynomial.X (c+u-tau) := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero b)
        simpa only [tripleProduct_vec,mul_assoc] using hm
      have hh := variable_product_reading _ _ _ _ hm'
      rcases hh with hh | hh <;> omega
    · have hm' : (MvPolynomial.X b : Gluing.HomLambda)*MvPolynomial.X c =
          MvPolynomial.X x*MvPolynomial.X v := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero u)
        simp only [tripleProduct_vec] at hm
        convert hm using 1 <;> ring
      have hh := variable_product_reading _ _ _ _ hm'
      rcases hh with hh | hh
      · omega
      · exact ⟨hh.1,hh.2.symm⟩
    · have hm' : (MvPolynomial.X b : Gluing.HomLambda)*MvPolynomial.X c =
          MvPolynomial.X p*MvPolynomial.X (x+v-p) := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero u)
        simp only [tripleProduct_vec] at hm
        convert hm using 1 <;> ring
      have hh := variable_product_reading _ _ _ _ hm'
      rcases hh with hh | hh <;> omega
  obtain ⟨hbv,hxc⟩ := hbx
  have hLv : v<u+v-tau := by omega
  have hsum2 :
      tripleProduct ![c,tau,u+v-tau]+tripleProduct ![p,v,c+u-p] =
      tripleProduct ![v,tau,c+u-tau]+tripleProduct ![p,u,c+v-p] := by
    simp only [tripleProduct_vec]
    rw [hbv,hxc] at he
    linear_combination he
  have hmatch2 := positive_two_match _ _ _ _ hsum2
  have hrest : tau=p ∧ c=u := by
    rcases hmatch2 with hm | hm
    · have hm' : (MvPolynomial.X c : Gluing.HomLambda)*MvPolynomial.X (u+v-tau) =
          MvPolynomial.X v*MvPolynomial.X (c+u-tau) := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero tau)
        simp only [tripleProduct_vec] at hm
        convert hm using 1 <;> ring
      have hh := variable_product_reading _ _ _ _ hm'
      rcases hh with hh | hh <;> omega
    · simp only [tripleProduct_vec] at hm
      have hpdiv : (MvPolynomial.X p : Gluing.HomLambda) ∣
          MvPolynomial.X c*MvPolynomial.X tau*MvPolynomial.X (u+v-tau) := by
        rw [hm]
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      simp only [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X] at hpdiv
      have htp : tau=p := by omega
      have hm' : (MvPolynomial.X c : Gluing.HomLambda)*MvPolynomial.X (u+v-tau) =
          MvPolynomial.X u*MvPolynomial.X (c+v-p) := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero p)
        rw [htp] at hm ⊢
        convert hm using 1 <;> ring
      have hh := variable_product_reading _ _ _ _ hm'
      rcases hh with hh | hh
      · exact ⟨htp,hh.1⟩
      · omega
  exact ⟨hbv,hrest.1,hrest.2,hxc.trans hrest.2⟩

/-- The Regime II contact polynomial forces its exceptional bottom and middle rows. -/
theorem regimeII_four_term (u v p b c xi : ℕ)
    (hu : p<u) (hv : p<v) (hb : p<b) (hc : v+p<c)
    (hxi : xi=c+b-p+u-v)
    (he : (MvPolynomial.X b : Gluing.HomLambda) *
      (MvPolynomial.X (u+v-p)*MvPolynomial.X c -
        MvPolynomial.X v*MvPolynomial.X (c+u-p)) +
      MvPolynomial.X v *
      (MvPolynomial.X v*MvPolynomial.X xi -
        MvPolynomial.X u*MvPolynomial.X (c+b-p))=0) :
    b=v ∧ c=u := by
  have hLv : v<u+v-p := by omega
  have hcv : v<c := by omega
  have hsum :
      tripleProduct ![b,u+v-p,c]+tripleProduct ![v,v,xi] =
      tripleProduct ![b,v,c+u-p]+tripleProduct ![v,u,c+b-p] := by
    simp only [tripleProduct_vec]
    linear_combination he
  have hmatch := positive_two_match _ _ _ _ hsum
  have hbv : b=v := by
    rcases hmatch with hm | hm
    · have hm' : (MvPolynomial.X (u+v-p) : Gluing.HomLambda)*MvPolynomial.X c =
          MvPolynomial.X v*MvPolynomial.X (c+u-p) := by
        apply mul_left_cancel₀ (MvPolynomial.X_ne_zero b)
        simpa only [tripleProduct_vec,mul_assoc] using hm
      have hh := variable_product_reading _ _ _ _ hm'
      rcases hh with hh | hh <;> omega
    · have hd : (MvPolynomial.X v : Gluing.HomLambda) ∣
          MvPolynomial.X b*MvPolynomial.X (u+v-p)*MvPolynomial.X c := by
        rw [show MvPolynomial.X b*MvPolynomial.X (u+v-p)*MvPolynomial.X c =
          MvPolynomial.X v*MvPolynomial.X u*MvPolynomial.X (c+b-p) from by
            simpa only [tripleProduct_vec] using hm]
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      simp only [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X] at hd
      omega
  have hxi' : xi=c+u-p := by omega
  have hm : (MvPolynomial.X (u+v-p) : Gluing.HomLambda)*MvPolynomial.X c =
      MvPolynomial.X u*MvPolynomial.X (c+v-p) := by
    apply mul_left_cancel₀ (MvPolynomial.X_ne_zero v)
    rw [hbv,hxi'] at he
    linear_combination he
  have hr := variable_product_reading _ _ _ _ hm
  rcases hr with hr | hr
  · omega
  · exact ⟨hbv,hr.2⟩

/-- The Regime III residual is impossible throughout its full source domain. -/
theorem regimeIII_residual_ne_zero (u v tau c : ℕ)
    (hu : tau<u) (hv : u<v) (hc : u+v<c) :
    2 * MvPolynomial.X (u+v-tau) * MvPolynomial.X v * MvPolynomial.X c -
      MvPolynomial.X (u+v-tau) * MvPolynomial.X u *
        MvPolynomial.X (c+v-u) -
      MvPolynomial.X v * MvPolynomial.X v * MvPolynomial.X (c+u-tau) ≠
        (0 : Gluing.HomLambda) := by
  intro he
  have hLv : v<u+v-tau := by omega
  have hsum :
      tripleProduct ![u+v-tau,v,c]+tripleProduct ![u+v-tau,v,c] =
      tripleProduct ![u+v-tau,u,c+v-u]+tripleProduct ![v,v,c+u-tau] := by
    simp only [tripleProduct_vec]
    linear_combination he
  have hm := positive_two_match _ _ _ _ hsum
  rcases hm with hm | hm
  · have hh : (MvPolynomial.X v : Gluing.HomLambda)*MvPolynomial.X c =
        MvPolynomial.X u*MvPolynomial.X (c+v-u) := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (u+v-tau))
      simpa only [tripleProduct_vec,mul_assoc] using hm
    have hr := variable_product_reading _ _ _ _ hh
    rcases hr with hr | hr <;> omega
  · have hh : (MvPolynomial.X (u+v-tau) : Gluing.HomLambda)*MvPolynomial.X c =
        MvPolynomial.X v*MvPolynomial.X (c+u-tau) := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero v)
      simp only [tripleProduct_vec] at hm
      convert hm using 1 <;> ring
    have hr := variable_product_reading _ _ _ _ hh
    rcases hr with hr | hr <;> omega

noncomputable def regimeIContact (t s : Parameters) : Gluing.HomLambda :=
  G t.u t.tau t.b t.p t.c -
    (if mixedContactLabel t s=middleRightCandidate t then
      MvPolynomial.X t.x * B t.u t.v t.tau else 0) +
    (if mixedContactLabel t s=endRightCandidate s then
      MvPolynomial.X t.p * F s.v s.x s.tau else 0)

theorem regimeI_contact_zero (t s : Parameters)
    (ha : t.a=s.a) (hp : t.p=s.p) (hap : t.a=t.p)
    (hB : B t.u t.v t.tau=B s.u s.v s.tau)
    (hR : mixedContactLabel t s=middleTopCandidate t)
    (hR' : mixedContactLabel t s ≠ endTopCandidate s)
    (hK : mixedContactCoefficient t s=0) : regimeIContact t s=0 := by
  simp only [mixedContactCoefficient,if_pos hR,if_neg hR'] at hK
  simp only [← ha,← hp,← hB,hap] at hK
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.p)
  simp only [regimeIContact,mul_zero]
  split_ifs at hK ⊢ <;> linear_combination hK

theorem regimeI_both_right_active (t s : Parameters) (ht : ValidM t)
    (hzero : regimeIContact t s=0) :
    mixedContactLabel t s=middleRightCandidate t ∧
      mixedContactLabel t s=endRightCandidate s := by
  have hZ : mixedContactLabel t s=middleRightCandidate t := by
    by_contra hn
    simp only [regimeIContact,if_neg hn] at hzero
    have hh := congrArg (eraseOne t.p) hzero
    have hne := eraseOne_ne_zero_of_coordinate_not_dvd t.p
      (G t.u t.tau t.b t.p t.c) (M_G_coordinate_not_dvd t ht t.p)
    simp [apply_ite,hne] at hh
  refine ⟨hZ,?_⟩
  by_contra hn
  have hh : G t.u t.tau t.b t.p t.c = MvPolynomial.X t.x * B t.u t.v t.tau := by
    simpa only [regimeIContact,if_pos hZ,if_neg hn,add_zero,sub_eq_zero] using hzero
  apply M_G_coordinate_not_dvd t ht t.x
  exact ⟨B t.u t.v t.tau,hh⟩

/-- Regime I forces the second exceptional normal-form pair, uniformly in every parameter. -/
theorem mixed_regimeI_core (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur)
    (hap : t.a=t.p) (hgt : endTopCandidate s < middleTopCandidate t) :
    t.b=t.v ∧ t.tau=t.p ∧ t.c=t.u ∧ t.x=t.u ∧
      s.u=t.u ∧ s.v=t.v ∧ s.x=2*t.u-t.p := by
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  have hm := (mixed_marker_readings t s ht hs he).1
  have hK := mixed_strict_contact_zero t s ht hs hr he
  have hactive := mixed_contact_active t s ht hs ha hp hK
  have hle : middleTopCandidate t ≤ mixedContactLabel t s := by
    unfold mixedContactLabel
    omega
  have hR' : mixedContactLabel t s ≠ endTopCandidate s := by omega
  have hR : mixedContactLabel t s=middleTopCandidate t := by tauto
  have hzero := regimeI_contact_zero t s ha hp hap hB hR hR' hK
  obtain ⟨hZ,hZ'⟩ := regimeI_both_right_active t s ht hzero
  have htu := ht.1
  have htv := ht.2.1
  have htb := ht.2.2.1
  have htx := ht.2.2.2.1
  have hty := ht.2.2.2.2.1
  have htc := ht.2.2.2.2.2
  have hsu := hs.1
  have hsv := hs.2.1
  have hsb := hs.2.2.1
  have hsx := hs.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have hsc := hs.2.2.2.2.2
  have hcontact : middleTopCandidate t=middleRightCandidate t := hR.symm.trans hZ
  have hright : middleRightCandidate t=endRightCandidate s := hZ.symm.trans hZ'
  have hx : t.x=t.c+t.b-t.v := by
    dsimp [middleTopCandidate,middleRightCandidate] at hcontact
    omega
  have hxi : s.x=t.x+s.u-t.p := by
    dsimp [m] at hm
    dsimp [middleRightCandidate,endRightCandidate] at hright
    omega
  have hshift : t.c+t.u-t.tau+(t.b-t.p)=s.x+s.v-s.tau := by
    rcases hcore with hcore | hcore <;> omega
  have hres : MvPolynomial.X t.b * F t.u t.c t.tau -
      MvPolynomial.X t.x * B t.u t.v t.tau +
      MvPolynomial.X t.p *
        (MvPolynomial.X s.v * MvPolynomial.X s.x -
          MvPolynomial.X t.u * MvPolynomial.X (t.c+t.q))=0 := by
    simp only [regimeIContact,if_pos hZ,if_pos hZ'] at hzero
    simp only [G,T,F] at hzero ⊢
    rw [hshift] at hzero
    rw [← htau] at hzero
    change _ = 0 at hzero
    dsimp [Parameters.q]
    linear_combination hzero
  have haligned : s.u=t.u ∧ s.v=t.v := by
    rcases hcore with hcore | hcore
    · exact ⟨hcore.1.symm,hcore.2.symm⟩
    · have hxi' : s.x=t.c+t.q := by dsimp [Parameters.q]; omega
      have hh : MvPolynomial.X t.b * F t.u t.c t.tau =
          MvPolynomial.X t.x * B t.u t.v t.tau := by
        rw [← hcore.1,hxi'] at hres
        linear_combination hres
      have hbx := (coordinate_single_reading _ _ _ _
        (B_coordinate_not_dvd _ _ _ t.b htu htv) hh).1
      omega
  have hxi' : s.x=t.x+t.u-t.p := by omega
  have hsix :
      MvPolynomial.X t.b*MvPolynomial.X t.u*MvPolynomial.X t.c -
      MvPolynomial.X t.b*MvPolynomial.X t.tau*MvPolynomial.X (t.c+t.u-t.tau) -
      MvPolynomial.X t.x*MvPolynomial.X t.u*MvPolynomial.X t.v +
      MvPolynomial.X t.x*MvPolynomial.X t.tau*MvPolynomial.X (t.u+t.v-t.tau) +
      MvPolynomial.X t.p*MvPolynomial.X t.v*MvPolynomial.X (t.x+t.u-t.p) -
      MvPolynomial.X t.p*MvPolynomial.X t.u*MvPolynomial.X (t.x+t.v-t.p)=
        (0 : Gluing.HomLambda) := by
    have hw : t.c+t.q=t.x+t.v-t.p := by dsimp [Parameters.q]; omega
    rw [haligned.2,hxi',hw] at hres
    unfold F B at hres
    linear_combination hres
  obtain ⟨hbv,htp,hcu,hxu⟩ :=
    regimeI_six_term _ _ _ _ _ _ _ htu htv htb htc hx hsix
  exact ⟨hbv,htp,hcu,hxu,haligned.1,haligned.2,by omega⟩

theorem profile_five_rows (P : Gluing.Profile 4) :
    P.rowMultiset = {P.r 0,P.r 1,P.r 2,P.r 3,P.r 4} := by
  have hv : (Finset.univ : Finset (Fin 5)).val = {0,1,2,3,4} := by decide
  rw [Gluing.Profile.rowMultiset,hv]
  simp

theorem multiset_cancel_middle (a b c d e : ℕ)
    (h : ({a,c,b} : Multiset ℕ)={d,e,c}) : ({a,b} : Multiset ℕ)={d,e} := by
  have hleft : ({c,a,b} : Multiset ℕ)={a,c,b} := Multiset.cons_swap c a {b}
  have hright : ({d,e,c} : Multiset ℕ)={c,d,e} :=
    (congrArg (Multiset.cons d) (Multiset.cons_swap e c 0)).trans
      (Multiset.cons_swap d c {e})
  exact (Multiset.cons_inj_right c).mp (hleft.trans (h.trans hright))

theorem multiset_cancel_last (a b c d e : ℕ)
    (h : ({a,b,c} : Multiset ℕ)={d,e,c}) : ({a,b} : Multiset ℕ)={d,e} := by
  have hleft : ({a,c,b} : Multiset ℕ)={a,b,c} :=
    congrArg (Multiset.cons a) (Multiset.cons_swap c b 0)
  exact multiset_cancel_middle a b c d e (hleft.trans h)

/-- The free three-row candidates are recovered after canceling the read core row and endpoint. -/
theorem mixed_free_rows (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hL : t.L=s.L) (hb : t.b=s.b)
    (he : (M t ht).schur=(E s hs).schur) :
    ({t.x,t.y,t.c} : Multiset ℕ) = {s.x,s.y,s.c} := by
  have hh := (mixed_readings t s ht hs he).1
  rw [profile_five_rows,profile_five_rows] at hh
  change ({t.x}+({t.y}+({t.L}+({t.c}+{t.b}))) : Multiset ℕ) =
    {s.x}+({s.L}+({s.y}+({s.c}+{s.b}))) at hh
  have hh' : (({t.x}+({t.y}+{t.c}))+({t.L}+{t.b}) : Multiset ℕ) =
      ({s.x}+({s.y}+{s.c}))+({s.L}+{s.b}) := by
    convert hh using 1 <;> ac_rfl
  rw [hL,hb] at hh'
  exact add_right_cancel hh'

/-- The complete `eq:cross-output` parameter list in Regime I. -/
theorem mixed_regimeI_output (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur)
    (hap : t.a=t.p) (hgt : endTopCandidate s < middleTopCandidate t) :
    t.tau=t.p ∧ t.b=t.v ∧ t.c=t.u ∧ t.y=2*t.u-t.p ∧ t.v+t.p<t.u ∧
      s.x=t.y ∧ s.y=t.x ∧ s.c=t.c ∧ s.u=t.u ∧ s.v=t.v ∧ t.x=t.u := by
  obtain ⟨hbv,htp,hcu,hxu,hsu,hsv,hsx⟩ := mixed_regimeI_core t s ht hs hr he hap hgt
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hL : t.L=s.L := by simp [Parameters.L,hsu,hsv,← htau]
  have hfree := mixed_free_rows t s ht hs hL hb he
  have hu := ht.1
  have hc := ht.2.2.2.2.2
  have hmem : s.x∈({t.x,t.y,t.c} : Multiset ℕ) := by rw [hfree]; simp
  have hy : t.y=s.x := by
    have hmem' : s.x=t.x ∨ s.x=t.y ∨ s.x=t.c := by simpa using hmem
    omega
  have hpair : ({t.u,t.u} : Multiset ℕ)={s.y,s.c} := by
    rw [hxu,hcu,hy] at hfree
    have hr : ({s.x,s.y,s.c} : Multiset ℕ)={s.y,s.c,s.x} :=
      (Multiset.cons_swap s.x s.y {s.c}).trans
        (congrArg (Multiset.cons s.y) (Multiset.cons_swap s.x s.c 0))
    exact multiset_cancel_middle t.u t.u s.x s.y s.c (hfree.trans hr)
  have hsy : s.y=t.u := by
    have hh : s.y∈({t.u,t.u} : Multiset ℕ) := by rw [hpair]; simp
    simpa using hh
  have hsc : s.c=t.u := by
    have hh : s.c∈({t.u,t.u} : Multiset ℕ) := by rw [hpair]; simp
    simpa using hh
  exact ⟨htp,hbv,hcu,by omega,by omega,hy.symm,by omega,by omega,hsu,hsv,hxu⟩

/-- Half-turn on the middle-opening parameter word. -/
def rotateMiddle (t : Parameters) : Parameters where
  x := t.b
  y := t.c
  c := t.y
  b := t.x
  a := t.p
  u := t.v
  v := t.u
  p := t.a
  tau := t.tau

theorem rotateMiddle_valid (t : Parameters) (ht : ValidM t) : ValidM (rotateMiddle t) := by
  rcases ht with ⟨hu,hv,hb,hx,hy,hc⟩
  exact ⟨hv,hu,hx,hb,by simpa [rotateMiddle,Nat.add_comm] using hc,
    by simpa [rotateMiddle,Nat.add_comm] using hy⟩

theorem rotateMiddle_schur (t : Parameters) (ht : ValidM t) :
    (M (rotateMiddle t) (rotateMiddle_valid t ht)).schur=(M t ht).schur := by
  have hp : mProfile (rotateMiddle t) (rotateMiddle_valid t ht) =
      (mProfile t ht).rotate := by
    apply Gluing.Profile.ext
    · funext i
      fin_cases i <;> simp [mProfile,rotateMiddle,Gluing.Profile.rotate,
        Parameters.L,Fin.rev,Nat.add_comm]
    · funext i
      fin_cases i <;> simp [mProfile,rotateMiddle,Gluing.Profile.rotate,Fin.rev]
  have hh := congrArg Gluing.Profile.schur hp
  rw [Gluing.Profile.schur_rotate] at hh
  simpa only [M,Gluing.Profile.toBetaDiagram_schur] using hh

/-- Every mixed equality has a strict orientation; a tied middle corner was excluded algebraically. -/
theorem mixed_strict_orientation (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur=(E s hs).schur) :
    ∃ t', ∃ ht' : ValidM t', (t'=t ∨ t'=rotateMiddle t) ∧
      t'.q<deltaM t' ∧ (M t' ht').schur=(E s hs).schur := by
  by_cases hr : t.q<deltaM t
  · exact ⟨t,ht,Or.inl rfl,hr,he⟩
  · have hne := mixed_middle_untied t s ht hs he
    refine ⟨rotateMiddle t,rotateMiddle_valid t ht,Or.inr rfl,?_,?_⟩
    · change t.x-t.a<t.b-t.p
      dsimp [Parameters.q,deltaM] at hr hne
      omega
    · exact (rotateMiddle_schur t ht).trans he

theorem regimeII_missing_end_contact (u v p b c : ℕ)
    (hu : p<u) (hv : p<v) (hb : p<b) (hc : v+p<c) :
    MvPolynomial.X (u+v-p) * T b p c -
      MvPolynomial.X v * T b p (c+u-p) -
      MvPolynomial.X (c+b-p) * B u v p ≠ (0 : Gluing.HomLambda) := by
  intro he
  have hw : c+(b-p)=c+b-p := by omega
  have hsum :
      tripleProduct ![p,v,c+u-p+(b-p)]+tripleProduct ![b,u+v-p,c] =
      tripleProduct ![b,v,c+u-p]+tripleProduct ![c+b-p,u,v] := by
    simp only [tripleProduct_vec]
    unfold T B at he
    rw [hw] at he
    linear_combination he
  have hm := positive_two_match _ _ _ _ hsum
  rcases hm with hm | hm
  · have hh : (MvPolynomial.X p : Gluing.HomLambda) *
        MvPolynomial.X (c+u-p+(b-p)) =
        MvPolynomial.X b * MvPolynomial.X (c+u-p) := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero v)
      simp only [tripleProduct_vec] at hm
      convert hm using 1 <;> ring
    have hr := variable_product_reading _ _ _ _ hh
    rcases hr with hr | hr <;> omega
  · have hh : (MvPolynomial.X p : Gluing.HomLambda) *
        MvPolynomial.X (c+u-p+(b-p)) =
        MvPolynomial.X (c+b-p) * MvPolynomial.X u := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero v)
      simp only [tripleProduct_vec] at hm
      convert hm using 1 <;> ring
    have hr := variable_product_reading _ _ _ _ hh
    rcases hr with hr | hr <;> omega

noncomputable def regimeIIContact (t s : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.L * T t.b t.p t.c -
    MvPolynomial.X t.v * T t.b t.p (t.c+t.u-t.p) -
    (if mixedContactLabel t s=middleRightCandidate t then
      MvPolynomial.X t.x * B t.u t.v t.tau else 0) +
    (if mixedContactLabel t s=endRightCandidate s then
      MvPolynomial.X t.v * F s.v s.x s.tau else 0)

theorem regimeII_contact_zero (t s : Parameters)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (hav : t.a=t.v) (htp : t.tau=t.p) (hd : s.c=t.c)
    (hB : B t.u t.v t.tau=B s.u s.v s.tau)
    (hR : mixedContactLabel t s=middleTopCandidate t)
    (hR' : mixedContactLabel t s=endTopCandidate s)
    (hK : mixedContactCoefficient t s=0) : regimeIIContact t s=0 := by
  simp only [mixedContactCoefficient,if_pos hR,if_pos hR'] at hK
  simp only [← ha,← hp,← hb,← hB,hd,hav] at hK
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.p)
  simp only [regimeIIContact,mul_zero]
  simp only [G,B,Parameters.L,htp] at hK ⊢
  split_ifs at hK ⊢ <;> linear_combination hK

theorem regimeII_middle_right_active (t s : Parameters) (ht : ValidM t)
    (htp : t.tau=t.p) (hzero : regimeIIContact t s=0) :
    mixedContactLabel t s=middleRightCandidate t := by
  by_contra hn
  have hvL : t.L ≠ t.v := by
    have hu := ht.1
    dsimp [Parameters.L]
    omega
  have hT := eraseOne_ne_zero_of_coordinate_not_dvd t.v (T t.b t.p t.c)
    (T_coordinate_not_dvd _ _ _ t.v ht.2.2.1 (by
      have hc := ht.2.2.2.2.2
      omega))
  simp only [regimeIIContact,if_neg hn] at hzero
  have hh := congrArg (eraseOne t.v) hzero
  simp [apply_ite,hvL,hT] at hh

/-- Regime II forces the first exceptional normal-form pair. -/
theorem mixed_regimeII_core (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur)
    (hav : t.a=t.v) (htp : t.tau=t.p) (hd : s.c=t.c)
    (hcontact : middleTopCandidate t=endTopCandidate s) :
    t.b=t.v ∧ t.c=t.u ∧ t.x=t.u+t.v-t.p ∧
      s.u=t.u ∧ s.v=t.v ∧ s.x=2*t.u-t.p := by
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  have hm := (mixed_marker_readings t s ht hs he).1
  have hK := mixed_strict_contact_zero t s ht hs hr he
  have hactive := mixed_contact_active t s ht hs ha hp hK
  have hR : mixedContactLabel t s=middleTopCandidate t := by
    rcases hactive.1 with h | h <;> omega
  have hR' : mixedContactLabel t s=endTopCandidate s := by omega
  have hzero := regimeII_contact_zero t s ha hb hp hav htp hd hB hR hR' hK
  have hZ := regimeII_middle_right_active t s ht htp hzero
  have htu := ht.1
  have htv := ht.2.1
  have htb := ht.2.2.1
  have htx := ht.2.2.2.1
  have hty := ht.2.2.2.2.1
  have htc := ht.2.2.2.2.2
  have hsu := hs.1
  have hsv := hs.2.1
  have hsb := hs.2.2.1
  have hsx := hs.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have hsc := hs.2.2.2.2.2
  have htopright : middleTopCandidate t=middleRightCandidate t := by omega
  have hx : t.x=t.c+t.b-t.p := by
    dsimp [middleTopCandidate,middleRightCandidate] at htopright
    omega
  have hL : t.L=t.u+t.v-t.p := by simp [Parameters.L,htp]
  have hZ' : mixedContactLabel t s=endRightCandidate s := by
    by_contra hn
    have hh : MvPolynomial.X t.L * T t.b t.p t.c -
        MvPolynomial.X t.v * T t.b t.p (t.c+t.u-t.p) -
        MvPolynomial.X t.x * B t.u t.v t.tau=0 := by
      simpa only [regimeIIContact,if_pos hZ,if_neg hn,add_zero] using hzero
    rw [hL,hx,htp] at hh
    exact regimeII_missing_end_contact _ _ _ _ _ (by omega) (by omega) htb htc hh
  have hright : middleRightCandidate t=endRightCandidate s := by omega
  have hxi : s.x=t.c+t.b-t.p+s.u-t.v := by
    dsimp [m] at hm
    dsimp [middleRightCandidate,endRightCandidate] at hright
    omega
  have hshift : t.c+t.u-t.p+(t.b-t.p)=s.x+s.v-s.tau := by
    rcases hcore with hcore | hcore <;> omega
  have hres : (MvPolynomial.X t.b : Gluing.HomLambda) *
      (MvPolynomial.X t.L * MvPolynomial.X t.c -
        MvPolynomial.X t.v * MvPolynomial.X (t.c+t.u-t.p)) +
      MvPolynomial.X t.v *
      (MvPolynomial.X s.v * MvPolynomial.X s.x -
        MvPolynomial.X t.u * MvPolynomial.X (t.c+t.q))=0 := by
    simp only [regimeIIContact,if_pos hZ,if_pos hZ'] at hzero
    unfold T F B at hzero
    rw [hshift,← htau,htp,hx] at hzero
    have hw : t.c+(t.b-t.p)=t.c+t.b-t.p := by omega
    rw [hw,hL] at hzero
    dsimp [Parameters.q]
    rw [hL,hw]
    linear_combination hzero
  have haligned : s.u=t.u ∧ s.v=t.v := by
    rcases hcore with hcore | hcore
    · exact ⟨hcore.1.symm,hcore.2.symm⟩
    · have hxi' : s.x=t.c+t.q := by dsimp [Parameters.q]; omega
      rw [← hcore.1,hxi'] at hres
      have hz : (MvPolynomial.X t.L : Gluing.HomLambda) * MvPolynomial.X t.c =
          MvPolynomial.X t.v * MvPolynomial.X (t.c+t.u-t.p) := by
        have hh : (MvPolynomial.X t.b : Gluing.HomLambda) *
            (MvPolynomial.X t.L * MvPolynomial.X t.c -
              MvPolynomial.X t.v * MvPolynomial.X (t.c+t.u-t.p))=0 := by
          simpa using hres
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (MvPolynomial.X_ne_zero _))
      have hpair := variable_product_reading _ _ _ _ hz
      dsimp [Parameters.L] at hpair
      rcases hpair with hpair | hpair <;> omega
  have hxi' : s.x=t.c+t.b-t.p+t.u-t.v := by omega
  have hres' :
      (MvPolynomial.X t.b : Gluing.HomLambda) *
      (MvPolynomial.X (t.u+t.v-t.p) * MvPolynomial.X t.c -
        MvPolynomial.X t.v * MvPolynomial.X (t.c+t.u-t.p)) +
      MvPolynomial.X t.v *
      (MvPolynomial.X t.v * MvPolynomial.X s.x -
        MvPolynomial.X t.u * MvPolynomial.X (t.c+t.b-t.p))=0 := by
    have hw : t.c+t.q=t.c+t.b-t.p := by dsimp [Parameters.q]; omega
    simpa only [hL,haligned.2,hw] using hres
  obtain ⟨hbv,hcu⟩ := regimeII_four_term _ _ _ _ _ _
    (by omega) (by omega) htb htc hxi' hres'
  exact ⟨hbv,hcu,by omega,haligned.1,haligned.2,by omega⟩

/-- The complete `eq:cross-output` parameter list in Regime II. -/
theorem mixed_regimeII_output (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur)
    (hav : t.a=t.v) (htp : t.tau=t.p) (hd : s.c=t.c)
    (hcontact : middleTopCandidate t=endTopCandidate s) :
    t.tau=t.p ∧ t.b=t.v ∧ t.c=t.u ∧ t.y=2*t.u-t.p ∧ t.v+t.p<t.u ∧
      s.x=t.y ∧ s.y=t.x ∧ s.c=t.c ∧ s.u=t.u ∧ s.v=t.v ∧
      t.a=t.v ∧ t.x=t.u+t.v-t.p := by
  obtain ⟨hbv,hcu,hx,hsu,hsv,hsx⟩ :=
    mixed_regimeII_core t s ht hs hr he hav htp hd hcontact
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hL : t.L=s.L := by simp [Parameters.L,hsu,hsv,← htau]
  have hfree := mixed_free_rows t s ht hs hL hb he
  have hu := ht.1
  have hc := ht.2.2.2.2.2
  have hmem : s.x∈({t.x,t.y,t.c} : Multiset ℕ) := by rw [hfree]; simp
  have hy : t.y=s.x := by
    have hmem' : s.x=t.x ∨ s.x=t.y ∨ s.x=t.c := by simpa using hmem
    omega
  have hsum : t.x+(t.y+t.c)=s.x+(s.y+s.c) := by
    simpa only [Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton,Nat.add_zero]
      using congrArg Multiset.sum hfree
  exact ⟨htp,hbv,hcu,by omega,by omega,hy.symm,by omega,hd,hsu,hsv,hav,hx⟩

theorem regimeIII_missing_end_contact (u v tau b c : ℕ)
    (hu : tau<u) (hv : tau<v) (hb : u<b) (hc : u+v<c) :
    MvPolynomial.X (u+v-tau) * T b u c -
      MvPolynomial.X v * T b u (c+u-tau) -
      MvPolynomial.X (c+b-tau) * B u v tau ≠ (0 : Gluing.HomLambda) := by
  intro he
  have hshift : c+u-tau+(b-u)=c+b-tau := by omega
  have hsum :
      tripleProduct ![c+b-tau,tau,u+v-tau]+tripleProduct ![u+v-tau,b,c] =
      tripleProduct ![u+v-tau,u,c+(b-u)]+tripleProduct ![v,b,c+u-tau] := by
    simp only [tripleProduct_vec]
    unfold T B at he
    rw [hshift] at he
    linear_combination he
  have hm := positive_two_match _ _ _ _ hsum
  rcases hm with hm | hm
  · have hh : (MvPolynomial.X (c+b-tau) : Gluing.HomLambda)*MvPolynomial.X tau =
        MvPolynomial.X u*MvPolynomial.X (c+(b-u)) := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (u+v-tau))
      simp only [tripleProduct_vec] at hm
      convert hm using 1 <;> ring
    have hr := variable_product_reading _ _ _ _ hh
    rcases hr with hr | hr <;> omega
  · have hd : (MvPolynomial.X tau : Gluing.HomLambda) ∣
        MvPolynomial.X v*MvPolynomial.X b*MvPolynomial.X (c+u-tau) := by
      have hleft : (MvPolynomial.X tau : Gluing.HomLambda) ∣
          MvPolynomial.X (c+b-tau)*MvPolynomial.X tau*MvPolynomial.X (u+v-tau) := by
        exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      have hm' : (MvPolynomial.X (c+b-tau) : Gluing.HomLambda) *
          MvPolynomial.X tau * MvPolynomial.X (u+v-tau) =
          MvPolynomial.X v * MvPolynomial.X b * MvPolynomial.X (c+u-tau) := by
        simpa only [tripleProduct_vec] using hm
      rw [hm'] at hleft
      exact hleft
    simp only [MvPolynomial.X_dvd_mul_iff,MvPolynomial.X_dvd_X] at hd
    omega

noncomputable def regimeIIIContact (t s : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.L * T t.b t.p t.c -
    MvPolynomial.X t.v * T t.b t.p s.c -
    (if mixedContactLabel t s=middleRightCandidate t then
      MvPolynomial.X t.x * B t.u t.v t.tau else 0) +
    (if mixedContactLabel t s=endRightCandidate s then
      MvPolynomial.X t.L * F s.v s.x s.tau else 0)

theorem regimeIII_contact_zero (t s : Parameters)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (hpu : t.p=t.u) (haL : t.a=t.L) (hd : s.c=t.c+t.u-t.tau)
    (hB : B t.u t.v t.tau=B s.u s.v s.tau)
    (hR : mixedContactLabel t s=middleTopCandidate t)
    (hR' : mixedContactLabel t s=endTopCandidate s)
    (hK : mixedContactCoefficient t s=0) : regimeIIIContact t s=0 := by
  simp only [mixedContactCoefficient,if_pos hR,if_pos hR'] at hK
  simp only [← ha,← hp,← hb,← hB,haL,hpu] at hK
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.u)
  simp only [regimeIIIContact,mul_zero]
  simp only [G,B,Parameters.L,hpu,hd] at hK ⊢
  split_ifs at hK ⊢ <;> linear_combination hK

theorem regimeIII_middle_right_active (t s : Parameters) (ht : ValidM t)
    (hpu : t.p=t.u) (hd : s.c=t.c+t.u-t.tau)
    (hzero : regimeIIIContact t s=0) :
    mixedContactLabel t s=middleRightCandidate t := by
  by_contra hn
  have hvL : t.v ≠ t.L := by
    have hu := ht.1
    dsimp [Parameters.L]
    omega
  have hT := eraseOne_ne_zero_of_coordinate_not_dvd t.L (T t.b t.p s.c)
    (T_coordinate_not_dvd _ _ _ t.L ht.2.2.1 (by
      have hc := ht.2.2.2.2.2
      have hu := ht.1
      omega))
  simp only [regimeIIIContact,if_neg hn] at hzero
  have hh := congrArg (eraseOne t.L) hzero
  simp [apply_ite,hvL,hT] at hh

/-- The right-contact row beta is read by subtracting the common span equations. -/
theorem mixed_right_contact_xi (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (htau : t.tau=s.tau)
    (hm : m t=m s) (hright : middleRightCandidate t=endRightCandidate s) :
    s.x+t.a=t.x+s.u := by
  rcases ht with ⟨hu,hv,hb',hx,hy,hc⟩
  rcases hs with ⟨hU,hV,hB,hX,hY,hC⟩
  dsimp only [m] at hm
  dsimp only [middleRightCandidate,endRightCandidate] at hright
  omega

/-- The third mixed contact regime is impossible for actual Schur-equal boards. -/
theorem mixed_regimeIII_impossible (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur)
    (hpu : t.p=t.u) (haL : t.a=t.L) (hd : s.c=t.c+t.u-t.tau)
    (hcontact : middleTopCandidate t=endTopCandidate s) : False := by
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (mixed_first_marker_eq t s ht hs he)).2
  have hm := (mixed_marker_readings t s ht hs he).1
  have hK := mixed_strict_contact_zero t s ht hs hr he
  have hactive := mixed_contact_active t s ht hs ha hp hK
  have hR : mixedContactLabel t s=middleTopCandidate t := by
    rcases hactive.1 with h | h <;> omega
  have hR' : mixedContactLabel t s=endTopCandidate s := by omega
  have hzero := regimeIII_contact_zero t s ha hb hp hpu haL hd hB hR hR' hK
  have hZ := regimeIII_middle_right_active t s ht hpu hd hzero
  have htu := ht.1
  have htv := ht.2.1
  have htb := ht.2.2.1
  have htx := ht.2.2.2.1
  have hty := ht.2.2.2.2.1
  have htc := ht.2.2.2.2.2
  have hsu := hs.1
  have hsv := hs.2.1
  have hsb := hs.2.2.1
  have hsx := hs.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have hsc := hs.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hL' : t.L=s.L := by
    rcases hcore with hcore | hcore <;>
      simp [Parameters.L,← htau,← hcore.1,← hcore.2,Nat.add_comm]
  have hfree := mixed_free_rows t s ht hs hL' hb he
  have htopright : middleTopCandidate t=middleRightCandidate t := by omega
  have hx : t.x=t.c+t.b-t.tau := by
    dsimp [middleTopCandidate,middleRightCandidate] at htopright
    omega
  have hdc : t.c<s.c := by omega
  have hdx : s.c<t.x := by omega
  have hdmem : s.c∈({t.x,t.y,t.c} : Multiset ℕ) := by rw [hfree]; simp
  have hyd : t.y=s.c := by
    have hdmem' : s.c=t.x ∨ s.c=t.y ∨ s.c=t.c := by simpa using hdmem
    omega
  have hpair : ({t.x,t.c} : Multiset ℕ)={s.x,s.y} := by
    rw [hyd] at hfree
    exact multiset_cancel_middle t.x t.c s.c s.x s.y hfree
  have hsxmem : s.x=t.x ∨ s.x=t.c := by
    have hh : s.x∈({t.x,t.c} : Multiset ℕ) := by rw [hpair]; simp
    simpa using hh
  have hZ' : mixedContactLabel t s=endRightCandidate s := by
    by_contra hn
    have hh : MvPolynomial.X t.L * T t.b t.p t.c -
        MvPolynomial.X t.v * T t.b t.p s.c -
        MvPolynomial.X t.x * B t.u t.v t.tau=0 := by
      simpa only [regimeIIIContact,if_pos hZ,if_neg hn,add_zero] using hzero
    rw [show t.L=t.u+t.v-t.tau from rfl,hpu,hd,hx] at hh
    exact regimeIII_missing_end_contact _ _ _ _ _ htu htv (by omega) (by omega) hh
  have hright : middleRightCandidate t=endRightCandidate s := by omega
  have hxi : s.x=t.c+t.b-t.u+s.u-t.v := by
    have hxiadd:=mixed_right_contact_xi t s ht hs ha hb hp htau hm hright
    omega
  have haligned : s.u=t.u ∧ s.v=t.v := by
    rcases hcore with hcore | hcore
    · exact ⟨hcore.1.symm,hcore.2.symm⟩
    · rcases hsxmem with h | h <;> omega
  have hsxc : s.x=t.c := by
    rcases hsxmem with h | h <;> omega
  have hbv : t.b=t.v := by omega
  have huv : t.u<t.v := by omega
  have hshift : t.c+t.u-t.tau+(t.v-t.u)=t.c+t.v-t.tau := by omega
  have hshift' : t.c+(t.v-t.u)=t.c+t.v-t.u := by omega
  have hres :
      2 * MvPolynomial.X (t.u+t.v-t.tau) * MvPolynomial.X t.v * MvPolynomial.X t.c -
      MvPolynomial.X (t.u+t.v-t.tau) * MvPolynomial.X t.u *
        MvPolynomial.X (t.c+t.v-t.u) -
      MvPolynomial.X t.v * MvPolynomial.X t.v * MvPolynomial.X (t.c+t.u-t.tau)=
        (0 : Gluing.HomLambda) := by
    simp only [regimeIIIContact,if_pos hZ,if_pos hZ',hpu,hd,haligned.2,hsxc,
      ← htau,hbv] at hzero
    unfold T F B at hzero
    rw [hshift,hshift',hx,hbv] at hzero
    dsimp [Parameters.L] at hzero
    linear_combination hzero
  exact regimeIII_residual_ne_zero _ _ _ _ htu huv (by omega) hres

/-- The exact arithmetic-progression output, including all common endpoint parameters. -/
structure CrossOutput (t s : Parameters) : Prop where
  tau_eq : t.tau=t.p
  bottom_eq : t.b=t.v
  middle_eq : t.c=t.u
  free_eq : t.y=2*t.u-t.p
  core_gap : t.v+t.p<t.u
  xi_eq : s.x=t.y
  eta_eq : s.y=t.x
  d_eq : s.c=t.c
  U_eq : s.u=t.u
  V_eq : s.v=t.v
  a_eq : s.a=t.a
  b_eq : s.b=t.b
  p_eq : s.p=t.p
  tau_mate_eq : s.tau=t.tau
  family : (t.a=t.v ∧ t.x=t.u+t.v-t.p) ∨ (t.a=t.p ∧ t.x=t.u)

/-- Necessity of `eq:cross-output`, with all three contact regimes fully resolved. -/
theorem mixed_strict_output (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) (he : (M t ht).schur=(E s hs).schur) : CrossOutput t s := by
  obtain ⟨ha,hb,hp,htau,hcore⟩ := mixed_strict_endpoint_reading t s ht hs hr he
  rcases mixed_strict_contact_regimes t s ht hs hr he with hI | hII | hIII
  · obtain ⟨htp,hbv,hcu,hy,hgap,hxi,heta,hd,hU,hV,hx⟩ :=
      mixed_regimeI_output t s ht hs hr he hI.2 hI.1
    exact ⟨htp,hbv,hcu,hy,hgap,hxi,heta,hd,hU,hV,
      ha.symm,hb.symm,hp.symm,htau.symm,Or.inr ⟨hI.2,hx⟩⟩
  · obtain ⟨hcontact,hav,htp,hd⟩ := hII
    obtain ⟨htp,hbv,hcu,hy,hgap,hxi,heta,hd,hU,hV,hav,hx⟩ :=
      mixed_regimeII_output t s ht hs hr he hav htp hd hcontact
    exact ⟨htp,hbv,hcu,hy,hgap,hxi,heta,hd,hU,hV,
      ha.symm,hb.symm,hp.symm,htau.symm,Or.inl ⟨hav,hx⟩⟩
  · obtain ⟨hcontact,hpu,haL,hd⟩ := hIII
    exact (mixed_regimeIII_impossible t s ht hs hr he hpu haL hd hcontact).elim

/-- Unrestricted mixed equality produces one of the two exceptional pairs after a possible half-turn. -/
theorem mixed_output (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur=(E s hs).schur) :
    ∃ t', ∃ ht' : ValidM t', (t'=t ∨ t'=rotateMiddle t) ∧ CrossOutput t' s := by
  obtain ⟨t',ht',horient,hr,he'⟩ := mixed_strict_orientation t s ht hs he
  exact ⟨t',ht',horient,mixed_strict_output t' s ht' hs hr he'⟩

/-- The family parameters are recovered from the opening quadratic. -/
def exceptionalParameters (t : Parameters) (ht : ValidM t) (hgap : t.v+t.p<t.u)
    (htp : t.tau=t.p) : FiveExceptional.Parameters where
  q := (t.v : ℤ)-t.p
  b := t.v
  g := (t.u : ℤ)-t.p
  q_pos := by have hv := ht.2.1; omega
  q_le_b := by omega
  b_lt_g := by omega

/-- The exact mixed output reconstructs the manuscript beta lists, not only their polynomials. -/
theorem cross_output_families (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ho : CrossOutput t s) :
    ∃ (P : FiveExceptional.Parameters) (second : Bool),
      (M t ht).TranslationEquivalent (FiveExceptional.F P second) ∧
      (E s hs).TranslationEquivalent (FiveExceptional.H P second) := by
  let P := exceptionalParameters t ht ho.core_gap ho.tau_eq
  have htu := ht.1
  have htv := ht.2.1
  have hL : t.L+t.p=t.u+t.v := by dsimp [Parameters.L]; have := ho.tau_eq; omega
  have hsL : s.L=t.L := by
    simp [Parameters.L,ho.U_eq,ho.V_eq,ho.tau_mate_eq]
  have hy : t.y+t.p=2*t.u := by have := ho.free_eq; have := ho.core_gap; omega
  have htp := ho.tau_eq
  have hb := ho.bottom_eq
  have hc := ho.middle_eq
  have hxi := ho.xi_eq
  have heta := ho.eta_eq
  have hd := ho.d_eq
  have hU := ho.U_eq
  have hV := ho.V_eq
  have ha := ho.a_eq
  have hmb := ho.b_eq
  have hp := ho.p_eq
  have hmt := ho.tau_mate_eq
  rcases ho.family with ⟨hav,hx⟩ | ⟨hap,hx⟩
  · refine ⟨P,false,⟨0,?_,?_⟩,⟨0,?_,?_⟩⟩
    all_goals
      intro i
      fin_cases i <;>
        norm_num [M,E,mProfile,eProfile,Gluing.Profile.toBetaDiagram,
          Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ,
          FiveExceptional.F,FiveExceptional.H,FiveExceptional.rows,
          FiveExceptional.fCols,FiveExceptional.hCols,P,exceptionalParameters] <;> omega
  · refine ⟨P,true,⟨0,?_,?_⟩,⟨0,?_,?_⟩⟩
    all_goals
      intro i
      fin_cases i <;>
        norm_num [M,E,mProfile,eProfile,Gluing.Profile.toBetaDiagram,
          Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ,
          FiveExceptional.F,FiveExceptional.H,FiveExceptional.rows,
          FiveExceptional.fCols,FiveExceptional.hCols,P,exceptionalParameters] <;> omega

/-- Sufficiency is an equality of the actual full-board Schur polynomials. -/
theorem cross_output_schur_eq (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (ho : CrossOutput t s) : (M t ht).schur=(E s hs).schur := by
  obtain ⟨P,second,hM,hE⟩ := cross_output_families t s ht hs ho
  exact hM.schur_eq.trans ((FiveExceptional.F_schur_eq_H P second).trans hE.schur_eq.symm)

/-- Mixed strict-orientation necessity and sufficiency. -/
theorem mixed_strict_iff (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (hr : t.q<deltaM t) :
    (M t ht).schur=(E s hs).schur ↔ CrossOutput t s :=
  ⟨mixed_strict_output t s ht hs hr, cross_output_schur_eq t s ht hs⟩

theorem middle_marker_readings (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (he : (M t ht).schur=(M s hs).schur) :
    m t=m s ∧ NM t=NM s ∧ secondM t=secondM s := by
  have heh := ((M t ht).homSchur_eq_iff (M s hs)).mpr he
  have hm := maximal_variable_unique _ _ _ _ (M_largest_variable t ht)
    (M_largest_variable s hs) heh
  have heEr : eraseOne (m t) (M t ht).homSchur =
      eraseOne (m s) (M s hs).homSchur := by
    rw [← hm]
    exact congrArg (eraseOne (m t)) heh
  have hn := maximal_variable_unique _ _ _ _ (M_next_variable t ht)
    (M_next_variable s hs) heEr
  have hc := congrArg (MvPolynomial.pderiv (NM t)) heEr
  rw [M_second_coefficient,hn,M_second_coefficient] at hc
  exact ⟨hm,hn,hc⟩

theorem end_marker_readings (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : (E t ht).schur=(E s hs).schur) :
    m t=m s ∧ NE t=NE s ∧ secondE t=secondE s := by
  have heh := ((E t ht).homSchur_eq_iff (E s hs)).mpr he
  have hm := maximal_variable_unique _ _ _ _ (E_largest_variable t ht)
    (E_largest_variable s hs) heh
  have heEr : eraseOne (m t) (E t ht).homSchur =
      eraseOne (m s) (E s hs).homSchur := by
    rw [← hm]
    exact congrArg (eraseOne (m t)) heh
  have hn := maximal_variable_unique _ _ _ _ (E_next_variable t ht)
    (E_next_variable s hs) heEr
  have hc := congrArg (MvPolynomial.pderiv (NE t)) heEr
  rw [E_second_coefficient,hn,E_second_coefficient] at hc
  exact ⟨hm,hn,hc⟩

def endRegimeDegree (t : Parameters) : ℕ :=
  if t.q<deltaE t then 3 else if deltaE t<t.q then 2 else 1

theorem end_gcd_degree (t : Parameters) (ht : ValidE t) :
    (gcd (C15 t) (secondE t)).totalDegree=endRegimeDegree t := by
  by_cases hq : t.q<deltaE t
  · rw [endRegimeDegree,if_pos hq]
    exact E_gcd_degree_strict_q t ht hq
  · by_cases hd : deltaE t<t.q
    · rw [endRegimeDegree,if_neg hq,if_pos hd]
      exact E_gcd_degree_strict_delta t ht hd
    · rw [endRegimeDegree,if_neg hq,if_neg hd]
      exact E_gcd_degree_tied t ht (by omega)

/-- The gcd degrees separate all three end-opening regimes under unrestricted equality. -/
theorem end_corner_regime_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : (E t ht).schur=(E s hs).schur) :
    (t.q<deltaE t ↔ s.q<deltaE s) ∧
    (deltaE t<t.q ↔ deltaE s<s.q) ∧ (t.q=deltaE t ↔ s.q=deltaE s) := by
  have hfirst := end_first_marker_eq t s ht hs he
  have hsecond := (end_marker_readings t s ht hs he).2.2
  have hd : endRegimeDegree t=endRegimeDegree s := by
    rw [← end_gcd_degree t ht,← end_gcd_degree s hs,hfirst,hsecond]
  unfold endRegimeDegree at hd
  split_ifs at hd <;> omega

/-- Strict lower-corner end equality determines the ordered endpoint parameters. -/
theorem end_strict_endpoint_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hr : t.q<deltaE t) (he : (E t ht).schur=(E s hs).schur) :
    t.a=s.a ∧ t.b=s.b ∧ t.p=s.p ∧ t.tau=s.tau ∧
      ((t.u=s.u ∧ t.v=s.v) ∨ (t.u=s.v ∧ t.v=s.u)) := by
  have hsreg := ((end_corner_regime_reading t s ht hs he).1).mp hr
  have hsecond := (end_marker_readings t s ht hs he).2.2
  rw [secondE_strict_q t hr,secondE_strict_q s hsreg] at hsecond
  have hsecond' : MvPolynomial.X t.a * MvPolynomial.X t.b * B t.u t.v t.tau =
      MvPolynomial.X s.a * MvPolynomial.X s.b * B s.u s.v s.tau := by
    simpa only [C14,neg_inj] using hsecond
  exact strict_two_marker_reading t s ht.1 ht.2.1 ht.2.2.1
    hs.1 hs.2.1 hs.2.2.1 (end_first_marker_eq t s ht hs he) hsecond'

def VarsBounded (f : Gluing.HomLambda) (N : ℕ) : Prop := ∀ j,j∈f.vars → j≤N

theorem varsBounded_X (j N : ℕ) (h : j≤N) : VarsBounded (MvPolynomial.X j) N := by
  intro k hk
  have hk' : k=j := by simpa using hk
  omega

theorem varsBounded_add (f g : Gluing.HomLambda) (N : ℕ)
    (hf : VarsBounded f N) (hg : VarsBounded g N) : VarsBounded (f+g) N := by
  intro j hj
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hj) with h | h
  · exact hf j h
  · exact hg j h

theorem varsBounded_neg (f : Gluing.HomLambda) (N : ℕ)
    (hf : VarsBounded f N) : VarsBounded (-f) N := by
  intro j hj
  exact hf j (by simpa using hj)

theorem varsBounded_sub (f g : Gluing.HomLambda) (N : ℕ)
    (hf : VarsBounded f N) (hg : VarsBounded g N) : VarsBounded (f-g) N := by
  rw [sub_eq_add_neg]
  exact varsBounded_add _ _ _ hf (varsBounded_neg _ _ hg)

theorem varsBounded_mul (f g : Gluing.HomLambda) (N : ℕ)
    (hf : VarsBounded f N) (hg : VarsBounded g N) : VarsBounded (f*g) N := by
  intro j hj
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hj) with h | h
  · exact hf j h
  · exact hg j h

noncomputable def endPrefixPart (t : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.a * MvPolynomial.X t.p *
    (B t.u t.v t.tau * MvPolynomial.X (m t) -
      F t.v t.x t.tau * MvPolynomial.X (m t-t.x+t.u) +
      endA0 t * MvPolynomial.X (m t-t.x+t.tau))

noncomputable def endRemainder (t : Parameters) : Gluing.HomLambda :=
  endJ t t.y * T t.b t.p t.c -
    MvPolynomial.X t.a * MvPolynomial.X t.b * endJ t (t.y+t.c-t.a)

/-- Subtract the common upper-prefix contribution of an end-opening board. -/
theorem end_prefix_split (t : Parameters) (ht : ValidE t) :
    (E t ht).homSchur=endPrefixPart t+endRemainder t := by
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hc := ht.2.2.2.2.2
  have h1 : m t-t.x+t.u=t.u+t.y+t.c+t.b-t.tau-t.a-t.p := by dsimp [m]; omega
  have h2 : m t-t.x+t.tau=t.y+t.c+t.b-t.a-t.p := by dsimp [m]; omega
  have h3 : t.x+(t.y+t.c-t.a)-t.tau=t.x+t.y+t.c-t.tau-t.a := by omega
  have h4 : t.y+t.c-t.a+t.u-t.tau=t.u+t.y+t.c-t.tau-t.a := by omega
  rw [end_block_expansion]
  unfold endPrefixPart endRemainder endCornerPart endJ
  rw [h1,h2,h3,h4]
  ring

def endRemainderTop (t : Parameters) : ℕ := t.x+t.y+t.c-t.tau-t.a
def endRemainderRight (t : Parameters) : ℕ := t.c+t.q
def endRemainderMax (t : Parameters) : ℕ := max (endRemainderTop t) (endRemainderRight t)

/-- No variable beyond the two remaining private positions occurs in the end remainder. -/
theorem end_remainder_vars (t : Parameters) (ht : ValidE t) :
    VarsBounded (endRemainder t) (endRemainderMax t) := by
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hc := ht.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : endRemainderTop t≤endRemainderMax t := le_max_left _ _
  have hN2 : endRemainderRight t≤endRemainderMax t := le_max_right _ _
  dsimp [endRemainderTop] at hN1
  dsimp [endRemainderRight,Parameters.q] at hN2
  have hX (j : ℕ) (hj : j≤endRemainderMax t) :
      VarsBounded (MvPolynomial.X j) (endRemainderMax t) := varsBounded_X j _ hj
  have hB : VarsBounded (B t.u t.v t.tau) (endRemainderMax t) := by
    unfold B
    exact varsBounded_sub _ _ _
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
  have hF : VarsBounded (F t.v t.x t.tau) (endRemainderMax t) := by
    unfold F
    exact varsBounded_sub _ _ _
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
  have hA : VarsBounded (endA0 t) (endRemainderMax t) := by
    unfold endA0
    exact varsBounded_sub _ _ _
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
  have hJ (z : ℕ) (hz : z≤endRemainderMax t)
      (hzu : z+t.u-t.tau≤endRemainderMax t)
      (hxz : t.x+z-t.tau≤endRemainderMax t) :
      VarsBounded (endJ t z) (endRemainderMax t) := by
    unfold endJ
    exact varsBounded_add _ _ _
      (varsBounded_sub _ _ _
        (varsBounded_mul _ _ _ hA (hX z hz))
        (varsBounded_mul _ _ _ hF (hX _ hzu)))
      (varsBounded_mul _ _ _ hB (hX _ hxz))
  have hT : VarsBounded (T t.b t.p t.c) (endRemainderMax t) := by
    unfold T
    exact varsBounded_sub _ _ _
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
  unfold endRemainder
  exact varsBounded_sub _ _ _
    (varsBounded_mul _ _ _ (hJ _ (by omega) (by omega) (by omega)) hT)
    (varsBounded_mul _ _ _
      (varsBounded_mul _ _ _ (hX _ (by omega)) (hX _ (by omega)))
      (hJ _ (by omega) (by omega) (by omega)))

noncomputable def endRemainderCoefficient (t : Parameters) : Gluing.HomLambda :=
  (if endRemainderMax t=endRemainderTop t then
    -(MvPolynomial.X t.a * MvPolynomial.X t.b * B t.u t.v t.tau) else 0) +
  (if endRemainderMax t=endRemainderRight t then
    -(MvPolynomial.X t.p * endJ t t.y) else 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem end_remainder_coefficient (t : Parameters) (ht : ValidE t) :
    MvPolynomial.pderiv (endRemainderMax t) (endRemainder t)=endRemainderCoefficient t := by
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hc := ht.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : endRemainderTop t≤endRemainderMax t := le_max_left _ _
  have hN2 : endRemainderRight t≤endRemainderMax t := le_max_right _ _
  have htop : t.x+(t.y+t.c-t.a)-t.tau=endRemainderTop t := by
    dsimp [endRemainderTop]
    omega
  have hright : t.c+(t.b-t.p)=endRemainderRight t := rfl
  have hlt1 : t.x+t.y-t.tau<endRemainderMax t := by dsimp [endRemainderTop] at hN1; omega
  have hlt2 : t.x+t.v-t.tau<endRemainderMax t := by omega
  have hlt3 : t.y+t.u-t.tau<endRemainderMax t := by dsimp [endRemainderTop] at hN1; omega
  have hlt4 : t.y+t.c-t.a+t.u-t.tau<endRemainderMax t := by
    dsimp [endRemainderTop] at hN1
    omega
  have hlt5 : t.y+t.c-t.a<endRemainderMax t := by omega
  have hlt6 : t.c<endRemainderMax t := by
    dsimp [endRemainderRight,Parameters.q] at hN2
    omega
  have hlt7 : t.b<endRemainderMax t := by
    dsimp [endRemainderRight,Parameters.q] at hN2
    omega
  have hlt8 : t.x<endRemainderMax t := by omega
  have hlt9 : t.y<endRemainderMax t := by omega
  have hlt10 : t.u<endRemainderMax t := by omega
  have hlt11 : t.v<endRemainderMax t := by omega
  have hlt12 : t.tau<endRemainderMax t := by omega
  have hlt13 : t.L<endRemainderMax t := by omega
  have hlt14 : t.a<endRemainderMax t := by omega
  have hlt15 : t.p<endRemainderMax t := by omega
  simp only [endRemainder,endRemainderCoefficient,endJ,endA0,F,B,T,htop,hright,
    map_add,map_sub,map_neg,MvPolynomial.pderiv_mul]
  simp only [MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt1),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt2),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt3),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt4),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt5),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt6),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt7),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt8),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt9),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt10),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt11),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt12),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt13),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt14),
    MvPolynomial.pderiv_X_of_ne (ne_of_lt hlt15)]
  simp only [MvPolynomial.pderiv_X,Pi.single_apply]
  split_ifs <;> try omega
  all_goals ring

theorem B_not_dvd_endJ (t : Parameters) (ht : ValidE t) :
    ¬ B t.u t.v t.tau ∣ endJ t t.y := by
  have hy : t.v<t.y := by have := ht.2.2.2.2.1; omega
  intro hd
  have hq := quadratic_homSchur t.u t.v t.tau ht.1 ht.2.1
  rw [← B_eq_F] at hq
  have hJ := endJ_eq_homSchur t ht t.y hy
  have hassoc := (B_irreducible _ _ _ ht.1 ht.2.1).associated_of_dvd
    (endJ_irreducible t ht t.y hy) hd
  rw [← hq,hJ] at hassoc
  have he := homSchur_eq_of_associated _ _ hassoc
  have hdeg := congrArg MvPolynomial.totalDegree he
  rw [BetaDiagram.homSchur_totalDegree,BetaDiagram.homSchur_totalDegree] at hdeg
  omega

theorem end_remainder_coefficient_ne_zero (t : Parameters) (ht : ValidE t) :
    endRemainderCoefficient t ≠ 0 := by
  have hy : t.v<t.y := by have := ht.2.2.2.2.1; omega
  have hBne := (B_irreducible _ _ _ ht.1 ht.2.1).ne_zero
  have hJne := (endJ_irreducible t ht t.y hy).ne_zero
  by_cases htop : endRemainderMax t=endRemainderTop t <;>
    by_cases hright : endRemainderMax t=endRemainderRight t
  · intro hz
    simp only [endRemainderCoefficient,if_pos htop,if_pos hright] at hz
    have heq : MvPolynomial.X t.a * MvPolynomial.X t.b * B t.u t.v t.tau =
        -(MvPolynomial.X t.p * endJ t t.y) := by linear_combination -hz
    have hd : (MvPolynomial.X t.p : Gluing.HomLambda) ∣
        MvPolynomial.X t.a * MvPolynomial.X t.b * B t.u t.v t.tau := by
      rw [heq]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    simp only [MvPolynomial.X_dvd_mul_iff,MvPolynomial.X_dvd_X] at hd
    have hpn := B_coordinate_not_dvd _ _ _ t.p ht.1 ht.2.1
    have hb := ht.2.2.1
    have hbn : t.p ≠ t.b := by omega
    have hpa : t.p=t.a := by tauto
    have hap : t.a=t.p := hpa.symm
    have hcancel : MvPolynomial.X t.b * B t.u t.v t.tau = -endJ t t.y := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.p)
      rw [hap] at heq
      convert heq using 1 <;> ring
    apply endJ_coordinate_not_dvd t ht t.y hy t.b
    exact ⟨-B t.u t.v t.tau,by linear_combination hcancel⟩
  · simpa only [endRemainderCoefficient,if_pos htop,if_neg hright,add_zero] using
      (neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero (MvPolynomial.X_ne_zero t.a) (MvPolynomial.X_ne_zero t.b)) hBne))
  · simpa only [endRemainderCoefficient,if_neg htop,if_pos hright,zero_add] using
      (neg_ne_zero.mpr (mul_ne_zero (MvPolynomial.X_ne_zero t.p) hJne))
  · unfold endRemainderMax at htop hright
    omega

theorem end_remainder_B_dvd_iff (t : Parameters) (ht : ValidE t) :
    B t.u t.v t.tau ∣ endRemainderCoefficient t ↔ endRemainderRight t<endRemainderTop t := by
  constructor
  · intro hd
    have hright : endRemainderMax t ≠ endRemainderRight t := by
      intro hright
      have htop : B t.u t.v t.tau ∣
          (if endRemainderMax t=endRemainderTop t then
            -(MvPolynomial.X t.a*MvPolynomial.X t.b*B t.u t.v t.tau) else 0) := by
        split_ifs
        · exact dvd_neg.mpr (dvd_mul_left _ _)
        · exact dvd_zero _
      have hrest := dvd_sub hd htop
      have hdiv : B t.u t.v t.tau ∣ MvPolynomial.X t.p * endJ t t.y := by
        have heq : endRemainderCoefficient t -
            (if endRemainderMax t=endRemainderTop t then
              -(MvPolynomial.X t.a*MvPolynomial.X t.b*B t.u t.v t.tau) else 0) =
            -(MvPolynomial.X t.p*endJ t t.y) := by
          simp only [endRemainderCoefficient,if_pos hright]
          ring
        rw [heq] at hrest
        exact dvd_neg.mp hrest
      rcases (B_irreducible _ _ _ ht.1 ht.2.1).prime.dvd_mul.mp hdiv with h | h
      · exact B_not_dvd_X _ _ _ _ ht.1 ht.2.1 h
      · exact B_not_dvd_endJ t ht h
    unfold endRemainderMax at hright
    omega
  · intro hstrict
    have htop : endRemainderMax t=endRemainderTop t := max_eq_left hstrict.le
    have hright : endRemainderMax t ≠ endRemainderRight t := by
      rw [htop]
      omega
    simp only [endRemainderCoefficient,if_pos htop,if_neg hright,add_zero]
    exact ⟨-(MvPolynomial.X t.a*MvPolynomial.X t.b),by ring⟩

theorem end_remainder_largest (t : Parameters) (ht : ValidE t) :
    endRemainderMax t∈(endRemainder t).vars ∧ VarsBounded (endRemainder t) (endRemainderMax t) := by
  refine ⟨?_,end_remainder_vars t ht⟩
  by_contra hn
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars hn
  rw [end_remainder_coefficient t ht] at hz
  exact end_remainder_coefficient_ne_zero t ht hz

theorem end_prefix_remainder_eq (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hx : t.x=s.x) (hu : t.u=s.u) (hv : t.v=s.v) (htau : t.tau=s.tau)
    (hm : m t=m s) (he : (E t ht).schur=(E s hs).schur) :
    endRemainder t=endRemainder s := by
  have hap := (end_first_reading t s ht hs he).1
  have hprod : (MvPolynomial.X t.a : Gluing.HomLambda)*MvPolynomial.X t.p =
      MvPolynomial.X s.a*MvPolynomial.X s.p := by
    rcases hap with hap | hap <;> rw [hap.1,hap.2] <;> ring
  have hprefix : endPrefixPart t=endPrefixPart s := by
    simp only [endPrefixPart,hprod,endA0,B,F,Parameters.L,hx,hu,hv,htau,hm]
  have hh := ((E t ht).homSchur_eq_iff (E s hs)).mpr he
  rw [end_prefix_split t ht,end_prefix_split s hs,hprefix] at hh
  exact add_left_cancel hh

theorem end_prefix_remainder_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hx : t.x=s.x) (hu : t.u=s.u) (hv : t.v=s.v) (htau : t.tau=s.tau)
    (hm : m t=m s) (he : (E t ht).schur=(E s hs).schur) :
    endRemainderMax t=endRemainderMax s ∧
      endRemainderCoefficient t=endRemainderCoefficient s := by
  have hh := end_prefix_remainder_eq t s ht hs hx hu hv htau hm he
  have hmax := maximal_variable_unique _ _ _ _ (end_remainder_largest t ht)
    (end_remainder_largest s hs) hh
  have hc := congrArg (MvPolynomial.pderiv (endRemainderMax t)) hh
  rw [end_remainder_coefficient t ht,hmax,end_remainder_coefficient s hs] at hc
  exact ⟨hmax,hc⟩

theorem end_prefix_three_rows (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hx : t.x=s.x) (hL : t.L=s.L) (he : (E t ht).schur=(E s hs).schur) :
    ({t.y,t.c,t.b} : Multiset ℕ)={s.y,s.c,s.b} := by
  have hh := (end_end_readings t s ht hs he).1
  rw [profile_five_rows,profile_five_rows] at hh
  change ({t.x}+({t.L}+({t.y}+({t.c}+{t.b}))) : Multiset ℕ) =
    {s.x}+({s.L}+({s.y}+({s.c}+{s.b}))) at hh
  rw [hx,hL] at hh
  exact add_left_cancel (add_left_cancel hh)

theorem pair_nat_reading (a b c d : ℕ) (he : ({a,b} : Multiset ℕ)={c,d}) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hm : a=c ∨ a=d := by
    have hmem : a∈({c,d} : Multiset ℕ) := by rw [← he]; simp
    simpa using hmem
  have hs : a+b=c+d := by
    simpa only [Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton,Nat.add_zero]
      using congrArg Multiset.sum he
  rcases hm with hm | hm
  · exact Or.inl ⟨hm,by omega⟩
  · exact Or.inr ⟨hm,by omega⟩

theorem end_prefix_same_endpoints (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hx : t.x=s.x) (hu : t.u=s.u) (hv : t.v=s.v) (htau : t.tau=s.tau)
    (hm : m t=m s) (ha : t.a=s.a) (hp : t.p=s.p)
    (hw : endRemainderRight t=endRemainderRight s)
    (he : (E t ht).schur=(E s hs).schur) : t=s := by
  have hty := ht.2.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have htu := ht.1
  have hsu := hs.1
  have htv := ht.2.1
  have hsv := hs.2.1
  have htb := ht.2.2.1
  have hsb := hs.2.2.1
  have hy : t.y=s.y := by
    dsimp [m] at hm
    dsimp [endRemainderRight,Parameters.q] at hw
    omega
  have hL : t.L=s.L := by simp [Parameters.L,hu,hv,htau]
  have hthree := end_prefix_three_rows t s ht hs hx hL he
  rw [hy] at hthree
  have hpair : ({t.c,t.b} : Multiset ℕ)={s.c,s.b} :=
    (Multiset.cons_inj_right s.y).mp hthree
  have hpair' := pair_nat_reading _ _ _ _ hpair
  have hT : T t.b t.p t.c=T s.b s.p s.c := by
    have hsum : t.c+t.b=s.c+s.b := by
      simpa only [Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton,Nat.add_zero]
        using congrArg Multiset.sum hpair
    have hindex : t.c+(t.b-t.p)=s.c+(s.b-s.p) := by omega
    unfold T
    rw [hindex,hp]
    rcases hpair' with h | h <;> rw [h.1,h.2] <;> ring
  have hJ (z : ℕ) : endJ t z=endJ s z := by
    simp only [endJ,endA0,F,B,Parameters.L,hx,hu,hv,htau]
  have hrest := end_prefix_remainder_eq t s ht hs hx hu hv htau hm he
  simp only [endRemainder] at hrest
  simp_rw [hJ] at hrest
  rw [hy,hT,ha] at hrest
  have hprod : MvPolynomial.X t.b * endJ s (s.y+t.c-s.a) =
      MvPolynomial.X s.b * endJ s (s.y+s.c-s.a) := by
    apply mul_left_cancel₀ (MvPolynomial.X_ne_zero s.a)
    linear_combination -hrest
  have hsz : s.v<s.y+s.c-s.a := by omega
  have hb := (coordinate_single_reading _ _ _ _
    (endJ_coordinate_not_dvd s hs _ hsz t.b) hprod).1
  exact end_joint_anchor t s ht hs hx hu hv htau hm ha hb hp he

/-- Full upper-prefix rigidity, including endpoint interchange and residual ties. -/
theorem end_prefix_rigidity (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hx : t.x=s.x) (hu : t.u=s.u) (hv : t.v=s.v) (htau : t.tau=s.tau)
    (hm : m t=m s) (he : (E t ht).schur=(E s hs).schur) : t=s := by
  obtain ⟨hmax,hcoeff⟩ := end_prefix_remainder_reading t s ht hs hx hu hv htau hm he
  have hB : B t.u t.v t.tau=B s.u s.v s.tau := by simp only [hu,hv,htau]
  have hreg : endRemainderRight t<endRemainderTop t ↔
      endRemainderRight s<endRemainderTop s := by
    rw [← end_remainder_B_dvd_iff t ht,← end_remainder_B_dvd_iff s hs,hB,hcoeff]
  by_cases htop : endRemainderRight t<endRemainderTop t
  · have htop' := hreg.mp htop
    have hNt : endRemainderMax t=endRemainderTop t := max_eq_left htop.le
    have hNs : endRemainderMax s=endRemainderTop s := max_eq_left htop'.le
    have hnrt : endRemainderMax t ≠ endRemainderRight t := by omega
    have hnrs : endRemainderMax s ≠ endRemainderRight s := by omega
    have hsecond : MvPolynomial.X t.a*MvPolynomial.X t.b*B t.u t.v t.tau =
        MvPolynomial.X s.a*MvPolynomial.X s.b*B s.u s.v s.tau := by
      simpa only [endRemainderCoefficient,if_pos hNt,if_pos hNs,if_neg hnrt,if_neg hnrs,
        add_zero,neg_inj] using hcoeff
    obtain ⟨ha,hb,hp,_,_⟩ := strict_two_marker_reading t s ht.1 ht.2.1 ht.2.2.1
      hs.1 hs.2.1 hs.2.2.1 (end_first_marker_eq t s ht hs he) hsecond
    exact end_joint_anchor t s ht hs hx hu hv htau hm ha hb hp he
  · have htop' : ¬ endRemainderRight s<endRemainderTop s := by tauto
    have hNt : endRemainderMax t=endRemainderRight t := max_eq_right (by omega)
    have hNs : endRemainderMax s=endRemainderRight s := max_eq_right (by omega)
    have hw : endRemainderRight t=endRemainderRight s := by omega
    rcases (end_first_reading t s ht hs he).1 with h | h
    · exact end_prefix_same_endpoints t s ht hs hx hu hv htau hm h.1 h.2 hw he
    · by_cases hap : t.a=t.p
      · exact end_prefix_same_endpoints t s ht hs hx hu hv htau hm
          (by omega) (by omega) hw he
      · have hty : t.v<t.y := by have := ht.2.2.2.2.1; omega
        have hsy : s.v<s.y := by have := hs.2.2.2.2.1; omega
        have htop_s : endRemainderMax s=endRemainderTop s := by
          by_contra hn
          have hcoeff' := hcoeff
          simp only [endRemainderCoefficient,if_pos hNt,if_pos hNs,if_neg hn] at hcoeff'
          have hh := congrArg (eraseOne t.a) hcoeff'
          have hJ := eraseOne_ne_zero_of_coordinate_not_dvd t.a (endJ t t.y)
            (endJ_coordinate_not_dvd t ht t.y hty t.a)
          have hpa : t.p ≠ t.a := Ne.symm hap
          simp [apply_ite,← h.1,← h.2,hpa,hJ] at hh
        have htop_t : endRemainderMax t=endRemainderTop t := by
          by_contra hn
          have hcoeff' := hcoeff
          simp only [endRemainderCoefficient,if_pos hNt,if_pos hNs,if_neg hn] at hcoeff'
          have hh := congrArg (eraseOne t.p) hcoeff'
          have hJ := eraseOne_ne_zero_of_coordinate_not_dvd t.p (endJ s s.y)
            (endJ_coordinate_not_dvd s hs s.y hsy t.p)
          simp [apply_ite,← h.1,← h.2,hap,hJ] at hh
        have hA : endRemainderTop t=endRemainderRight t := by omega
        have hA' : endRemainderTop s=endRemainderRight s := by omega
        have htb := ht.2.2.1
        have hsb := hs.2.2.1
        have htu := ht.1
        have hsu := hs.1
        have hty' := ht.2.2.2.2.1
        have hsy' := hs.2.2.2.2.1
        have htc := ht.2.2.2.2.2
        have hsc := hs.2.2.2.2.2
        have hc : t.c=s.c := by
          dsimp [m] at hm
          dsimp [endRemainderTop,endRemainderRight,Parameters.q] at hA hA' hw
          omega
        have hL : t.L=s.L := by simp [Parameters.L,hu,hv,htau]
        have hthree := end_prefix_three_rows t s ht hs hx hL he
        have hpair : ({t.y,t.b} : Multiset ℕ)={s.y,s.b} := by
          rw [hc] at hthree
          have hr : ({s.y,s.c,s.b} : Multiset ℕ)={s.y,s.b,s.c} :=
            congrArg (Multiset.cons s.y) (Multiset.cons_swap s.c s.b 0)
          exact multiset_cancel_middle t.y t.b s.c s.y s.b (hthree.trans hr)
        have hpair' := pair_nat_reading _ _ _ _ hpair
        dsimp [m] at hm
        dsimp [endRemainderTop,endRemainderRight,Parameters.q] at hA hA' hw
        have hxu := ht.2.2.2.1
        rcases hpair' with hpair' | hpair' <;> omega

noncomputable def endLower (t : Parameters) (z : ℕ) : Gluing.HomLambda :=
  MvPolynomial.X z * T t.b t.p t.c -
    MvPolynomial.X t.a *
      (MvPolynomial.X t.b * MvPolynomial.X (z+t.c-t.a) -
        MvPolynomial.X t.p * MvPolynomial.X (z+t.c+t.b-t.a-t.p))

noncomputable def endFour (t : Parameters) (r z : ℕ) : Gluing.HomLambda :=
  MvPolynomial.X r * endLower t z -
    MvPolynomial.X t.tau * endLower t (z+r-t.tau)

def endFourProfile (t : Parameters) (ht : ValidE t) (r z : ℕ)
    (hr : t.tau<r) (hz : t.tau+t.a<z) : Gluing.Profile 3 where
  r := ![r,z,t.c,t.b]
  g := ![t.tau,t.a,t.p]
  r_pos := by
    have hb := ht.2.2.1
    have hc := ht.2.2.2.2.2
    intro i
    fin_cases i <;> simp <;> omega
  g_lt_castSucc := by
    have hb := ht.2.2.1
    have hc := ht.2.2.2.2.2
    intro i
    fin_cases i <;> simp <;> omega
  g_lt_succ := by
    have hb := ht.2.2.1
    have hc := ht.2.2.2.2.2
    intro i
    fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem endFour_eq_homSchur (t : Parameters) (ht : ValidE t) (r z : ℕ)
    (hr : t.tau<r) (hz : t.tau+t.a<z) :
    endFour t r z=(endFourProfile t ht r z hr hz).toBetaDiagram.homSchur := by
  have hb := ht.2.2.1
  have hc := ht.2.2.2.2.2
  have hm : (endFourProfile t ht r z hr hz).toBetaDiagram.homMatrix =
      !![MvPolynomial.X r,MvPolynomial.X (r+z-t.tau),
          MvPolynomial.X (r+z+t.c-t.tau-t.a),
          MvPolynomial.X (r+z+t.c+t.b-t.tau-t.a-t.p);
        MvPolynomial.X t.tau,MvPolynomial.X z,MvPolynomial.X (z+t.c-t.a),
          MvPolynomial.X (z+t.c+t.b-t.a-t.p);
        0,MvPolynomial.X t.a,MvPolynomial.X t.c,MvPolynomial.X (t.c+t.b-t.p);
        0,0,MvPolynomial.X t.p,MvPolynomial.X t.b] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [BetaDiagram.homMatrix,Gluing.Profile.toBetaDiagram,endFourProfile,
        Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ,Gluing.hTilde] <;>
      (try split_ifs) <;> first | rfl | omega | (congr 1 <;> omega)
  have h1 : z+r-t.tau=r+z-t.tau := by omega
  have h2 : z+r-t.tau+t.c-t.a=r+z+t.c-t.tau-t.a := by omega
  have h3 : z+r-t.tau+t.c+t.b-t.a-t.p=r+z+t.c+t.b-t.tau-t.a-t.p := by omega
  have h4 : t.c+(t.b-t.p)=t.c+t.b-t.p := by omega
  have hflat (w : ℕ) : w+(z+r-t.tau)=w+z+r-t.tau := by omega
  have hflat' (w : ℕ) : w+(r+z-t.tau)=w+r+z-t.tau := by omega
  have hlast : t.c+(r+(z+t.b)-t.tau)-t.a-t.p =
      r+(z+(t.c+t.b))-t.tau-t.a-t.p := by omega
  rw [BetaDiagram.homSchur,hm]
  norm_num [endFour,endLower,T,Matrix.det_succ_row_zero,Matrix.det_unique,
    Matrix.det_fin_three,Matrix.submatrix_apply,Matrix.of_apply,
    Fin.sum_univ_succ,Fin.succAbove,h1,h2,h3,h4]
  simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  simp only [hflat,hflat']
  simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  rw [hlast]
  ring

theorem endFour_coordinate_not_dvd (t : Parameters) (ht : ValidE t) (r z : ℕ)
    (hr : t.tau<r) (hz : t.tau+t.a<z) (j : ℕ) :
    ¬ (MvPolynomial.X j : Gluing.HomLambda) ∣ endFour t r z := by
  rw [endFour_eq_homSchur t ht r z hr hz]
  exact homSchur_coordinate_not_dvd _ (Gluing.Profile.toBetaDiagram_connected _) j

noncomputable def endCommonTop (t : Parameters) : Gluing.HomLambda :=
  B t.u t.v t.tau *
    (MvPolynomial.X (t.x+t.y-t.tau) * T t.b t.p t.c -
      MvPolynomial.X t.a * MvPolynomial.X t.b *
        MvPolynomial.X (t.x+t.y+t.c-t.tau-t.a) +
      MvPolynomial.X t.a * MvPolynomial.X t.p * MvPolynomial.X (m t))

noncomputable def endTwoColumn (t : Parameters) : Gluing.HomLambda :=
  endA0 t * endLower t t.y -
    F t.v t.x t.tau * endLower t (t.y+t.u-t.tau)

theorem end_two_column_split (t : Parameters) (ht : ValidE t) :
    (E t ht).homSchur=endCommonTop t+endTwoColumn t := by
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hc := ht.2.2.2.2.2
  have h1 : t.y+t.u-t.tau+t.c-t.a=t.u+t.y+t.c-t.tau-t.a := by omega
  have h2 : t.y+t.u-t.tau+t.c+t.b-t.a-t.p =
      t.u+t.y+t.c+t.b-t.tau-t.a-t.p := by omega
  rw [end_block_expansion]
  unfold endCommonTop endTwoColumn endCornerPart endJ endLower
  rw [h1,h2]
  ring

theorem end_bottom_edge_two_column_eq (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (hc : t.c=s.c)
    (htau : t.tau=s.tau) (hB : B t.u t.v t.tau=B s.u s.v s.tau)
    (he : (E t ht).schur=(E s hs).schur) :
    endTwoColumn t=endTwoColumn s := by
  have hm := (end_marker_readings t s ht hs he).1
  have hty := ht.2.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have htu := ht.1
  have hsu := hs.1
  have htv := ht.2.1
  have hsv := hs.2.1
  have htb := ht.2.2.1
  have hsb := hs.2.2.1
  have hxy : t.x+t.y=s.x+s.y := by dsimp [m] at hm; omega
  have hidx : t.x+t.y+t.c-t.tau-t.a=s.x+s.y+s.c-s.tau-s.a := by omega
  have htop : endCommonTop t=endCommonTop s := by
    unfold endCommonTop
    rw [hidx,hxy,hB,ha,hb,hp,hc,htau,hm]
  have hh := ((E t ht).homSchur_eq_iff (E s hs)).mpr he
  rw [end_two_column_split t ht,end_two_column_split s hs,htop] at hh
  exact add_left_cancel hh

def swapEndCore (t : Parameters) : Parameters := {t with u:=t.v,v:=t.u}
def swapEndFree (t : Parameters) : Parameters := {t with x:=t.y,y:=t.x}

def endCoreComparisonMax (t : Parameters) : ℕ :=
  max (t.x+t.u-t.tau) (endRightCandidate t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem end_core_swap_coefficient (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndCore t)) (huv : t.v<t.u) :
    MvPolynomial.pderiv (endCoreComparisonMax t)
      (endTwoColumn t-endTwoColumn (swapEndCore t)) =
    (if endCoreComparisonMax t=t.x+t.u-t.tau then endFour t t.v t.y else 0) -
    (if endCoreComparisonMax t=endRightCandidate t then
      MvPolynomial.X t.a*MvPolynomial.X t.p*F t.v t.x t.tau else 0) := by
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hy' : t.a+t.u<t.y := hs.2.2.2.2.1
  have hc := ht.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : t.x+t.u-t.tau≤endCoreComparisonMax t := le_max_left _ _
  have hN2 : endRightCandidate t≤endCoreComparisonMax t := le_max_right _ _
  dsimp [endRightCandidate] at hN2
  have h0 : t.y+t.u-t.tau+t.c+t.b-t.a-t.p=endRightCandidate t := by
    dsimp [endRightCandidate]; omega
  have h1 : t.x+t.v-t.tau<endCoreComparisonMax t := by omega
  have h2 : t.y+t.u-t.tau<endCoreComparisonMax t := by omega
  have h3 : t.y+t.v-t.tau<endCoreComparisonMax t := by omega
  have h4 : t.y+t.c+t.b-t.a-t.p<endCoreComparisonMax t := by omega
  have h5 : t.y+t.v-t.tau+t.c+t.b-t.a-t.p<endCoreComparisonMax t := by omega
  have h6 : t.y+t.u-t.tau+t.c-t.a<endCoreComparisonMax t := by omega
  have h7 : t.y+t.v-t.tau+t.c-t.a<endCoreComparisonMax t := by omega
  have h8 : t.y+t.c-t.a<endCoreComparisonMax t := by omega
  have h9 : t.c+(t.b-t.p)<endCoreComparisonMax t := by omega
  have h10 : t.x<endCoreComparisonMax t := by omega
  have h11 : t.y<endCoreComparisonMax t := by omega
  have h12 : t.c<endCoreComparisonMax t := by omega
  have h13 : t.b<endCoreComparisonMax t := by omega
  have h14 : t.a<endCoreComparisonMax t := by omega
  have h15 : t.p<endCoreComparisonMax t := by omega
  have h16 : t.u<endCoreComparisonMax t := by omega
  have h17 : t.v<endCoreComparisonMax t := by omega
  have h18 : t.tau<endCoreComparisonMax t := by omega
  have h19 : t.L<endCoreComparisonMax t := by omega
  have hLs : (swapEndCore t).L=t.L := by simp [swapEndCore,Parameters.L,Nat.add_comm]
  dsimp only [swapEndCore] at hLs h0
  simp only [endTwoColumn,endA0,endFour,endLower,F,T,hLs,swapEndCore,h0,
    map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  simp only [if_neg (ne_of_lt h1),if_neg (ne_of_lt h2),if_neg (ne_of_lt h3),
    if_neg (ne_of_lt h4),if_neg (ne_of_lt h5),if_neg (ne_of_lt h6),
    if_neg (ne_of_lt h7),if_neg (ne_of_lt h8),if_neg (ne_of_lt h9),
    if_neg (ne_of_lt h10),if_neg (ne_of_lt h11),if_neg (ne_of_lt h12),
    if_neg (ne_of_lt h13),if_neg (ne_of_lt h14),if_neg (ne_of_lt h15),
    if_neg (ne_of_lt h16),if_neg (ne_of_lt h17),if_neg (ne_of_lt h18),
    if_neg (ne_of_lt h19),if_neg (ne_of_gt h1),if_neg (ne_of_gt h2),
    if_neg (ne_of_gt h3),if_neg (ne_of_gt h4),if_neg (ne_of_gt h5),
    if_neg (ne_of_gt h6),if_neg (ne_of_gt h7),if_neg (ne_of_gt h8),
    if_neg (ne_of_gt h9),if_neg (ne_of_gt h10),if_neg (ne_of_gt h11),
    if_neg (ne_of_gt h12),if_neg (ne_of_gt h13),if_neg (ne_of_gt h14),
    if_neg (ne_of_gt h15),if_neg (ne_of_gt h16),if_neg (ne_of_gt h17),
    if_neg (ne_of_gt h18),if_neg (ne_of_gt h19)]
  by_cases htop : endCoreComparisonMax t=t.x+t.u-t.tau <;>
    by_cases hright : endCoreComparisonMax t=endRightCandidate t <;>
    simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,zero_add,add_zero,
      zero_sub,sub_zero,neg_zero,one_mul,mul_one] <;>
    ring

/-- Core interchange cannot preserve an end-opening board with a fixed bottom edge. -/
theorem end_core_swap_ne (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndCore t)) (huv : t.v<t.u) :
    (E t ht).schur ≠ (E (swapEndCore t) hs).schur := by
  intro he
  have hB : B t.u t.v t.tau =
      B (swapEndCore t).u (swapEndCore t).v (swapEndCore t).tau := by
    simp [B,swapEndCore,Nat.add_comm,mul_comm]
  have htwo := end_bottom_edge_two_column_eq t (swapEndCore t) ht hs
    rfl rfl rfl rfl rfl hB he
  have hd := congrArg (MvPolynomial.pderiv (endCoreComparisonMax t)) htwo
  have hz : MvPolynomial.pderiv (endCoreComparisonMax t)
      (endTwoColumn t-endTwoColumn (swapEndCore t))=0 := by
    rw [map_sub,hd,sub_self]
  rw [end_core_swap_coefficient t ht hs huv] at hz
  have hzy : t.tau+t.a<t.y := by
    have hy := ht.2.2.2.2.1
    have hv := ht.2.1
    omega
  have hC := endFour_coordinate_not_dvd t ht t.v t.y ht.2.1 hzy t.a
  have hCn : endFour t t.v t.y ≠ 0 := by
    intro h0
    apply hC
    rw [h0]
    exact dvd_zero _
  have hKn : MvPolynomial.X t.a*MvPolynomial.X t.p*F t.v t.x t.tau ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
    exact (F_irreducible _ _ _ ht.2.1 (by
      have hu := ht.1
      have hx := ht.2.2.2.1
      omega)).ne_zero
  by_cases hA : endCoreComparisonMax t=t.x+t.u-t.tau <;>
    by_cases hZ : endCoreComparisonMax t=endRightCandidate t
  · simp only [if_pos hA,if_pos hZ] at hz
    have hprod := sub_eq_zero.mp hz
    apply hC
    exact ⟨MvPolynomial.X t.p*F t.v t.x t.tau,by simpa [mul_assoc] using hprod⟩
  · simp only [if_pos hA,if_neg hZ,sub_zero] at hz
    exact hCn hz
  · simp only [if_neg hA,if_pos hZ,zero_sub,neg_eq_zero] at hz
    exact hKn hz
  · unfold endCoreComparisonMax at hA hZ
    omega

def endFreeComparisonMax (t : Parameters) : ℕ :=
  max (t.y+t.v-t.tau) (endRightCandidate t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem end_free_swap_coefficient (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndFree t)) (hxy : t.x<t.y) :
    MvPolynomial.pderiv (endFreeComparisonMax t)
      (endTwoColumn t-endTwoColumn (swapEndFree t)) =
    (if endFreeComparisonMax t=t.y+t.v-t.tau then endFour t t.u t.x else 0) -
    (if endFreeComparisonMax t=endRightCandidate t then
      MvPolynomial.X t.a*MvPolynomial.X t.p*F t.v t.x t.tau else 0) := by
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hx' : t.a+t.v<t.x := hs.2.2.2.2.1
  have hy' : t.u<t.y := hs.2.2.2.1
  have hc := ht.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : t.y+t.v-t.tau≤endFreeComparisonMax t := le_max_left _ _
  have hN2 : endRightCandidate t≤endFreeComparisonMax t := le_max_right _ _
  dsimp [endRightCandidate] at hN2
  have h0 : t.y+t.u-t.tau+t.c+t.b-t.a-t.p=endRightCandidate t := by
    dsimp [endRightCandidate]; omega
  have h1 : t.x+t.v-t.tau<endFreeComparisonMax t := by omega
  have h2 : t.y+t.u-t.tau<endFreeComparisonMax t := by omega
  have h3 : t.x+t.u-t.tau<endFreeComparisonMax t := by omega
  have h4 : t.y+t.c+t.b-t.a-t.p<endFreeComparisonMax t := by omega
  have h5 : t.x+t.c+t.b-t.a-t.p<endFreeComparisonMax t := by omega
  have h6 : t.x+t.u-t.tau+t.c+t.b-t.a-t.p<endFreeComparisonMax t := by omega
  have h7 : t.y+t.u-t.tau+t.c-t.a<endFreeComparisonMax t := by omega
  have h8 : t.x+t.u-t.tau+t.c-t.a<endFreeComparisonMax t := by omega
  have h9 : t.y+t.c-t.a<endFreeComparisonMax t := by omega
  have h10 : t.x+t.c-t.a<endFreeComparisonMax t := by omega
  have h11 : t.c+(t.b-t.p)<endFreeComparisonMax t := by omega
  have h12 : t.x<endFreeComparisonMax t := by omega
  have h13 : t.y<endFreeComparisonMax t := by omega
  have h14 : t.c<endFreeComparisonMax t := by omega
  have h15 : t.b<endFreeComparisonMax t := by omega
  have h16 : t.a<endFreeComparisonMax t := by omega
  have h17 : t.p<endFreeComparisonMax t := by omega
  have h18 : t.u<endFreeComparisonMax t := by omega
  have h19 : t.v<endFreeComparisonMax t := by omega
  have h20 : t.tau<endFreeComparisonMax t := by omega
  have h21 : t.L<endFreeComparisonMax t := by omega
  have hLs : (swapEndFree t).L=t.L := rfl
  dsimp only [swapEndFree] at hLs h0
  simp only [endTwoColumn,endA0,endFour,endLower,F,T,hLs,swapEndFree,h0,
    map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  simp only [if_neg (ne_of_lt h1),if_neg (ne_of_lt h2),if_neg (ne_of_lt h3),
    if_neg (ne_of_lt h4),if_neg (ne_of_lt h5),if_neg (ne_of_lt h6),
    if_neg (ne_of_lt h7),if_neg (ne_of_lt h8),if_neg (ne_of_lt h9),
    if_neg (ne_of_lt h10),if_neg (ne_of_lt h11),if_neg (ne_of_lt h12),
    if_neg (ne_of_lt h13),if_neg (ne_of_lt h14),if_neg (ne_of_lt h15),
    if_neg (ne_of_lt h16),if_neg (ne_of_lt h17),if_neg (ne_of_lt h18),
    if_neg (ne_of_lt h19),if_neg (ne_of_lt h20),if_neg (ne_of_lt h21),
    if_neg (ne_of_gt h1),if_neg (ne_of_gt h2),if_neg (ne_of_gt h3),
    if_neg (ne_of_gt h4),if_neg (ne_of_gt h5),if_neg (ne_of_gt h6),
    if_neg (ne_of_gt h7),if_neg (ne_of_gt h8),if_neg (ne_of_gt h9),
    if_neg (ne_of_gt h10),if_neg (ne_of_gt h11),if_neg (ne_of_gt h12),
    if_neg (ne_of_gt h13),if_neg (ne_of_gt h14),if_neg (ne_of_gt h15),
    if_neg (ne_of_gt h16),if_neg (ne_of_gt h17),if_neg (ne_of_gt h18),
    if_neg (ne_of_gt h19),if_neg (ne_of_gt h20),if_neg (ne_of_gt h21)]
  by_cases htop : endFreeComparisonMax t=t.y+t.v-t.tau <;>
    by_cases hright : endFreeComparisonMax t=endRightCandidate t <;>
    simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,zero_add,add_zero,
      zero_sub,sub_zero,neg_zero,one_mul,mul_one] <;>
    ring

theorem end_free_swap_ne (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndFree t)) (hxy : t.x<t.y) :
    (E t ht).schur ≠ (E (swapEndFree t) hs).schur := by
  intro he
  have htwo := end_bottom_edge_two_column_eq t (swapEndFree t) ht hs
    rfl rfl rfl rfl rfl rfl he
  have hd := congrArg (MvPolynomial.pderiv (endFreeComparisonMax t)) htwo
  have hz : MvPolynomial.pderiv (endFreeComparisonMax t)
      (endTwoColumn t-endTwoColumn (swapEndFree t))=0 := by
    rw [map_sub,hd,sub_self]
  rw [end_free_swap_coefficient t ht hs hxy] at hz
  have hzx : t.tau+t.a<t.x := by
    have hx' : t.a+t.v<t.x := hs.2.2.2.2.1
    have hv := ht.2.1
    omega
  have hC := endFour_coordinate_not_dvd t ht t.u t.x ht.1 hzx t.a
  have hCn : endFour t t.u t.x ≠ 0 := by
    intro h0
    apply hC
    rw [h0]
    exact dvd_zero _
  have hKn : MvPolynomial.X t.a*MvPolynomial.X t.p*F t.v t.x t.tau ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
    exact (F_irreducible _ _ _ ht.2.1 (by
      have hu := ht.1
      have hx := ht.2.2.2.1
      omega)).ne_zero
  by_cases hA : endFreeComparisonMax t=t.y+t.v-t.tau <;>
    by_cases hZ : endFreeComparisonMax t=endRightCandidate t
  · simp only [if_pos hA,if_pos hZ] at hz
    apply hC
    exact ⟨MvPolynomial.X t.p*F t.v t.x t.tau,
      by simpa [mul_assoc] using sub_eq_zero.mp hz⟩
  · simp only [if_pos hA,if_neg hZ,sub_zero] at hz
    exact hCn hz
  · simp only [if_neg hA,if_pos hZ,zero_sub,neg_eq_zero] at hz
    exact hKn hz
  · unfold endFreeComparisonMax at hA hZ
    omega

def swapEndBoth (t : Parameters) : Parameters := swapEndCore (swapEndFree t)
def endBothComparisonMax (t : Parameters) : ℕ :=
  max (endRightCandidate t) (endRightCandidate (swapEndBoth t))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem end_both_swap_coefficient (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndBoth t)) :
    MvPolynomial.pderiv (endBothComparisonMax t)
      (endTwoColumn t-endTwoColumn (swapEndBoth t)) =
    -(if endBothComparisonMax t=endRightCandidate t then
      MvPolynomial.X t.a*MvPolynomial.X t.p*F t.v t.x t.tau else 0) +
    (if endBothComparisonMax t=endRightCandidate (swapEndBoth t) then
      MvPolynomial.X t.a*MvPolynomial.X t.p*F t.u t.y t.tau else 0) := by
  rw [show endRightCandidate (swapEndBoth t)=
    t.v+t.x+t.c+t.b-t.tau-t.a-t.p from rfl]
  have hu := ht.1
  have hv := ht.2.1
  have hb := ht.2.2.1
  have hx := ht.2.2.2.1
  have hy := ht.2.2.2.2.1
  have hx' : t.a+t.u<t.x := hs.2.2.2.2.1
  have hy' : t.v<t.y := hs.2.2.2.1
  have hc := ht.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : endRightCandidate t≤endBothComparisonMax t := le_max_left _ _
  have hN2 : endRightCandidate (swapEndBoth t)≤endBothComparisonMax t := le_max_right _ _
  dsimp [endRightCandidate,swapEndBoth,swapEndCore,swapEndFree] at hN1 hN2
  have h0 : t.y+t.u-t.tau+t.c+t.b-t.a-t.p=endRightCandidate t := by
    dsimp [endRightCandidate]; omega
  have h0' : t.x+t.v-t.tau+t.c+t.b-t.a-t.p =
      t.v+t.x+t.c+t.b-t.tau-t.a-t.p := by omega
  have h1 : t.x+t.v-t.tau<endBothComparisonMax t := by omega
  have h2 : t.y+t.u-t.tau<endBothComparisonMax t := by omega
  have h3 : t.y+t.c+t.b-t.a-t.p<endBothComparisonMax t := by omega
  have h4 : t.x+t.c+t.b-t.a-t.p<endBothComparisonMax t := by omega
  have h5 : t.y+t.u-t.tau+t.c-t.a<endBothComparisonMax t := by omega
  have h6 : t.x+t.v-t.tau+t.c-t.a<endBothComparisonMax t := by omega
  have h7 : t.y+t.c-t.a<endBothComparisonMax t := by omega
  have h8 : t.x+t.c-t.a<endBothComparisonMax t := by omega
  have h9 : t.c+(t.b-t.p)<endBothComparisonMax t := by omega
  have h10 : t.x<endBothComparisonMax t := by omega
  have h11 : t.y<endBothComparisonMax t := by omega
  have h12 : t.c<endBothComparisonMax t := by omega
  have h13 : t.b<endBothComparisonMax t := by omega
  have h14 : t.a<endBothComparisonMax t := by omega
  have h15 : t.p<endBothComparisonMax t := by omega
  have h16 : t.u<endBothComparisonMax t := by omega
  have h17 : t.v<endBothComparisonMax t := by omega
  have h18 : t.tau<endBothComparisonMax t := by omega
  have h19 : t.L<endBothComparisonMax t := by omega
  have hLs : (swapEndBoth t).L=t.L := by
    simp [swapEndBoth,swapEndCore,swapEndFree,Parameters.L,Nat.add_comm]
  dsimp only [swapEndBoth,swapEndCore,swapEndFree] at hLs h0 h0'
  simp only [endTwoColumn,endA0,endLower,F,T,hLs,swapEndBoth,swapEndCore,swapEndFree,h0,h0',
    map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  simp only [if_neg (ne_of_lt h1),if_neg (ne_of_lt h2),if_neg (ne_of_lt h3),
    if_neg (ne_of_lt h4),if_neg (ne_of_lt h5),if_neg (ne_of_lt h6),
    if_neg (ne_of_lt h7),if_neg (ne_of_lt h8),if_neg (ne_of_lt h9),
    if_neg (ne_of_lt h10),if_neg (ne_of_lt h11),if_neg (ne_of_lt h12),
    if_neg (ne_of_lt h13),if_neg (ne_of_lt h14),if_neg (ne_of_lt h15),
    if_neg (ne_of_lt h16),if_neg (ne_of_lt h17),if_neg (ne_of_lt h18),
    if_neg (ne_of_lt h19),if_neg (ne_of_gt h1),if_neg (ne_of_gt h2),
    if_neg (ne_of_gt h3),if_neg (ne_of_gt h4),if_neg (ne_of_gt h5),
    if_neg (ne_of_gt h6),if_neg (ne_of_gt h7),if_neg (ne_of_gt h8),
    if_neg (ne_of_gt h9),if_neg (ne_of_gt h10),if_neg (ne_of_gt h11),
    if_neg (ne_of_gt h12),if_neg (ne_of_gt h13),if_neg (ne_of_gt h14),
    if_neg (ne_of_gt h15),if_neg (ne_of_gt h16),if_neg (ne_of_gt h17),
    if_neg (ne_of_gt h18),if_neg (ne_of_gt h19)]
  by_cases hright : endBothComparisonMax t=endRightCandidate t <;>
    by_cases hright' : endBothComparisonMax t=t.v+t.x+t.c+t.b-t.tau-t.a-t.p <;>
    simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,zero_add,add_zero,
      zero_sub,sub_zero,neg_zero,one_mul,mul_one] <;>
    ring

theorem end_both_swap_ne (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndBoth t)) (hdiff : t.x≠t.y ∨ t.u≠t.v) :
    (E t ht).schur ≠ (E (swapEndBoth t) hs).schur := by
  intro he
  have hB : B t.u t.v t.tau =
      B (swapEndBoth t).u (swapEndBoth t).v (swapEndBoth t).tau := by
    simp [B,swapEndBoth,swapEndCore,swapEndFree,Nat.add_comm,mul_comm]
  have htwo := end_bottom_edge_two_column_eq t (swapEndBoth t) ht hs
    rfl rfl rfl rfl rfl hB he
  have hd := congrArg (MvPolynomial.pderiv (endBothComparisonMax t)) htwo
  have hz : MvPolynomial.pderiv (endBothComparisonMax t)
      (endTwoColumn t-endTwoColumn (swapEndBoth t))=0 := by rw [map_sub,hd,sub_self]
  rw [end_both_swap_coefficient t ht hs] at hz
  have htx : t.tau<t.x := by have hu:=ht.1; have hx:=ht.2.2.2.1; omega
  have hty : t.tau<t.y := by have hv:=ht.2.1; have hy:=ht.2.2.2.2.1; omega
  have hF : F t.v t.x t.tau ≠ F t.u t.y t.tau := by
    intro heF
    have hb : B t.v t.x t.tau=B t.u t.y t.tau := by simpa only [B_eq_F] using heF
    have hp := (quadratic_parameter_reading _ _ _ _ _ _ ht.2.1 htx ht.1 hty hb).2
    have hx:=ht.2.2.2.1
    have hy:=ht.2.2.2.2.1
    rcases hp with hp | hp <;> omega
  have hn1 := mul_ne_zero
    (mul_ne_zero (MvPolynomial.X_ne_zero t.a) (MvPolynomial.X_ne_zero t.p))
    (F_irreducible _ _ _ ht.2.1 htx).ne_zero
  have hn2 := mul_ne_zero
    (mul_ne_zero (MvPolynomial.X_ne_zero t.a) (MvPolynomial.X_ne_zero t.p))
    (F_irreducible _ _ _ ht.1 hty).ne_zero
  by_cases hA : endBothComparisonMax t=endRightCandidate t <;>
    by_cases hZ : endBothComparisonMax t=endRightCandidate (swapEndBoth t)
  · simp only [if_pos hA,if_pos hZ] at hz
    apply hF
    apply mul_left_cancel₀
      (mul_ne_zero (MvPolynomial.X_ne_zero t.a) (MvPolynomial.X_ne_zero t.p))
    linear_combination -hz
  · simp only [if_pos hA,if_neg hZ,add_zero,neg_eq_zero] at hz
    exact hn1 hz
  · simp only [if_neg hA,if_pos hZ,neg_zero,zero_add] at hz
    exact hn2 hz
  · unfold endBothComparisonMax at hA hZ
    omega

theorem end_core_swap_ne_of_ne (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndCore t)) (hne : t.u≠t.v) :
    (E t ht).schur ≠ (E (swapEndCore t) hs).schur := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hback : ValidE (swapEndCore (swapEndCore t)) := by
      simpa only [swapEndCore] using ht
    intro he
    apply end_core_swap_ne (swapEndCore t) hs hback (by simpa [swapEndCore] using h)
    simpa only [swapEndCore] using he.symm
  · exact end_core_swap_ne t ht hs h

theorem end_free_swap_ne_of_ne (t : Parameters) (ht : ValidE t)
    (hs : ValidE (swapEndFree t)) (hne : t.x≠t.y) :
    (E t ht).schur ≠ (E (swapEndFree t) hs).schur := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact end_free_swap_ne t ht hs h
  · have hback : ValidE (swapEndFree (swapEndFree t)) := by
      simpa only [swapEndFree] using ht
    intro he
    apply end_free_swap_ne (swapEndFree t) hs hback (by simpa [swapEndFree] using h)
    simpa only [swapEndFree] using he.symm

/-- End-opening rigidity with its complete bottom edge fixed. -/
theorem end_bottom_edge_rigidity (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (hc : t.c=s.c)
    (he : (E t ht).schur=(E s hs).schur) : t=s := by
  obtain ⟨_,htau,hcore⟩ := end_first_reading t s ht hs he
  have hL : t.L=s.L := by
    rcases hcore with h | h <;> simp [Parameters.L,h.1,h.2,htau,Nat.add_comm]
  have hrows := (end_end_readings t s ht hs he).1
  rw [profile_five_rows,profile_five_rows] at hrows
  simp only [eProfile,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] at hrows
  change ({t.x}+({t.L}+({t.y}+({t.c}+{t.b}))) : Multiset ℕ) =
    {s.x}+({s.L}+({s.y}+({s.c}+{s.b}))) at hrows
  have hrows' : (({t.x}+{t.y})+({t.L}+({t.c}+{t.b})) : Multiset ℕ) =
      ({s.x}+{s.y})+({s.L}+({s.c}+{s.b})) := by
    convert hrows using 1 <;> ac_rfl
  rw [hL,hc,hb] at hrows'
  have hxy := pair_nat_reading t.x t.y s.x s.y (add_right_cancel hrows')
  rcases hxy with hxy | hxy <;> rcases hcore with hcore | hcore
  · cases t
    cases s
    simp_all
  · have hseq : s=swapEndCore t := by
      cases t
      cases s
      simp_all [swapEndCore]
    by_cases huv : t.u=t.v
    · cases t
      cases s
      simp_all [swapEndCore]
    · subst s
      exact (end_core_swap_ne_of_ne t ht hs huv he).elim
  · have hseq : s=swapEndFree t := by
      cases t
      cases s
      simp_all [swapEndFree]
    by_cases hfree : t.x=t.y
    · cases t
      cases s
      simp_all [swapEndFree]
    · subst s
      exact (end_free_swap_ne_of_ne t ht hs hfree he).elim
  · have hseq : s=swapEndBoth t := by
      cases t
      cases s
      simp_all [swapEndBoth,swapEndCore,swapEndFree]
    by_cases hd : t.x=t.y ∧ t.u=t.v
    · cases t
      cases s
      simp_all [swapEndBoth,swapEndCore,swapEndFree]
    · subst s
      have hdiff : t.x≠t.y ∨ t.u≠t.v := by tauto
      exact (end_both_swap_ne t ht hs hdiff he).elim

theorem end_endpoint_tail_eq (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (he : (E t ht).schur=(E s hs).schur) : endTail t=endTail s := by
  have htau := (end_first_reading t s ht hs he).2.1
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (end_first_marker_eq t s ht hs he)).2
  have hm := (end_marker_readings t s ht hs he).1
  have hty := ht.2.2.2.2.1
  have hsy := hs.2.2.2.2.1
  have htu := ht.1
  have hsu := hs.1
  have htv := ht.2.1
  have hsv := hs.2.1
  have htb := ht.2.2.1
  have hsb := hs.2.2.1
  have hindex : t.x+t.y+t.c-t.tau-t.a=s.x+s.y+s.c-s.tau-s.a := by
    dsimp [m] at hm
    omega
  have hh := ((E t ht).homSchur_eq_iff (E s hs)).mpr he
  rw [end_tail_split t ht,end_tail_split s hs,hindex,ha,hb,hp,hB,hm] at hh
  exact add_left_cancel hh

def endEndpointContactMax (t s : Parameters) : ℕ :=
  max (max (endTopCandidate t) (endTopCandidate s))
    (max (endRightCandidate t) (endRightCandidate s))

/-- End-opening rigidity with only its bottom endpoint fixed. -/
theorem end_endpoint_rigidity (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (he : (E t ht).schur=(E s hs).schur) : t=s := by
  have htail := end_endpoint_tail_eq t s ht hs ha hb hp he
  have hm := (end_marker_readings t s ht hs he).1
  obtain ⟨_,htau,hcore⟩ := end_first_reading t s ht hs he
  have hRt : endTopCandidate t≤endEndpointContactMax t s := by unfold endEndpointContactMax; omega
  have hRs : endTopCandidate s≤endEndpointContactMax t s := by unfold endEndpointContactMax; omega
  have hZt : endRightCandidate t≤endEndpointContactMax t s := by unfold endEndpointContactMax; omega
  have hZs : endRightCandidate s≤endEndpointContactMax t s := by unfold endEndpointContactMax; omega
  have hsome : endEndpointContactMax t s=endTopCandidate t ∨
      endEndpointContactMax t s=endTopCandidate s ∨
      endEndpointContactMax t s=endRightCandidate t ∨
      endEndpointContactMax t s=endRightCandidate s := by unfold endEndpointContactMax; omega
  have hd := congrArg (MvPolynomial.pderiv (endEndpointContactMax t s)) htail
  rw [end_tail_coefficient t ht _ hRt hZt,end_tail_coefficient s hs _ hRs hZs] at hd
  have hbt : eraseOne t.a (B t.u t.v t.tau) ≠ 0 :=
    eraseOne_ne_zero_of_coordinate_not_dvd _ _ (B_coordinate_not_dvd _ _ _ _ ht.1 ht.2.1)
  have hbs : eraseOne t.a (B s.u s.v s.tau) ≠ 0 :=
    eraseOne_ne_zero_of_coordinate_not_dvd _ _ (B_coordinate_not_dvd _ _ _ _ hs.1 hs.2.1)
  have hTt : eraseOne t.a (T t.b t.p t.c) ≠ 0 :=
    eraseOne_ne_zero_of_coordinate_not_dvd _ _
      (T_coordinate_not_dvd _ _ _ _ ht.2.2.1 (by have := ht.2.2.2.2.2; omega))
  have hTs : eraseOne t.a (T s.b s.p s.c) ≠ 0 :=
    eraseOne_ne_zero_of_coordinate_not_dvd _ _
      (T_coordinate_not_dvd _ _ _ _ hs.2.2.1 (by have := hs.2.2.2.2.2; omega))
  by_cases hR : endEndpointContactMax t s=endTopCandidate t <;>
    by_cases hR' : endEndpointContactMax t s=endTopCandidate s
  · have hty:=ht.2.2.2.2.1
    have hsy:=hs.2.2.2.2.1
    have htu:=ht.1
    have hsu:=hs.1
    have htv:=ht.2.1
    have hsv:=hs.2.1
    have htb:=ht.2.2.1
    have hsb:=hs.2.2.1
    have hc : t.c=s.c := by
      dsimp [endTopCandidate] at hR hR'
      dsimp [m] at hm
      omega
    exact end_bottom_edge_rigidity t s ht hs ha hb hp hc he
  · simp only [if_pos hR,if_neg hR'] at hd
    have hh := congrArg (eraseOne t.a) hd
    simp [apply_ite,← ha,hbt,hTt] at hh
  · simp only [if_neg hR,if_pos hR'] at hd
    have hh := congrArg (eraseOne t.a) hd
    simp [apply_ite,← ha,hbs,hTs] at hh
  · have htx : t.tau<t.x := by have hu:=ht.1; have hx:=ht.2.2.2.1; omega
    have hsx : s.tau<s.x := by have hu:=hs.1; have hx:=hs.2.2.2.1; omega
    have hFt := (F_irreducible t.v t.x t.tau ht.2.1 htx).ne_zero
    have hFs := (F_irreducible s.v s.x s.tau hs.2.1 hsx).ne_zero
    simp only [if_neg hR,if_neg hR'] at hd
    have hF : F t.v t.x t.tau=F s.v s.x s.tau := by
      by_cases hZ : endEndpointContactMax t s=endRightCandidate t <;>
        by_cases hZ' : endEndpointContactMax t s=endRightCandidate s
      · simp only [if_pos hZ,if_pos hZ',zero_sub,neg_inj,← ha,← hp] at hd
        exact mul_left_cancel₀
          (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)) hd
      · have hn := mul_ne_zero
          (mul_ne_zero (MvPolynomial.X_ne_zero t.a) (MvPolynomial.X_ne_zero t.p)) hFt
        simp only [if_pos hZ,if_neg hZ',zero_sub,neg_zero] at hd
        exact (hn (by linear_combination -hd)).elim
      · have hn := mul_ne_zero
          (mul_ne_zero (MvPolynomial.X_ne_zero s.a) (MvPolynomial.X_ne_zero s.p)) hFs
        simp only [if_neg hZ,if_pos hZ',zero_sub,neg_zero] at hd
        exact (hn (by linear_combination hd)).elim
      · rcases hsome with h | h | h | h
        · exact (hR h).elim
        · exact (hR' h).elim
        · exact (hZ h).elim
        · exact (hZ' h).elim
    have hFB : B t.v t.x t.tau=B s.v s.x s.tau := by simpa only [B_eq_F] using hF
    have hside := (quadratic_parameter_reading _ _ _ _ _ _ ht.2.1 htx hs.2.1 hsx hFB).2
    have hx0:=ht.2.2.2.1
    have hsx0:=hs.2.2.2.1
    have hpref : t.x=s.x ∧ t.u=s.u ∧ t.v=s.v := by
      rcases hcore with hcore | hcore <;> rcases hside with hside | hside <;>
        exact ⟨by omega,by omega,by omega⟩
    exact end_prefix_rigidity t s ht hs hpref.1 hpref.2.1 hpref.2.2 htau hm he

/-- Upper-corner end equality reads the ordered upper prefix. -/
theorem end_upper_prefix_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hr : deltaE t<t.q) (he : (E t ht).schur=(E s hs).schur) :
    t.x=s.x ∧ t.u=s.u ∧ t.v=s.v ∧ t.tau=s.tau := by
  have hsreg := ((end_corner_regime_reading t s ht hs he).2.1).mp hr
  obtain ⟨hend,htau,hcore⟩ := end_first_reading t s ht hs he
  have hprod : (MvPolynomial.X t.a : Gluing.HomLambda)*MvPolynomial.X t.p =
      MvPolynomial.X s.a*MvPolynomial.X s.p := by
    rcases hend with h | h <;> rw [h.1,h.2] <;> ring
  have hsecond := (end_marker_readings t s ht hs he).2.2
  rw [secondE_strict_delta t hr,secondE_strict_delta s hsreg] at hsecond
  have hside : F t.v t.x t.tau=F s.v s.x s.tau := by
    have hh : (MvPolynomial.X t.a*MvPolynomial.X t.p) * F t.v t.x t.tau =
        (MvPolynomial.X s.a*MvPolynomial.X s.p) * F s.v s.x s.tau := by
      simpa only [C25E,neg_inj] using hsecond
    rw [← hprod] at hh
    exact mul_left_cancel₀
      (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)) hh
  have htx : t.tau<t.x := by have hu:=ht.1; have hx:=ht.2.2.2.1; omega
  have hsx : s.tau<s.x := by have hu:=hs.1; have hx:=hs.2.2.2.1; omega
  have hb : B t.v t.x t.tau=B s.v s.x s.tau := by simpa only [B_eq_F] using hside
  have hsides := (quadratic_parameter_reading _ _ _ _ _ _ ht.2.1 htx hs.2.1 hsx hb).2
  have hx0:=ht.2.2.2.1
  have hsx0:=hs.2.2.2.1
  rcases hcore with hcore | hcore <;> rcases hsides with hsides | hsides <;>
    exact ⟨by omega,by omega,by omega,htau⟩

/-- At a tied end corner, the degree-one gcd and a coordinate erasure orient the endpoint. -/
theorem end_tied_endpoint_reading (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (hr : t.q=deltaE t) (he : (E t ht).schur=(E s hs).schur) :
    t.a=s.a ∧ t.b=s.b ∧ t.p=s.p := by
  have hsreg := ((end_corner_regime_reading t s ht hs he).2.2).mp hr
  have hfirst := end_first_marker_eq t s ht hs he
  have hsecond := (end_marker_readings t s ht hs he).2.2
  have hgt := E_gcd_tied t ht hr
  have hgs := E_gcd_tied s hs hsreg
  rw [hfirst,hsecond] at hgt
  have hassoc : Associated (MvPolynomial.X t.a : Gluing.HomLambda) (MvPolynomial.X s.a) :=
    hgt.symm.trans hgs
  have ha : t.a=s.a := MvPolynomial.X_dvd_X.mp hassoc.dvd
  have hend := (end_first_reading t s ht hs he).1
  have hp : t.p=s.p := by rcases hend with h | h <;> omega
  have hB := (first_marker_reading t s hs.1 hs.2.1 hfirst).2
  have hparent : endTieParenthesis t=endTieParenthesis s := by
    have htied t (h : t.q=deltaE t) :
        secondE t=-(MvPolynomial.X t.a*endTieParenthesis t) := by
      rw [secondE_tied t h]
      unfold C14 C25E endTieParenthesis
      ring
    rw [htied t hr,htied s hsreg,← ha] at hsecond
    exact mul_left_cancel₀ (MvPolynomial.X_ne_zero t.a) (neg_injective hsecond)
  have hbne : t.b ≠ t.p := by have := ht.2.2.1; omega
  have hsbne : s.b ≠ t.p := by have := hs.2.2.1; omega
  have hBne := eraseOne_ne_zero_of_coordinate_not_dvd t.p (B t.u t.v t.tau)
    (B_coordinate_not_dvd _ _ _ t.p ht.1 ht.2.1)
  have hparent' :
      MvPolynomial.X t.b*B t.u t.v t.tau + MvPolynomial.X t.p*F t.v t.x t.tau =
      MvPolynomial.X s.b*B t.u t.v t.tau + MvPolynomial.X t.p*F s.v s.x s.tau := by
    simpa only [endTieParenthesis,← hp,← hB] using hparent
  have hkill : eraseOne t.p (MvPolynomial.X t.p)=0 := by
    rw [eraseOne_X,if_pos rfl]
  have hkeepb : eraseOne t.p (MvPolynomial.X t.b)=MvPolynomial.X t.b := by
    rw [eraseOne_X,if_neg hbne]
  have hkeepsb : eraseOne t.p (MvPolynomial.X s.b)=MvPolynomial.X s.b := by
    rw [eraseOne_X,if_neg hsbne]
  have hh := congrArg (eraseOne t.p) hparent'
  simp only [map_add,map_mul,hkill,hkeepb,hkeepsb,zero_mul,add_zero] at hh
  have hX : (MvPolynomial.X t.b : Gluing.HomLambda)=MvPolynomial.X s.b :=
    mul_right_cancel₀ hBne hh
  have hdiv : (MvPolynomial.X t.b : Gluing.HomLambda) ∣ MvPolynomial.X s.b := by
    rw [← hX]
  exact ⟨ha,MvPolynomial.X_dvd_X.mp hdiv,hp⟩

/-- Equal end-opening boards, in the common orientation, have identical actual parameters. -/
theorem end_same_opening (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (he : (E t ht).schur=(E s hs).schur) : t=s := by
  rcases lt_trichotomy t.q (deltaE t) with hr | hr | hr
  · obtain ⟨ha,hb,hp,_,_⟩ := end_strict_endpoint_reading t s ht hs hr he
    exact end_endpoint_rigidity t s ht hs ha hb hp he
  · obtain ⟨ha,hb,hp⟩ := end_tied_endpoint_reading t s ht hs hr he
    exact end_endpoint_rigidity t s ht hs ha hb hp he
  · obtain ⟨hx,hu,hv,htau⟩ := end_upper_prefix_reading t s ht hs hr he
    exact end_prefix_rigidity t s ht hs hx hu hv htau (end_marker_readings t s ht hs he).1 he

def middleAProfile (t : Parameters) (ht : ValidM t) (z : ℕ) (hz : t.u<z) :
    Gluing.Profile 3 where
  r := ![z,t.L,t.c,t.b]
  g := ![t.u,t.v,t.p]
  r_pos := by
    have hu:=ht.1
    have hv:=ht.2.1
    have hb:=ht.2.2.1
    have hc:=ht.2.2.2.2.2
    intro i
    fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_castSucc := by
    have hu:=ht.1
    have hv:=ht.2.1
    have hc:=ht.2.2.2.2.2
    intro i
    fin_cases i <;> simp [Parameters.L] <;> omega
  g_lt_succ := by
    have hu:=ht.1
    have hv:=ht.2.1
    have hb:=ht.2.2.1
    have hc:=ht.2.2.2.2.2
    intro i
    fin_cases i <;> simp [Parameters.L] <;> omega

noncomputable def middleA (t : Parameters) (z : ℕ) : Gluing.HomLambda :=
  (!![MvPolynomial.X z,MvPolynomial.X (z+t.v-t.tau),
      MvPolynomial.X (z+t.c-t.tau),MvPolynomial.X (z+t.c+t.b-t.tau-t.p);
    MvPolynomial.X t.u,MvPolynomial.X t.L,MvPolynomial.X (t.u+t.c-t.tau),
      MvPolynomial.X (t.u+t.c+t.b-t.tau-t.p);
    MvPolynomial.X t.tau,MvPolynomial.X t.v,MvPolynomial.X t.c,MvPolynomial.X (t.c+t.q);
    0,0,MvPolynomial.X t.p,MvPolynomial.X t.b] : Matrix (Fin 4) (Fin 4) Gluing.HomLambda).det

theorem middleA_eq_homSchur (t : Parameters) (ht : ValidM t) (z : ℕ) (hz : t.u<z) :
    middleA t z=(middleAProfile t ht z hz).toBetaDiagram.homSchur := by
  have hu:=ht.1
  have hv:=ht.2.1
  have hb:=ht.2.2.1
  have hc:=ht.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  unfold middleA BetaDiagram.homSchur
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [BetaDiagram.homMatrix,Gluing.Profile.toBetaDiagram,middleAProfile,
      Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ,Gluing.hTilde,Parameters.q] <;>
    (try split_ifs) <;> first | rfl | omega | (congr 1 <;> omega)

theorem middleA_coordinate_not_dvd (t : Parameters) (ht : ValidM t) (z : ℕ) (hz : t.u<z) (j : ℕ) :
    ¬ (MvPolynomial.X j : Gluing.HomLambda) ∣ middleA t z := by
  rw [middleA_eq_homSchur t ht z hz]
  exact homSchur_coordinate_not_dvd _ (Gluing.Profile.toBetaDiagram_connected _) j

noncomputable def middleFirstColumnMinor (t : Parameters) : Gluing.HomLambda :=
  ((mMatrix t).submatrix (1 : Fin 5).succAbove (0 : Fin 5).succAbove).det

theorem middle_first_column_split (t : Parameters) (ht : ValidM t) :
    (M t ht).homSchur =
      MvPolynomial.X t.x*middleA t t.y -
        MvPolynomial.X t.a*middleFirstColumnMinor t := by
  have hA : ((mMatrix t).submatrix Fin.succ Fin.succ).det=middleA t t.y := by
    unfold middleA
    congr 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hfirst (i : Fin 5) : mMatrix t i 0 =
      if i=0 then MvPolynomial.X t.x else if i=1 then MvPolynomial.X t.a else 0 := by
    fin_cases i <;> simp [mMatrix]
  rw [BetaDiagram.homSchur,M_homMatrix t ht,Matrix.det_succ_column _ (0 : Fin 5)]
  simp [Fin.sum_univ_succ,hfirst,hA,middleFirstColumnMinor,sub_eq_add_neg] <;> ring

/-- A fixed middle core and bottom edge determine both free upper rows. -/
theorem middle_core_fixed_rigidity (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p) (hc : t.c=s.c)
    (hu : t.u=s.u) (hv : t.v=s.v) (htau : t.tau=s.tau)
    (he : (M t ht).schur=(M s hs).schur) : t=s := by
  have hm := (middle_marker_readings t s ht hs he).1
  have hty:=ht.2.2.2.2.1
  have hsy:=hs.2.2.2.2.1
  have htu:=ht.1
  have hsu:=hs.1
  have htv:=ht.2.1
  have hsv:=hs.2.1
  have htb:=ht.2.2.1
  have hsb:=hs.2.2.1
  have hsum : t.x+t.y=s.x+s.y := by dsimp [m] at hm; omega
  have hminor : middleFirstColumnMinor t=middleFirstColumnMinor s := by
    unfold middleFirstColumnMinor
    congr 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [mMatrix,Fin.succAbove,hsum,ha,hb,hp,hc,hu,hv,htau,hm,Parameters.L,Parameters.q]
  have hh := ((M t ht).homSchur_eq_iff (M s hs)).mpr he
  rw [middle_first_column_split t ht,middle_first_column_split s hs,hminor,ha] at hh
  have hprod : MvPolynomial.X t.x*middleA t t.y =
      MvPolynomial.X s.x*middleA s s.y := by linear_combination hh
  have hx := (coordinate_single_reading _ _ _ _
    (middleA_coordinate_not_dvd s hs s.y (by omega) t.x) hprod).1
  have hy : t.y=s.y := by omega
  cases t
  cases s
  simp_all

theorem B_not_dvd_middle_G (t : Parameters) (ht : ValidM t) :
    ¬ B t.u t.v t.tau ∣ G t.u t.tau t.b t.p t.c := by
  intro hd
  have hq := quadratic_homSchur t.u t.v t.tau ht.1 ht.2.1
  rw [← B_eq_F] at hq
  have hG := M_G_determinant t ht
  have hassoc := (B_irreducible _ _ _ ht.1 ht.2.1).associated_of_dvd
    (M_G_irreducible t ht) hd
  rw [← hq,← hG] at hassoc
  have he := homSchur_eq_of_associated _ _ hassoc
  have hdeg := congrArg MvPolynomial.totalDegree he
  rw [BetaDiagram.homSchur_totalDegree,BetaDiagram.homSchur_totalDegree] at hdeg
  omega

theorem middle_endpoint_tail_eq (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (he : (M t ht).schur=(M s hs).schur) : middleTail t=middleTail s := by
  have htau := (middle_first_reading t s ht hs he).2.1
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (middle_first_marker_eq t s ht hs he)).2
  have hm := (middle_marker_readings t s ht hs he).1
  have hty:=ht.2.2.2.2.1
  have hsy:=hs.2.2.2.2.1
  have htu:=ht.1
  have hsu:=hs.1
  have htv:=ht.2.1
  have hsv:=hs.2.1
  have htb:=ht.2.2.1
  have hsb:=hs.2.2.1
  have hindex : t.x+t.y+t.c-t.a-t.tau=s.x+s.y+s.c-s.a-s.tau := by
    dsimp [m] at hm
    omega
  have hh := ((M t ht).homSchur_eq_iff (M s hs)).mpr he
  rw [middle_tail_split t ht,middle_tail_split s hs,hindex,ha,hb,hp,hB,hm] at hh
  exact add_left_cancel hh

/-- The prime obstruction orients the core whenever both upper contacts are active. -/
theorem G_core_alignment (u v U V tau b p c d : ℕ)
    (hu : tau<u) (hv : tau<v) (hb : p<b) (hc : v+p<c) (hd : V+p<d)
    (hcore : (u=U ∧ v=V) ∨ (u=V ∧ v=U)) (hrow : d+v=c+V)
    (hdiv : B u v tau ∣ G u tau b p c-G U tau b p d) :
    u=U ∧ v=V ∧ c=d := by
  rcases hcore with ⟨rfl,rfl⟩ | ⟨hU,hV⟩
  · exact ⟨rfl,rfl,by omega⟩
  · subst V
    subst U
    by_cases huv : u=v
    · exact ⟨huv,huv.symm,by omega⟩
    · rcases lt_or_gt_of_ne huv with huv | huv
      · have hc' : c=d+v-u := by omega
        have hs : d+v-tau=c+u-tau := by omega
        have hreverse : B v u tau ∣ G v tau b p d-G u tau b p c := by
          have hh := dvd_neg.mpr hdiv
          simpa [B,Nat.add_comm,mul_comm] using hh
        have hpoly : G v tau b p d-G u tau b p c =
            MvPolynomial.X v*T b p d-MvPolynomial.X u*T b p (d+v-u) := by
          unfold G
          rw [hs,hc']
          ring
        rw [hpoly] at hreverse
        exact (B_not_dvd_T_difference v u tau b p d huv hu hb hd hreverse).elim
      · have hd' : d=c+u-v := by omega
        have hs : c+u-tau=d+v-tau := by omega
        have hpoly : G u tau b p c-G v tau b p d =
            MvPolynomial.X u*T b p c-MvPolynomial.X v*T b p (c+u-v) := by
          unfold G
          rw [← hs,hd']
          ring
        rw [hpoly] at hdiv
        exact (B_not_dvd_T_difference u v tau b p c huv hv hb hc hdiv).elim

def swapMiddleCore (t : Parameters) : Parameters := {t with u:=t.v,v:=t.u}
def swapMiddleFree (t : Parameters) : Parameters := {t with y:=t.c,c:=t.y}
def swapMiddleBoth (t : Parameters) : Parameters := swapMiddleCore (swapMiddleFree t)
def middleResidualRight (t : Parameters) : ℕ := t.u+t.c+t.b-t.tau-t.p
def middleCoreComparisonMax (t : Parameters) : ℕ :=
  max (middleTopCandidate (swapMiddleCore t)) (middleResidualRight t)

theorem middle_both_end_remainder_eq (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (hx : t.x=s.x) (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (he : (M t ht).schur=(M s hs).schur) : middleRemainder t=middleRemainder s := by
  have htau := (middle_first_reading t s ht hs he).2.1
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (middle_first_marker_eq t s ht hs he)).2
  have hm := (middle_marker_readings t s ht hs he).1
  have hty:=ht.2.2.2.2.1
  have hsy:=hs.2.2.2.2.1
  have htu:=ht.1
  have hsu:=hs.1
  have htv:=ht.2.1
  have hsv:=hs.2.1
  have htb:=ht.2.2.1
  have hsb:=hs.2.2.1
  have hsum : t.y+t.c=s.y+s.c := by dsimp [m] at hm; omega
  have h1 : t.x+t.y+t.c-t.a-t.tau=s.x+s.y+s.c-s.a-s.tau := by omega
  have h2 : t.y+t.c+t.b-t.tau-t.p=s.y+s.c+s.b-s.tau-s.p := by omega
  have h3 : t.y+t.c-t.tau=s.y+s.c-s.tau := by omega
  have hcorner : middleCornerPart t=middleCornerPart s := by
    unfold middleCornerPart
    rw [h1,h2,h3,hB,hx,ha,hb,hp,hm]
  have hh := ((M t ht).homSchur_eq_iff (M s hs)).mpr he
  rw [middle_remainder_expansion t ht,middle_remainder_expansion s hs,hcorner] at hh
  exact add_left_cancel hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem middle_core_swap_coefficient (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleCore t)) (huv : t.v<t.u) :
    MvPolynomial.pderiv (middleCoreComparisonMax t)
      (middleRemainder t-middleRemainder (swapMiddleCore t)) =
    -(if middleCoreComparisonMax t=middleTopCandidate (swapMiddleCore t) then
      MvPolynomial.X t.a*G t.v t.tau t.b t.p t.c else 0) +
    (if middleCoreComparisonMax t=middleResidualRight t then
      MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.y else 0) := by
  rw [show middleTopCandidate (swapMiddleCore t)=t.x+t.y+t.u-t.a-t.tau from rfl]
  have hu:=ht.1
  have hv:=ht.2.1
  have hb:=ht.2.2.1
  have hx:=ht.2.2.2.1
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  have hc' : t.u+t.p<t.c := hs.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : middleTopCandidate (swapMiddleCore t) ≤ middleCoreComparisonMax t := le_max_left _ _
  have hN2 : middleResidualRight t ≤ middleCoreComparisonMax t := le_max_right _ _
  dsimp [middleTopCandidate,swapMiddleCore] at hN1
  dsimp [middleResidualRight] at hN2
  have h0 : t.y+t.u-t.tau+t.x-t.a=t.x+t.y+t.u-t.a-t.tau := by omega
  have h0' : t.c+t.u-t.tau+(t.b-t.p)=middleResidualRight t := by
    dsimp [middleResidualRight]; omega
  have hq : t.y+t.x-t.a+t.v-t.tau=t.y+t.v-t.tau+t.x-t.a := by omega
  have h1 : t.y+t.x-t.a < middleCoreComparisonMax t := by omega
  have h2 : t.y+t.v-t.tau+t.x-t.a < middleCoreComparisonMax t := by omega
  have h3 : t.y+t.v-t.tau < middleCoreComparisonMax t := by omega
  have h4 : t.y+t.u-t.tau < middleCoreComparisonMax t := by omega
  have h5 : t.c+t.v-t.tau+(t.b-t.p) < middleCoreComparisonMax t := by omega
  have h6 : t.c+t.u-t.tau < middleCoreComparisonMax t := by omega
  have h7 : t.c+t.v-t.tau < middleCoreComparisonMax t := by omega
  have h8 : t.c+(t.b-t.p) < middleCoreComparisonMax t := by omega
  have h9 : t.x < middleCoreComparisonMax t := by omega
  have h10 : t.y < middleCoreComparisonMax t := by omega
  have h11 : t.c < middleCoreComparisonMax t := by omega
  have h12 : t.b < middleCoreComparisonMax t := by omega
  have h13 : t.a < middleCoreComparisonMax t := by omega
  have h14 : t.p < middleCoreComparisonMax t := by omega
  have h15 : t.u < middleCoreComparisonMax t := by omega
  have h16 : t.v < middleCoreComparisonMax t := by omega
  have h17 : t.tau < middleCoreComparisonMax t := by omega
  have h18 : t.L < middleCoreComparisonMax t := by omega
  have hLs : (swapMiddleCore t).L=t.L := by simp [swapMiddleCore,Parameters.L,Nat.add_comm]
  dsimp only [swapMiddleCore] at hLs h0 h0'
  simp only [middleRemainder,upperQuadratic,G,Q,F,T,hLs,swapMiddleCore,h0,h0',hq,
    map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  simp only [if_neg (ne_of_lt h1),if_neg (ne_of_lt h2),if_neg (ne_of_lt h3),
    if_neg (ne_of_lt h4),if_neg (ne_of_lt h5),if_neg (ne_of_lt h6),
    if_neg (ne_of_lt h7),if_neg (ne_of_lt h8),if_neg (ne_of_lt h9),
    if_neg (ne_of_lt h10),if_neg (ne_of_lt h11),if_neg (ne_of_lt h12),
    if_neg (ne_of_lt h13),if_neg (ne_of_lt h14),if_neg (ne_of_lt h15),
    if_neg (ne_of_lt h16),if_neg (ne_of_lt h17),if_neg (ne_of_lt h18),
    if_neg (ne_of_gt h1),if_neg (ne_of_gt h2),if_neg (ne_of_gt h3),
    if_neg (ne_of_gt h4),if_neg (ne_of_gt h5),if_neg (ne_of_gt h6),
    if_neg (ne_of_gt h7),if_neg (ne_of_gt h8),if_neg (ne_of_gt h9),
    if_neg (ne_of_gt h10),if_neg (ne_of_gt h11),if_neg (ne_of_gt h12),
    if_neg (ne_of_gt h13),if_neg (ne_of_gt h14),if_neg (ne_of_gt h15),
    if_neg (ne_of_gt h16),if_neg (ne_of_gt h17),if_neg (ne_of_gt h18)]
  by_cases htop : middleCoreComparisonMax t=t.x+t.y+t.u-t.a-t.tau <;>
    by_cases hright : middleCoreComparisonMax t=middleResidualRight t <;>
    simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,zero_add,add_zero,
      zero_sub,sub_zero,neg_zero,one_mul,mul_one] <;>
    (try simp only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]) <;> ring

theorem G_end_factor (s tau b p z : ℕ) (hs : tau<s) (hb : p<b) (hz : tau+p<z) :
    G s tau b p z=MvPolynomial.X b*F s z tau-MvPolynomial.X p*F s (z+(b-p)) tau := by
  have hidx : z+s-tau+(b-p)=z+(b-p)+s-tau := by omega
  unfold G T F
  rw [hidx]
  ring

theorem middle_core_swap_oriented (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleCore t)) (huv : t.v<t.u)
    (he : (M t ht).schur=(M (swapMiddleCore t) hs).schur) :
    t.a=t.p ∧ t.x=t.b ∧ t.y=t.c := by
  have hrem := middle_both_end_remainder_eq t (swapMiddleCore t) ht hs rfl rfl rfl rfl he
  have hz : MvPolynomial.pderiv (middleCoreComparisonMax t)
      (middleRemainder t-middleRemainder (swapMiddleCore t))=0 := by
    rw [hrem,sub_self,map_zero]
  rw [middle_core_swap_coefficient t ht hs huv] at hz
  have hGn : MvPolynomial.X t.a*G t.v t.tau t.b t.p t.c ≠ 0 := by
    simpa only [swapMiddleCore] using
      mul_ne_zero (MvPolynomial.X_ne_zero t.a) (M_G_irreducible (swapMiddleCore t) hs).ne_zero
  have hQn := mul_ne_zero (MvPolynomial.X_ne_zero t.p) (M_Q_irreducible t ht).ne_zero
  have hA : middleCoreComparisonMax t=middleTopCandidate (swapMiddleCore t) := by
    by_contra hn
    have hZ : middleCoreComparisonMax t=middleResidualRight t := by
      unfold middleCoreComparisonMax at hn ⊢
      omega
    have hh := hz
    simp only [if_neg hn,if_pos hZ,neg_zero,zero_add] at hh
    exact hQn hh
  have hZ : middleCoreComparisonMax t=middleResidualRight t := by
    by_contra hn
    have hh := hz
    simp only [if_pos hA,if_neg hn,add_zero,neg_eq_zero] at hh
    exact hGn hh
  have hprod : MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.y =
      MvPolynomial.X t.a*G t.v t.tau t.b t.p t.c := by
    have hh := hz
    simp only [if_pos hA,if_pos hZ] at hh
    linear_combination hh
  have hread := coordinate_single_reading _ _ _ _
    (M_G_coordinate_not_dvd (swapMiddleCore t) hs t.p) hprod
  have hap : t.a=t.p := hread.1.symm
  have hu:=ht.1
  have hv:=ht.2.1
  have hb:=ht.2.2.1
  have hx:=ht.2.2.2.1
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  have hcontact : t.y+t.x-t.a=t.c+(t.b-t.p) := by
    dsimp [middleCoreComparisonMax,middleTopCandidate,middleResidualRight,swapMiddleCore] at hA hZ
    omega
  have hQG : Q t.x t.a t.v t.tau t.y=G t.v t.tau t.b t.p t.c := by
    simpa only [swapMiddleCore] using hread.2
  rw [G_end_factor t.v t.tau t.b t.p t.c hv hb (by omega)] at hQG
  unfold Q at hQG
  rw [hcontact,hap] at hQG
  have hquad : MvPolynomial.X t.x*F t.v t.y t.tau =
      MvPolynomial.X t.b*F t.v t.c t.tau := by linear_combination hQG
  have hsingle := coordinate_single_reading _ _ _ _
    (F_coordinate_not_dvd _ _ _ t.x hv (by omega)) hquad
  have hFB : B t.v t.y t.tau=B t.v t.c t.tau := by
    simpa only [B_eq_F] using hsingle.2
  have hpair := (quadratic_parameter_reading _ _ _ _ _ _ hv (by omega) hv (by omega) hFB).2
  exact ⟨hap,hsingle.1,by rcases hpair with h | h <;> omega⟩

noncomputable def middleSurvivor (u v tau y c : ℕ) : Gluing.HomLambda :=
  MvPolynomial.X u*(MvPolynomial.X c*MvPolynomial.X (y+v-tau) -
    MvPolynomial.X y*MvPolynomial.X (c+v-tau)) -
  MvPolynomial.X v*(MvPolynomial.X c*MvPolynomial.X (y+u-tau) -
    MvPolynomial.X y*MvPolynomial.X (c+u-tau)) +
  MvPolynomial.X tau*(MvPolynomial.X (c+v-tau)*MvPolynomial.X (y+u-tau) -
    MvPolynomial.X (c+u-tau)*MvPolynomial.X (y+v-tau))

theorem middle_survivor_oriented_ne (u v tau y c : ℕ)
    (hu : v<u) (hv : tau<v) (hc : u<c) (hy : c<y) :
    middleSurvivor u v tau y c ≠ 0 := by
  have h1 : u<y+u-tau := by omega
  have h2 : v<y+u-tau := by omega
  have h3 : tau<y+u-tau := by omega
  have h4 : y<y+u-tau := by omega
  have h5 : c<y+u-tau := by omega
  have h6 : y+v-tau<y+u-tau := by omega
  have h7 : c+u-tau<y+u-tau := by omega
  have h8 : c+v-tau<y+u-tau := by omega
  have hd : MvPolynomial.pderiv (y+u-tau) (middleSurvivor u v tau y c)=-F v c tau := by
    simp [middleSurvivor,F,MvPolynomial.pderiv_mul,Pi.single_apply,
      ne_of_lt h1,ne_of_lt h2,ne_of_lt h3,ne_of_lt h4,ne_of_lt h5,
      ne_of_lt h6,ne_of_lt h7,ne_of_lt h8,
      ne_of_gt h1,ne_of_gt h2,ne_of_gt h3,ne_of_gt h4,ne_of_gt h5,
      ne_of_gt h6,ne_of_gt h7,ne_of_gt h8]
    ring
  intro hz
  rw [hz,map_zero] at hd
  exact (neg_ne_zero.mpr (F_irreducible _ _ _ hv (by omega)).ne_zero) hd.symm

theorem middle_survivor_ne (u v tau y c : ℕ)
    (hu : tau<u) (hv : tau<v) (hne : u≠v) (hcu : u<c) (hcv : v<c) (hy : c<y) :
    middleSurvivor u v tau y c ≠ 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hanti : middleSurvivor v u tau y c=-middleSurvivor u v tau y c := by
      unfold middleSurvivor
      ring
    intro hz
    apply middle_survivor_oriented_ne v u tau y c h hu hcv hy
    rw [hanti,hz,neg_zero]
  · exact middle_survivor_oriented_ne u v tau y c h hv hcu hy

def middleFreeComparisonMax (t : Parameters) : ℕ :=
  max (middleTopCandidate t) (middleResidualRight (swapMiddleFree t))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem middle_free_swap_coefficient (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleFree t)) (hyc : t.c<t.y) :
    MvPolynomial.pderiv (middleFreeComparisonMax t)
      (middleRemainder t-middleRemainder (swapMiddleFree t)) =
    (if middleFreeComparisonMax t=middleTopCandidate t then
      MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c else 0) -
    (if middleFreeComparisonMax t=middleResidualRight (swapMiddleFree t) then
      MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.c else 0) := by
  have hu:=ht.1
  have hv:=ht.2.1
  have hb:=ht.2.2.1
  have hx:=ht.2.2.2.1
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  have hc' : t.a+t.u<t.c := hs.2.2.2.2.1
  have hy' : t.v+t.p<t.y := hs.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : middleTopCandidate t ≤ middleFreeComparisonMax t := le_max_left _ _
  have hN2 : middleResidualRight (swapMiddleFree t) ≤ middleFreeComparisonMax t := le_max_right _ _
  dsimp [middleTopCandidate] at hN1
  dsimp [middleResidualRight,swapMiddleFree] at hN2
  have h0 : t.y+t.v-t.tau+t.x-t.a=middleTopCandidate t := by
    dsimp [middleTopCandidate]; omega
  have h0' : t.y+t.u-t.tau+(t.b-t.p)=middleResidualRight (swapMiddleFree t) := by
    dsimp [middleResidualRight,swapMiddleFree]; omega
  have hq : t.c+t.x-t.a+t.v-t.tau=t.c+t.v-t.tau+t.x-t.a := by omega
  have h1 : t.y+t.x-t.a < middleFreeComparisonMax t := by omega
  have h2 : t.c+t.x-t.a < middleFreeComparisonMax t := by omega
  have h3 : t.c+t.v-t.tau+t.x-t.a < middleFreeComparisonMax t := by omega
  have h4 : t.y+t.v-t.tau < middleFreeComparisonMax t := by omega
  have h5 : t.c+t.v-t.tau < middleFreeComparisonMax t := by omega
  have h6 : t.c+t.u-t.tau+(t.b-t.p) < middleFreeComparisonMax t := by omega
  have h7 : t.y+t.u-t.tau < middleFreeComparisonMax t := by omega
  have h8 : t.c+t.u-t.tau < middleFreeComparisonMax t := by omega
  have h9 : t.y+(t.b-t.p) < middleFreeComparisonMax t := by omega
  have h10 : t.c+(t.b-t.p) < middleFreeComparisonMax t := by omega
  have h11 : t.x < middleFreeComparisonMax t := by omega
  have h12 : t.y < middleFreeComparisonMax t := by omega
  have h13 : t.c < middleFreeComparisonMax t := by omega
  have h14 : t.b < middleFreeComparisonMax t := by omega
  have h15 : t.a < middleFreeComparisonMax t := by omega
  have h16 : t.p < middleFreeComparisonMax t := by omega
  have h17 : t.u < middleFreeComparisonMax t := by omega
  have h18 : t.v < middleFreeComparisonMax t := by omega
  have h19 : t.tau < middleFreeComparisonMax t := by omega
  have h20 : t.L < middleFreeComparisonMax t := by omega
  have hLs : (swapMiddleFree t).L=t.L := rfl
  dsimp only [swapMiddleFree] at hLs h0 h0'
  simp only [middleRemainder,upperQuadratic,G,Q,F,T,hLs,swapMiddleFree,h0,h0',hq,
    map_add,map_sub,map_neg,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  simp only [if_neg (ne_of_lt h1),if_neg (ne_of_lt h2),if_neg (ne_of_lt h3),
    if_neg (ne_of_lt h4),if_neg (ne_of_lt h5),if_neg (ne_of_lt h6),
    if_neg (ne_of_lt h7),if_neg (ne_of_lt h8),if_neg (ne_of_lt h9),
    if_neg (ne_of_lt h10),if_neg (ne_of_lt h11),if_neg (ne_of_lt h12),
    if_neg (ne_of_lt h13),if_neg (ne_of_lt h14),if_neg (ne_of_lt h15),
    if_neg (ne_of_lt h16),if_neg (ne_of_lt h17),if_neg (ne_of_lt h18),
    if_neg (ne_of_lt h19),if_neg (ne_of_lt h20),
    if_neg (ne_of_gt h1),if_neg (ne_of_gt h2),if_neg (ne_of_gt h3),
    if_neg (ne_of_gt h4),if_neg (ne_of_gt h5),if_neg (ne_of_gt h6),
    if_neg (ne_of_gt h7),if_neg (ne_of_gt h8),if_neg (ne_of_gt h9),
    if_neg (ne_of_gt h10),if_neg (ne_of_gt h11),if_neg (ne_of_gt h12),
    if_neg (ne_of_gt h13),if_neg (ne_of_gt h14),if_neg (ne_of_gt h15),
    if_neg (ne_of_gt h16),if_neg (ne_of_gt h17),if_neg (ne_of_gt h18),
    if_neg (ne_of_gt h19),if_neg (ne_of_gt h20)]
  by_cases htop : middleFreeComparisonMax t=middleTopCandidate t <;>
    by_cases hright : middleFreeComparisonMax t=middleResidualRight (swapMiddleFree t) <;>
    dsimp only [swapMiddleFree] at hright <;>
    simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,zero_add,add_zero,
      zero_sub,sub_zero,neg_zero,one_mul,mul_one] <;>
    simp only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] <;> ring

theorem profile_three_rows (P : Gluing.Profile 2) :
    P.rowMultiset={P.r 0,P.r 1,P.r 2} := by
  have hv : (Finset.univ : Finset (Fin 3)).val={0,1,2} := by decide
  rw [Gluing.Profile.rowMultiset,hv]
  simp

theorem middle_free_swap_oriented (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleFree t)) (hyc : t.c<t.y)
    (he : (M t ht).schur=(M (swapMiddleFree t) hs).schur) :
    t.a=t.p ∧ t.x=t.b ∧ t.u=t.v := by
  have hrem := middle_both_end_remainder_eq t (swapMiddleFree t) ht hs rfl rfl rfl rfl he
  have hz : MvPolynomial.pderiv (middleFreeComparisonMax t)
      (middleRemainder t-middleRemainder (swapMiddleFree t))=0 := by
    rw [hrem,sub_self,map_zero]
  rw [middle_free_swap_coefficient t ht hs hyc] at hz
  have hGn := mul_ne_zero (MvPolynomial.X_ne_zero t.a) (M_G_irreducible t ht).ne_zero
  have hQn : MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.c ≠ 0 := by
    simpa only [swapMiddleFree] using
      mul_ne_zero (MvPolynomial.X_ne_zero t.p) (M_Q_irreducible (swapMiddleFree t) hs).ne_zero
  have hA : middleFreeComparisonMax t=middleTopCandidate t := by
    by_contra hn
    have hZ : middleFreeComparisonMax t=middleResidualRight (swapMiddleFree t) := by
      unfold middleFreeComparisonMax at hn ⊢
      omega
    have hh := hz
    simp only [if_neg hn,if_pos hZ,zero_sub,neg_eq_zero] at hh
    exact hQn hh
  have hZ : middleFreeComparisonMax t=middleResidualRight (swapMiddleFree t) := by
    by_contra hn
    have hh := hz
    simp only [if_pos hA,if_neg hn,sub_zero] at hh
    exact hGn hh
  have hprod : MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c =
      MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.c := by
    have hh := hz
    simp only [if_pos hA,if_pos hZ] at hh
    exact sub_eq_zero.mp hh
  obtain ⟨hap,hGQ⟩ := coordinate_single_reading _ _ _ _
    (M_Q_coordinate_not_dvd (swapMiddleFree t) hs t.a) hprod
  have hpoly : (gDiagramM t ht).schur=(qDiagramM (swapMiddleFree t) hs).schur := by
    apply ((gDiagramM t ht).homSchur_eq_iff (qDiagramM (swapMiddleFree t) hs)).mp
    rw [M_G_determinant,M_Q_determinant]
    exact hGQ
  have hrows : ({t.u,t.c,t.b} : Multiset ℕ)={t.x,t.c,t.v} := by
    unfold gDiagramM qDiagramM at hpoly
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur] at hpoly
    have hh := (Gluing.Profile.rows_eq_of_schur_eq hpoly).2
    rw [profile_three_rows,profile_three_rows] at hh
    exact hh
  have hpair : ({t.u,t.b} : Multiset ℕ)={t.x,t.v} := by
    have hh := hrows
    simp only [Multiset.insert_eq_cons] at hh ⊢
    rw [Multiset.cons_swap t.u t.c,Multiset.cons_swap t.x t.c] at hh
    exact (Multiset.cons_inj_right t.c).mp hh
  rcases pair_nat_reading _ _ _ _ hpair with ⟨hux,hbv⟩ | ⟨huv,hbx⟩
  · by_cases huv : t.u=t.v
    · exact ⟨hap,by omega,huv⟩
    · have hu:=ht.1
      have hv:=ht.2.1
      have hb:=ht.2.2.1
      have hy:=ht.2.2.2.2.1
      have hc:=ht.2.2.2.2.2
      have hc' : t.a+t.u<t.c := hs.2.2.2.2.1
      have htp : t.tau=t.p := by
        rcases (gDiagramM t ht).small_rows_rigidity_same_order
          (qDiagramM (swapMiddleFree t) hs)
          (Gluing.Profile.toBetaDiagram_connected _)
          (Gluing.Profile.toBetaDiagram_connected _) (by omega) hpoly with h | h
        · obtain ⟨k,hr,hcol⟩ := h
          have hr1:=hr 1
          have hc0:=hcol 0
          norm_num [gDiagramM,qDiagramM,Gluing.Profile.toBetaDiagram,cubicProfile,
            Gluing.Profile.xi,Gluing.Profile.zeta,swapMiddleFree,Fin.sum_univ_succ] at hr1 hc0
          omega
        · obtain ⟨k,hr,hcol⟩ := h
          have hr0:=hr 0
          have hc0:=hcol 0
          norm_num [gDiagramM,qDiagramM,Gluing.Profile.toBetaDiagram,cubicProfile,
            Gluing.Profile.xi,Gluing.Profile.zeta,swapMiddleFree,Fin.sum_univ_succ,Fin.rev] at hr0 hc0
          omega
      have haτ : t.a=t.tau := by omega
      have hxp : t.x=t.u := hux.symm
      have hpt : t.p=t.tau := htp.symm
      have hshift (z : ℕ) (hz : t.tau<z) :
          z+t.v-t.tau+t.u-t.tau=z+t.u-t.tau+t.v-t.tau := by omega
      have hshift' (z : ℕ) (hz : t.tau<z) :
          z+t.u-t.tau+(t.v-t.tau)=z+t.u-t.tau+t.v-t.tau := by omega
      have hsimple (z : ℕ) (hz : t.tau<z) : z+(t.v-t.tau)=z+t.v-t.tau := by omega
      have hBS : B t.u t.v t.tau*middleSurvivor t.u t.v t.tau t.y t.c=0 := by
        unfold middleRemainder upperQuadratic T at hrem
        simp only [swapMiddleFree,hxp,hbv,haτ,hpt] at hrem
        rw [hshift t.y (by omega),hshift t.c (by omega),
          hshift' t.y (by omega),hshift' t.c (by omega),
          hsimple t.y (by omega),hsimple t.c (by omega)] at hrem
        unfold B middleSurvivor
        dsimp [Parameters.L] at hrem
        linear_combination -hrem
      have hSne := middle_survivor_ne t.u t.v t.tau t.y t.c hu hv huv (by omega) (by omega) hyc
      exact (hSne ((mul_eq_zero.mp hBS).resolve_left (B_irreducible _ _ _ hu hv).ne_zero)).elim
  · exact ⟨hap,hbx.symm,huv⟩

def middleBothComparisonMax (t : Parameters) : ℕ :=
  max (max (middleTopCandidate t) (middleTopCandidate (swapMiddleBoth t)))
    (max (middleResidualRight t) (middleResidualRight (swapMiddleBoth t)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem middle_both_swap_coefficient (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleBoth t)) :
    MvPolynomial.pderiv (middleBothComparisonMax t)
      (middleRemainder t-middleRemainder (swapMiddleBoth t)) =
    (if middleBothComparisonMax t=middleTopCandidate t then
      MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c else 0) -
    (if middleBothComparisonMax t=middleTopCandidate (swapMiddleBoth t) then
      MvPolynomial.X t.a*G t.v t.tau t.b t.p t.y else 0) +
    (if middleBothComparisonMax t=middleResidualRight t then
      MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.y else 0) -
    (if middleBothComparisonMax t=middleResidualRight (swapMiddleBoth t) then
      MvPolynomial.X t.p*Q t.x t.a t.u t.tau t.c else 0) := by
  rw [show middleTopCandidate (swapMiddleBoth t)=t.x+t.c+t.u-t.a-t.tau from rfl,
    show middleResidualRight (swapMiddleBoth t)=t.v+t.y+t.b-t.tau-t.p from rfl]
  have hu:=ht.1
  have hv:=ht.2.1
  have hb:=ht.2.2.1
  have hx:=ht.2.2.2.1
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  have hc' : t.a+t.v<t.c := hs.2.2.2.2.1
  have hy' : t.u+t.p<t.y := hs.2.2.2.2.2
  have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
  have hN1 : middleTopCandidate t ≤ middleBothComparisonMax t := by unfold middleBothComparisonMax; omega
  have hN2 : middleTopCandidate (swapMiddleBoth t) ≤ middleBothComparisonMax t := by
    unfold middleBothComparisonMax; omega
  have hN3 : middleResidualRight t ≤ middleBothComparisonMax t := by unfold middleBothComparisonMax; omega
  have hN4 : middleResidualRight (swapMiddleBoth t) ≤ middleBothComparisonMax t := by
    unfold middleBothComparisonMax; omega
  dsimp [middleTopCandidate,middleResidualRight,swapMiddleBoth,swapMiddleCore,swapMiddleFree]
    at hN1 hN2 hN3 hN4
  have h0 : t.y+t.v-t.tau+t.x-t.a=middleTopCandidate t := by dsimp [middleTopCandidate]; omega
  have h0' : t.c+t.u-t.tau+t.x-t.a=t.x+t.c+t.u-t.a-t.tau := by omega
  have h00 : t.c+t.u-t.tau+(t.b-t.p)=middleResidualRight t := by
    dsimp [middleResidualRight]; omega
  have h00' : t.y+t.v-t.tau+(t.b-t.p)=t.v+t.y+t.b-t.tau-t.p := by omega
  have hq : t.y+t.x-t.a+t.v-t.tau=t.y+t.v-t.tau+t.x-t.a := by omega
  have hq' : t.c+t.x-t.a+t.u-t.tau=t.c+t.u-t.tau+t.x-t.a := by omega
  have h1 : t.y+t.x-t.a < middleBothComparisonMax t := by omega
  have h2 : t.c+t.x-t.a < middleBothComparisonMax t := by omega
  have h3 : t.y+t.v-t.tau < middleBothComparisonMax t := by omega
  have h4 : t.c+t.u-t.tau < middleBothComparisonMax t := by omega
  have h5 : t.y+(t.b-t.p) < middleBothComparisonMax t := by omega
  have h6 : t.c+(t.b-t.p) < middleBothComparisonMax t := by omega
  have h7 : t.x < middleBothComparisonMax t := by omega
  have h8 : t.y < middleBothComparisonMax t := by omega
  have h9 : t.c < middleBothComparisonMax t := by omega
  have h10 : t.b < middleBothComparisonMax t := by omega
  have h11 : t.a < middleBothComparisonMax t := by omega
  have h12 : t.p < middleBothComparisonMax t := by omega
  have h13 : t.u < middleBothComparisonMax t := by omega
  have h14 : t.v < middleBothComparisonMax t := by omega
  have h15 : t.tau < middleBothComparisonMax t := by omega
  have h16 : t.L < middleBothComparisonMax t := by omega
  have hLs : (swapMiddleBoth t).L=t.L := by
    simp [swapMiddleBoth,swapMiddleCore,swapMiddleFree,Parameters.L,Nat.add_comm]
  dsimp only [swapMiddleBoth,swapMiddleCore,swapMiddleFree] at hLs h0 h0' h00 h00'
  simp only [middleRemainder,upperQuadratic,G,Q,F,T,hLs,swapMiddleBoth,swapMiddleCore,
    swapMiddleFree,h0,h0',h00,h00',hq,hq',map_add,map_sub,map_neg,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  simp only [if_neg (ne_of_lt h1),if_neg (ne_of_lt h2),if_neg (ne_of_lt h3),
    if_neg (ne_of_lt h4),if_neg (ne_of_lt h5),if_neg (ne_of_lt h6),
    if_neg (ne_of_lt h7),if_neg (ne_of_lt h8),if_neg (ne_of_lt h9),
    if_neg (ne_of_lt h10),if_neg (ne_of_lt h11),if_neg (ne_of_lt h12),
    if_neg (ne_of_lt h13),if_neg (ne_of_lt h14),if_neg (ne_of_lt h15),
    if_neg (ne_of_lt h16),if_neg (ne_of_gt h1),if_neg (ne_of_gt h2),
    if_neg (ne_of_gt h3),if_neg (ne_of_gt h4),if_neg (ne_of_gt h5),
    if_neg (ne_of_gt h6),if_neg (ne_of_gt h7),if_neg (ne_of_gt h8),
    if_neg (ne_of_gt h9),if_neg (ne_of_gt h10),if_neg (ne_of_gt h11),
    if_neg (ne_of_gt h12),if_neg (ne_of_gt h13),if_neg (ne_of_gt h14),
    if_neg (ne_of_gt h15),if_neg (ne_of_gt h16)]
  by_cases htop : middleBothComparisonMax t=middleTopCandidate t <;>
    by_cases htop' : middleBothComparisonMax t=t.x+t.c+t.u-t.a-t.tau <;>
    by_cases hright : middleBothComparisonMax t=middleResidualRight t <;>
    by_cases hright' : middleBothComparisonMax t=t.v+t.y+t.b-t.tau-t.p <;>
    simp (disch := omega) only [if_pos,if_neg,zero_mul,mul_zero,zero_add,add_zero,
      zero_sub,sub_zero,neg_zero,one_mul,mul_one] <;>
    (try simp only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]) <;> ring

theorem middle_both_G_reading (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleBoth t))
    (he : G t.u t.tau t.b t.p t.c=G t.v t.tau t.b t.p t.y) :
    t.u=t.v ∧ t.y=t.c := by
  have hh : (gDiagramM t ht).schur=(gDiagramM (swapMiddleBoth t) hs).schur := by
    apply ((gDiagramM t ht).homSchur_eq_iff (gDiagramM (swapMiddleBoth t) hs)).mp
    rw [M_G_determinant,M_G_determinant]
    exact he
  unfold gDiagramM at hh
  rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur] at hh
  have hrows := (Gluing.Profile.rows_eq_of_schur_eq hh).2
  rw [profile_three_rows,profile_three_rows] at hrows
  change ({t.u,t.c,t.b} : Multiset ℕ)={t.v,t.y,t.b} at hrows
  have hp : ({t.u,t.c} : Multiset ℕ)={t.v,t.y} := by
    exact multiset_cancel_last t.u t.c t.b t.v t.y hrows
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  rcases pair_nat_reading _ _ _ _ hp with h | h
  · exact ⟨h.1,h.2.symm⟩
  · omega

theorem middle_both_Q_reading (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleBoth t))
    (he : Q t.x t.a t.v t.tau t.y=Q t.x t.a t.u t.tau t.c) :
    t.u=t.v ∧ t.y=t.c := by
  have hh : (qDiagramM t ht).schur=(qDiagramM (swapMiddleBoth t) hs).schur := by
    apply ((qDiagramM t ht).homSchur_eq_iff (qDiagramM (swapMiddleBoth t) hs)).mp
    rw [M_Q_determinant,M_Q_determinant]
    exact he
  unfold qDiagramM at hh
  rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur] at hh
  have hrows := (Gluing.Profile.rows_eq_of_schur_eq hh).2
  rw [profile_three_rows,profile_three_rows] at hrows
  change ({t.x,t.y,t.v} : Multiset ℕ)={t.x,t.c,t.u} at hrows
  have hp := (Multiset.cons_inj_right t.x).mp hrows
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  rcases pair_nat_reading _ _ _ _ hp with h | h
  · exact ⟨h.2.symm,h.1⟩
  · omega

noncomputable def middleEndpointFactor (t : Parameters) : Gluing.HomLambda :=
  MvPolynomial.X t.a*MvPolynomial.X t.b-MvPolynomial.X t.p*MvPolynomial.X t.x

theorem middle_contact_factor (t : Parameters) (ht : ValidM t) (s z : ℕ)
    (hs : t.tau<s) (hz : t.tau+t.p<z) (hd : deltaM t=t.q) :
    MvPolynomial.X t.a*G s t.tau t.b t.p z -
      MvPolynomial.X t.p*Q t.x t.a s t.tau z=middleEndpointFactor t*F s z t.tau := by
  have hx:=ht.2.2.2.1
  have hb:=ht.2.2.1
  have harg : z+t.x-t.a=z+(t.b-t.p) := by
    dsimp [deltaM,Parameters.q] at hd
    omega
  rw [G_end_factor _ _ _ _ _ hs hb hz]
  unfold Q middleEndpointFactor
  rw [harg]
  ring

theorem middle_endpoint_factor_reading (t : Parameters) (ht : ValidM t)
    (he : middleEndpointFactor t=0) : t.a=t.p ∧ t.x=t.b := by
  have hp := variable_product_reading _ _ _ _ (sub_eq_zero.mp he)
  have hx:=ht.2.2.2.1
  rcases hp with hp | hp
  · exact ⟨hp.1,hp.2.symm⟩
  · omega

/-- Double interchange has only the unchanged and half-turn middle-opening outcomes. -/
theorem middle_both_swap_reading (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleBoth t))
    (he : (M t ht).schur=(M (swapMiddleBoth t) hs).schur) :
    (t.u=t.v ∧ t.y=t.c) ∨ (t.a=t.p ∧ t.x=t.b) := by
  have hrem := middle_both_end_remainder_eq t (swapMiddleBoth t) ht hs rfl rfl rfl rfl he
  have hz : MvPolynomial.pderiv (middleBothComparisonMax t)
      (middleRemainder t-middleRemainder (swapMiddleBoth t))=0 := by
    rw [hrem,sub_self,map_zero]
  rw [middle_both_swap_coefficient t ht hs] at hz
  have hu:=ht.1
  have hv:=ht.2.1
  have hb:=ht.2.2.1
  have hx:=ht.2.2.2.1
  have hy:=ht.2.2.2.2.1
  have hc:=ht.2.2.2.2.2
  have hc' : t.a+t.v<t.c := hs.2.2.2.2.1
  have hy' : t.u+t.p<t.y := hs.2.2.2.2.2
  let h := t.y+t.v-t.tau
  let k := t.c+t.u-t.tau
  let d := deltaM t
  let q := t.q
  have hRt : middleTopCandidate t=h+d := by dsimp [middleTopCandidate,h,d,deltaM]; omega
  have hRs : middleTopCandidate (swapMiddleBoth t)=k+d := by
    dsimp [middleTopCandidate,swapMiddleBoth,swapMiddleCore,swapMiddleFree,k,d,deltaM]; omega
  have hSt : middleResidualRight t=k+q := by
    dsimp [middleResidualRight,k,q,Parameters.q]; omega
  have hSs : middleResidualRight (swapMiddleBoth t)=h+q := by
    dsimp [middleResidualRight,swapMiddleBoth,swapMiddleCore,swapMiddleFree,h,q,Parameters.q]; omega
  have hN : middleBothComparisonMax t=max h k+max d q := by
    unfold middleBothComparisonMax
    rw [hRt,hRs,hSt,hSs]
    omega
  simp only [hRt,hRs,hSt,hSs,hN] at hz
  have hG1 := mul_ne_zero (MvPolynomial.X_ne_zero t.a) (M_G_irreducible t ht).ne_zero
  have hG2 := mul_ne_zero (MvPolynomial.X_ne_zero t.a)
    (M_G_irreducible (swapMiddleBoth t) hs).ne_zero
  have hQ1 := mul_ne_zero (MvPolynomial.X_ne_zero t.p) (M_Q_irreducible t ht).ne_zero
  have hQ2 := mul_ne_zero (MvPolynomial.X_ne_zero t.p)
    (M_Q_irreducible (swapMiddleBoth t) hs).ne_zero
  dsimp only [swapMiddleBoth,swapMiddleCore,swapMiddleFree] at hG2 hQ2
  have hfactor_c (hdq : d=q) :
      MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c -
        MvPolynomial.X t.p*Q t.x t.a t.u t.tau t.c =
        middleEndpointFactor t*F t.u t.c t.tau :=
    middle_contact_factor t ht t.u t.c hu (by omega) hdq
  have hfactor_y (hdq : d=q) :
      MvPolynomial.X t.a*G t.v t.tau t.b t.p t.y -
        MvPolynomial.X t.p*Q t.x t.a t.v t.tau t.y =
        middleEndpointFactor t*F t.v t.y t.tau :=
    middle_contact_factor t ht t.v t.y hv (by omega) hdq
  have hDc (hh : middleEndpointFactor t*F t.u t.c t.tau=0) :
      (t.u=t.v ∧ t.y=t.c) ∨ (t.a=t.p ∧ t.x=t.b) := by
    exact Or.inr (middle_endpoint_factor_reading t ht
      ((mul_eq_zero.mp hh).resolve_right (F_irreducible _ _ _ hu (by omega)).ne_zero))
  have hDy (hh : middleEndpointFactor t*F t.v t.y t.tau=0) :
      (t.u=t.v ∧ t.y=t.c) ∨ (t.a=t.p ∧ t.x=t.b) := by
    exact Or.inr (middle_endpoint_factor_reading t ht
      ((mul_eq_zero.mp hh).resolve_right (F_irreducible _ _ _ hv (by omega)).ne_zero))
  rcases lt_trichotomy h k with hhk | hhk | hhk <;>
    rcases lt_trichotomy d q with hdq | hdq | hdq
  all_goals simp (disch := omega) only [if_pos,if_neg] at hz
  · exact (hQ1 (by linear_combination hz)).elim
  · apply hDy
    rw [← hfactor_y hdq]
    linear_combination -hz
  · exact (hG2 (by linear_combination -hz)).elim
  · have hQ : Q t.x t.a t.v t.tau t.y=Q t.x t.a t.u t.tau t.c := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.p)
      linear_combination hz
    exact Or.inl (middle_both_Q_reading t ht hs hQ)
  · have hshift : t.c+t.u-t.tau=t.y+t.v-t.tau := by dsimp [h,k] at hhk; omega
    have hfc := hfactor_c hdq
    have hfy := hfactor_y hdq
    have hFdiff : F t.u t.c t.tau-F t.v t.y t.tau =
        MvPolynomial.X t.u*MvPolynomial.X t.c-MvPolynomial.X t.v*MvPolynomial.X t.y := by
      unfold F
      rw [hshift]
      ring
    have hprod : middleEndpointFactor t *
        (MvPolynomial.X t.u*MvPolynomial.X t.c-MvPolynomial.X t.v*MvPolynomial.X t.y)=0 := by
      rw [← hFdiff]
      linear_combination hz-hfc+hfy
    rcases mul_eq_zero.mp hprod with hD | hsmall
    · exact Or.inr (middle_endpoint_factor_reading t ht hD)
    · have hpair := variable_product_reading _ _ _ _ (sub_eq_zero.mp hsmall)
      rcases hpair with hpair | hpair
      · exact Or.inl ⟨hpair.1,hpair.2.symm⟩
      · omega
  · have hG : G t.u t.tau t.b t.p t.c=G t.v t.tau t.b t.p t.y := by
      apply mul_left_cancel₀ (MvPolynomial.X_ne_zero t.a)
      linear_combination hz
    exact Or.inl (middle_both_G_reading t ht hs hG)
  · exact (hQ2 (by linear_combination -hz)).elim
  · apply hDc
    rw [← hfactor_c hdq]
    linear_combination hz
  · exact (hG1 (by linear_combination hz)).elim

theorem middle_core_swap_reading (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleCore t))
    (he : (M t ht).schur=(M (swapMiddleCore t) hs).schur) :
    t.u=t.v ∨ (t.a=t.p ∧ t.x=t.b ∧ t.y=t.c) := by
  by_cases huv : t.u=t.v
  · exact Or.inl huv
  · apply Or.inr
    rcases lt_or_gt_of_ne huv with huv | huv
    · have hback : ValidM (swapMiddleCore (swapMiddleCore t)) := by
        simpa only [swapMiddleCore] using ht
      have hr := middle_core_swap_oriented (swapMiddleCore t) hs hback
        (by simpa [swapMiddleCore] using huv)
        (by simpa only [swapMiddleCore] using he.symm)
      exact hr
    · exact middle_core_swap_oriented t ht hs huv he

theorem middle_free_swap_reading (t : Parameters) (ht : ValidM t)
    (hs : ValidM (swapMiddleFree t))
    (he : (M t ht).schur=(M (swapMiddleFree t) hs).schur) :
    t.y=t.c ∨ (t.a=t.p ∧ t.x=t.b ∧ t.u=t.v) := by
  by_cases hyc : t.y=t.c
  · exact Or.inl hyc
  · apply Or.inr
    rcases lt_or_gt_of_ne hyc with hyc | hyc
    · have hback : ValidM (swapMiddleFree (swapMiddleFree t)) := by
        simpa only [swapMiddleFree] using ht
      have hr := middle_free_swap_oriented (swapMiddleFree t) hs hback
        (by simpa [swapMiddleFree] using hyc)
        (by simpa only [swapMiddleFree] using he.symm)
      exact hr
    · exact middle_free_swap_oriented t ht hs hyc he

def MiddleClass (t s : Parameters) : Prop := t=s ∨ s=rotateMiddle t

/-- Middle-opening rigidity with both actual endpoints fixed. -/
theorem middle_both_end_rigidity (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (hx : t.x=s.x) (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (he : (M t ht).schur=(M s hs).schur) : MiddleClass t s := by
  obtain ⟨_,htau,hcore⟩ := middle_first_reading t s ht hs he
  have hL : t.L=s.L := by
    rcases hcore with h | h <;> simp [Parameters.L,h.1,h.2,htau,Nat.add_comm]
  have hrows := (middle_middle_readings t s ht hs he).1
  rw [profile_five_rows,profile_five_rows] at hrows
  simp only [mProfile,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] at hrows
  change ({t.x}+({t.y}+({t.L}+({t.c}+{t.b}))) : Multiset ℕ) =
    {s.x}+({s.y}+({s.L}+({s.c}+{s.b}))) at hrows
  have hrows' : (({t.y}+{t.c})+({t.x}+({t.L}+{t.b})) : Multiset ℕ) =
      ({s.y}+{s.c})+({s.x}+({s.L}+{s.b})) := by
    convert hrows using 1 <;> ac_rfl
  rw [hx,hL,hb] at hrows'
  have hfree := pair_nat_reading t.y t.c s.y s.c (add_right_cancel hrows')
  rcases hfree with hfree | hfree <;> rcases hcore with hcore | hcore
  · apply Or.inl
    cases t
    cases s
    simp_all
  · have hseq : s=swapMiddleCore t := by
      cases t
      cases s
      simp_all [swapMiddleCore]
    subst s
    rcases middle_core_swap_reading t ht hs he with h | h
    · apply Or.inl
      cases t
      simp_all [swapMiddleCore]
    · apply Or.inr
      cases t
      simp_all [swapMiddleCore,rotateMiddle]
  · have hseq : s=swapMiddleFree t := by
      cases t
      cases s
      simp_all [swapMiddleFree]
    subst s
    rcases middle_free_swap_reading t ht hs he with h | h
    · apply Or.inl
      cases t
      simp_all [swapMiddleFree]
    · apply Or.inr
      cases t
      simp_all [swapMiddleFree,rotateMiddle]
  · have hseq : s=swapMiddleBoth t := by
      cases t
      cases s
      simp_all [swapMiddleBoth,swapMiddleCore,swapMiddleFree]
    subst s
    rcases middle_both_swap_reading t ht hs he with h | h
    · apply Or.inl
      rcases h with ⟨huv,hyc⟩
      cases t with
      | mk x y c b a u v p tau =>
        change u=v at huv
        change y=c at hyc
        subst v
        subst c
        rfl
    · apply Or.inr
      rcases h with ⟨hap,hxb⟩
      cases t with
      | mk x y c b a u v p tau =>
        change a=p at hap
        change x=b at hxb
        subst p
        subst b
        rfl

def middleEndpointContactMax (t s : Parameters) : ℕ :=
  max (max (middleTopCandidate t) (middleTopCandidate s))
    (max (middleRightCandidate t) (middleRightCandidate s))

/-- Middle-opening rigidity with only its actual bottom endpoint fixed. -/
theorem middle_endpoint_rigidity (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (ha : t.a=s.a) (hb : t.b=s.b) (hp : t.p=s.p)
    (he : (M t ht).schur=(M s hs).schur) : MiddleClass t s := by
  have htail := middle_endpoint_tail_eq t s ht hs ha hb hp he
  have hm := (middle_marker_readings t s ht hs he).1
  obtain ⟨_,htau,hcore⟩ := middle_first_reading t s ht hs he
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (middle_first_marker_eq t s ht hs he)).2
  have hRt : middleTopCandidate t ≤ middleEndpointContactMax t s := by unfold middleEndpointContactMax; omega
  have hRs : middleTopCandidate s ≤ middleEndpointContactMax t s := by unfold middleEndpointContactMax; omega
  have hZt : middleRightCandidate t ≤ middleEndpointContactMax t s := by unfold middleEndpointContactMax; omega
  have hZs : middleRightCandidate s ≤ middleEndpointContactMax t s := by unfold middleEndpointContactMax; omega
  have hsome : middleEndpointContactMax t s=middleTopCandidate t ∨
      middleEndpointContactMax t s=middleTopCandidate s ∨
      middleEndpointContactMax t s=middleRightCandidate t ∨
      middleEndpointContactMax t s=middleRightCandidate s := by unfold middleEndpointContactMax; omega
  have hd := congrArg (MvPolynomial.pderiv (middleEndpointContactMax t s)) htail
  rw [middle_tail_coefficient t ht _ hRt hZt,middle_tail_coefficient s hs _ hRs hZs] at hd
  have hdivt : B t.u t.v t.tau ∣
      (if middleEndpointContactMax t s=middleRightCandidate t then
        MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau else 0) := by
    split_ifs
    · exact ⟨MvPolynomial.X t.x*MvPolynomial.X t.p,by ring⟩
    · exact dvd_zero _
  have hdivs : B t.u t.v t.tau ∣
      (if middleEndpointContactMax t s=middleRightCandidate s then
        MvPolynomial.X s.x*MvPolynomial.X s.p*B s.u s.v s.tau else 0) := by
    rw [hB]
    split_ifs
    · exact ⟨MvPolynomial.X s.x*MvPolynomial.X s.p,by ring⟩
    · exact dvd_zero _
  by_cases hR : middleEndpointContactMax t s=middleTopCandidate t <;>
    by_cases hR' : middleEndpointContactMax t s=middleTopCandidate s
  · have htop : B t.u t.v t.tau ∣
        MvPolynomial.X t.a*(G t.u t.tau t.b t.p t.c-G s.u s.tau s.b s.p s.c) := by
      have heq : MvPolynomial.X t.a*(G t.u t.tau t.b t.p t.c-G s.u s.tau s.b s.p s.c) =
          (if middleEndpointContactMax t s=middleRightCandidate t then
            MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau else 0) -
          (if middleEndpointContactMax t s=middleRightCandidate s then
            MvPolynomial.X s.x*MvPolynomial.X s.p*B s.u s.v s.tau else 0) := by
        simp only [if_pos hR,if_pos hR',← ha] at hd
        linear_combination hd
      rw [heq]
      exact dvd_sub hdivt hdivs
    have hdiff : B t.u t.v t.tau ∣
        G t.u t.tau t.b t.p t.c-G s.u s.tau s.b s.p s.c :=
      ((B_irreducible _ _ _ ht.1 ht.2.1).prime.dvd_mul.mp htop).resolve_left
        (B_not_dvd_X _ _ _ _ ht.1 ht.2.1)
    rw [← htau,← hb,← hp] at hdiff
    have hty:=ht.2.2.2.2.1
    have hsy:=hs.2.2.2.2.1
    have htu:=ht.1
    have hsu:=hs.1
    have htv:=ht.2.1
    have hsv:=hs.2.1
    have htb:=ht.2.2.1
    have hsb:=hs.2.2.1
    have hrow : s.c+t.v=t.c+s.v := by
      dsimp [m] at hm
      dsimp [middleTopCandidate] at hR hR'
      omega
    obtain ⟨hu,hv,hc⟩ := G_core_alignment _ _ _ _ _ _ _ _ _
      ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.2.2 (by have := hs.2.2.2.2.2; omega) hcore hrow hdiff
    exact Or.inl (middle_core_fixed_rigidity t s ht hs ha hb hp hc hu hv htau he)
  · have htop : B t.u t.v t.tau ∣ MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c := by
      have heq : MvPolynomial.X t.a*G t.u t.tau t.b t.p t.c =
          (if middleEndpointContactMax t s=middleRightCandidate t then
            MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau else 0) -
          (if middleEndpointContactMax t s=middleRightCandidate s then
            MvPolynomial.X s.x*MvPolynomial.X s.p*B s.u s.v s.tau else 0) := by
        simp only [if_pos hR,if_neg hR',zero_sub] at hd
        linear_combination hd
      rw [heq]
      exact dvd_sub hdivt hdivs
    rcases (B_irreducible _ _ _ ht.1 ht.2.1).prime.dvd_mul.mp htop with h | h
    · exact (B_not_dvd_X _ _ _ _ ht.1 ht.2.1 h).elim
    · exact (B_not_dvd_middle_G t ht h).elim
  · have htop : B s.u s.v s.tau ∣ MvPolynomial.X s.a*G s.u s.tau s.b s.p s.c := by
      rw [← hB]
      have heq : MvPolynomial.X s.a*G s.u s.tau s.b s.p s.c =
          (if middleEndpointContactMax t s=middleRightCandidate s then
            MvPolynomial.X s.x*MvPolynomial.X s.p*B s.u s.v s.tau else 0) -
          (if middleEndpointContactMax t s=middleRightCandidate t then
            MvPolynomial.X t.x*MvPolynomial.X t.p*B t.u t.v t.tau else 0) := by
        simp only [if_neg hR,if_pos hR',zero_sub] at hd
        linear_combination -hd
      rw [heq]
      exact dvd_sub hdivs hdivt
    rcases (B_irreducible _ _ _ hs.1 hs.2.1).prime.dvd_mul.mp htop with h | h
    · exact (B_not_dvd_X _ _ _ _ hs.1 hs.2.1 h).elim
    · exact (B_not_dvd_middle_G s hs h).elim
  · have hBnt := (B_irreducible _ _ _ ht.1 ht.2.1).ne_zero
    have hBns := (B_irreducible _ _ _ hs.1 hs.2.1).ne_zero
    simp only [if_neg hR,if_neg hR'] at hd
    have hx : t.x=s.x := by
      by_cases hZ : middleEndpointContactMax t s=middleRightCandidate t <;>
        by_cases hZ' : middleEndpointContactMax t s=middleRightCandidate s
      · simp only [if_pos hZ,if_pos hZ',zero_sub,neg_inj,← hp,← hB] at hd
        have hX : (MvPolynomial.X t.x : Gluing.HomLambda)=MvPolynomial.X s.x := by
          apply mul_right_cancel₀ (mul_ne_zero (MvPolynomial.X_ne_zero t.p) hBnt)
          simpa only [mul_assoc] using hd
        exact MvPolynomial.X_dvd_X.mp (by rw [← hX])
      · have hn := mul_ne_zero
          (mul_ne_zero (MvPolynomial.X_ne_zero t.x) (MvPolynomial.X_ne_zero t.p)) hBnt
        simp only [if_pos hZ,if_neg hZ',zero_sub,neg_zero] at hd
        exact (hn (by linear_combination -hd)).elim
      · have hn := mul_ne_zero
          (mul_ne_zero (MvPolynomial.X_ne_zero s.x) (MvPolynomial.X_ne_zero s.p)) hBns
        simp only [if_neg hZ,if_pos hZ',zero_sub,neg_zero] at hd
        exact (hn (by linear_combination hd)).elim
      · rcases hsome with h | h | h | h
        · exact (hR h).elim
        · exact (hR' h).elim
        · exact (hZ h).elim
        · exact (hZ' h).elim
    exact middle_both_end_rigidity t s ht hs hx ha hb hp he

theorem rotateMiddle_involutive (t : Parameters) : rotateMiddle (rotateMiddle t)=t := by
  cases t
  rfl

theorem middle_class_rotate_left (t s : Parameters) (h : MiddleClass (rotateMiddle t) s) :
    MiddleClass t s := by
  rcases h with h | h
  · exact Or.inr h.symm
  · exact Or.inl (by simpa only [rotateMiddle_involutive] using h.symm)

theorem middle_class_rotate_right (t s : Parameters) (h : MiddleClass t (rotateMiddle s)) :
    MiddleClass t s := by
  rcases h with h | h
  · exact Or.inr (by simpa only [rotateMiddle_involutive] using (congrArg rotateMiddle h).symm)
  · exact Or.inl (by simpa only [rotateMiddle_involutive] using (congrArg rotateMiddle h).symm)

theorem middle_class_of_oriented (t s t' s' : Parameters)
    (ht : t'=t ∨ t'=rotateMiddle t) (hs : s'=s ∨ s'=rotateMiddle s)
    (h : MiddleClass t' s') : MiddleClass t s := by
  rcases ht with ht | ht <;> rcases hs with hs | hs
  · rw [ht,hs] at h
    exact h
  · rw [ht,hs] at h
    exact middle_class_rotate_right t s h
  · rw [ht,hs] at h
    exact middle_class_rotate_left t s h
  · rw [ht,hs] at h
    exact middle_class_rotate_left t s (middle_class_rotate_right (rotateMiddle t) s h)

theorem middle_weak_orientation (t : Parameters) (ht : ValidM t) :
    ∃ t', ∃ ht' : ValidM t', (t'=t ∨ t'=rotateMiddle t) ∧
      t'.q≤deltaM t' ∧ (M t' ht').schur=(M t ht).schur := by
  by_cases hq : t.q≤deltaM t
  · exact ⟨t,ht,Or.inl rfl,hq,rfl⟩
  · refine ⟨rotateMiddle t,rotateMiddle_valid t ht,Or.inr rfl,?_,rotateMiddle_schur t ht⟩
    change t.x-t.a≤t.b-t.p
    dsimp [deltaM,Parameters.q] at hq
    omega

theorem middle_tie_reading (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (he : (M t ht).schur=(M s hs).schur) :
    t.q=deltaM t ↔ s.q=deltaM s := by
  have hsecond := (middle_marker_readings t s ht hs he).2.2
  have hB := (first_marker_reading t s hs.1 hs.2.1
    (middle_first_marker_eq t s ht hs he)).2
  rw [secondM_factor,secondM_factor,← hB] at hsecond
  have hquot := mul_left_cancel₀ (B_irreducible _ _ _ ht.1 ht.2.1).ne_zero hsecond
  have hv := congrArg (MvPolynomial.eval (fun _ : ℕ => (1 : ℚ))) hquot
  rw [middleSecondQuotient_eval_one,middleSecondQuotient_eval_one] at hv
  by_cases hqt : t.q=deltaM t <;> by_cases hqs : s.q=deltaM s <;>
    simp_all

/-- The unrestricted middle comparison after both half-turn orientations are chosen. -/
theorem middle_oriented_rigidity (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (hqt : t.q≤deltaM t) (hqs : s.q≤deltaM s)
    (he : (M t ht).schur=(M s hs).schur) : MiddleClass t s := by
  obtain ⟨hm,hn,hsecond⟩ := middle_marker_readings t s ht hs he
  obtain ⟨hend,htau,hcore⟩ := middle_first_reading t s ht hs he
  have htie := middle_tie_reading t s ht hs he
  by_cases htt : t.q=deltaM t
  · have hst := htie.mp htt
    have hty:=ht.2.2.2.2.1
    have hsy:=hs.2.2.2.2.1
    have htu:=ht.1
    have hsu:=hs.1
    have htv:=ht.2.1
    have hsv:=hs.2.1
    have htb:=ht.2.2.1
    have hsb:=hs.2.2.1
    have htx:=ht.2.2.2.1
    have hsx:=hs.2.2.2.1
    have htc:=ht.2.2.2.2.2
    have hsc:=hs.2.2.2.2.2
    have hqmt : t.q ≤ m t := by dsimp [m,Parameters.q]; omega
    have hqms : s.q ≤ m s := by dsimp [m,Parameters.q]; omega
    have hNt : NM t=m t-t.q := by simp only [NM,min_eq_left hqt]
    have hNs : NM s=m s-s.q := by simp only [NM,min_eq_left hqs]
    rw [hNt,hNs] at hn
    have hqeq : t.q=s.q := by omega
    have hxt : t.x=t.a+t.q := by dsimp only [Parameters.q,deltaM] at htt ⊢; omega
    have hxs : s.x=s.a+s.q := by dsimp only [Parameters.q,deltaM] at hst ⊢; omega
    have hbt : t.b=t.p+t.q := by dsimp [Parameters.q]; omega
    have hbs : s.b=s.p+s.q := by dsimp [Parameters.q]; omega
    rcases hend with h | h
    · exact middle_both_end_rigidity t s ht hs (by omega) h.1 (by omega) h.2 he
    · have hsr := rotateMiddle_valid s hs
      have he' : (M t ht).schur=(M (rotateMiddle s) hsr).schur :=
        he.trans (rotateMiddle_schur s hs).symm
      have hr := middle_both_end_rigidity t (rotateMiddle s) ht hsr
        (by change t.x=s.b; omega) h.1
        (by change t.b=s.x; omega) h.2 he'
      exact middle_class_rotate_right t s hr
  · have hst : s.q ≠ deltaM s := by tauto
    have hrt : t.q<deltaM t := by omega
    have hrs : s.q<deltaM s := by omega
    rw [secondM_strict_q t hrt,secondM_strict_q s hrs] at hsecond
    have hsecond' : MvPolynomial.X t.a*MvPolynomial.X t.b*B t.u t.v t.tau =
        MvPolynomial.X s.a*MvPolynomial.X s.b*B s.u s.v s.tau := by
      simpa only [C14,neg_inj] using hsecond
    obtain ⟨ha,hb,hp,_,_⟩ := strict_two_marker_reading t s ht.1 ht.2.1 ht.2.2.1
      hs.1 hs.2.1 hs.2.2.1 (middle_first_marker_eq t s ht hs he) hsecond'
    exact middle_endpoint_rigidity t s ht hs ha hb hp he

/-- Equal middle-opening boards are identical or actual half-turns, with no endpoint assumptions. -/
theorem middle_same_opening (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (he : (M t ht).schur=(M s hs).schur) : MiddleClass t s := by
  obtain ⟨t',ht',hott,hqt,het⟩ := middle_weak_orientation t ht
  obtain ⟨s',hs',hoss,hqs,hes⟩ := middle_weak_orientation s hs
  have he' : (M t' ht').schur=(M s' hs').schur := het.trans (he.trans hes.symm)
  exact middle_class_of_oriented t s t' s' hott hoss
    (middle_oriented_rigidity t' s' ht' hs' hqt hqs he')

def ActualOrbit (D E : BetaDiagram 5) : Prop :=
  D.TranslationEquivalent E ∨ D.RotationEquivalent E

theorem actual_orbit_refl (D : BetaDiagram 5) : ActualOrbit D D :=
  Or.inl ⟨0,fun i => by simp,fun i => by simp⟩

theorem actual_orbit_symm {D E : BetaDiagram 5} (h : ActualOrbit D E) : ActualOrbit E D := by
  rcases h with ⟨c,hr,hc⟩ | h
  · refine Or.inl ⟨-c,?_,?_⟩
    · intro i
      have := hr i
      omega
    · intro i
      have := hc i
      omega
  · exact Or.inr (FiveExceptional.rotationEquivalent_symm h)

theorem actual_orbit_trans {D E F : BetaDiagram 5}
    (hDE : ActualOrbit D E) (hEF : ActualOrbit E F) : ActualOrbit D F := by
  rcases hDE with ⟨c,hr,hc⟩ | ⟨c,hr,hc⟩ <;>
    rcases hEF with ⟨d,hs,hd⟩ | ⟨d,hs,hd⟩
  · refine Or.inl ⟨c+d,?_,?_⟩ <;> intro i <;> first
    | have := hr i; have := hs i; omega
    | have := hc i; have := hd i; omega
  · refine Or.inr ⟨c+d,?_,?_⟩ <;> intro i <;> first
    | have := hr i; have := hs i; omega
    | have := hc i; have := hd i; omega
  · refine Or.inr ⟨c-d,?_,?_⟩ <;> intro i <;> first
    | have := hr i; have := hd i.rev; omega
    | have := hc i; have := hs i.rev; omega
  · refine Or.inl ⟨c-d,?_,?_⟩ <;> intro i <;> first
    | have hh := hr i; have hh' := hd i.rev; simp only [Fin.rev_rev] at hh'; omega
    | have hh := hc i; have hh' := hs i.rev; simp only [Fin.rev_rev] at hh'; omega

theorem actual_orbit_schur {D E : BetaDiagram 5} (h : ActualOrbit D E) : D.schur=E.schur := by
  rcases h with h | ⟨c,hr,hc⟩
  · exact h.schur_eq
  · have ht : D.TranslationEquivalent E.rotate := by
      refine ⟨c,?_,?_⟩ <;> intro i
      · change D.row i = -E.col i.rev+c
        have := hr i
        omega
      · change D.col i = -E.row i.rev+c
        have := hc i
        omega
    exact ht.schur_eq.trans E.rotate_schur

theorem orbit_of_rotate_translation (D E : BetaDiagram 5)
    (h : D.rotate.TranslationEquivalent E) : ActualOrbit D E := by
  obtain ⟨c,hr,hc⟩ := h
  refine Or.inr ⟨-c,?_,?_⟩
  · intro i
    have hh := hc i.rev
    simp only [BetaDiagram.rotate,Fin.rev_rev] at hh
    omega
  · intro i
    have hh := hr i.rev
    simp only [BetaDiagram.rotate,Fin.rev_rev] at hh
    omega

theorem middle_rotation_bridge (t : Parameters) (ht : ValidM t) :
    ActualOrbit (M t ht) (M (rotateMiddle t) (rotateMiddle_valid t ht)) := by
  apply actual_orbit_symm
  refine Or.inr ⟨(m t : ℤ),?_,?_⟩
  · intro i
    change (mProfile (rotateMiddle t) (rotateMiddle_valid t ht)).xi i =
      (m t : ℤ)-(mProfile t ht).zeta i.rev
    have ht' := ht
    obtain ⟨hu,hv,hb,hx,hy,hc⟩ := ht'
    have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
    have hLr : (rotateMiddle t).L=t.L := by
      simp only [rotateMiddle,Parameters.L,Nat.add_comm]
    fin_cases i <;> norm_num [mProfile,hLr,rotateMiddle,Parameters.L,
      Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ,Fin.rev,m] <;> omega
  · intro i
    change (mProfile (rotateMiddle t) (rotateMiddle_valid t ht)).zeta i =
      (m t : ℤ)-(mProfile t ht).xi i.rev
    have ht' := ht
    obtain ⟨hu,hv,hb,hx,hy,hc⟩ := ht'
    have hL : t.L+t.tau=t.u+t.v := by dsimp [Parameters.L]; omega
    have hLr : (rotateMiddle t).L=t.L := by
      simp only [rotateMiddle,Parameters.L,Nat.add_comm]
    fin_cases i <;> norm_num [mProfile,hLr,rotateMiddle,Parameters.L,
      Gluing.Profile.xi,Gluing.Profile.zeta,Fin.sum_univ_succ,Fin.rev,m] <;> omega

theorem middle_class_actual_orbit (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (h : MiddleClass t s) : ActualOrbit (M t ht) (M s hs) := by
  rcases h with rfl | rfl
  · exact actual_orbit_refl _
  · exact middle_rotation_bridge t ht

theorem normal_form_actual_orbit (D : BetaDiagram 5) (hD : D.Connected)
    (hν : negativeCount D=5) :
    (∃ t, ∃ ht : ValidM t, ActualOrbit D (M t ht)) ∨
    (∃ t, ∃ ht : ValidE t, ActualOrbit D (E t ht)) := by
  rcases normal_form_exhaustion D hD hν with h | h | h
  · obtain ⟨t,ht,h⟩ := h
    exact Or.inl ⟨t,ht,Or.inl h⟩
  · obtain ⟨t,ht,h⟩ := h
    exact Or.inr ⟨t,ht,Or.inl h⟩
  · obtain ⟨t,ht,h⟩ := h
    exact Or.inr ⟨t,ht,orbit_of_rotate_translation D (E t ht) h⟩

def ExceptionalMember (P : FiveExceptional.Parameters) (second : Bool) (D : BetaDiagram 5) : Prop :=
  ActualOrbit D (FiveExceptional.F P second) ∨ ActualOrbit D (FiveExceptional.H P second)

theorem mixed_exceptional_orbits (t s : Parameters) (ht : ValidM t) (hs : ValidE s)
    (he : (M t ht).schur=(E s hs).schur) :
    ∃ P second, ExceptionalMember P second (M t ht) ∧ ExceptionalMember P second (E s hs) := by
  obtain ⟨t',ht',horient,ho⟩ := mixed_output t s ht hs he
  obtain ⟨P,second,hM,hE⟩ := cross_output_families t' s ht' hs ho
  refine ⟨P,second,Or.inl ?_,Or.inr (Or.inl hE)⟩
  have hO : ActualOrbit (M t ht) (M t' ht') := by
    rcases horient with rfl | rfl
    · exact actual_orbit_refl _
    · exact middle_rotation_bridge t ht
  exact actual_orbit_trans hO (Or.inl hM)

theorem exceptional_member_schur (P : FiveExceptional.Parameters) (second : Bool)
    (D : BetaDiagram 5) (h : ExceptionalMember P second D) :
    D.schur=(FiveExceptional.F P second).schur := by
  rcases h with h | h
  · exact actual_orbit_schur h
  · exact (actual_orbit_schur h).trans (FiveExceptional.F_schur_eq_H P second).symm

/-- Complete same-order pair classification for arbitrary connected five-negative sources. -/
theorem five_base_pair (D W : BetaDiagram 5) (hD : D.Connected) (hE : W.Connected)
    (hν : negativeCount D=5) :
    D.schur=W.schur ↔ ActualOrbit D W ∨
      ∃ P second, ExceptionalMember P second D ∧ ExceptionalMember P second W := by
  constructor
  · intro he
    have hνE : negativeCount W=5 := by rw [← D.negativeCount_eq_of_schur_eq W he]; exact hν
    rcases normal_form_actual_orbit D hD hν with ⟨t,ht,hDO⟩ | ⟨t,ht,hDO⟩ <;>
      rcases normal_form_actual_orbit W hE hνE with ⟨s,hs,hEO⟩ | ⟨s,hs,hEO⟩
    · have he' : (M t ht).schur=(M s hs).schur :=
        (actual_orbit_schur hDO).symm.trans (he.trans (actual_orbit_schur hEO))
      exact Or.inl (actual_orbit_trans hDO
        (actual_orbit_trans (middle_class_actual_orbit t s ht hs
          (middle_same_opening t s ht hs he')) (actual_orbit_symm hEO)))
    · have he' : (M t ht).schur=(E s hs).schur :=
        (actual_orbit_schur hDO).symm.trans (he.trans (actual_orbit_schur hEO))
      obtain ⟨P,second,hM,hE'⟩ := mixed_exceptional_orbits t s ht hs he'
      refine Or.inr ⟨P,second,?_,?_⟩
      · rcases hM with h | h <;> first
        | exact Or.inl (actual_orbit_trans hDO h)
        | exact Or.inr (actual_orbit_trans hDO h)
      · rcases hE' with h | h <;> first
        | exact Or.inl (actual_orbit_trans hEO h)
        | exact Or.inr (actual_orbit_trans hEO h)
    · have he' : (M s hs).schur=(E t ht).schur :=
        (actual_orbit_schur hEO).symm.trans (he.symm.trans (actual_orbit_schur hDO))
      obtain ⟨P,second,hM,hE'⟩ := mixed_exceptional_orbits s t hs ht he'
      refine Or.inr ⟨P,second,?_,?_⟩
      · rcases hE' with h | h <;> first
        | exact Or.inl (actual_orbit_trans hDO h)
        | exact Or.inr (actual_orbit_trans hDO h)
      · rcases hM with h | h <;> first
        | exact Or.inl (actual_orbit_trans hEO h)
        | exact Or.inr (actual_orbit_trans hEO h)
    · have he' : (E t ht).schur=(E s hs).schur :=
        (actual_orbit_schur hDO).symm.trans (he.trans (actual_orbit_schur hEO))
      have hts := end_same_opening t s ht hs he'
      subst s
      exact Or.inl (actual_orbit_trans hDO (actual_orbit_symm hEO))
  · rintro (h | ⟨P,second,hD',hE'⟩)
    · exact actual_orbit_schur h
    · exact (exceptional_member_schur P second D hD').trans
        (exceptional_member_schur P second W hE').symm

/-- `thm:five-base` against connected mates of arbitrary initial row count. -/
theorem five_base {n : ℕ} (D : BetaDiagram 5) (hD : D.Connected) (hν : negativeCount D=5)
    (W : BetaDiagram n) (hW : W.Connected) :
    D.schur=W.schur ↔ ∃ hn : n=5,
      ActualOrbit D (W.castOrder hn) ∨
        ∃ P second, ExceptionalMember P second D ∧ ExceptionalMember P second (W.castOrder hn) := by
  constructor
  · intro he
    have hn : n=5 := (D.row_count_of_schur_eq W he).symm
    refine ⟨hn,?_⟩
    apply (five_base_pair D (W.castOrder hn) hD ((W.castOrder_connected hn).mpr hW) hν).mp
    simpa only [BetaDiagram.castOrder_schur] using he
  · rintro ⟨hn,hclass⟩
    have hh := (five_base_pair D (W.castOrder hn) hD
      ((W.castOrder_connected hn).mpr hW) hν).mpr hclass
    simpa only [BetaDiagram.castOrder_schur] using hh

theorem exceptional_F_orbit_injective (P Q : FiveExceptional.Parameters) (s t : Bool)
    (h : ActualOrbit (FiveExceptional.F P s) (FiveExceptional.F Q t)) : P=Q ∧ s=t := by
  rcases h with ⟨c,hr,hc⟩ | h
  · have hc4:=hc 4
    have hr4:=hr 4
    have hr3:=hr 3
    have hc3:=hc 3
    have hc0:=hc 0
    norm_num [FiveExceptional.F,FiveExceptional.rows,FiveExceptional.fCols] at hc4 hr4 hr3 hc3 hc0
    have hb : P.b=Q.b := by omega
    have hg : P.g=Q.g := by omega
    have hq : P.q=Q.q := by omega
    have hst : s=t := by
      have hqp:=P.q_pos
      have hqq:=Q.q_pos
      cases s <;> cases t <;> simp_all <;> omega
    have hPQ : P=Q := by
      cases P
      cases Q
      simp_all
    exact ⟨hPQ,hst⟩
  · exact (FiveExceptional.F_not_rotation_F P Q s t h).elim

theorem exceptional_H_orbit_injective (P Q : FiveExceptional.Parameters) (s t : Bool)
    (h : ActualOrbit (FiveExceptional.H P s) (FiveExceptional.H Q t)) : P=Q ∧ s=t := by
  rcases h with ⟨c,hr,hc⟩ | h
  · have hc4:=hc 4
    have hr4:=hr 4
    have hr3:=hr 3
    have hc3:=hc 3
    have hc2:=hc 2
    norm_num [FiveExceptional.H,FiveExceptional.rows,FiveExceptional.hCols] at hc4 hr4 hr3 hc3 hc2
    have hb : P.b=Q.b := by omega
    have hg : P.g=Q.g := by omega
    have hq : P.q=Q.q := by omega
    have hst : s=t := by
      have hqp:=P.q_pos
      have hqq:=Q.q_pos
      cases s <;> cases t <;> simp_all <;> omega
    have hPQ : P=Q := by
      cases P
      cases Q
      simp_all
    exact ⟨hPQ,hst⟩
  · exact (FiveExceptional.H_not_rotation_H P Q s t h).elim

theorem exceptional_FH_orbit_disjoint (P Q : FiveExceptional.Parameters) (s t : Bool) :
    ¬ ActualOrbit (FiveExceptional.F P s) (FiveExceptional.H Q t) := by
  rintro (h | h)
  · exact FiveExceptional.F_not_translation_H P Q s t h
  · exact FiveExceptional.F_not_rotation_H P Q s t h

/-- Exceptional parameters and family numbers are unique even under translation and half-turn. -/
theorem exceptional_member_unique (P Q : FiveExceptional.Parameters) (s t : Bool)
    (D : BetaDiagram 5) (hP : ExceptionalMember P s D) (hQ : ExceptionalMember Q t D) :
    P=Q ∧ s=t := by
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · exact exceptional_F_orbit_injective P Q s t
      (actual_orbit_trans (actual_orbit_symm hP) hQ)
  · exact (exceptional_FH_orbit_disjoint P Q s t
      (actual_orbit_trans (actual_orbit_symm hP) hQ)).elim
  · exact (exceptional_FH_orbit_disjoint Q P t s
      (actual_orbit_trans (actual_orbit_symm hQ) hP)).elim
  · exact exceptional_H_orbit_injective P Q s t
      (actual_orbit_trans (actual_orbit_symm hP) hQ)

/-- The complete class of each exceptional member is exactly its displayed quartet of translation classes. -/
theorem five_base_complete_class {n : ℕ} (P : FiveExceptional.Parameters) (second : Bool)
    (D : BetaDiagram 5) (hD : D.Connected) (hmem : ExceptionalMember P second D)
    (W : BetaDiagram n) (hW : W.Connected) :
    D.schur=W.schur ↔ ∃ hn : n=5, ExceptionalMember P second (W.castOrder hn) := by
  have hDF := exceptional_member_schur P second D hmem
  have hν : negativeCount D=5 := by
    rw [D.negativeCount_eq_of_schur_eq (FiveExceptional.F P second) hDF]
    exact FiveExceptional.F_negativeCount P second
  constructor
  · intro he
    obtain ⟨hn,hclass⟩ := (five_base D hD hν W hW).mp he
    refine ⟨hn,?_⟩
    rcases hclass with hO | ⟨Q,j,hD',hW'⟩
    · rcases hmem with hmem | hmem
      · exact Or.inl (actual_orbit_trans (actual_orbit_symm hO) hmem)
      · exact Or.inr (actual_orbit_trans (actual_orbit_symm hO) hmem)
    · obtain ⟨rfl,rfl⟩ := exceptional_member_unique P Q second j D hmem hD'
      exact hW'
  · rintro ⟨hn,hW'⟩
    have hh := (exceptional_member_schur P second D hmem).trans
      (exceptional_member_schur P second (W.castOrder hn) hW').symm
    simpa only [BetaDiagram.castOrder_schur] using hh

/-- A five-negative source outside the two displayed families is rotation-rigid against every mate. -/
theorem five_base_rotation_rigid (D : BetaDiagram 5) (hD : D.Connected)
    (hν : negativeCount D=5)
    (hnot : ¬ ∃ P second, ExceptionalMember P second D) : D.RotationRigid := by
  apply (D.rotationRigid_iff_same_order).mpr
  intro W hW he
  rcases (five_base_pair D W hD hW hν).mp he.symm with h | ⟨P,second,hD',_⟩
  · exact h
  · exact (hnot ⟨P,second,hD'⟩).elim

theorem end_diagram_congr (t s : Parameters) (ht : ValidE t) (hs : ValidE s)
    (h : t=s) : E t ht=E s hs := by
  cases h
  rfl

/-- The same-opening proposition on actual beta diagrams, before choosing normal-form parameters. -/
theorem same_opening_rigidity (D W : BetaDiagram 5) (hD : D.Connected) (hW : W.Connected)
    (k : Fin 3) (hDo : FiveOpening.HasOpening D k) (hWo : FiveOpening.HasOpening W k)
    (he : D.schur=W.schur) : ActualOrbit D W := by
  fin_cases k
  · let t:=endParameters D
    let s:=endParameters W
    let ht:=endParameters_valid D hD hDo
    let hs:=endParameters_valid W hW hWo
    have hDt : ActualOrbit D (E t ht) := Or.inl (end_reconstruction D hD hDo)
    have hWs : ActualOrbit W (E s hs) := Or.inl (end_reconstruction W hW hWo)
    have hep : (E t ht).schur=(E s hs).schur :=
      (actual_orbit_schur hDt).symm.trans (he.trans (actual_orbit_schur hWs))
    have hts := end_same_opening t s ht hs hep
    have hWs' : ActualOrbit W (E t ht) := by
      rw [end_diagram_congr t s ht hs hts]
      exact hWs
    exact actual_orbit_trans hDt (actual_orbit_symm hWs')
  · let t:=middleParameters D
    let s:=middleParameters W
    let ht:=middleParameters_valid D hD hDo
    let hs:=middleParameters_valid W hW hWo
    have hDt : ActualOrbit D (M t ht) := Or.inl (middle_reconstruction D hD hDo)
    have hWs : ActualOrbit W (M s hs) := Or.inl (middle_reconstruction W hW hWo)
    have hep : (M t ht).schur=(M s hs).schur :=
      (actual_orbit_schur hDt).symm.trans (he.trans (actual_orbit_schur hWs))
    exact actual_orbit_trans hDt (actual_orbit_trans
      (middle_class_actual_orbit t s ht hs (middle_same_opening t s ht hs hep))
      (actual_orbit_symm hWs))
  · have hDr:=D.rotate_connected hD
    have hWr:=W.rotate_connected hW
    have hoD:=rotate_end_opening D hDo
    have hoW:=rotate_end_opening W hWo
    let t:=endParameters D.rotate
    let s:=endParameters W.rotate
    let ht:=endParameters_valid D.rotate hDr hoD
    let hs:=endParameters_valid W.rotate hWr hoW
    have hDt : ActualOrbit D (E t ht) :=
      orbit_of_rotate_translation D (E t ht) (end_reconstruction D.rotate hDr hoD)
    have hWs : ActualOrbit W (E s hs) :=
      orbit_of_rotate_translation W (E s hs) (end_reconstruction W.rotate hWr hoW)
    have hep : (E t ht).schur=(E s hs).schur :=
      (actual_orbit_schur hDt).symm.trans (he.trans (actual_orbit_schur hWs))
    have hts:=end_same_opening t s ht hs hep
    have hWs' : ActualOrbit W (E t ht) := by
      rw [end_diagram_congr t s ht hs hts]
      exact hWs
    exact actual_orbit_trans hDt (actual_orbit_symm hWs')

end FiveNegative
end SkewJacobiNegative
