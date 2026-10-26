/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.TenClassification
import SkewJacobiNegative.ConnectedBorderRigidity
import SkewJacobiNegative.ThreeComponentContexts
import SkewJacobiNegative.TenCompositionCells

/-!
# Endpoint isolation for exceptional seven-row families

The endpoint and cross-orbit assertions of `lem:ten-negative-endpoints`
follow directly from `prop:exceptional-singleton-context`: a positive
endpoint shift moves the genuine singleton parent off its exceptional locus.
Gamma transport includes every common-beta unit.
The all-margin separation in `lem:ten-negative-border-separation` uses the
actual private coefficients of `lem:border` and the tied-border separator.
-/

namespace SkewJacobiNegative.TenParameters

private theorem singleton_rows (Q : BetaDiagram 5) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).row =
      ![Q.row 0+v+g+s+u,Q.row 0+v+g+s,v+Q.row 0,v+Q.row 1,
        v+Q.row 2,v+Q.row 3,v+Q.row 4] := by
  funext i
  cases i using Fin.cases with
  | zero =>
    simpa only [Matrix.cons_val_zero] using Q.singletonContext_row_zero s u v g hs hu hv hg
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Matrix.cons_val_succ,Matrix.cons_val_zero] using
        Q.singletonContext_row_one s u v g hs hu hv hg
    | succ i =>
      rw [BetaDiagram.singletonContext_row_core]
      fin_cases i <;> norm_num [Matrix.cons_val]

private theorem singleton_cols (Q : BetaDiagram 5) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).col =
      ![v+Q.row 0+g,v+Q.col 0,v+Q.col 1,v+Q.col 2,v+Q.col 3,v+Q.col 4,Q.col 4] := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    rw [BetaDiagram.singletonContext_col_last]
    norm_num [Fin.last,Matrix.cons_val]
  | cast i =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.castSucc_zero,Matrix.cons_val_zero] using
        Q.singletonContext_col_zero s u v g hs hu hv hg
    | succ i =>
      rw [BetaDiagram.singletonContext_col_core]
      fin_cases i <;> norm_num [Fin.castSucc,Matrix.cons_val]

set_option maxHeartbeats 0 in
/-- A seven-row endpoint is the actual singleton parent with one changed margin. -/
theorem endpoint_singleton_translation (P : TenParameters) (hd : 0 < P.d)
    (familyB other top : Bool) (t : ℤ) (ht : 0 < t) :
    (P.endpoint (pairKind familyB other) top t ht).TranslationEquivalent
      ((FiveExceptional.coreCandidate P.singletonCoreParameters (!familyB) other true).singletonContext
          P.d (P.a + if top then t else 0)
          (P.b + if top then 0 else t) (P.b-P.a-P.d)
          hd
          (by have := P.a_pos; cases top <;> simp <;> omega)
          (by have := P.b_pos; cases top <;> simp <;> omega)
          (by have := P.separated; omega)) := by
  let Q := FiveExceptional.coreCandidate P.singletonCoreParameters (!familyB) other true
  have hU : 0 < P.a + if top then t else 0 := by
    have := P.a_pos
    cases top <;> simp <;> omega
  have hV : 0 < P.b + if top then 0 else t := by
    have := P.b_pos
    cases top <;> simp <;> omega
  have hG : 0 < P.b-P.a-P.d := by have := P.separated; omega
  have hrow := singleton_rows Q P.d (P.a + if top then t else 0)
    (P.b + if top then 0 else t) (P.b-P.a-P.d) hd hU hV hG
  have hcol := singleton_cols Q P.d (P.a + if top then t else 0)
    (P.b + if top then 0 else t) (P.b-P.a-P.d) hd hU hV hG
  refine ⟨P.a+P.d+4*P.b - (if top then 0 else t), ?_, ?_⟩
  · intro i
    rw [hrow]
    cases familyB <;> cases other <;> cases top <;> fin_cases i <;>
      norm_num [Q, endpoint, pairKind, singletonCoreParameters,
        BetaDiagram.extendTop, BetaDiagram.extendBottom,
        FiveExceptional.coreCandidate, BetaDiagram.rotate,
        FiveExceptional.F, FiveExceptional.H, FiveExceptional.rows,
        FiveExceptional.fCols, FiveExceptional.hCols, diagram, rowBase, column,
        Fin.rev, Matrix.cons_val] <;> omega
  · intro i
    rw [hcol]
    cases familyB <;> cases other <;> cases top <;> fin_cases i <;>
      norm_num [Q, endpoint, pairKind, singletonCoreParameters,
        BetaDiagram.extendTop, BetaDiagram.extendBottom,
        FiveExceptional.coreCandidate, BetaDiagram.rotate,
        FiveExceptional.F, FiveExceptional.H, FiveExceptional.rows,
        FiveExceptional.fCols, FiveExceptional.hCols, diagram, rowBase, column,
        Fin.rev, Matrix.cons_val] <;> omega

/-- Positive endpoints leave the genuine singleton exception locus. -/
theorem endpoint_rotationRigid_zeroFree (P : TenParameters) (hd : 0 < P.d)
    (familyB other top : Bool) (t : ℤ) (ht : 0 < t) :
    (P.endpoint (pairKind familyB other) top t ht).RotationRigid := by
  have hp : P.singletonCoreParameters.q < P.singletonCoreParameters.b := by
    change P.a < P.a+P.d
    omega
  have hu : 0 < P.a + if top then t else 0 := by
    have := P.a_pos
    cases top <;> simp <;> omega
  have hv : 0 < P.b + if top then 0 else t := by
    have := P.b_pos
    cases top <;> simp <;> omega
  have hg : 0 < P.b-P.a-P.d := by have := P.separated; omega
  have hNo : ¬ (true=true ∧
      (P.d,P.a + if top then t else 0,P.b + if top then 0 else t,P.b-P.a-P.d) =
        (P.singletonCoreParameters.b-P.singletonCoreParameters.q,
          P.singletonCoreParameters.q,P.singletonCoreParameters.g,
          P.singletonCoreParameters.g-P.singletonCoreParameters.b)) := by
    intro hbad
    have hU := congrArg (fun z : ℤ × ℤ × ℤ × ℤ => z.2.1) hbad.2
    have hV := congrArg (fun z : ℤ × ℤ × ℤ × ℤ => z.2.2.1) hbad.2
    cases top <;> simp [singletonCoreParameters] at hU hV <;> omega
  have hRigid := FiveExceptional.exceptional_singleton_rotationRigid
    P.singletonCoreParameters hp (!familyB) other true P.d
    (P.a + if top then t else 0) (P.b + if top then 0 else t)
    (P.b-P.a-P.d) hd hu hv hg hNo
  exact BetaDiagram.rotationRigid_of_translation _ _
    (P.endpoint_singleton_translation hd familyB other top t ht) hRigid

/-- Endpoint rigidity descends from the actual affine family, including `d=0`. -/
theorem endpoint_rotationRigid (P : TenParameters) (familyB other top : Bool)
    (t : ℤ) (ht : 0 < t) :
    (P.endpoint (pairKind familyB other) top t ht).RotationRigid := by
  have hC : (P.endpoint (pairKind familyB other) top t ht).Connected := by
    cases top
    · exact (P.diagram _).extendBottom_connected (P.connected _) t ht
    · exact (P.diagram _).extendTop_connected (P.connected _) t ht
  apply BetaDiagram.gamma_rigidity_descends _ hC
  have hT :
      (P.endpoint (pairKind familyB other) top t ht).gamma.TranslationEquivalent
        (P.gammaParameters.endpoint (pairKind familyB other) top (2*t) (by omega)) := by
    refine ⟨0, ?_, ?_⟩ <;> intro i
    all_goals
      cases familyB <;> cases other <;> cases top <;> fin_cases i <;>
        norm_num [BetaDiagram.gamma, endpoint, pairKind, diagram, rowBase, column,
          BetaDiagram.extendTop, BetaDiagram.extendBottom, gammaParameters] <;> omega
  exact BetaDiagram.rotationRigid_of_translation _ _ hT
    (P.gammaParameters.endpoint_rotationRigid_zeroFree
      P.gammaParameters_d_pos familyB other top (2*t) (by omega))

/-- Different actual core representatives cannot merge under any positive endpoint shifts. -/
theorem cross_orbit_endpoints_ne (P : TenParameters) (familyB : Bool)
    (other mate top bottom : Bool) (hne : other ≠ mate)
    (t z : ℤ) (ht : 0 < t) (hz : 0 < z) :
    (P.endpoint (pairKind familyB other) top t ht).schur ≠
      (P.endpoint (pairKind familyB mate) bottom z hz).schur := by
  intro he
  have hE : (P.endpoint (pairKind familyB mate) bottom z hz).Connected := by
    cases bottom
    · exact (P.diagram _).extendBottom_connected (P.connected _) z hz
    · exact (P.diagram _).extendTop_connected (P.connected _) z hz
  obtain ⟨hn, hm⟩ := P.endpoint_rotationRigid familyB other top t ht 7
    (P.endpoint (pairKind familyB mate) bottom z hz) hE he.symm
  have hh : hn = rfl := Subsingleton.elim _ _
  rw [hh] at hm
  simp only [BetaDiagram.castOrder] at hm
  rcases hm with hT | hR
  · exact P.endpoints_not_translation_of_distinct _ _
      (by cases familyB <;> cases other <;> cases mate <;> simp_all [pairKind])
      top bottom t z ht hz hT
  · exact P.endpoints_not_rotation P _ _ top bottom t z ht hz hR

/-- Equal opposite endpoints of an arbitrary seven-row source cannot belong
to an exceptional family.  The unchanged first gap and reflected last gap
exclude mixed orientations; the common column progression excludes the others. -/
theorem opposite_endpoints_ne_of_exceptional_top (P : TenParameters)
    (familyB other : Bool) (R : BetaDiagram 7) (hR : R.Connected)
    (t : ℤ) (ht : 0 < t)
    (hTop : (P.diagram (pairKind familyB other)).MotionEquivalent (R.extendTop t ht)) :
    (R.extendTop t ht).schur ≠ (R.extendBottom t ht).schur := by
  intro he
  have hfunc := (BetaDiagram.ten_motion_schur_eq hTop).trans he
  obtain ⟨mate, hbotOrder, hBot⟩ :=
    (P.complete_class familyB other (R.extendBottom t ht)
      (R.extendBottom_connected hR t ht)).mp hfunc
  obtain ⟨htopOrder,hTop⟩ := hTop
  have hhTop : htopOrder = rfl := Subsingleton.elim _ _
  have hhBot : hbotOrder = rfl := Subsingleton.elim _ _
  rw [hhTop] at hTop
  rw [hhBot] at hBot
  simp only [BetaDiagram.castOrder] at hTop hBot
  rcases hTop with ⟨c,hr,hc⟩ | ⟨c,hr,hc⟩ <;>
    rcases hBot with ⟨d,hs,hd⟩ | ⟨d,hs,hd⟩
  · have h0 := hc 0
    have h6 := hc 6
    have s0 := hd 0
    have s6 := hd 6
    norm_num [diagram, column, BetaDiagram.extendTop, BetaDiagram.extendBottom]
      at h0 h6 s0 s6
    omega
  · have h1 := hr 1
    have h0 := hc 0
    have s6 := hs 6
    have s5 := hd 5
    have hb := P.b_pos
    have ha := P.a_pos
    cases familyB <;> cases other <;> cases mate <;>
      norm_num [pairKind, diagram, rowBase, column,
        BetaDiagram.extendTop, BetaDiagram.extendBottom, Fin.rev] at h1 h0 s6 s5 <;>
      omega
  · have h6 := hr 6
    have h5 := hc 5
    have s1 := hs 1
    have s0 := hd 0
    have hb := P.b_pos
    have ha := P.a_pos
    cases familyB <;> cases other <;> cases mate <;>
      norm_num [pairKind, diagram, rowBase, column,
        BetaDiagram.extendTop, BetaDiagram.extendBottom, Fin.rev] at h6 h5 s1 s0 <;>
      omega
  · have h0 := hc 0
    have h6 := hc 6
    have s0 := hd 0
    have s6 := hd 6
    norm_num [diagram, column, BetaDiagram.extendTop, BetaDiagram.extendBottom, Fin.rev]
      at h0 h6 s0 s6
    omega

private theorem border_row_multiset {n m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (he : D.schur = E.schur) :
    (List.ofFn D.rowLength : Multiset ℤ) = (List.ofFn E.rowLength : Multiset ℤ) := by
  classical
  have hi := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [D.square_initial_monomial, E.square_initial_monomial] at hi
  have hx : D.diagonalExponent = E.diagonalExponent := by
    by_contra hn
    have hc := congrArg (fun p : CompleteRing => p.coeff D.diagonalExponent) hi
    simp [MvPolynomial.coeff_monomial, Ne.symm hn] at hc
  rw [D.diagonalExponent_eq_rowLengths, E.diagonalExponent_eq_rowLengths] at hx
  have hm := (Base.exponentVector_eq_iff _ _).mp hx
  unfold Base.positiveIndexMultiset at hm
  rw [Multiset.filter_eq_self.mpr D.rowLengthList_positive,
    Multiset.filter_eq_self.mpr E.rowLengthList_positive] at hm
  have hc := congrArg (Multiset.map (fun k : ℕ => (k : ℤ))) hm
  have hD : (fun i => ((D.rowLength i).toNat : ℤ)) = D.rowLength := by
    funext i
    exact Int.toNat_of_nonneg (D.rowLength_pos i).le
  have hE : (fun i => ((E.rowLength i).toNat : ℤ)) = E.rowLength := by
    funext i
    exact Int.toNat_of_nonneg (E.rowLength_pos i).le
  simpa only [Multiset.map_coe, List.map_ofFn, Function.comp_def, hD, hE] using hc

/-- The tied cross-orbit row comparison forces exactly the manuscript margin,
and its actual coefficient separator then excludes equality, including units. -/
theorem equal_margin_cross_border_ne (P : TenParameters) (familyB : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((P.diagram (pairKind familyB false)).positiveBorder t t ht ht).schur ≠
      ((P.diagram (pairKind familyB true)).positiveBorder t t ht ht).schur := by
  intro he
  have hm := border_row_multiset _ _ he
  have hs := congrArg (fun xs : Multiset ℤ => (xs.map (fun k => k^2)).sum) hm
  have hsquare :
      (∑ i, ((P.diagram (pairKind familyB false)).positiveBorder t t ht ht).rowLength i ^ 2) =
      ∑ i, ((P.diagram (pairKind familyB true)).positiveBorder t t ht ht).rowLength i ^ 2 := by
    simpa only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn,
      List.sum_ofFn, Function.comp_def] using hs
  have hdouble : 2*((if familyB then P.b-P.a else P.b)*(t-P.b)) = 0 := by
    cases familyB
    · change 2*(P.b*(t-P.b)) = 0
      norm_num [pairKind, BetaDiagram.rowLength, BetaDiagram.positiveBorder,
        diagram, rowBase, column, Fin.sum_univ_succ] at hsquare
      linear_combination hsquare
    · change 2*((P.b-P.a)*(t-P.b)) = 0
      norm_num [pairKind, BetaDiagram.rowLength, BetaDiagram.positiveBorder,
        diagram, rowBase, column, Fin.sum_univ_succ] at hsquare
      linear_combination hsquare
  have hprod : (if familyB then P.b-P.a else P.b) * (t-P.b) = 0 := by omega
  have hn : (if familyB then P.b-P.a else P.b) ≠ 0 := by
    have := P.b_pos
    have := P.separated
    have := P.d_nonneg
    cases familyB <;> simp <;> omega
  have htb : t = P.b := by
    have := (mul_eq_zero.mp hprod).resolve_left hn
    omega
  subst t
  exact P.tiedBorder_schur_ne_including_units familyB (by
    cases familyB <;> simpa [pairKind] using he)

private theorem strict_top_border_endpoint_eq (P : TenParameters)
    (familyB other mate : Bool) (u v : ℤ) (hu : 0 < u) (hv : 0 < v)
    (huv : u < v) (swapped : Bool)
    (he :
      ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).schur =
      ((P.diagram (pairKind familyB mate)).positiveBorder
        (if swapped then v else u) (if swapped then u else v)
        (by cases swapped <;> simp <;> assumption)
        (by cases swapped <;> simp <;> assumption)).schur) :
    (P.endpoint (pairKind familyB other) true u hu).schur =
      (P.endpoint (pairKind familyB mate) (!swapped) u hu).schur := by
  let D := (P.diagram (pairKind familyB other)).positiveBorder u v hu hv
  have hPD := (P.diagram (pairKind familyB other)).positiveBorder_positiveCorner u v hu hv
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel-u).toNat, by
    have hp := D.exterior_top_label_pos
    simpa [D] using hp⟩
  have hD :
      MvPolynomial.pderiv M (eraseGenerator N D.schur) =
        (P.endpoint (pairKind familyB other) true u hu).schur := by
    have h := D.border_top_coefficient hPD (by simpa [D] using huv)
    norm_num at h
    simpa [D, N, M, endpoint] using h
  cases swapped
  · let E := (P.diagram (pairKind familyB mate)).positiveBorder u v hu hv
    have hPE := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner u v hu hv
    have hspan : D.largestLabel = E.largestLabel :=
      D.largestLabel_eq_of_schur_eq E
        ((P.diagram _).positiveBorder_connected u v hu hv)
        ((P.diagram _).positiveBorder_connected u v hu hv) he
    have hE :
        MvPolynomial.pderiv M (eraseGenerator N E.schur) =
          (P.endpoint (pairKind familyB mate) true u hu).schur := by
      have h := E.border_top_coefficient hPE (by simpa [E] using huv)
      norm_num at h
      simpa [E, N, M, hspan, endpoint] using h
    have hc := congrArg (fun p : CompleteRing => MvPolynomial.pderiv M (eraseGenerator N p)) he
    simpa [Bool.not_false] using hD.symm.trans (hc.trans hE)
  · let E := (P.diagram (pairKind familyB mate)).positiveBorder v u hv hu
    have hPE := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner v u hv hu
    have hspan : D.largestLabel = E.largestLabel :=
      D.largestLabel_eq_of_schur_eq E
        ((P.diagram _).positiveBorder_connected u v hu hv)
        ((P.diagram _).positiveBorder_connected v u hv hu) he
    have hE :
        MvPolynomial.pderiv M (eraseGenerator N E.schur) =
          (P.endpoint (pairKind familyB mate) false u hu).schur := by
      have h := E.border_bottom_coefficient hPE (by simpa [E] using huv)
      norm_num at h
      simpa [E, N, M, hspan, endpoint] using h
    have hc := congrArg (fun p : CompleteRing => MvPolynomial.pderiv M (eraseGenerator N p)) he
    simpa [Bool.not_true] using hD.symm.trans (hc.trans hE)

private theorem strict_bottom_border_endpoint_eq (P : TenParameters)
    (familyB other mate : Bool) (u v : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hvu : v < u) (swapped : Bool)
    (he :
      ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).schur =
      ((P.diagram (pairKind familyB mate)).positiveBorder
        (if swapped then v else u) (if swapped then u else v)
        (by cases swapped <;> simp <;> assumption)
        (by cases swapped <;> simp <;> assumption)).schur) :
    (P.endpoint (pairKind familyB other) false v hv).schur =
      (P.endpoint (pairKind familyB mate) swapped v hv).schur := by
  let D := (P.diagram (pairKind familyB other)).positiveBorder u v hu hv
  have hPD := (P.diagram (pairKind familyB other)).positiveBorder_positiveCorner u v hu hv
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel-v).toNat, by
    have hp := D.rotate.exterior_top_label_pos
    rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
    simpa [D] using hp⟩
  have hD :
      MvPolynomial.pderiv M (eraseGenerator N D.schur) =
        (P.endpoint (pairKind familyB other) false v hv).schur := by
    have h := D.border_bottom_coefficient hPD (by simpa [D] using hvu)
    norm_num at h
    simpa [D, N, M, endpoint] using h
  cases swapped
  · let E := (P.diagram (pairKind familyB mate)).positiveBorder u v hu hv
    have hPE := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner u v hu hv
    have hspan : D.largestLabel = E.largestLabel :=
      D.largestLabel_eq_of_schur_eq E
        ((P.diagram _).positiveBorder_connected u v hu hv)
        ((P.diagram _).positiveBorder_connected u v hu hv) he
    have hE :
        MvPolynomial.pderiv M (eraseGenerator N E.schur) =
          (P.endpoint (pairKind familyB mate) false v hv).schur := by
      have h := E.border_bottom_coefficient hPE (by simpa [E] using hvu)
      norm_num at h
      simpa [E, N, M, hspan, endpoint] using h
    have hc := congrArg (fun p : CompleteRing => MvPolynomial.pderiv M (eraseGenerator N p)) he
    exact hD.symm.trans (hc.trans hE)
  · let E := (P.diagram (pairKind familyB mate)).positiveBorder v u hv hu
    have hPE := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner v u hv hu
    have hspan : D.largestLabel = E.largestLabel :=
      D.largestLabel_eq_of_schur_eq E
        ((P.diagram _).positiveBorder_connected u v hu hv)
        ((P.diagram _).positiveBorder_connected v u hv hu) he
    have hE :
        MvPolynomial.pderiv M (eraseGenerator N E.schur) =
          (P.endpoint (pairKind familyB mate) true v hv).schur := by
      have h := E.border_top_coefficient hPE (by simpa [E] using hvu)
      norm_num at h
      simpa [E, N, M, hspan, endpoint] using h
    have hc := congrArg (fun p : CompleteRing => MvPolynomial.pderiv M (eraseGenerator N p)) he
    exact hD.symm.trans (hc.trans hE)

private theorem equal_margin_borders_ne_of_distinct (P : TenParameters)
    (familyB other mate : Bool) (hne : other ≠ mate) (t : ℤ) (ht : 0 < t) :
    ((P.diagram (pairKind familyB other)).positiveBorder t t ht ht).schur ≠
      ((P.diagram (pairKind familyB mate)).positiveBorder t t ht ht).schur := by
  cases other <;> cases mate
  · exact (hne rfl).elim
  · exact P.equal_margin_cross_border_ne familyB t ht
  · exact (P.equal_margin_cross_border_ne familyB t ht).symm
  · exact (hne rfl).elim

private theorem cross_orbit_borders_ne_aligned (P : TenParameters) (familyB : Bool)
    (other mate : Bool) (hne : other ≠ mate)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (swapped : Bool)
    (he :
      ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).schur =
      ((P.diagram (pairKind familyB mate)).positiveBorder
        (if swapped then v else u) (if swapped then u else v)
        (by cases swapped <;> simp <;> assumption)
        (by cases swapped <;> simp <;> assumption)).schur) : False := by
  rcases lt_trichotomy u v with h | h | h
  · exact P.cross_orbit_endpoints_ne familyB other mate true (!swapped) hne u u hu hu
      (P.strict_top_border_endpoint_eq familyB other mate u v hu hv h swapped he)
  · subst v
    apply P.equal_margin_borders_ne_of_distinct familyB other mate hne u hu
    cases swapped <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using he
  · exact P.cross_orbit_endpoints_ne familyB other mate false swapped hne v v hv hv
      (P.strict_bottom_border_endpoint_eq familyB other mate u v hu hv h swapped he)

private theorem family_largestLabel (P : TenParameters) (k : TenKind) :
    (P.diagram k).largestLabel = P.a+6*P.b+P.d := by
  cases k <;> norm_num [BetaDiagram.largestLabel,diagram,rowBase,column]

/-- Every cross-orbit comparison with arbitrary positive margins is excluded.
The unordered margins are recovered from the actual parent functions. -/
theorem cross_orbit_borders_ne (P : TenParameters) (familyB : Bool)
    (other mate : Bool) (hne : other ≠ mate)
    (u v x y : ℤ) (hu : 0 < u) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) :
    ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).schur ≠
      ((P.diagram (pairKind familyB mate)).positiveBorder x y hx hy).schur := by
  intro he
  let D := (P.diagram (pairKind familyB other)).positiveBorder u v hu hv
  let E := (P.diagram (pairKind familyB mate)).positiveBorder x y hx hy
  have hPD := (P.diagram (pairKind familyB other)).positiveBorder_positiveCorner u v hu hv
  have hPE := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner x y hx hy
  have hmin : min u v = min x y := by
    have h := D.border_minMargin_eq_of_schur_eq E
      ((P.diagram _).positiveBorder_connected u v hu hv)
      ((P.diagram _).positiveBorder_connected x y hx hy) hPD hPE
      (by simpa [D] using P.connected (pairKind familyB other))
      (by simpa [E] using P.connected (pairKind familyB mate)) he
    simpa [D, E] using h
  have hsum : u+v = x+y := by
    have h := D.largestLabel_eq_of_schur_eq E
      ((P.diagram _).positiveBorder_connected u v hu hv)
      ((P.diagram _).positiveBorder_connected x y hx hy) he
    simp only [D,E,BetaDiagram.positiveBorder_largestLabel,family_largestLabel] at h
    omega
  have hmargins : (x=u ∧ y=v) ∨ (x=v ∧ y=u) := by omega
  rcases hmargins with ⟨hxu,hyv⟩ | ⟨hxv,hyu⟩
  · apply P.cross_orbit_borders_ne_aligned familyB other mate hne u v hu hv false
    simpa only [Bool.false_eq_true,ite_false,hxu,hyv] using he
  · apply P.cross_orbit_borders_ne_aligned familyB other mate hne u v hu hv true
    simpa only [ite_true,hxv,hyu] using he

private theorem border_aligned_family (P : TenParameters) (familyB other mate : Bool)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (E : BetaDiagram 8)
    (hE : E.Connected) (hPE : E.PositiveCorner)
    (hcore : (P.diagram (pairKind familyB mate)).TranslationEquivalent (E.cornerDiagram hPE))
    (he : ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).schur = E.schur) :
    ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).TranslationEquivalent E ∨
      ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).RotationEquivalent E := by
  let D := (P.diagram (pairKind familyB other)).positiveBorder u v hu hv
  let B := (P.diagram (pairKind familyB mate)).positiveBorder
    E.topMargin E.bottomMargin E.topMargin_pos E.bottomMargin_pos
  have hPB := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner
    E.topMargin E.bottomMargin E.topMargin_pos E.bottomMargin_pos
  have hBE : B.TranslationEquivalent E := by
    apply B.translation_of_corner_translation_of_margins E hPB hPE
    · simpa [B] using hcore
    · simp [B]
    · simp [B]
  have hsame : other = mate := by
    by_contra hn
    exact P.cross_orbit_borders_ne familyB other mate hn u v E.topMargin E.bottomMargin
      hu hv E.topMargin_pos E.bottomMargin_pos (he.trans hBE.schur_eq.symm)
  subst mate
  have hPD := (P.diagram (pairKind familyB other)).positiveBorder_positiveCorner u v hu hv
  have hCE : (E.cornerDiagram hPE).Connected := by
    apply BetaDiagram.connected_of_schur_irreducible _ (by omega)
    rw [← hcore.schur_eq]
    exact (P.diagram _).schur_irreducible (P.connected _)
  apply D.connected_border_aligned_rigidity E
    ((P.diagram _).positiveBorder_connected u v hu hv) hE hPD hPE
    (by simpa [D] using P.connected (pairKind familyB other)) hCE
    (by simpa [D] using hcore) ?_ he
  intro t ht hends
  have hne := P.exceptional_endpoint_ne_including_units (pairKind familyB other) t ht
  exact (hne (by simpa [D] using hends)).elim

/-- Every positive border over an exceptional seven-row representative is rigid
against arbitrary connected mates, for all margins and all common-beta boundaries. -/
theorem positiveBorder_rotationRigid (P : TenParameters) (familyB other : Bool)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).RotationRigid := by
  let D := (P.diagram (pairKind familyB other)).positiveBorder u v hu hv
  have hD : D.Connected := (P.diagram _).positiveBorder_connected u v hu hv
  have hPD := (P.diagram (pairKind familyB other)).positiveBorder_positiveCorner u v hu hv
  apply (D.rotationRigid_iff_same_order).mpr
  intro E hE he
  let hPE := D.positiveCorner_of_cornerPolynomial_eq E hD hE hPD
    (D.cornerPolynomial_eq_of_schur_eq E hD hE he.symm)
  have hCE := D.connected_corner_of_corner_eq E hD hE hPD
    (by simpa [D] using P.connected (pairKind familyB other)) he.symm
  have hchild : (P.diagram (pairKind familyB other)).schur = (E.cornerDiagram hPE).schur := by
    rw [E.cornerDiagram_schur hPE]
    simpa [D] using D.cornerPolynomial_eq_of_schur_eq E hD hE he.symm
  obtain ⟨mate, hn, hm⟩ := (P.complete_class familyB other (E.cornerDiagram hPE) hCE).mp hchild
  have hh : hn = rfl := Subsingleton.elim _ _
  rw [hh] at hm
  simp only [BetaDiagram.castOrder] at hm
  rcases hm with hT | hR
  · exact P.border_aligned_family familyB other mate u v hu hv E hE hPE hT he.symm
  · let B := (P.diagram (pairKind familyB mate)).positiveBorder u v hu hv
    have hPB := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner u v hu hv
    have hRot :
        (P.diagram (pairKind familyB mate)).TranslationEquivalent
          (E.rotate.cornerDiagram (E.rotate_positiveCorner hPE)) := by
      have h := B.corner_translation_of_rotation E hPB hPE (by simpa [B] using hR)
      simpa [B] using h
    have hEq : D.schur = E.rotate.schur := he.symm.trans E.rotate_schur.symm
    rcases P.border_aligned_family familyB other mate u v hu hv E.rotate
      (E.rotate_connected hE) (E.rotate_positiveCorner hPE) hRot hEq with hT | hR
    · exact Or.inr ((D.translation_rotate_iff_rotation E).mp hT)
    · exact Or.inl ((D.rotation_rotate_iff_translation E).mp hR)

/-- No connectedness or order restriction is imposed on the full-board mate. -/
theorem positiveBorder_full_class {n : ℕ} (P : TenParameters) (familyB other : Bool)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (E : BetaDiagram n)
    (he : E.schur = ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).schur) :
    ((P.diagram (pairKind familyB other)).positiveBorder u v hu hv).MotionEquivalent E :=
  (P.positiveBorder_rotationRigid familyB other u v hu hv).full_mate
    ((P.diagram _).positiveBorder_connected u v hu hv) E he

private theorem positiveBorder_rotate_translation {n : ℕ} (Q : BetaDiagram (n+1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (Q.rotate.positiveBorder u v hu hv).TranslationEquivalent
      (Q.positiveBorder v u hv hu).rotate := by
  refine ⟨0,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      simp only [BetaDiagram.positiveBorder_row_zero,BetaDiagram.rotate,
        Fin.rev_zero,BetaDiagram.positiveBorder_col_last]
      ring
    | succ i =>
      simp only [BetaDiagram.positiveBorder_row_succ,BetaDiagram.rotate,
        Fin.rev_succ,BetaDiagram.positiveBorder_col_castSucc,add_zero]
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [BetaDiagram.positiveBorder_col_last,BetaDiagram.rotate,
        Fin.rev_last,BetaDiagram.positiveBorder_row_zero]
      ring
    | cast i =>
      simp only [BetaDiagram.positiveBorder_col_castSucc,BetaDiagram.rotate,
        Fin.rev_castSucc,BetaDiagram.positiveBorder_row_succ,add_zero]

/-- The other two translation classes have the same all-margin border rigidity:
their positive borders are literal rotations of the margin-swapped borders. -/
theorem rotated_positiveBorder_rotationRigid (P : TenParameters) (familyB other : Bool)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    ((P.diagram (pairKind familyB other)).rotate.positiveBorder u v hu hv).RotationRigid := by
  let B := (P.diagram (pairKind familyB other)).positiveBorder v u hv hu
  have hT := positiveBorder_rotate_translation (P.diagram (pairKind familyB other)) u v hu hv
  exact BetaDiagram.rotationRigid_of_translation _ _ hT
    (BetaDiagram.rotationRigid_rotate B
      (P.positiveBorder_rotationRigid familyB other v u hv hu))

/-- The reflected-family full-board wrapper also derives every mate's order and connectedness. -/
theorem rotated_positiveBorder_full_class {n : ℕ} (P : TenParameters) (familyB other : Bool)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (E : BetaDiagram n)
    (he : E.schur =
      ((P.diagram (pairKind familyB other)).rotate.positiveBorder u v hu hv).schur) :
    ((P.diagram (pairKind familyB other)).rotate.positiveBorder u v hu hv).MotionEquivalent E :=
  (P.rotated_positiveBorder_rotationRigid familyB other u v hu hv).full_mate
    ((P.diagram _).rotate.positiveBorder_connected u v hu hv) E he

/-- An actual eight-row source with an exceptional child is rigid.
The child's complete class and every border margin are reconstructed inside the proof. -/
theorem corner_schur_rotationRigid (P : TenParameters) (familyB other : Bool)
    (D : BetaDiagram 8) (hD : D.Connected) (hPD : D.PositiveCorner)
    (hchild : (P.diagram (pairKind familyB other)).schur = (D.cornerDiagram hPD).schur) :
    D.RotationRigid := by
  have hC : (D.cornerDiagram hPD).Connected := by
    apply BetaDiagram.connected_of_schur_irreducible _ (by omega)
    rw [← hchild]
    exact (P.diagram _).schur_irreducible (P.connected _)
  obtain ⟨mate,hn,hm⟩ := (P.complete_class familyB other (D.cornerDiagram hPD) hC).mp hchild
  have hh : hn = rfl := Subsingleton.elim _ _
  rw [hh] at hm
  simp only [BetaDiagram.castOrder] at hm
  have aligned (F : BetaDiagram 8) (hF : F.Connected) (hPF : F.PositiveCorner)
      (hT : (P.diagram (pairKind familyB mate)).TranslationEquivalent
        (F.cornerDiagram hPF)) : F.RotationRigid := by
    let B := (P.diagram (pairKind familyB mate)).positiveBorder
      F.topMargin F.bottomMargin F.topMargin_pos F.bottomMargin_pos
    have hPB := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner
      F.topMargin F.bottomMargin F.topMargin_pos F.bottomMargin_pos
    have hBF : B.TranslationEquivalent F := by
      apply B.translation_of_corner_translation_of_margins F hPB hPF
      · simpa [B] using hT
      · simp [B]
      · simp [B]
    have hFB : F.TranslationEquivalent B := by
      obtain ⟨c,hr,hc⟩ := hBF
      refine ⟨-c,?_,?_⟩ <;> intro i
      · have := hr i; omega
      · have := hc i; omega
    exact F.rotationRigid_of_translation B hFB
      (P.positiveBorder_rotationRigid familyB mate
        F.topMargin F.bottomMargin F.topMargin_pos F.bottomMargin_pos)
  rcases hm with hT | hR
  · exact aligned D hD hPD hT
  · let B := (P.diagram (pairKind familyB mate)).positiveBorder 1 1
      (by norm_num) (by norm_num)
    have hPB := (P.diagram (pairKind familyB mate)).positiveBorder_positiveCorner 1 1
      (by norm_num) (by norm_num)
    have hT : (P.diagram (pairKind familyB mate)).TranslationEquivalent
        (D.rotate.cornerDiagram (D.rotate_positiveCorner hPD)) := by
      have h := B.corner_translation_of_rotation D hPB hPD (by simpa [B] using hR)
      simpa [B] using h
    exact D.rotationRigid_of_rotate
      (aligned D.rotate (D.rotate_connected hD) (D.rotate_positiveCorner hPD) hT)

end SkewJacobiNegative.TenParameters

namespace SkewJacobiNegative.BetaDiagram

/-- `lem:ten-negative-endpoints` for every seven-row source in the stratum:
opposite endpoint equality forces symmetry without assuming endpoint rigidity. -/
theorem ten_seven_endpoint_isolation (D : BetaDiagram 7) (hD : D.Connected)
    (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7)
    (t : ℤ) (ht : 0 < t)
    (he : (D.extendTop t ht).schur = (D.extendBottom t ht).schur) : D.Symmetric := by
  have hTopCount : negativeCount (D.extendTop t ht) = 10 := by
    rw [D.extendTop_negativeCount]
    exact hCount
  have hTopMin : minimumRealizingRows (negativePartition (D.extendTop t ht)) = 7 := by
    rw [D.extendTop_negativePartition]
    exact hMin
  rcases (D.extendTop t ht).ten_seven_classification
    (D.extendTop_connected hD t ht) hTopCount hTopMin with hRigid | hExceptional
  · apply (D.endpointDifference_eq_zero_iff_of_rigidity hD t ht hRigid).mp
    exact sub_eq_zero.mpr he
  · obtain ⟨P,familyB,other,hm⟩ := hExceptional
    exact (P.opposite_endpoints_ne_of_exceptional_top familyB other D hD t ht
      (ten_motion_symm hm) he).elim

/-- The complete endpoint assertion, with common betas retained. -/
theorem ten_seven_endpoint_eq_iff (D : BetaDiagram 7) (hD : D.Connected)
    (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7)
    (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).schur = (D.extendBottom t ht).schur ↔ D.Symmetric := by
  constructor
  · exact D.ten_seven_endpoint_isolation hD hCount hMin t ht
  · intro hS
    have hz := D.endpointDifference_eq_zero_of_symmetric hS t ht
    exact sub_eq_zero.mp hz

/-- Genuine connected-child induction in the minimum-seven ten-negative
stratum.  The first higher-row step uses all-margin exceptional-child
separation, not a false assertion that every seven-row child is rigid. -/
theorem ten_higher_zeroFree_rigidity {n : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) (hn : 8 ≤ n) :
    D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3,by omega⟩
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    let C := D.cornerDiagram hP
    have hC : C.Connected := (D.corner_connected_iff_above_minimum hP).mpr (by omega)
    have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
    have hCCount : negativeCount C = 10 := by
      rw [D.corner_negativeCount]
      exact hCount
    have hCMin : minimumRealizingRows (negativePartition C) = 7 := by
      rw [D.corner_negativePartition]
      exact hMin
    by_cases hk : k = 5
    · subst k
      rcases C.ten_seven_zeroFree_classification hC hCZ hCCount hCMin
        with hRigid | ⟨P,familyB,other,hm⟩
      · apply D.connected_border_endpoint_isolation hD hP hC hRigid
        intro t ht he
        exact C.ten_seven_endpoint_isolation hC hCCount hCMin t ht he
      · exact P.corner_schur_rotationRigid familyB other D hD hP
          (ten_motion_schur_eq hm).symm
    · have hCOrder : 8 ≤ k+2 := by omega
      have hRigid := ih (k+2) (by omega) C hC hCZ hCCount hCMin hCOrder
      apply D.connected_border_rigidity hD hP hC hRigid
      intro t ht
      apply ih (k+2) (by omega) (C.extendTop t ht)
        (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
      · rw [C.extendTop_negativeCount]
        exact hCCount
      · rw [C.extendTop_negativePartition]
        exact hCMin
      · exact hCOrder

/-- Every actual row count at least eight is rigid, including common-beta units. -/
theorem ten_higher_rigidity {n : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) (hn : 8 ≤ n) :
    D.RotationRigid := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  apply D.gamma_rigidity_descends hD
  apply D.gamma.ten_higher_zeroFree_rigidity ((D.gamma_connected_iff).mpr hD)
    D.gamma_zeroFree
  · rw [D.gamma_negativeCount]
    exact hCount
  · rw [D.gamma_negative_partition]
    exact hMin
  · exact hn

/-- Higher-row rigidity imposes no connectedness or order restriction on a full-board mate. -/
theorem ten_higher_full_class {n m : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) (hn : 8 ≤ n)
    (E : BetaDiagram m) : E.schur = D.schur ↔ D.MotionEquivalent E := by
  constructor
  · exact (D.ten_higher_rigidity hD hCount hMin hn).full_mate hD E
  · intro hm
    exact (ten_motion_schur_eq hm).symm

/-- `thm:ten-negative-classification` in the full-board model.  The only source
assumptions are connectedness, exactly ten negatives, and minimum realizing
order seven.  Exceptional classes are the four distinct actual translation
classes with proper literal charts; all higher actual row counts are rigid. -/
theorem ten_negative_classification {n : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) :
    (D.RotationRigid ∨
      ∃ (P : TenParameters) (familyB other : Bool),
        n = 7 ∧ D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) ∧
        (∀ (m : ℕ) (E : BetaDiagram m), E.schur = D.schur ↔
          ∃ mate, (P.diagram (TenParameters.pairKind familyB mate)).MotionEquivalent E) ∧
        [P.diagram (TenParameters.pairKind familyB false),
          (P.diagram (TenParameters.pairKind familyB false)).rotate,
          P.diagram (TenParameters.pairKind familyB true),
          (P.diagram (TenParameters.pairKind familyB true)).rotate].Pairwise
            (fun F G => ¬ F.TranslationEquivalent G) ∧
        (∀ k : TenKind, TenCells.ConnectedIntervals (TenCells.outer k) ∧
          ((0,1) ∈ TenCells.outer k ∧ (0,2) ∈ TenCells.outer k) ∧
          TenCells.translate (TenCells.compositionC P k) (5,0) =
            TenCells.betaCells (P.diagram k))) ∧
    (8 ≤ n → D.RotationRigid) := by
  classical
  refine ⟨?_,D.ten_higher_rigidity hD hCount hMin⟩
  have hSeven : 7 ≤ n := by
    have h := (D.connected_iff_minimumRealizingRows_le).mp hD
    rw [hMin] at h
    exact h
  by_cases hn : n = 7
  · subst n
    rcases D.ten_seven_classification hD hCount hMin with hRigid | ⟨P,familyB,other,hm⟩
    · exact Or.inl hRigid
    · refine Or.inr ⟨P,familyB,other,rfl,hm,?_,P.complete_class_distinct familyB,?_⟩
      · intro m E
        exact D.ten_complete_exceptional_class P familyB other hm E
      · intro k
        exact ⟨TenCells.outer_connected k,TenCells.outer_proper k,
          TenCells.compositionC_eq_betaCells P k⟩
  · exact Or.inl (D.ten_higher_rigidity hD hCount hMin (by omega))

/-- Necessity and sufficiency of the two displayed families as the complete
nonrigidity locus; exceptional membership is a conclusion, never an assumption. -/
theorem ten_negative_rotationRigid_iff {n : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) :
    D.RotationRigid ↔ ¬ ∃ (P : TenParameters) (familyB other : Bool),
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
  constructor
  · intro hRigid hex
    exact D.not_rotationRigid_of_ten_exceptional hex hRigid
  · intro hNo
    rcases (D.ten_negative_classification hD hCount hMin).1 with hRigid | hExceptional
    · exact hRigid
    · obtain ⟨P,familyB,other,_,hm,_⟩ := hExceptional
      exact (hNo ⟨P,familyB,other,hm⟩).elim

/-- Every nonexceptional source is rigid against unrestricted full-board mates. -/
theorem ten_negative_nonexceptional_full_class {n m : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7)
    (hNo : ¬ ∃ (P : TenParameters) (familyB other : Bool),
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)))
    (E : BetaDiagram m) : E.schur = D.schur ↔ D.MotionEquivalent E := by
  constructor
  · exact ((D.ten_negative_rotationRigid_iff hD hCount hMin).mpr hNo).full_mate hD E
  · intro hm
    exact (ten_motion_schur_eq hm).symm

end SkewJacobiNegative.BetaDiagram
