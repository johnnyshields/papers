/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.TenExceptionalContexts
import SkewJacobiNegative.TenNegativeBorders
import SkewJacobiNegative.NegativeBudgetInventory
import SkewJacobiNegative.TwoComponentLift
import SkewJacobiNegative.LowNegativePatterns
import SkewJacobiNegative.FiveSingletonRigidity
import SkewJacobiNegative.OneNegativeThreeComponentPlacements
import SkewJacobiNegative.NegativeThreshold
import SkewJacobiNegative.FiveBorderExclusion

/-!
# Complete classes of the displayed ten-negative families

The exceptional-class assertion of `thm:ten-negative-classification`, using
`prop:exceptional-singleton-context` on the genuine singleton parents.
Faithful Gamma transport retains the common-beta boundary and recovers the
original integer parameters as in `lem:homogenization`.
The source-cut ingredients of `prop:ten-negative-base` use the genuine
reconstruction in `lem:two-component-lift` and `lem:singleton-five-rigid`.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

private theorem ten_diagram_ext {n : ℕ} {D E : BetaDiagram n}
    (hr : D.row = E.row) (hc : D.col = E.col) : D = E := by
  cases D
  cases E
  simp only [BetaDiagram.mk.injEq]
  exact ⟨hr, hc⟩

private theorem ten_translation_symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : E.TranslationEquivalent D := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨-c, ?_, ?_⟩ <;> intro i
  · have := hr i; omega
  · have := hc i; omega

private theorem ten_translation_trans {n : ℕ} {D E F : BetaDiagram n}
    (h : D.TranslationEquivalent E) (h' : E.TranslationEquivalent F) :
    D.TranslationEquivalent F := by
  obtain ⟨c, hr, hc⟩ := h
  obtain ⟨d, hs, hd⟩ := h'
  refine ⟨c + d, ?_, ?_⟩ <;> intro i
  · have := hr i; have := hs i; omega
  · have := hc i; have := hd i; omega

/-- Translation of the source preserves its arbitrary-order motion class. -/
theorem ten_motion_source_translation_iff {n m : ℕ} {D F : BetaDiagram n}
    (h : D.TranslationEquivalent F) (E : BetaDiagram m) :
    D.MotionEquivalent E ↔ F.MotionEquivalent E := by
  have step {A B : BetaDiagram n} (hAB : A.TranslationEquivalent B)
      (hm : A.MotionEquivalent E) : B.MotionEquivalent E := by
    obtain ⟨hn, ht | hr⟩ := hm
    · exact ⟨hn, Or.inl (ten_translation_trans (ten_translation_symm hAB) ht)⟩
    · refine ⟨hn, Or.inr ?_⟩
      apply (B.translation_rotate_iff_rotation _).mp
      exact ten_translation_trans (ten_translation_symm hAB)
        ((A.translation_rotate_iff_rotation _).mpr hr)
  exact ⟨step h, step (ten_translation_symm h)⟩

/-- The actual motion relation implies equality of the full Schur functions. -/
theorem ten_motion_schur_eq {n m : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    (h : D.MotionEquivalent E) : D.schur = E.schur := by
  obtain ⟨hn, ht | hr⟩ := h
  · simpa only [castOrder_schur] using ht.schur_eq
  · have ht := (D.translation_rotate_iff_rotation _).mpr hr
    simpa only [rotate_schur, castOrder_schur] using ht.schur_eq

end BetaDiagram

namespace TenParameters

/-- The two displayed representatives, with the Boolean selecting family B. -/
def pairKind (familyB other : Bool) : TenKind :=
  if familyB then (if other then .hb else .fb) else (if other then .ha else .fa)

/-- Every displayed representative has its family's original Schur function. -/
theorem pair_schur_eq (P : TenParameters) (familyB other : Bool) :
    (P.diagram (pairKind familyB other)).schur =
      (P.diagram (pairKind familyB false)).schur := by
  cases familyB <;> cases other
  · rfl
  · change (P.diagram .ha).schur = (P.diagram .fa).schur
    exact P.schur_eq_A.symm
  · rfl
  · change (P.diagram .hb).schur = (P.diagram .fb).schur
    exact P.schur_eq_B.symm

/-- The inverse five-row parameters are read from the seven-row family parameters. -/
def singletonCoreParameters (P : TenParameters) : FiveExceptional.Parameters where
  q := P.a
  b := P.a + P.d
  g := P.b
  q_pos := P.a_pos
  q_le_b := by have := P.d_nonneg; omega
  b_lt_g := P.separated

private theorem singletonCore_strict (P : TenParameters) (hd : 0 < P.d) :
    P.singletonCoreParameters.q < P.singletonCoreParameters.b := by
  change P.a < P.a + P.d
  omega

private theorem singletonCore_tenParameters (P : TenParameters) (hd : 0 < P.d) :
    FiveExceptional.singletonTenParameters P.singletonCoreParameters
      (P.singletonCore_strict hd) = P := by
  cases P
  simp only [singletonCoreParameters, FiveExceptional.singletonTenParameters,
    TenParameters.mk.injEq]
  constructor
  · trivial
  constructor
  · trivial
  · omega

private theorem singletonCore_translation (P : TenParameters) (hd : 0 < P.d)
    (familyB other : Bool) :
    (FiveExceptional.exceptionalSingleton P.singletonCoreParameters
      (P.singletonCore_strict hd) (!familyB) other).TranslationEquivalent
      (P.diagram (pairKind familyB other)) := by
  have h := FiveExceptional.exceptionalSingleton_translation P.singletonCoreParameters
    (P.singletonCore_strict hd) (!familyB) other
  rw [P.singletonCore_tenParameters hd] at h
  cases familyB <;> cases other <;>
    simpa only [pairKind, FiveExceptional.singletonTenKind, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, if_false, if_true] using h

/-- Necessity of the quartet class, obtained from actual singleton reconstruction. -/
theorem complete_class_zeroFree {n : ℕ} (P : TenParameters) (hd : 0 < P.d)
    (familyB other : Bool) (E : BetaDiagram n) (hE : E.Connected)
    (he : (P.diagram (pairKind familyB other)).schur = E.schur) :
    ∃ mate, (P.diagram (pairKind familyB mate)).MotionEquivalent E := by
  let C := P.singletonCoreParameters
  let hp := P.singletonCore_strict hd
  obtain ⟨hs, hu, hv, hg⟩ := FiveExceptional.singleton_locus_positive C hp
  have hlocal :
      ((FiveExceptional.coreCandidate C (!familyB) other true).singletonContext
        (C.b-C.q) C.q C.g (C.g-C.b) hs hu hv hg).schur = E.schur := by
    have hT := P.singletonCore_translation hd familyB other
    have hcontext :
        ((FiveExceptional.coreCandidate C (!familyB) other true).singletonContext
          (C.b-C.q) C.q C.g (C.g-C.b) hs hu hv hg).schur =
        (P.diagram (pairKind familyB other)).schur := by
      cases other <;>
        simpa [FiveExceptional.exceptionalSingleton, FiveExceptional.coreCandidate,
          C, hp] using hT.schur_eq
    exact hcontext.trans he
  obtain ⟨mate, rotated, hallowed, hm⟩ :=
    (FiveExceptional.exceptional_singleton_complete_class C hp (!familyB) other true
      (C.b-C.q) C.q C.g (C.g-C.b) hs hu hv hg E hE).mp hlocal
  have hr : rotated = true := by
    rcases hallowed with hsame | hbad
    · exact (congrArg Prod.snd hsame).symm
    · exact hbad.2.1
  subst rotated
  refine ⟨mate, ?_⟩
  apply (BetaDiagram.ten_motion_source_translation_iff
    (P.singletonCore_translation hd familyB mate) E).mp
  cases mate <;>
    simpa [FiveExceptional.exceptionalSingleton, FiveExceptional.coreCandidate,
      C, hp] using hm

/-- Gamma transforms every genuine seven-row representative with no deleted units. -/
theorem gamma_diagram (P : TenParameters) (k : TenKind) :
    (P.diagram k).gamma = P.gammaParameters.diagram k := by
  apply BetaDiagram.ten_diagram_ext
  · funext i
    cases k <;> fin_cases i <;>
      simp [BetaDiagram.gamma, diagram, rowBase, gammaParameters] <;> ring
  · funext i
    fin_cases i <;> simp [BetaDiagram.gamma, diagram, column, gammaParameters] <;> ring

/-- Every connected mate of a displayed family member lies in its exact quartet,
including the original common-beta boundary. -/
theorem complete_class {n : ℕ} (P : TenParameters) (familyB other : Bool)
    (E : BetaDiagram n) (hE : E.Connected) :
    (P.diagram (pairKind familyB other)).schur = E.schur ↔
      ∃ mate, (P.diagram (pairKind familyB mate)).MotionEquivalent E := by
  constructor
  · intro he
    have hn : n = 7 := ((P.diagram (pairKind familyB other)).row_count_of_schur_eq E he).symm
    let F := E.castOrder hn
    have hF : F.Connected := (E.castOrder_connected hn).mpr hE
    have heF : (P.diagram (pairKind familyB other)).schur = F.schur := by
      simpa only [F, BetaDiagram.castOrder_schur] using he
    have heG := ((P.diagram (pairKind familyB other)).gamma_schur_eq_iff_same_order
      F (P.connected _) hF).mpr heF
    rw [P.gamma_diagram] at heG
    obtain ⟨mate, hh, hm⟩ := P.gammaParameters.complete_class_zeroFree
      P.gammaParameters_d_pos familyB other F.gamma
      ((F.gamma_connected_iff).mpr hF) heG
    have hhh : hh = rfl := Subsingleton.elim _ _
    rw [hhh] at hm
    simp only [BetaDiagram.castOrder] at hm
    rw [← P.gamma_diagram] at hm
    refine ⟨mate, hn.symm, ?_⟩
    rcases hm with ht | hr
    · exact Or.inl (((P.diagram _).gamma_translation_iff F).mp ht)
    · exact Or.inr (((P.diagram _).gamma_rotation_iff F).mp hr)
  · rintro ⟨mate, hm⟩
    have hpair : (P.diagram (pairKind familyB other)).schur =
        (P.diagram (pairKind familyB mate)).schur :=
      (P.pair_schur_eq familyB other).trans (P.pair_schur_eq familyB mate).symm
    exact hpair.trans (BetaDiagram.ten_motion_schur_eq hm)

/-- The full-board wrapper derives connectedness and retains arbitrary mate row count. -/
theorem full_class {n : ℕ} (P : TenParameters) (familyB other : Bool)
    (E : BetaDiagram n) :
    (P.diagram (pairKind familyB other)).schur = E.schur ↔
      ∃ mate, (P.diagram (pairKind familyB mate)).MotionEquivalent E := by
  constructor
  · intro he
    exact (P.complete_class familyB other E
      ((P.diagram _).connected_full_mate_of_schur_eq E (P.connected _) he)).mp he
  · rintro ⟨mate, hm⟩
    have hE : E.Connected := by
      have he : (P.diagram (pairKind familyB mate)).schur = E.schur :=
        BetaDiagram.ten_motion_schur_eq hm
      exact (P.diagram _).connected_full_mate_of_schur_eq E (P.connected _) he
    exact (P.complete_class familyB other E hE).mpr ⟨mate, hm⟩

/-- The quartet has exactly four distinct translation classes, not four rotation classes. -/
theorem complete_class_distinct (P : TenParameters) (familyB : Bool) :
    [P.diagram (pairKind familyB false), (P.diagram (pairKind familyB false)).rotate,
      P.diagram (pairKind familyB true), (P.diagram (pairKind familyB true)).rotate].Pairwise
      (fun D E => ¬ D.TranslationEquivalent E) := by
  apply P.quartet_pairwise_distinct
  cases familyB <;> decide

/-- Every displayed representative is a genuine nonrotation exception. -/
theorem not_rotationRigid (P : TenParameters) (familyB other : Bool) :
    ¬ (P.diagram (pairKind familyB other)).RotationRigid := by
  intro hR
  have he : (P.diagram (pairKind familyB (!other))).schur =
      (P.diagram (pairKind familyB other)).schur :=
    (P.pair_schur_eq familyB (!other)).trans (P.pair_schur_eq familyB other).symm
  obtain ⟨hn, hm⟩ := hR 7 (P.diagram (pairKind familyB (!other))) (P.connected _) he
  have hhn : hn = rfl := Subsingleton.elim _ _
  rw [hhn] at hm
  simp only [BetaDiagram.castOrder] at hm
  rcases hm with ht | hr
  · exact P.not_translation _ _ (by cases familyB <;> cases other <;> decide) ht
  · exact P.not_rotation _ _ hr

end TenParameters
end SkewJacobiNegative

namespace SkewJacobiNegative.TenParameters

private theorem parameters_ext {P Q : TenParameters}
    (ha : P.a = Q.a) (hb : P.b = Q.b) (hd : P.d = Q.d) : P = Q := by
  cases P
  cases Q
  simp only [TenParameters.mk.injEq]
  exact ⟨ha, hb, hd⟩

/-- The actual Gamma beta lists force even `a,b` and odd `d`, and recover
the original family parameters without deleting common beta entries. -/
theorem parameters_of_gamma_translation (P : TenParameters) (D : BetaDiagram 7)
    (k : TenKind) (h : D.gamma.TranslationEquivalent (P.diagram k)) :
    ∃ Q : TenParameters, P = Q.gammaParameters ∧
      D.TranslationEquivalent (Q.diagram k) := by
  obtain ⟨c, hr, hc⟩ := h
  have hr0 := hr 0
  have hr1 := hr 1
  have hc0 := hc 0
  have hc5 := hc 5
  have hc6 := hc 6
  have ha : P.a = 2 * (D.row 0 - D.row 1) := by
    cases k <;>
      norm_num [BetaDiagram.gamma, diagram, rowBase] at hr0 hr1 <;> omega
  have hb : P.b = 2 * (D.col 5 - D.col 6) := by
    norm_num [BetaDiagram.gamma, diagram, column] at hc5 hc6
    omega
  have hd : P.d = 2 * (D.row 1 - D.col 0) + 1 := by
    cases k <;>
      norm_num [BetaDiagram.gamma, diagram, rowBase, column] at hr1 hc0 <;> omega
  let Q : TenParameters :=
    { a := D.row 0 - D.row 1
      b := D.col 5 - D.col 6
      d := D.row 1 - D.col 0
      a_pos := by have := P.a_pos; omega
      d_nonneg := by have := P.d_nonneg; omega
      separated := by have := P.separated; omega }
  have hpq : P = Q.gammaParameters := by
    apply parameters_ext
    · change P.a = 2 * (D.row 0 - D.row 1)
      exact ha
    · change P.b = 2 * (D.col 5 - D.col 6)
      exact hb
    · change P.d = 2 * (D.row 1 - D.col 0) + 1
      exact hd
  refine ⟨Q, hpq, ?_⟩
  apply (D.gamma_translation_iff (Q.diagram k)).mp
  rw [Q.gamma_diagram, ← hpq]
  exact ⟨c, hr, hc⟩

/-- Parameter recovery also covers either orientation of the affine image. -/
theorem parameters_of_gamma_motion (P : TenParameters) (D : BetaDiagram 7)
    (k : TenKind) (h : D.gamma.MotionEquivalent (P.diagram k)) :
    ∃ Q : TenParameters, P = Q.gammaParameters ∧
      D.MotionEquivalent (Q.diagram k) := by
  obtain ⟨hn, hm⟩ := h
  have hh : hn = rfl := Subsingleton.elim _ _
  rw [hh] at hm
  simp only [BetaDiagram.castOrder] at hm
  rcases hm with ht | hr
  · obtain ⟨Q, hpq, hQ⟩ := P.parameters_of_gamma_translation D k ht
    exact ⟨Q, hpq, rfl, Or.inl hQ⟩
  · obtain ⟨c, hrow, hcol⟩ := hr
    have hrot : D.rotate.gamma.TranslationEquivalent (P.diagram k) := by
      refine ⟨1 - c, ?_, ?_⟩ <;> intro i
      · have h := hcol i.rev
        simp only [BetaDiagram.gamma, Fin.rev_rev] at h
        change 2 * (-D.col i.rev) + 1 = (P.diagram k).row i + (1 - c)
        omega
      · have h := hrow i.rev
        simp only [BetaDiagram.gamma, Fin.rev_rev] at h
        change 2 * (-D.row i.rev) = (P.diagram k).col i + (1 - c)
        omega
    obtain ⟨Q, hpq, t, hQrow, hQcol⟩ :=
      P.parameters_of_gamma_translation D.rotate k hrot
    refine ⟨Q, hpq, rfl, Or.inr ⟨-t, ?_, ?_⟩⟩ <;> intro i
    · have h := hQcol i.rev
      simp only [BetaDiagram.rotate, Fin.rev_rev] at h
      change D.row i = -t - (Q.diagram k).col i.rev
      omega
    · have h := hQrow i.rev
      simp only [BetaDiagram.rotate, Fin.rev_rev] at h
      change D.col i = -t - (Q.diagram k).row i.rev
      omega

end SkewJacobiNegative.TenParameters

namespace SkewJacobiNegative.BetaDiagram

/-- The exact six-row maximal-cofactor inventory in `eq:ten-negative-budget`
is produced from the actual seven-row source and its canonical decomposition. -/
theorem ten_seven_maximal_cofactor_inventory (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) :
    let R := D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)
    ((R.componentDecomposition.components.map Sigma.fst).insertionSort (· ≤ ·),
      (R.componentDecomposition.components.map (fun X => negativeCount X.2)).sum) ∈
      [([1,5],5), ([2,4],2), ([3,3],1), ([1,1,4],1)] := by
  let R := D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)
  let C := R.componentDecomposition
  change ((C.components.map Sigma.fst).insertionSort (· ≤ ·),
    (C.components.map (fun X => negativeCount X.2)).sum) ∈
      [([1,5],5), ([2,4],2), ([3,3],1), ([1,1,4],1)]
  have hR : ¬ R.Connected := (D.corner_disconnected_iff_minimum hD _).mpr hMin.symm
  have hCountR : negativeCount R = 10 := by
    rw [D.corner_negativeCount]
    exact hCount
  have h := C.ten_negative_inventory_exact (by omega) hR hCountR
  have hsum := C.component_rows_sum
  have hsort := List.perm_insertionSort (fun a b : ℕ => a ≤ b)
    (C.components.map Sigma.fst)
  have hs : ((C.components.map Sigma.fst).insertionSort (· ≤ ·)).sum = 6 := by
    exact hsort.sum_eq.trans hsum
  simp only [ComponentOrderInventory.tenPatterns, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨horders,hinternal⟩
    rw [horders] at hs
    norm_num at hs <;> simp [horders, hinternal]

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.FiveExceptional

/-- A nonrigid genuine singleton parent over an exceptional five-row core
forces the displayed seven-row parameters and an actual translated representative. -/
theorem nonrigid_singleton_is_ten_family (P : Parameters) (hp : P.q < P.b)
    (second middle rotated : Bool) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g)
    (hnonrigid :
      ¬ ((coreCandidate P second middle rotated).singletonContext
        s u v g hs hu hv hg).RotationRigid) :
    ∃ T : TenParameters, ∃ familyB other,
      ((coreCandidate P second middle rotated).singletonContext
        s u v g hs hu hv hg).TranslationEquivalent
        (T.diagram (TenParameters.pairKind familyB other)) := by
  classical
  have hbad : rotated = true ∧ (s,u,v,g) = (P.b-P.q,P.q,P.g,P.g-P.b) := by
    by_contra hno
    exact hnonrigid ((exceptional_singleton_rotationRigid_iff P hp
      second middle rotated s u v g hs hu hv hg).mpr hno)
  obtain ⟨hr, hlocus⟩ := hbad
  have hl : s=P.b-P.q ∧ u=P.q ∧ v=P.g ∧ g=P.g-P.b := by
    simpa only [Prod.mk.injEq] using hlocus
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hl
  subst rotated
  refine ⟨singletonTenParameters P hp, !second, middle, ?_⟩
  have h := exceptionalSingleton_translation P hp second middle
  cases second <;> cases middle <;>
    simpa [coreCandidate, exceptionalSingleton, singletonTenKind,
      TenParameters.pairKind] using h

end SkewJacobiNegative.FiveExceptional

namespace SkewJacobiNegative.TenParameters

/-- The actual column progression and the first two row betas recover all parameters. -/
theorem parameters_eq_of_translation (P Q : TenParameters) (k l : TenKind)
    (h : (P.diagram k).TranslationEquivalent (Q.diagram l)) : P = Q := by
  obtain ⟨c, hr, hc⟩ := h
  have hc5 := hc 5
  have hc6 := hc 6
  have hr0 := hr 0
  have hr1 := hr 1
  have hb : P.b = Q.b := by
    norm_num [diagram, column] at hc5 hc6
    omega
  have ha : P.a = Q.a := by
    cases k <;> cases l <;>
      norm_num [diagram, rowBase, column] at hc6 hr0 hr1 <;> omega
  have hd : P.d = Q.d := by
    cases k <;> cases l <;>
      norm_num [diagram, rowBase, column] at hc6 hr1 <;> omega
  exact parameters_ext ha hb hd

/-- No representative of either family can be a reflected representative,
even after changing family parameters. -/
theorem not_rotation_any_parameters (P Q : TenParameters) (k l : TenKind) :
    ¬ (P.diagram k).RotationEquivalent (Q.diagram l) := by
  rintro ⟨c, hr, hc⟩
  have h3 := hr 3
  have h4 := hr 4
  have h5 := hr 5
  have h6 := hr 6
  have ha := P.a_pos
  have hb := P.separated
  have hd := P.d_nonneg
  cases k <;> cases l <;>
    norm_num [diagram, rowBase, column, Fin.rev] at h3 h4 h5 h6 <;> omega

/-- Distinct family parameters or different family types cannot describe one
connected Schur class.  The conclusion is derived from the complete actual class. -/
theorem family_parameters_eq_of_schur_eq (P Q : TenParameters)
    (familyB familyC other mate : Bool)
    (he : (P.diagram (pairKind familyB other)).schur =
      (Q.diagram (pairKind familyC mate)).schur) : P = Q ∧ familyB = familyC := by
  obtain ⟨candidate, hn, hm⟩ :=
    (P.complete_class familyB other (Q.diagram (pairKind familyC mate)) (Q.connected _)).mp he
  have hh : hn = rfl := Subsingleton.elim _ _
  rw [hh] at hm
  simp only [BetaDiagram.castOrder] at hm
  rcases hm with hT | hR
  · have hPQ := P.parameters_eq_of_translation Q _ _ hT
    subst Q
    refine ⟨rfl, ?_⟩
    by_contra hBC
    have hkind : pairKind familyB candidate ≠ pairKind familyC mate := by
      cases familyB <;> cases familyC <;> cases candidate <;> cases mate <;>
        simp_all [pairKind]
    exact P.not_translation _ _ hkind hT
  · exact (P.not_rotation_any_parameters Q _ _ hR).elim

end SkewJacobiNegative.TenParameters

namespace SkewJacobiNegative.BetaDiagram

private theorem ten_dense_of_zero_count {n : ℕ} (D : BetaDiagram n)
    (hZ : D.ZeroFree) (hCount : negativeCount D = 0) : D.Dense := by
  intro i j
  have hn : ¬ D.row i < D.col j := by
    intro h
    have hp : 0 < negativeCount D :=
      Finset.card_pos.mpr ⟨(i,j), (D.mem_negativeSites i j).mpr h⟩
    omega
  have := hZ i j
  omega

/-- Every actual four-row component with at most two negatives supplies its fixed leader. -/
theorem ten_four_core_endpointLeader (Q : BetaDiagram 4) (hQ : Q.Connected)
    (hZ : Q.ZeroFree) (hCount : negativeCount Q ≤ 2) (hS : ¬ Q.Symmetric) :
    Q.EndpointLeader := by
  interval_cases h : negativeCount Q
  · exact Q.endpointLeader_dense (ten_dense_of_zero_count Q hZ h) hS
  · exact Q.endpointLeader_one_negative_four hQ hZ h hS
  · exact Q.endpointLeader_two_negative_four hQ hZ h

/-- The connected three-row mask has at most its southwest negative cell;
its genuine binomial or dense leader supplies the lifting premise. -/
theorem ten_three_core_endpointLeader (Q : BetaDiagram 3) (hQ : Q.Connected)
    (hZ : Q.ZeroFree) (hS : ¬ Q.Symmetric) : Q.EndpointLeader := by
  have hbound := (Q.connected_iff_negativeRowCount_bound).mp hQ
  have h0 := hbound.2 0
  have h1 := hbound.2 1
  have h2 := hbound.2 2
  have hCount : negativeCount Q ≤ 1 := by
    rw [Q.negativeCount_eq_sum]
    norm_num [Fin.sum_univ_succ] at h0 h1 h2 ⊢
    omega
  interval_cases h : negativeCount Q
  · exact Q.endpointLeader_dense (ten_dense_of_zero_count Q hZ h) hS
  · exact Q.endpointLeader_one_negative_three hQ hZ h hS

/-- An actual `2+4` maximal cut in the ten-negative seven-row source is rigid.
The earlier singleton cut is separated explicitly; no mate placement is supplied. -/
theorem ten_two_four_cut_rigidity (D : BetaDiagram 7) (hD : D.Connected)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D = 10)
    (hcut : D.row 3 < D.col 1) (hNoFirst : ¬ D.row 2 < D.col 0) :
    D.RotationRigid := by
  let C := D.twoCutCore (p := 1) (r := 3) hP
  let Q := C.betaPrefix
  let R := C.suffix
  have hQZ : Q.ZeroFree := fun i j => hZ (i.castAdd 4).succ (j.castAdd 4).castSucc
  have hRZ : R.ZeroFree := fun i j => hZ (i.natAdd 2).succ (j.natAdd 2).castSucc
  have hQDense : Q.Dense := by
    intro i j
    have hz := hZ 2 0
    have hpos : D.col 0 < D.row 2 := by omega
    have hr := D.row_strictAnti.antitone
      (show (i.castAdd 4).succ ≤ (2 : Fin 7) by change i.val+1 ≤ 2; omega)
    have hc := D.col_strictAnti.antitone (Fin.zero_le (j.castAdd 4).castSucc)
    change D.col (j.castAdd 4).castSucc < D.row (i.castAdd 4).succ
    omega
  have hbudget := C.negativeCount_at_cut (a := 2) (b := 4)
    (by omega) (by omega) hcut
  have hCountC : negativeCount C = 10 := by
    change negativeCount ((D.cornerDiagram hP).reindexOrder _) = 10
    rw [reindexOrder_negativeCount, D.corner_negativeCount]
    exact hCount
  have hRCount : negativeCount R ≤ 2 := by
    dsimp [R]
    rw [hCountC] at hbudget
    omega
  have hR : R.Connected := R.connected_of_negativeCount_add_two_le (by omega)
  obtain ⟨hg,hparent⟩ := D.parent_twoComponentContext_of_cut
    (p := 1) (r := 3) hP hcut
  apply D.rotationRigid_of_translation _ hparent
  exact Q.twoComponentContext_rotationRigid R (hQDense.connected (by omega)) hR
    hQZ hRZ
    (Q.rotationRigid_of_nonnegative (hQDense.connected (by omega)) hQDense.nonnegative)
    (R.two_negative_rigidity hR hRCount)
    (fun hS => Q.endpointLeader_two hS)
    (fun hS => R.ten_four_core_endpointLeader hR hRZ hRCount hS)
    D.topMargin D.bottomMargin _ D.topMargin_pos D.bottomMargin_pos hg

/-- The actual `3+3` cofactor split has total internal negative budget one.
Both rigidity and fixed leaders are produced from its genuine three-row cores. -/
theorem ten_three_three_cut_rigidity (D : BetaDiagram 7) (hD : D.Connected)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D = 10)
    (hcut : D.row 4 < D.col 2) : D.RotationRigid := by
  let C := D.twoCutCore (p := 2) (r := 2) hP
  let Q := C.betaPrefix
  let R := C.suffix
  have hQZ : Q.ZeroFree := fun i j => hZ (i.castAdd 3).succ (j.castAdd 3).castSucc
  have hRZ : R.ZeroFree := fun i j => hZ (i.natAdd 3).succ (j.natAdd 3).castSucc
  have hbudget := C.negativeCount_at_cut (a := 3) (b := 3)
    (by omega) (by omega) hcut
  have hCountC : negativeCount C = 10 := by
    change negativeCount ((D.cornerDiagram hP).reindexOrder _) = 10
    rw [reindexOrder_negativeCount, D.corner_negativeCount]
    exact hCount
  rw [hCountC] at hbudget
  have hQCount : negativeCount Q ≤ 1 := by dsimp [Q]; omega
  have hRCount : negativeCount R ≤ 1 := by dsimp [R]; omega
  have hQ : Q.Connected := Q.connected_of_negativeCount_add_two_le (by omega)
  have hR : R.Connected := R.connected_of_negativeCount_add_two_le (by omega)
  obtain ⟨hg,hparent⟩ := D.parent_twoComponentContext_of_cut
    (p := 2) (r := 2) hP hcut
  apply D.rotationRigid_of_translation _ hparent
  exact Q.twoComponentContext_rotationRigid R hQ hR hQZ hRZ
    (Q.one_negative_rigidity hQ hQCount) (R.one_negative_rigidity hR hRCount)
    (fun hS => Q.ten_three_core_endpointLeader hQ hQZ hS)
    (fun hS => R.ten_three_core_endpointLeader hR hRZ hS)
    D.topMargin D.bottomMargin _ D.topMargin_pos D.bottomMargin_pos hg

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram

private theorem ten_exceptional_candidate (P : FiveExceptional.Parameters) (second : Bool)
    (Q : BetaDiagram 5) (h : FiveNegative.ExceptionalMember P second Q) :
    ∃ middle rotated, Q.TranslationEquivalent
      (FiveExceptional.coreCandidate P second middle rotated) := by
  rcases h with ht | ht
  · rcases ht with ht | hr
    · exact ⟨true,false,ht⟩
    · exact ⟨true,true,(Q.translation_rotate_iff_rotation (FiveExceptional.F P second)).mpr hr⟩
  · rcases ht with ht | hr
    · exact ⟨false,false,ht⟩
    · exact ⟨false,true,(Q.translation_rotate_iff_rotation (FiveExceptional.H P second)).mpr hr⟩

private theorem ten_candidate_parameter_strict (P : FiveExceptional.Parameters)
    (second middle rotated : Bool)
    (hZ : (FiveExceptional.coreCandidate P second middle rotated).ZeroFree) :
    P.q < P.b := by
  have hqb := P.q_le_b
  by_contra h
  have he : P.q = P.b := by omega
  have h43 := hZ 4 3
  have h10 := hZ 1 0
  cases second <;> cases middle <;> cases rotated <;>
    norm_num [FiveExceptional.coreCandidate, FiveExceptional.F, FiveExceptional.H,
      FiveExceptional.rows, FiveExceptional.fCols, FiveExceptional.hCols,
      rotate, Fin.rev, he] at h43 <;>
    norm_num [FiveExceptional.coreCandidate, FiveExceptional.F, FiveExceptional.H,
      FiveExceptional.rows, FiveExceptional.fCols, FiveExceptional.hCols,
      rotate, Fin.rev, he] at h10

/-- The genuine singleton-first seven-row source with a connected five-row
child is rigid or an actual member of one displayed ten-negative family. -/
theorem ten_singleton_connected_core_classification (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hcut : D.row 2 < D.col 0)
    (hQ : (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)).tail.Connected) :
    D.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
  classical
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C := D.cornerDiagram hP
  let Q := C.tail
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  have hCountQ : negativeCount Q = 5 := by
    have h := FiveExceptional.singleton_cut_negative_count C hcut
    rw [D.corner_negativeCount hP] at h
    dsimp [Q]
    omega
  obtain ⟨s,u,v,g,hs,hu,hv,hg,hParent⟩ := D.singleton_parent_of_first_cut hP hcut
  by_cases hex : ∃ P second, FiveNegative.ExceptionalMember P second Q
  · obtain ⟨P,second,hmem⟩ := hex
    obtain ⟨middle,rotated,hCore⟩ := ten_exceptional_candidate P second Q hmem
    let R := FiveExceptional.coreCandidate P second middle rotated
    have hR : R.Connected := FiveExceptional.coreCandidate_connected P second middle rotated
    have hRZ : R.ZeroFree := Q.zeroFree_of_schur_eq R hQ hR hQZ hCore.schur_eq
    have hp : P.q < P.b := ten_candidate_parameter_strict P second middle rotated hRZ
    have hCtx := Q.singletonContext_translation R hCore s u v g hs hu hv hg
    have hDR := ten_translation_trans hParent hCtx
    by_cases hRigid : (R.singletonContext s u v g hs hu hv hg).RotationRigid
    · exact Or.inl (D.rotationRigid_of_translation _ hDR hRigid)
    · obtain ⟨T,familyB,other,hT⟩ :=
        FiveExceptional.nonrigid_singleton_is_ten_family P hp second middle rotated
          s u v g hs hu hv hg hRigid
      exact Or.inr ⟨T,familyB,other,rfl,Or.inl (ten_translation_trans hDR hT)⟩
  · have hQRigid := FiveNegative.five_base_rotation_rigid Q hQ hCountQ hex
    exact Or.inl (D.rotationRigid_of_translation _ hParent
      (Q.singleton_five_rotationRigid hQ hQZ hCountQ hQRigid s u v g hs hu hv hg))

private theorem ten_singleton_count_zero (Q : BetaDiagram 1) : negativeCount Q = 0 := by
  have h := Q.row_nonempty 0
  rw [Q.negativeCount_eq_cell_sum]
  simp only [Fin.sum_univ_one, not_lt_of_ge h.le, if_false]

private theorem ten_singleton_schur (Q : BetaDiagram 1) :
    Q.schur = complete (Q.row 0-Q.col 0) := by
  simp [schur, matrix, Matrix.det_fin_one]

private theorem ten_one_suffix_eq_tail (C : BetaDiagram 6) :
    C.suffix (a := 1) (b := 5) = C.tail := by
  apply ten_diagram_ext
  · funext i
    change C.row (i.natAdd 1) = C.row i.succ
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_succ]
    omega
  · funext i
    change C.col (i.natAdd 1) = C.col i.succ
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_succ]
    omega

private theorem ten_first_cut_schur (C : BetaDiagram 5)
    (hcut : C.row 1 < C.col 0) :
    C.schur = complete (C.row 0-C.col 0) * (C.suffix (a := 1) (b := 4)).schur := by
  have h := C.schur_factor_at_cut (a := 1) (b := 4) (by omega) (by omega) hcut
  rw [ten_singleton_schur] at h
  exact h

private theorem ten_six_first_cut_schur (C : BetaDiagram 6)
    (hcut : C.row 1 < C.col 0) :
    C.schur = complete (C.row 0-C.col 0) * C.tail.schur := by
  have h := C.schur_factor_at_cut (a := 1) (b := 5) (by omega) (by omega) hcut
  rw [ten_singleton_schur, ten_one_suffix_eq_tail] at h
  exact h

private theorem ten_last_cut_schur {n : ℕ} (C : BetaDiagram (n+2))
    (hcut : C.row (Fin.last (n+1)) < C.col ⟨n,by omega⟩) :
    C.schur = (C.betaPrefix (a := n+1) (b := 1)).schur *
      complete (C.row (Fin.last (n+1))-C.col (Fin.last (n+1))) := by
  have h := C.schur_factor_at_cut (a := n+1) (b := 1) (by omega) (by omega) hcut
  rw [ten_singleton_schur] at h
  exact h

/-- A disconnected five-row tail in the actual first-cut source produces the
one-negative four-row component and both positive singleton factors. -/
theorem ten_singleton_disconnected_core_data (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hcut : D.row 2 < D.col 0)
    (hQ : ¬ (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)).tail.Connected) :
    ∃ (R : BetaDiagram 4) (ell m : ℤ), R.Connected ∧ R.ZeroFree ∧
      negativeCount R = 1 ∧ 0 < ell ∧ 0 < m ∧
      D.cornerPolynomial = complete ell * complete m * R.schur := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C := D.cornerDiagram hP
  let Q := C.tail
  let ell := C.row 0-C.col 0
  have hell : 0 < ell := sub_pos.mpr (C.row_nonempty 0)
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  have hCountQ : negativeCount Q = 5 := by
    have h := FiveExceptional.singleton_cut_negative_count C hcut
    rw [D.corner_negativeCount hP] at h
    dsimp [Q]
    omega
  have hfacC : D.cornerPolynomial = complete ell * Q.schur := by
    have h := ten_six_first_cut_schur C hcut
    exact (D.cornerDiagram_schur hP).symm.trans h
  obtain ⟨i,hi,hcutQ⟩ := Q.exists_negative_cut (by omega) hQ
  have hrect := Q.cut_rectangle_le_negativeCount i hi hcutQ
  rw [hCountQ] at hrect
  fin_cases i
  · let T := Q.betaPrefix (a := 1) (b := 4)
    let R := Q.suffix (a := 1) (b := 4)
    let m := T.row 0-T.col 0
    have hm : 0 < m := sub_pos.mpr (T.row_nonempty 0)
    have hbudget := Q.negativeCount_at_cut (a := 1) (b := 4)
      (by omega) (by omega) hcutQ
    have hRCount : negativeCount R = 1 := by
      rw [hCountQ, ten_singleton_count_zero] at hbudget
      dsimp [R]
      omega
    have hR : R.Connected := R.connected_of_negativeCount_add_two_le (by omega)
    have hRZ : R.ZeroFree := fun a b => hQZ (a.natAdd 1) (b.natAdd 1)
    have hfac := ten_first_cut_schur Q hcutQ
    refine ⟨R,ell,m,hR,hRZ,hRCount,hell,hm,?_⟩
    rw [hfacC,hfac]
    change complete ell * (complete m * R.schur) = complete ell * complete m * R.schur
    ring
  · norm_num at hrect
  · norm_num at hrect
  · let R := Q.betaPrefix (a := 4) (b := 1)
    let T := Q.suffix (a := 4) (b := 1)
    let m := T.row 0-T.col 0
    have hm : 0 < m := sub_pos.mpr (T.row_nonempty 0)
    have hbudget := Q.negativeCount_at_cut (a := 4) (b := 1)
      (by omega) (by omega) hcutQ
    have hRCount : negativeCount R = 1 := by
      rw [hCountQ, ten_singleton_count_zero] at hbudget
      dsimp [R]
      omega
    have hR : R.Connected := R.connected_of_negativeCount_add_two_le (by omega)
    have hRZ : R.ZeroFree := fun a b => hQZ (a.castAdd 1) (b.castAdd 1)
    have hfac := ten_last_cut_schur Q hcutQ
    refine ⟨R,ell,m,hR,hRZ,hRCount,hell,hm,?_⟩
    rw [hfacC,hfac]
    change complete ell * (R.schur * complete m) = complete ell * complete m * R.schur
    ring
  · norm_num at hi

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.BetaDiagram

/-- The arbitrary-row motion relation is symmetric, with its order equality
transported rather than assumed. -/
theorem ten_motion_symm {n m : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    (h : D.MotionEquivalent E) : E.MotionEquivalent D := by
  obtain ⟨hn,hm⟩ := h
  cases hn
  refine ⟨rfl, ?_⟩
  apply motion_symm D E
  simpa only [castOrder] using hm

/-- Motion composes through the actual equalities of full row count. -/
theorem ten_motion_trans {n m r : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    {F : BetaDiagram r} (hDE : D.MotionEquivalent E) (hEF : E.MotionEquivalent F) :
    D.MotionEquivalent F := by
  obtain ⟨hn,hm⟩ := hDE
  obtain ⟨hr,hf⟩ := hEF
  cases hn
  cases hr
  refine ⟨rfl, ?_⟩
  apply motion_trans D E F
  · simpa only [castOrder] using hm
  · simpa only [castOrder] using hf

/-- The literal half-turn is always in the original full-board motion class. -/
theorem ten_motion_rotate {n : ℕ} (D : BetaDiagram n) : D.MotionEquivalent D.rotate := by
  refine ⟨rfl, Or.inr ?_⟩
  apply (D.rotation_rotate_iff_translation D).mpr
  exact ⟨0,fun i => by simp,fun i => by simp⟩

/-- Exceptional membership in the actual families is preserved and reflected
by Gamma, with the inverse parameters produced from the original beta lists. -/
theorem ten_exceptional_gamma_iff (D : BetaDiagram 7) :
    (∃ P : TenParameters, ∃ familyB other,
      D.gamma.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other))) ↔
    (∃ P : TenParameters, ∃ familyB other,
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other))) := by
  constructor
  · rintro ⟨P,familyB,other,hm⟩
    obtain ⟨Q,_,hQ⟩ := P.parameters_of_gamma_motion D _ hm
    exact ⟨Q,familyB,other,hQ⟩
  · rintro ⟨P,familyB,other,hn,hm⟩
    have hh : hn = rfl := Subsingleton.elim _ _
    rw [hh] at hm
    simp only [castOrder] at hm
    refine ⟨P.gammaParameters,familyB,other,rfl,?_⟩
    rw [← P.gamma_diagram]
    rcases hm with ht | hr
    · exact Or.inl ((D.gamma_translation_iff (P.diagram _)).mpr ht)
    · exact Or.inr ((D.gamma_rotation_iff (P.diagram _)).mpr hr)

/-- An actual member of a displayed family cannot be rotation-rigid at any
initial row count. -/
theorem not_rotationRigid_of_ten_exceptional {n : ℕ} (D : BetaDiagram n)
    (hex : ∃ P : TenParameters, ∃ familyB other,
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other))) :
    ¬ D.RotationRigid := by
  obtain ⟨P,familyB,other,hm⟩ := hex
  let F := P.diagram (TenParameters.pairKind familyB other)
  have hfunc : D.schur = F.schur := ten_motion_schur_eq hm
  intro hRigid
  apply P.not_rotationRigid familyB other
  intro m E hE he
  have hDE : D.MotionEquivalent E := hRigid m E hE (he.trans hfunc.symm)
  exact ten_motion_trans (ten_motion_symm hm) hDE

/-- Once the actual source is identified with a displayed family, its complete
full-board class contains exactly the four translation classes of that family. -/
theorem ten_complete_exceptional_class {n m : ℕ} (D : BetaDiagram n)
    (P : TenParameters) (familyB other : Bool)
    (hD : D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)))
    (E : BetaDiagram m) :
    E.schur = D.schur ↔ ∃ mate,
      (P.diagram (TenParameters.pairKind familyB mate)).MotionEquivalent E := by
  have hfunc := ten_motion_schur_eq hD
  constructor
  · intro he
    exact (P.full_class familyB other E).mp (hfunc.symm.trans he.symm)
  · intro hclass
    have he := (P.full_class familyB other E).mpr hclass
    exact he.symm.trans hfunc.symm

/-- The actual singleton-first source is classified without prescribing whether
its five-row remainder is connected or supplying a placement certificate. -/
theorem ten_singleton_first_cut_classification (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hcut : D.row 2 < D.col 0) :
    D.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
  classical
  by_cases hQ : (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)).tail.Connected
  · exact D.ten_singleton_connected_core_classification hD hZ hCount hcut hQ
  · obtain ⟨R,ell,m,hR,hRZ,hRCount,hℓ,hm,hcof⟩ :=
      D.ten_singleton_disconnected_core_data hD hZ hCount hcut hQ
    exact Or.inl (D.three_component_cofactor_rotationRigid hD hZ R
      (Or.inr ⟨hR,hRZ,hRCount⟩) ell m hℓ hm hcof)

/-- `prop:ten-negative-base`: every zero-free source at the actual minimum
seven-row order is rigid or belongs to one of the displayed actual families.
All cofactor cuts, component budgets, and context parameters are produced. -/
theorem ten_seven_zeroFree_classification (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) :
    D.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
  classical
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  have hdis : ¬ (D.cornerDiagram hP).Connected :=
    (D.corner_disconnected_iff_minimum hD hP).mpr hMin.symm
  have twoFour (F : BetaDiagram 7) (hF : F.Connected) (hFZ : F.ZeroFree)
      (hFCount : negativeCount F = 10) (hFP : F.PositiveCorner)
      (hcut : F.row 3 < F.col 1) :
      F.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
        F.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
    by_cases hFirst : F.row 2 < F.col 0
    · exact F.ten_singleton_first_cut_classification hF hFZ hFCount hFirst
    · exact Or.inl (F.ten_two_four_cut_rigidity hF hFZ hFP hFCount hcut hFirst)
  have rotateBack
      (h : D.rotate.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
        D.rotate.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other))) :
      D.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
        D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
    rcases h with hR | ⟨P,familyB,other,hm⟩
    · exact Or.inl (D.rotationRigid_of_rotate hR)
    · exact Or.inr ⟨P,familyB,other,ten_motion_trans (ten_motion_rotate D) hm⟩
  have hDR := D.rotate_connected hD
  have hDZR := D.rotate_zeroFree hZ
  have hCountR : negativeCount D.rotate = 10 := by
    rw [← D.negativeCount_eq_of_schur_eq D.rotate D.rotate_schur.symm]
    exact hCount
  rcases D.threshold_seven_cut_alternatives hP hdis with
    hFirst | hTwoFour | hThreeThree | hRotTwoFour | hRotFirst
  · exact D.ten_singleton_first_cut_classification hD hZ hCount hFirst
  · exact twoFour D hD hZ hCount hP hTwoFour
  · exact Or.inl (D.ten_three_three_cut_rigidity hD hZ hP hCount hThreeThree)
  · exact rotateBack (twoFour D.rotate hDR hDZR hCountR
      (D.rotate_positiveCorner hP) hRotTwoFour)
  · exact rotateBack (D.rotate.ten_singleton_first_cut_classification
      hDR hDZR hCountR hRotFirst)

/-- The seven-row source classification descends faithfully to full boards,
retaining units and deriving the inverse exceptional parameters. -/
theorem ten_seven_classification (D : BetaDiagram 7) (hD : D.Connected)
    (hCount : negativeCount D = 10)
    (hMin : minimumRealizingRows (negativePartition D) = 7) :
    D.RotationRigid ∨ ∃ P : TenParameters, ∃ familyB other,
      D.MotionEquivalent (P.diagram (TenParameters.pairKind familyB other)) := by
  have hG := (D.gamma_connected_iff).mpr hD
  have hGCount : negativeCount D.gamma = 10 := by
    rw [D.gamma_negativeCount]
    exact hCount
  have hGMin : minimumRealizingRows (negativePartition D.gamma) = 7 := by
    rw [D.gamma_negative_partition]
    exact hMin
  rcases D.gamma.ten_seven_zeroFree_classification hG D.gamma_zeroFree hGCount hGMin
    with hRigid | hExceptional
  · exact Or.inl (D.gamma_rigidity_descends hD hRigid)
  · exact Or.inr ((D.ten_exceptional_gamma_iff).mp hExceptional)

end SkewJacobiNegative.BetaDiagram
