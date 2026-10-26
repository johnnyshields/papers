/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.RestorationComponents
import SkewCofactorIndependence.BetaBridge
import SkewCofactorIndependence.NonnegativeRigidity
import SkewCofactorIndependence.DilationGeometry

/-!
# Independent restorations against arbitrary connected mates

The residual-core, sign-alignment, coordinate-transport, and unit-independence
assembly for `cor:independent-restorations` of
`shields-2026-skew-cofactor-independence.tex`.
-/

namespace SkewCofactorIndependence

open scoped BigOperators
open BetaEndpointCounts

/-- A common positive finite-alphabet specialization for comparing deletion signs. -/
noncomputable def positiveSpecialization (b : ℕ) : CompleteRing →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ)
    (fun k => Shields.completeHom b (k : ℕ) (fun _ => (1 : ℝ)))

theorem positiveSpecialization_integerLift (b : ℕ) (p : Base.CompleteRing) :
    positiveSpecialization b (integerLift p) =
      Base.tableauSpecialization b (fun _ => (1 : ℝ)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [positiveSpecialization, integerLift, Base.tableauSpecialization, Base.specialize]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    rw [integerLift, MvPolynomial.map_X]
    change MvPolynomial.eval₂Hom (Rat.castHom ℝ)
        (fun j : ℕ+ => Shields.completeHom b (j : ℕ) (fun _ => (1 : ℝ)))
        (MvPolynomial.X k) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
        (fun j : ℕ+ => Shields.completeHom b (j : ℕ) (fun _ => (1 : ℝ)))
        (MvPolynomial.X k)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

namespace BetaDiagram

variable {n k a : ℕ}

theorem positiveSpecialization_schur_pos (D : BetaDiagram n) (hn : 0 < n)
    (b : ℕ) (hb : n ≤ b) : 0 < positiveSpecialization b D.schur := by
  rw [← D.toDiagram_schur hn, positiveSpecialization_integerLift,
    Base.Diagram.tableauSpecialization_schurFunction]
  apply Shields.skewSchur_pos (by intro i hi; norm_num)
  intro j
  apply le_trans (Nat.sub_le _ _) (le_trans ?_ hb)
  by_contra hh
  have hc : (n, j) ∈ (D.toDiagram hn).outerShape :=
    YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hh)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hz := Base.boundaryShape_rowLen_outside (D.toDiagram hn).outer
    (D.toDiagram hn).outer_antitone n le_rfl
  change (D.toDiagram hn).outerShape.rowLen n = 0 at hz
  omega

/-- Opposite signed residual polynomials cannot agree: both have a common positive
specialization. -/
theorem align_deletion_signs (C : BetaDiagram (k + 1)) (E : BetaDiagram (a + 1))
    (u v : ℤˣ)
    (he : ((u : ℤ) : CompleteRing) * C.schur =
      ((v : ℤ) : CompleteRing) * E.schur) :
    u = v ∧ C.schur = E.schur := by
  have hp := C.positiveSpecialization_schur_pos (by omega) (k + a + 2) (by omega)
  have hq := E.positiveSpecialization_schur_pos (by omega) (k + a + 2) (by omega)
  have hv := congrArg (positiveSpecialization (k + a + 2)) he
  have hu : u = v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · rfl
    · simp only [Units.val_one, Units.val_neg,
        Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hv
      simp only [map_neg] at hv
      exfalso
      linarith
    · simp only [Units.val_one, Units.val_neg,
        Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hv
      simp only [map_neg] at hv
      exfalso
      linarith
    · rfl
  refine ⟨hu, ?_⟩
  rw [← hu] at he
  rcases Int.units_eq_one_or u with rfl | rfl <;> simpa using he

theorem restore_coeff_below (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions)
    (d : ℕ) (hd : d < k + 1) :
    ordinaryComponent (C.restore hC hZero Z hZ).schur d = 0 :=
  C.restoration_coeff_below hZero Z (C.available_disjoint_rows Z hZ)
    (C.available_disjoint_cols Z hZ) _ (C.restore_rowSet hC hZero Z hZ)
    (C.restore_colSet hC hZero Z hZ) d hd

theorem restore_lowest_nonzero (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    ordinaryComponent (C.restore hC hZero Z hZ).schur (k + 1) ≠ 0 :=
  C.restoration_lowest_nonzero hZero Z (C.available_disjoint_rows Z hZ)
    (C.available_disjoint_cols Z hZ) _ (C.restore_rowSet hC hZero Z hZ)
    (C.restore_colSet hC hZero Z hZ)

/-- Lowest ordinary degree recovers the actual residual order of an unknown realization. -/
theorem restoration_core_order (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions)
    (E : BetaDiagram (a + 1)) (hE : E.Connected) (hEZero : E.ZeroFree)
    (W : Finset ℤ) (hW : W ⊆ E.availablePositions)
    (he : (C.restore hC hZero Z hZ).schur = (E.restore hE hEZero W hW).schur) :
    k = a := by
  rcases lt_trichotomy k a with h | h | h
  · have hz := E.restore_coeff_below hE hEZero W hW (k + 1) (by omega)
    rw [← he] at hz
    exact False.elim (C.restore_lowest_nonzero hC hZero Z hZ hz)
  · exact h
  · have hz := C.restore_coeff_below hC hZero Z hZ (a + 1) (by omega)
    rw [he] at hz
    exact False.elim (E.restore_lowest_nonzero hE hEZero W hW hz)

/-- After order recovery, positivity removes the deletion signs. -/
theorem restoration_core_polynomial (C E : BetaDiagram (k + 1))
    (hC : C.Connected) (hZero : C.ZeroFree) (Z : Finset ℤ)
    (hZ : Z ⊆ C.availablePositions) (hE : E.Connected) (hEZero : E.ZeroFree)
    (W : Finset ℤ) (hW : W ⊆ E.availablePositions)
    (he : (C.restore hC hZero Z hZ).schur = (E.restore hE hEZero W hW).schur) :
    C.schur = E.schur := by
  have hc := (C.restore_first_coefficients hC hZero Z hZ).1
  have hd := (E.restore_first_coefficients hE hEZero W hW).1
  have hm := congrArg (fun p => ordinaryComponent p (k + 1)) he
  rw [hc, hd] at hm
  exact (C.align_deletion_signs E _ _ hm).2

/-- Indicators live on the exact available-position subtype. -/
noncomputable def restorationIndicator (C : BetaDiagram (k + 1)) (Z : Finset ℤ) :
    C.Available → ℚ := fun z => if z.val ∈ Z then 1 else 0

theorem relationMap_indicator (C : BetaDiagram (k + 1)) (Z : Finset ℤ)
    (hZ : Z ⊆ C.availablePositions) :
    C.unitRelationMap (C.restorationIndicator Z) = ∑ z ∈ Z, C.unitVariation z := by
  classical
  change (∑ z : C.Available, (if z.val ∈ Z then (1 : ℚ) else 0) • C.unitVariation z.val) = _
  simp only [ite_smul, one_smul, zero_smul, ← Finset.sum_filter]
  apply Finset.sum_bij (fun z hz => z.val)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz w hw he
    exact Subtype.ext he
  · intro z hz
    refine ⟨⟨z, hZ hz⟩, ?_, rfl⟩
    simp [hz]
  · intro z hz
    rfl

theorem independent_units_determine_set (C : BetaDiagram (k + 1))
    (hKernel : C.unitKernel = ⊥) (Z W : Finset ℤ)
    (hZ : Z ⊆ C.availablePositions) (hW : W ⊆ C.availablePositions)
    (he : (∑ z ∈ Z, C.unitVariation z) = ∑ z ∈ W, C.unitVariation z) : Z = W := by
  classical
  have hm : C.restorationIndicator Z - C.restorationIndicator W ∈ C.unitKernel := by
    change C.unitRelationMap (C.restorationIndicator Z - C.restorationIndicator W) = 0
    rw [map_sub, C.relationMap_indicator Z hZ, C.relationMap_indicator W hW, he, sub_self]
  rw [hKernel, Submodule.mem_bot] at hm
  have hi : C.restorationIndicator Z = C.restorationIndicator W := sub_eq_zero.mp hm
  ext z
  by_cases hz : z ∈ C.availablePositions
  · have hv := congrFun hi ⟨z, hz⟩
    dsimp [restorationIndicator] at hv
    split_ifs at hv <;> simp_all
  · have hnZ : z ∉ Z := fun h => hz (hZ h)
    have hnW : z ∉ W := fun h => hz (hW h)
    simp [hnZ, hnW]

/-- On one literal core, equality of two full restorations forces identical common sets. -/
theorem same_core_restoration (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (hKernel : C.unitKernel = ⊥)
    (Z W : Finset ℤ) (hZ : Z ⊆ C.availablePositions) (hW : W ⊆ C.availablePositions)
    (he : (C.restore hC hZero Z hZ).schur = (C.restore hC hZero W hW).schur) : Z = W := by
  have hz := C.restore_first_coefficients hC hZero Z hZ
  have hw := C.restore_first_coefficients hC hZero W hW
  have hlow := congrArg (fun p => ordinaryComponent p (k + 1)) he
  rw [hz.1, hw.1] at hlow
  have hsign := (C.align_deletion_signs C _ _ hlow).1
  have hnext := congrArg (fun p => ordinaryComponent p (k + 2)) he
  rw [hz.2, hw.2, hsign] at hnext
  apply C.independent_units_determine_set hKernel Z W hZ hW
  rcases Int.units_eq_one_or
    (C.deletionSign W (C.available_disjoint_rows W hW) (C.available_disjoint_cols W hW)
      (C.restore hC hZero W hW) (C.restore_rowSet hC hZero W hW)
      (C.restore_colSet hC hZero W hW)) with hu | hu <;>
    simp only [hu, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg,
      neg_one_mul, neg_neg, one_mul] at hnext
  · exact neg_injective hnext
  · exact hnext

theorem translation_of_sets (D E : BetaDiagram n) (c : ℤ)
    (hr : D.rowSet = E.rowSet.image (fun x => x + c))
    (hc : D.colSet = E.colSet.image (fun x => x + c)) : D.TranslationEquivalent E := by
  classical
  have er : D.row = fun i => E.row i + c := by
    apply strictAnti_eq_of_image _ _ D.row_strictAnti
      (by intro i j hij; have := E.row_strictAnti hij; dsimp; omega)
    simpa [rowSet, Finset.image_image, Function.comp_def] using hr
  have ec : D.col = fun i => E.col i + c := by
    apply strictAnti_eq_of_image _ _ D.col_strictAnti
      (by intro i j hij; have := E.col_strictAnti hij; dsimp; omega)
    simpa [colSet, Finset.image_image, Function.comp_def] using hc
  exact ⟨c, congrFun er, congrFun ec⟩

theorem rotation_of_sets (D E : BetaDiagram n) (c : ℤ)
    (hr : D.rowSet = E.colSet.image (fun x => c - x))
    (hc : D.colSet = E.rowSet.image (fun x => c - x)) : D.RotationEquivalent E := by
  classical
  have rev_image (f : Fin n → ℤ) : Finset.univ.image (fun i : Fin n => f i.rev) =
      Finset.univ.image f := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i.rev, hi⟩,
      fun ⟨i, hi⟩ => ⟨i.rev, by simpa using hi⟩⟩
  have er : D.row = fun i => c - E.col i.rev := by
    apply strictAnti_eq_of_image _ _ D.row_strictAnti
      (by intro i j hij; have := E.col_strictAnti (Fin.rev_strictAnti hij); dsimp; omega)
    calc
      _ = Finset.univ.image (fun i => c - E.col i) := by
        simpa only [rowSet, colSet, Finset.image_image, Function.comp_def] using hr
      _ = _ := (rev_image (fun i => c - E.col i)).symm
  have ec : D.col = fun i => c - E.row i.rev := by
    apply strictAnti_eq_of_image _ _ D.col_strictAnti
      (by intro i j hij; have := E.row_strictAnti (Fin.rev_strictAnti hij); dsimp; omega)
    calc
      _ = Finset.univ.image (fun i => c - E.row i) := by
        simpa only [rowSet, colSet, Finset.image_image, Function.comp_def] using hc
      _ = _ := (rev_image (fun i => c - E.row i)).symm
  exact ⟨c, congrFun er, congrFun ec⟩

theorem RotationEquivalent.schur_eq {D E : BetaDiagram n} (h : D.RotationEquivalent E) :
    D.schur = E.schur :=
  ((D.translation_rotate_iff_rotation E).mpr h).schur_eq.trans E.rotate_schur

/-- Translates a restored set and supplies every available-coordinate side condition. -/
theorem available_image_translation (C E : BetaDiagram (k + 1))
    (c : ℤ) (hr : ∀ i, C.row i = E.row i + c) (hc : ∀ i, C.col i = E.col i + c)
    (W : Finset ℤ) (hW : W ⊆ E.availablePositions) :
    W.image (fun z => z + c) ⊆ C.availablePositions := by
  classical
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have h := (E.mem_availablePositions_sets_iff z).mp (hW hz)
  rw [C.mem_availablePositions_sets_iff, hr 0, hc (Fin.last k)]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    apply h.2.2.1
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    have hh := hr i
    omega
  · intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    apply h.2.2.2
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    have hh := hc i
    omega

theorem available_image_rotation (C E : BetaDiagram (k + 1))
    (c : ℤ) (hr : ∀ i, C.row i = c - E.col i.rev)
    (hc : ∀ i, C.col i = c - E.row i.rev)
    (W : Finset ℤ) (hW : W ⊆ E.availablePositions) :
    W.image (fun z => c - z) ⊆ C.availablePositions := by
  classical
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have h := (E.mem_availablePositions_sets_iff z).mp (hW hz)
  rw [C.mem_availablePositions_sets_iff, hr 0, hc (Fin.last k)]
  simp only [Fin.rev_zero, Fin.rev_last]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    apply h.2.2.2
    refine Finset.mem_image.mpr ⟨i.rev, Finset.mem_univ _, ?_⟩
    have hh := hr i
    omega
  · intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    apply h.2.2.1
    refine Finset.mem_image.mpr ⟨i.rev, Finset.mem_univ _, ?_⟩
    have hh := hc i
    omega

/-- Core motions lift to the full literal restorations, with no hypothesis on a mate's shape. -/
theorem restoration_transport (C E : BetaDiagram (k + 1))
    (hC : C.Connected) (hZero : C.ZeroFree) (hE : E.Connected) (hEZero : E.ZeroFree)
    (W : Finset ℤ) (hW : W ⊆ E.availablePositions)
    (hmotion : C.TranslationEquivalent E ∨ C.RotationEquivalent E) :
    ∃ (V : Finset ℤ) (hV : V ⊆ C.availablePositions)
      (hcard : k + 1 + V.card = k + 1 + W.card),
      ((C.restore hC hZero V hV).castOrder hcard).TranslationEquivalent
        (E.restore hE hEZero W hW) ∨
      ((C.restore hC hZero V hV).castOrder hcard).RotationEquivalent
        (E.restore hE hEZero W hW) := by
  classical
  rcases hmotion with ⟨c, hr, hc⟩ | ⟨c, hr, hc⟩
  · let V := W.image (fun z => z + c)
    have hV := C.available_image_translation E c hr hc W hW
    have hcard : k + 1 + V.card = k + 1 + W.card := by
      dsimp [V]
      have hinj : Function.Injective (fun z : ℤ => z + c) := by
        intro x y he
        change x + c = y + c at he
        omega
      rw [Finset.card_image_of_injective _ hinj]
    refine ⟨V, hV, hcard, Or.inl ?_⟩
    apply translation_of_sets _ _ c
    · rw [castOrder_rowSet, restore_rowSet, restore_rowSet, Finset.image_union]
      congr 1
      simp only [rowSet, Finset.image_image, Function.comp_def]
      congr 1
      funext i
      exact hr i
    · rw [castOrder_colSet, restore_colSet, restore_colSet, Finset.image_union]
      congr 1
      simp only [colSet, Finset.image_image, Function.comp_def]
      congr 1
      funext i
      exact hc i
  · let V := W.image (fun z => c - z)
    have hV := C.available_image_rotation E c hr hc W hW
    have hcard : k + 1 + V.card = k + 1 + W.card := by
      dsimp [V]
      have hinj : Function.Injective (fun z : ℤ => c - z) := by
        intro x y he
        change c - x = c - y at he
        omega
      rw [Finset.card_image_of_injective _ hinj]
    refine ⟨V, hV, hcard, Or.inr ?_⟩
    apply rotation_of_sets _ _ c
    · rw [castOrder_rowSet, restore_rowSet, restore_colSet, Finset.image_union]
      congr 1
      apply Finset.ext
      intro z
      simp only [rowSet, colSet, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨E.col i.rev, ⟨i.rev, rfl⟩, (hr i).symm⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.rev, by simpa using hr i.rev⟩
    · rw [castOrder_colSet, restore_colSet, restore_rowSet, Finset.image_union]
      congr 1
      apply Finset.ext
      intro z
      simp only [rowSet, colSet, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨E.row i.rev, ⟨i.rev, rfl⟩, (hc i).symm⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.rev, by simpa using hc i.rev⟩

/-- Composing finite-order casts only composes their proofs of equality. -/
theorem castOrder_trans {a b c : ℕ} (D : BetaDiagram a) (hab : a = b) (hbc : b = c) :
    (D.castOrder hab).castOrder hbc = D.castOrder (hab.trans hbc) := by
  cases hab
  cases hbc
  rfl

/-- `cor:independent-restorations`: the unknown connected diagram is arbitrary. -/
theorem independent_restorations (C : BetaDiagram (k + 1)) (hDense : C.Dense)
    (hKernel : C.unitKernel = ⊥) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions)
    {m : ℕ} (D : BetaDiagram m) (hD : D.Connected)
    (hEq : D.schur = (C.restore (hDense.connected (by omega)) hDense.zeroFree Z hZ).schur) :
    ∃ horder : k + 1 + Z.card = m,
      TranslationEquivalent
        ((C.restore (hDense.connected (by omega)) hDense.zeroFree Z hZ).castOrder horder) D ∨
      RotationEquivalent
        ((C.restore (hDense.connected (by omega)) hDense.zeroFree Z hZ).castOrder horder) D := by
  let hC := hDense.connected (by omega)
  let hZero := hDense.zeroFree
  obtain ⟨a, E, hE, hEZero, W, hW, hfull, hreal⟩ := D.exists_restoration hD
  have he : (C.restore hC hZero Z hZ).schur = (E.restore hE hEZero W hW).schur := by
    rw [← castOrder_schur _ hfull, hreal]
    exact hEq.symm
  have hcoreorder := C.restoration_core_order hC hZero Z hZ E hE hEZero W hW he
  subst a
  have hcore := C.restoration_core_polynomial E hC hZero Z hZ hE hEZero W hW he
  have hmotion := C.nonnegative_rigidity_same_order E hC hE hDense.nonnegative hcore
  obtain ⟨V, hV, hcard, htransport⟩ := C.restoration_transport E hC hZero hE hEZero W hW hmotion
  have hVeq : (C.restore hC hZero V hV).schur = (E.restore hE hEZero W hW).schur := by
    rw [← castOrder_schur _ hcard]
    rcases htransport with ht | hr
    · exact ht.schur_eq
    · exact hr.schur_eq
  have hsets := C.same_core_restoration hC hZero hKernel Z V hZ hV (he.trans hVeq.symm)
  subst V
  refine ⟨hcard.trans hfull, ?_⟩
  have hcast := castOrder_trans (C.restore hC hZero Z hZ) hcard hfull
  rw [← hcast, ← hreal]
  cases hfull
  exact htransport

end BetaDiagram
end SkewCofactorIndependence
